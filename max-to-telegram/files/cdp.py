# -*- coding: utf-8 -*-
"""
Минимальный клиент Chrome DevTools Protocol поверх собственного WebSocket.
Только стандартная библиотека Python. Нужен, чтобы внедрить хук веб-сокета MAX
в Edge через --remote-debugging-port (Edge 154 не грузит распакованные расширения).

WS(url)      — сырой клиент WebSocket (ws://127.0.0.1:port/...).
CDP(url)     — поверх WS: call(method, params) синхронно, on_event для событий.
http_targets(port) — список целей отладки (вкладок) с webSocketDebuggerUrl.
"""
import base64, json, os, socket, struct, threading, time, urllib.request


def http_targets(port, host="127.0.0.1"):
    with urllib.request.urlopen(f"http://{host}:{port}/json/list", timeout=10) as r:
        return json.loads(r.read().decode("utf-8", "replace"))


def http_version(port, host="127.0.0.1"):
    with urllib.request.urlopen(f"http://{host}:{port}/json/version", timeout=10) as r:
        return json.loads(r.read().decode("utf-8", "replace"))


class WS:
    """Клиентский WebSocket на сокете: text-кадры с маскировкой, сборка фрагментов,
    ответ pong на ping. Достаточно для CDP (JSON text-кадры)."""

    def __init__(self, url, timeout=15):
        assert url.startswith("ws://"), url
        rest = url[5:]
        hostport, _, path = rest.partition("/")
        path = "/" + path
        host, _, port = hostport.partition(":")
        port = int(port or 80)
        self.sock = socket.create_connection((host, port), timeout=timeout)
        self.sock.settimeout(timeout)
        self._buf = b""
        self._wlock = threading.Lock()
        key = base64.b64encode(os.urandom(16)).decode()
        req = ("GET %s HTTP/1.1\r\nHost: %s:%d\r\nUpgrade: websocket\r\n"
               "Connection: Upgrade\r\nSec-WebSocket-Key: %s\r\n"
               "Sec-WebSocket-Version: 13\r\n\r\n") % (path, host, port, key)
        self.sock.sendall(req.encode())
        head = self._read_until(b"\r\n\r\n")
        if b" 101 " not in head.split(b"\r\n", 1)[0]:
            raise ConnectionError("WS handshake: " + head.split(b"\r\n", 1)[0].decode("latin1"))
        # дальше читаем блокирующе: на «тихой» вкладке recv не должен падать по таймауту
        self.sock.settimeout(None)

    # -- низкий уровень чтения --
    def _recv_some(self):
        d = self.sock.recv(65536)
        if not d:
            raise ConnectionError("socket closed")
        self._buf += d

    def _read(self, n):
        while len(self._buf) < n:
            self._recv_some()
        d, self._buf = self._buf[:n], self._buf[n:]
        return d

    def _read_until(self, sep):
        while sep not in self._buf:
            self._recv_some()
        i = self._buf.index(sep) + len(sep)
        d, self._buf = self._buf[:i], self._buf[i:]
        return d

    # -- кадры --
    def _send_frame(self, opcode, payload=b""):
        n = len(payload)
        hdr = bytearray([0x80 | opcode])
        if n < 126:
            hdr.append(0x80 | n)
        elif n < 65536:
            hdr.append(0x80 | 126); hdr += struct.pack(">H", n)
        else:
            hdr.append(0x80 | 127); hdr += struct.pack(">Q", n)
        mask = os.urandom(4)
        hdr += mask
        masked = bytes(b ^ mask[i & 3] for i, b in enumerate(payload))
        with self._wlock:
            self.sock.sendall(bytes(hdr) + masked)

    def send(self, text):
        self._send_frame(0x1, text.encode("utf-8"))

    def recv(self):
        """Возвращает одно текстовое сообщение (собирает фрагменты, гасит ping)."""
        msg = bytearray()
        while True:
            b0, b1 = self._read(2)
            fin = b0 & 0x80
            opcode = b0 & 0x0f
            masked = b1 & 0x80
            ln = b1 & 0x7f
            if ln == 126:
                ln = struct.unpack(">H", self._read(2))[0]
            elif ln == 127:
                ln = struct.unpack(">Q", self._read(8))[0]
            mk = self._read(4) if masked else b""
            data = self._read(ln) if ln else b""
            if masked and data:
                data = bytes(b ^ mk[i & 3] for i, b in enumerate(data))
            if opcode == 0x9:        # ping
                self._send_frame(0xA, data)
                continue
            if opcode == 0xA:        # pong
                continue
            if opcode == 0x8:        # close
                raise ConnectionError("ws closed by peer")
            if opcode in (0x0, 0x1): # continuation / text
                msg += data
                if fin:
                    return bytes(msg).decode("utf-8", "replace")
            # бинарные кадры CDP не шлёт — игнор

    def close(self):
        try:
            self._send_frame(0x8, b"")
        except Exception:
            pass
        try:
            self.sock.close()
        except Exception:
            pass


class CDP:
    """CDP поверх WS: call() синхронно по id, события -> on_event(dict)."""

    def __init__(self, ws_url):
        self.ws = WS(ws_url)
        self._id = 0
        self._resp = {}
        self._lock = threading.Lock()
        self.on_event = None
        self._alive = True
        self._rx = threading.Thread(target=self._loop, daemon=True)
        self._rx.start()

    def _loop(self):
        try:
            while self._alive:
                m = json.loads(self.ws.recv())
                if "id" in m:
                    with self._lock:
                        self._resp[m["id"]] = m
                elif self.on_event:
                    try:
                        self.on_event(m)
                    except Exception:
                        pass
        except Exception:
            self._alive = False

    def call(self, method, params=None, timeout=15, session_id=None):
        with self._lock:
            self._id += 1
            mid = self._id
        msg = {"id": mid, "method": method, "params": params or {}}
        if session_id:
            msg["sessionId"] = session_id
        self.ws.send(json.dumps(msg))
        t0 = time.time()
        while time.time() - t0 < timeout:
            with self._lock:
                if mid in self._resp:
                    r = self._resp.pop(mid)
                    if "error" in r:
                        raise RuntimeError(f"{method}: {r['error']}")
                    return r.get("result", {})
            if not self._alive:
                raise ConnectionError("CDP connection lost")
            time.sleep(0.02)
        raise TimeoutError(method)

    def close(self):
        self._alive = False
        self.ws.close()
