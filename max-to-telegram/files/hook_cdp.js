// CDP-вариант хука: внедряется в web.max.ru через Page.addScriptToEvaluateOnNewDocument.
// Только ЧИТАЕТ входящие кадры веб-сокета api.oneme.ru и отдаёт новое входящее
// сообщение (opcode 128) целиком через биндинг __maxfwdSend (Runtime.addBinding) в пересыльщик.
// Ничего в MAX не отправляет и не меняет.
(() => {
  "use strict";
  if (window.__maxfwd_hook) return;      // не ставить дважды
  window.__maxfwd_hook = 1;
  const NativeWS = window.WebSocket;

  const _q = [];
  function send(obj) {
    let s;
    try { s = JSON.stringify(obj); } catch (_) { return; }
    try {
      if (typeof window.__maxfwdSend === "function") {
        while (_q.length) window.__maxfwdSend(_q.shift());
        window.__maxfwdSend(s);
      } else {
        _q.push(s);                       // биндинг ещё не готов — очередь
        if (_q.length > 50) _q.shift();
      }
    } catch (_) {}
  }

  // --- LZ4 block (как в самом веб-MAX) ---
  function lz4(src, outLen) {
    const out = new Uint8Array(outLen);
    let i = 0, o = 0;
    while (i < src.length) {
      const tok = src[i++];
      let lit = tok >>> 4;
      if (lit === 15) { let b; do { b = src[i++]; lit += b; } while (b === 255); }
      out.set(src.subarray(i, i + lit), o); i += lit; o += lit;
      if (i >= src.length) break;
      const off = src[i++] | (src[i++] << 8);
      let ml = (tok & 15) + 4;
      if ((tok & 15) === 15) { let b; do { b = src[i++]; ml += b; } while (b === 255); }
      let p = o - off;
      for (let k = 0; k < ml; k++) out[o++] = out[p++];
    }
    return out.subarray(0, o);
  }

  // --- msgpack ---
  const td = new TextDecoder();
  function unpack(buf) {
    const dv = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
    let p = 0;
    const int64 = (signed) => {
      const v = signed ? dv.getBigInt64(p) : dv.getBigUint64(p); p += 8;
      return (v <= BigInt(Number.MAX_SAFE_INTEGER) && v >= -BigInt(Number.MAX_SAFE_INTEGER)) ? Number(v) : String(v);
    };
    const str = (n) => { const s = td.decode(buf.subarray(p, p + n)); p += n; return s; };
    const bin = (n) => { const b = buf.subarray(p, p + n); p += n; return b; };
    const arr = (n) => { const a = []; for (let k = 0; k < n; k++) a.push(rd()); return a; };
    const map = (n) => { const m = {}; for (let k = 0; k < n; k++) { const key = rd(); m[String(key)] = rd(); } return m; };
    const ext = (n) => {
      const type = dv.getInt8(p++); const data = bin(n);
      return type === 1 ? unpack(data) : null;   // тип 1 = большое целое (id)
    };
    function rd() {
      const b = buf[p++];
      if (b <= 0x7f) return b;
      if (b >= 0xe0) return b - 256;
      if ((b & 0xf0) === 0x80) return map(b & 0x0f);
      if ((b & 0xf0) === 0x90) return arr(b & 0x0f);
      if ((b & 0xe0) === 0xa0) return str(b & 0x1f);
      let v;
      switch (b) {
        case 0xc0: return null;
        case 0xc2: return false;
        case 0xc3: return true;
        case 0xc4: v = buf[p]; p += 1; return bin(v);
        case 0xc5: v = dv.getUint16(p); p += 2; return bin(v);
        case 0xc6: v = dv.getUint32(p); p += 4; return bin(v);
        case 0xc7: v = buf[p]; p += 1; return ext(v);
        case 0xc8: v = dv.getUint16(p); p += 2; return ext(v);
        case 0xc9: v = dv.getUint32(p); p += 4; return ext(v);
        case 0xca: v = dv.getFloat32(p); p += 4; return v;
        case 0xcb: v = dv.getFloat64(p); p += 8; return v;
        case 0xcc: return buf[p++];
        case 0xcd: v = dv.getUint16(p); p += 2; return v;
        case 0xce: v = dv.getUint32(p); p += 4; return v;
        case 0xcf: return int64(false);
        case 0xd0: return dv.getInt8(p++);
        case 0xd1: v = dv.getInt16(p); p += 2; return v;
        case 0xd2: v = dv.getInt32(p); p += 4; return v;
        case 0xd3: return int64(true);
        case 0xd4: return ext(1);
        case 0xd5: return ext(2);
        case 0xd6: return ext(4);
        case 0xd7: return ext(8);
        case 0xd8: return ext(16);
        case 0xd9: v = buf[p]; p += 1; return str(v);
        case 0xda: v = dv.getUint16(p); p += 2; return str(v);
        case 0xdb: v = dv.getUint32(p); p += 4; return str(v);
        case 0xdc: v = dv.getUint16(p); p += 2; return arr(v);
        case 0xdd: v = dv.getUint32(p); p += 4; return arr(v);
        case 0xde: v = dv.getUint16(p); p += 2; return map(v);
        case 0xdf: v = dv.getUint32(p); p += 4; return map(v);
      }
      throw new Error("msgpack 0x" + b.toString(16));
    }
    return rd();
  }

  function decodeFrame(data) {
    const t = new Uint8Array(data);
    const dv = new DataView(t.buffer, t.byteOffset, t.byteLength);
    const f = { cmd: dv.getUint8(1), opcode: dv.getInt16(4), payload: undefined };
    const len = (dv.getUint8(7) << 16) | (dv.getUint8(8) << 8) | dv.getUint8(9);
    if (len <= 0) return f;
    let body = t.subarray(10, 10 + len);
    const k = dv.getUint8(6);
    if (k > 0) body = lz4(body, len * k);
    f.payload = unpack(body);
    return f;
  }

  function clean(v, depth) {
    if (depth > 8) return null;
    if (v instanceof Uint8Array) return null;
    if (Array.isArray(v)) return v.map(x => clean(x, depth + 1));
    if (v && typeof v === "object") {
      const o = {};
      for (const key of Object.keys(v)) o[key] = clean(v[key], depth + 1);
      return o;
    }
    return v;
  }

  // --- диагностика всех кадров (по флагу window.__maxfwd_fdiag) ---
  function findUrls(v, out, depth) {
    if (depth > 6 || out.length > 10) return;
    if (typeof v === "string") { if (/https?:\/\//.test(v) || /oneme|okcdn|\.ru\//.test(v)) out.push(v.slice(0, 200)); return; }
    if (Array.isArray(v)) { for (const x of v) findUrls(x, out, depth + 1); return; }
    if (v && typeof v === "object") { for (const k of Object.keys(v)) findUrls(v[k], out, depth + 1); }
  }
  function sketch(payload) {
    const urls = []; try { findUrls(payload, urls, 0); } catch (_) {}
    let keys = [];
    try { if (payload && typeof payload === "object" && !Array.isArray(payload)) keys = Object.keys(payload).slice(0, 25); } catch (_) {}
    return { keys: keys, urls: urls };
  }
  function reportFrame(dir, f) {
    try {
      if (window.__maxfwd_fdiag === 2) {
        // подробный режим: ВСЕ серверные события (cmd 0), кроме сообщений 128, — с содержимым
        if (dir === "in" && f.cmd === 0 && f.opcode !== 128) {
          let s = ""; try { s = JSON.stringify(clean(f.payload, 0)).slice(0, 1500); } catch (_) {}
          send({ fdiag: { dir: dir, cmd: f.cmd, op: f.opcode, p: s } });
        }
      } else if (window.__maxfwd_fdiag) send({ fdiag: { dir: dir, cmd: f.cmd, op: f.opcode, s: sketch(f.payload) } });
    } catch (_) {}
  }

  // Имена контактов (userId -> имя): из кадров и из базы MAX в браузере (IndexedDB max-db-*, store contacts).
  const _contacts = {};
  function contactName(names) {
    if (!Array.isArray(names) || !names.length) return "";
    const n = names.find(x => x && x.type === "CUSTOM") || names[0] || {};
    const full = ((n.firstName || "") + " " + (n.lastName || "")).trim();   // как в списке чатов MAX
    const nm = String(n.name || "").trim();
    return full.length > nm.length ? full : nm;
  }
  function noteContacts(p) {
    if (!p || typeof p !== "object") return;
    const list = Array.isArray(p.contacts) ? p.contacts : (p.contact ? [p.contact] : []);
    for (const c of list) if (c && c.id != null) {
      const nm = contactName(c.names); if (nm) _contacts[String(c.id)] = nm;
      if (c.phone != null) _phones[String(c.id)] = String(c.phone);
    }
  }
  const _phones = {};
  // {name, phone} — телефон нужен, чтобы подписать человека так, как он записан у владельца в Telegram
  window.__maxfwd_contactInfo = async function (id) {
    id = String(id);
    const name = await window.__maxfwd_contact(id);
    return { name: name, phone: _phones[id] || "" };
  };
  window.__maxfwd_contact = async function (id) {
    id = String(id);
    if (_contacts[id] && _phones[id] !== undefined) return _contacts[id];
    try {
      const dbs = await indexedDB.databases();
      const d = dbs.find(x => /^max-db-/.test(x.name || ""));
      if (!d) return "";
      const db = await new Promise((ok, err) => { const r = indexedDB.open(d.name); r.onsuccess = () => ok(r.result); r.onerror = () => err(r.error); });
      const v = await new Promise(ok => {
        try { const g = db.transaction("contacts", "readonly").objectStore("contacts").get(id);
              g.onsuccess = () => ok(g.result); g.onerror = () => ok(null); } catch (_) { ok(null); } });
      db.close();
      const m = v && (v.model || v);
      const nm = m ? contactName(m.names) : "";
      if (nm) _contacts[id] = nm;
      _phones[id] = m && m.phone != null ? String(m.phone) : "";
      return nm || _contacts[id] || "";
    } catch (_) { return _contacts[id] || ""; }
  };

  // Все контакты из базы MAX (для поиска «кому написать»): [{id, name, phone, chat, dialog}]
  // chat = myId ^ userId (номер личного чата), dialog — есть ли уже переписка (тип DIALOG).
  window.__maxfwd_allContacts = async function () {
    const dbs = await indexedDB.databases();
    const d = dbs.find(x => /^max-db-/.test(x.name || ""));
    if (!d) return [];
    const db = await new Promise((ok, err) => { const r = indexedDB.open(d.name); r.onsuccess = () => ok(r.result); r.onerror = () => err(r.error); });
    const all = await new Promise(ok => {
      const res = []; const cur = db.transaction("contacts", "readonly").objectStore("contacts").openCursor();
      cur.onsuccess = e => { const cc = e.target.result; if (!cc) { ok(res); return; }
        const m = cc.value.model || cc.value;
        // служебные аккаунты MAX (Госуслуги, «Безопасность», коды…) помечены BOT/OFFICIAL/SERVICE_ACCOUNT
        const svc = (m.options || []).some(o => /^(BOT|OFFICIAL|SERVICE_ACCOUNT)$/.test(o));
        // custom — человек подписан владельцем (MAX взял имя из контактов его телефона)
        const custom = (m.names || []).some(n => n && n.type === "CUSTOM");
        res.push({ id: String(m.id), name: contactName(m.names), phone: m.phone == null ? "" : String(m.phone),
                   svc: svc, custom: custom });
        cc.continue(); };
      cur.onerror = () => ok(res); });
    db.close();
    const me = window.__maxfwd_me, chats = window.__maxfwd_chats || {};
    for (const x of all) {
      let cid = "";
      try { cid = me ? String(BigInt(me) ^ BigInt(x.id)) : ""; } catch (_) {}
      x.chat = cid; x.dialog = !!(cid && chats[cid] && chats[cid].type === "DIALOG");
      x.t = (cid && chats[cid] && chats[cid].t) || 0;
      x.lm = (cid && chats[cid] && chats[cid].lm) || "";
    }
    return all;
  };

  // Кэш сообщений (id -> отправитель, текст, чат): чтобы по реакции понять, на ЧЬЁ сообщение она.
  const _msgs = new Map();
  function noteMsg(m, chatId) {
    if (!m || typeof m !== "object" || m.id == null) return;
    // диагностика: последние сообщения со вложенным блоком (пересланное / ответ) — как прислал MAX
    try {
      if (m.link) {
        if (!window.__maxfwd_links) window.__maxfwd_links = [];
        window.__maxfwd_links.push(JSON.stringify(clean({ chatId: chatId, message: m }, 0)).slice(0, 2500));
        if (window.__maxfwd_links.length > 20) window.__maxfwd_links.shift();
      }
    } catch (_) {}
    _msgs.set(String(m.id), { s: m.sender == null ? null : String(m.sender),
                              t: String(m.text || "").slice(0, 300), c: chatId == null ? null : String(chatId) });
    if (_msgs.size > 3000) _msgs.delete(_msgs.keys().next().value);
  }
  // Свой userId = участник, общий для всех личных диалогов на двоих.
  const _dlgPeers = {};
  function myId() {
    let best = null, bn = 0;
    for (const k in _dlgPeers) { if (_dlgPeers[k] > bn) { bn = _dlgPeers[k]; best = k; } }
    return bn >= 2 ? best : null;
  }
  function noteChat(c) {
    if (!c || typeof c !== "object" || c.id == null) return;
    if (!window.__maxfwd_chats) window.__maxfwd_chats = {};
    if (!window.__maxfwd_chatsample) window.__maxfwd_chatsample = Object.keys(c).slice(0, 40);
    let n = null, ids = [];
    try { if (c.participants && typeof c.participants === "object") { ids = Object.keys(c.participants); n = ids.length; } } catch (_) {}
    const key = String(c.id), typ = String(c.type == null ? "" : c.type);
    const p = typ === "DIALOG" ? ids : null;          // участники личного диалога (для имени собеседника)
    const t = Number(c.lastEventTime || c.modified || 0) || 0;   // свежесть переписки (для списка контактов)
    // последнее сообщение — чтобы владелец опознал собеседника без номера («Ольга» и кто это?)
    const lmText = c.lastMessage && c.lastMessage.text ? String(c.lastMessage.text).replace(/\s+/g, " ").slice(0, 70) : "";
    if (typ === "DIALOG" && n === 2 && !(window.__maxfwd_chats[key] && window.__maxfwd_chats[key].counted)) {
      for (const u of ids) _dlgPeers[u] = (_dlgPeers[u] || 0) + 1;
      window.__maxfwd_chats[key] = { type: typ, n: n, counted: 1, p: p, t: t, lm: lmText };
    } else {
      const prev = window.__maxfwd_chats[key];
      window.__maxfwd_chats[key] = { type: typ, n: n, counted: prev && prev.counted ? 1 : 0, p: p,
                                     t: Math.max(t, (prev && prev.t) || 0), lm: lmText || (prev && prev.lm) || "" };
    }
    if (c.lastMessage) noteMsg(c.lastMessage, c.id);
    window.__maxfwd_me = myId();
  }
  function collectChats(p) {
    if (!p || typeof p !== "object") return;
    if (Array.isArray(p.chats)) for (const c of p.chats) noteChat(c);
    if (p.chat && typeof p.chat === "object") noteChat(p.chat);
    if (p.message && typeof p.message === "object") noteMsg(p.message, p.chatId);
    if (Array.isArray(p.messages)) for (const m of p.messages) noteMsg(m, p.chatId);
  }
  // Реакция (сервер, opcode 155): {chatId, messageId, counters[{reaction,count}], totalCount}
  function onReaction(p) {
    if (!p || p.messageId == null) return;
    const ch = (window.__maxfwd_chats || {})[String(p.chatId)] || null;
    send({ reaction: { chatId: p.chatId, messageId: String(p.messageId), counters: clean(p.counters || [], 0),
                       total: p.totalCount, type: ch ? ch.type : "", me: window.__maxfwd_me || null,
                       msg: _msgs.get(String(p.messageId)) || null } });
  }

  function onFrame(ev) {
    if (!(ev.data instanceof ArrayBuffer)) return;
    let f;
    try { f = decodeFrame(ev.data); }
    catch (e) { if (window.__maxfwd_fdiag) { try { send({ fdiag: { dir: "in", err: String(e && e.message || e) } }); } catch (_) {} } return; }
    reportFrame("in", f);
    // тип каждого чата (DIALOG / CHAT / CHANNEL) — ответы из Telegram только в личные диалоги
    try { collectChats(f.payload); } catch (_) {}
    try { noteContacts(f.payload); } catch (_) {}
    // с задержкой: следом MAX шлёт обновление чата (135) с текстом сообщения — пусть попадёт в кэш
    try { if (f.cmd === 0 && f.opcode === 155) { const rp = f.payload; setTimeout(() => { try { onReaction(rp); } catch (_) {} }, 1500); } } catch (_) {}
    // подтверждение сервера на нашу отправку (op 64): в какой чат реально ушло
    try {
      if (f.cmd === 1 && f.opcode === 64 && f.payload) {
        const m = f.payload.message || {};
        window.__maxfwd_ack = { chatId: f.payload.chatId == null ? null : String(f.payload.chatId),
                                id: m.id == null ? null : String(m.id), n: (m.attaches || []).length, ts: Date.now() };
      }
    } catch (_) {}
    // ответ на резолв файла (op 88): прямая ссылка скачивания fd.oneme.ru/getfile
    try {
      if (f.cmd === 1 && f.opcode === 88 && f.payload && f.payload.url) {
        window.__maxfwd_lastfileurl = { url: f.payload.url, ts: Date.now() };
      }
    } catch (_) {}
    try {
      if (f.cmd !== 0 || f.opcode !== 128 || !f.payload || !f.payload.message) return;
      const p = f.payload;
      const cleaned = clean({ chatId: p.chatId, message: p.message }, 0);
      try {
        const m = cleaned && cleaned.message;
        if (m && m.attaches && m.attaches.length) {
          // стеш последнего вложения + кольцо последних — для подбора URL по типам через CDP
          const rec = { chatId: cleaned.chatId, msgid: m.id, attaches: m.attaches, ts: Date.now() };
          window.__maxfwd_lastatt = rec;
          if (!window.__maxfwd_atts) window.__maxfwd_atts = [];
          window.__maxfwd_atts.push(rec);
          if (window.__maxfwd_atts.length > 15) window.__maxfwd_atts.shift();
        }
      } catch (_) {}
      send(cleaned);
    } catch (e) {
      send({ error: String(e && e.message || e) });
    }
  }

  // Помощник: качает URL в контексте страницы (куки сессии MAX) и отдаёт base64.
  // Используется и для подбора формата URL, и для реальной пересылки вложений.
  window.__maxfwd_fetchb64 = async function (url, referer) {
    try {
      const opt = { credentials: "include" };
      const r = await fetch(url, opt);
      const ct = r.headers.get("content-type") || "";
      if (!r.ok) return { ok: false, status: r.status, ct: ct };
      const buf = await r.arrayBuffer();
      const bytes = new Uint8Array(buf);
      let bin = "", CH = 0x8000;
      for (let i = 0; i < bytes.length; i += CH) bin += String.fromCharCode.apply(null, bytes.subarray(i, i + CH));
      return { ok: true, status: r.status, ct: ct, len: bytes.length, b64: btoa(bin) };
    } catch (e) {
      return { ok: false, err: String(e && e.message || e) };
    }
  };

  function HookedWS(url, protocols) {
    const ws = protocols === undefined ? new NativeWS(url) : new NativeWS(url, protocols);
    try {
      if (String(url).indexOf("oneme.ru/websocket") !== -1) {
        ws.addEventListener("message", onFrame);
        const origSend = ws.send.bind(ws);
        ws.send = function (d) {
          try {
            const guard = window.__maxfwd_guard;
            if (window.__maxfwd_fdiag || guard) {
              let buf = d instanceof ArrayBuffer ? d : (ArrayBuffer.isView(d) ? d.buffer : null);
              if (buf) {
                const f = decodeFrame(buf);
                if (window.__maxfwd_fdiag === 2) {
                  let s = ""; try { s = JSON.stringify(clean(f.payload, 0)).slice(0, 1500); } catch (_) {}
                  send({ fdiag: { dir: "out", cmd: f.cmd, op: f.opcode, p: s } });
                } else if (window.__maxfwd_fdiag) reportFrame("out", f);
                // ЗАДЕРЖКА (отправка файла из Telegram): команду «отправить» держим, пересыльщик
                // сверяет chatId/вложения и выпускает ровно её (.go()) — или уничтожает.
                if (guard === "hold" && (f.opcode === 64 || (f.payload && f.payload.message))) {
                  if (!window.__maxfwd_held) window.__maxfwd_held = [];
                  window.__maxfwd_held.push({ op: f.opcode, p: clean(f.payload, 0), ts: Date.now(),
                                              go: () => { window.__maxfwd_guard = "drop"; return origSend(d); } });
                  return;
                }
                // ПРЕДОХРАНИТЕЛЬ (проверки / после выпуска): отправку сообщения не пускаем
                if (guard && (f.opcode === 64 || (f.payload && f.payload.message))) {
                  if (!window.__maxfwd_blocked) window.__maxfwd_blocked = [];
                  let s = ""; try { s = JSON.stringify(clean(f.payload, 0)).slice(0, 1500); } catch (_) {}
                  window.__maxfwd_blocked.push({ op: f.opcode, p: s, ts: Date.now() });
                  return;
                }
              }
            }
          } catch (_) { if (window.__maxfwd_guard) return; }   // не разобрали под предохранителем — не пускаем
          return origSend(d);
        };
      }
    } catch (_) {}
    return ws;
  }
  HookedWS.prototype = NativeWS.prototype;
  for (const k of ["CONNECTING", "OPEN", "CLOSING", "CLOSED"]) HookedWS[k] = NativeWS[k];
  window.WebSocket = HookedWS;

  // Перехват веб-уведомления MAX: берём только заголовок (имя отправителя) и тело
  // этого же входящего — чтобы подписать пересылку. Это метаданные сообщения, не база контактов.
  try {
    const NativeNotif = window.Notification;
    if (NativeNotif) {
      const HookedNotif = function (title, opts) {
        try { send({ notif: { t: String(title == null ? "" : title), b: String((opts && opts.body) || "") } }); } catch (_) {}
        return new NativeNotif(title, opts);
      };
      HookedNotif.prototype = NativeNotif.prototype;
      try { HookedNotif.requestPermission = NativeNotif.requestPermission.bind(NativeNotif); } catch (_) {}
      try { Object.defineProperty(HookedNotif, "permission", { get: () => NativeNotif.permission }); } catch (_) {}
      try { HookedNotif.maxActions = NativeNotif.maxActions; } catch (_) {}
      window.Notification = HookedNotif;
    }
  } catch (_) {}

  send({ hello: 1, src: "cdp" });          // сигнал, что хук внедрился
})();
