# -*- coding: utf-8 -*-
"""
Пересыльщик MAX -> Telegram (виртуалка max-vm).

Берёт уведомления Windows, которые показывает веб-версия MAX (web.max.ru в Edge),
и пересылает отправителя и текст в личку владельцу через Telegram-бота.
Читает базу уведомлений Windows (wpndatabase.db) — копию, ничего в ней не меняет.
В Telegram ходит только через SOCKS-прокси на ПК владельца (curl.exe), напрямую — нельзя.
Только стандартная библиотека Python.

Полный текст: уведомление MAX обрезает длинные сообщения («…»). При cdp_enabled=on
пересыльщик поднимает Edge с отладочным портом (отдельный профиль edge-cdp) и через
CDP внедряет хук hook_cdp.js, который в реальном времени читает ВХОДЯЩИЕ кадры веб-сокета
MAX в сеансе самого владельца и отдаёт полный текст. Edge 154 не грузит распакованные
расширения через командную строку — поэтому CDP, а не расширение (папка ext\\ — archив).
Триггером остаётся уведомление (даёт имя отправителя); текст берём из кадра по msgid,
если кадр пришёл, иначе — обрезанный текст уведомления. cdp_enabled=off -> режим как был
(только текст уведомлений, обычный профиль Edge).
"""
import configparser, ctypes, ctypes.wintypes as wt, datetime as dt, json
import os, re, shutil, sqlite3, subprocess, sys, tempfile, threading, time, traceback
import urllib.request, ssl
try:
    import cdp  # собственный CDP/WebSocket-клиент (cdp.py рядом)
except Exception:
    cdp = None

BASE = os.path.dirname(os.path.abspath(__file__))
CFG = os.path.join(BASE, "config.ini")
STATE = os.path.join(BASE, "state.json")
LOG = os.path.join(BASE, "maxfwd.log")
WPN = os.path.join(os.environ["LOCALAPPDATA"], r"Microsoft\Windows\Notifications\wpndatabase.db")
EDGE = r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe"
MAX_URL = "https://web.max.ru/"
CDP_PORT = 9222
CDP_PROFILE = os.path.join(BASE, "edge-cdp")
HOOK_FILE = os.path.join(BASE, "hook_cdp.js")
# JS-обёртка showNotification в service worker MAX: имя отправителя (заголовок уведомления)
# и тело -> биндинг __maxfwdSend. Берём ровно то, что MAX показал во всплывашке (не контакты).
SW_HOOK = r"""
try {
  if (!self.__maxfwd_sw) {
    self.__maxfwd_sw = 1;
    var reg = self.registration;
    if (reg && reg.showNotification) {
      var orig = reg.showNotification.bind(reg);
      reg.showNotification = function(title, opts) {
        try { self.__maxfwdSend(JSON.stringify({notif:{t:String(title==null?'':title),b:String((opts&&opts.body)||'')}})); } catch(e){}
        return orig(title, opts);
      };
    }
    try {
      if (self.Notification) {
        var N = self.Notification;
        var H = function(t,o){ try{ self.__maxfwdSend(JSON.stringify({notif:{t:String(t==null?'':t),b:String((o&&o.body)||'')}})); }catch(e){} return new N(t,o); };
        H.prototype = N.prototype; self.Notification = H;
      }
    } catch(e){}
  }
} catch(e){}
"""
ATTACH = ("фото", "видео", "файл", "голосов", "аудио", "стикер", "документ", "изображен",
          "gif", "геолокац", "контакт", "кружок", "видеосообщен", "photo", "video", "file", "voice")
ATT_LABEL = {
    "PHOTO": "фото", "IMAGE": "фото", "VIDEO": "видео", "VIDEO_MESSAGE": "кружок",
    "AUDIO": "аудио", "VOICE": "голосовое", "FILE": "файл", "STICKER": "стикер",
    "GIF": "GIF", "SHARE": "пересланное", "LOCATION": "геолокация", "CONTACT": "контакт",
    "CALL": "звонок",
}
TG_LIMIT = 3800          # запас до лимита Telegram в 4096 (текст)
CAPTION_LIMIT = 1000     # запас до лимита подписи Telegram в 1024
PHOTO_MAX = 10 * 1024 * 1024   # Telegram sendPhoto: не больше 10 МБ
MEDIA_MAX = 48 * 1024 * 1024   # Telegram bot sendVideo/Document: лимит ~50 МБ
NO_WINDOW = 0x08000000
# SSL без проверки сертификата — для CDN видео (okcdn, IP-хосты) и fd.oneme.ru
_SSL = ssl.create_default_context(); _SSL.check_hostname = False; _SSL.verify_mode = ssl.CERT_NONE
_cdp = [None]            # живой CDP-клиент (воркеры медиа дёргают страницу)
_cfg = [None]            # снимок конфига для воркеров
_media_lock = threading.Lock()   # медиа-воркеры по одному (общий DOM/активный чат)
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/154.0.0.0 Safari/537.36 Edg/154.0.0.0")

# кэш полного текста по msgid (наполняет расширение через HTTP-сервер)
_full_lock = threading.Lock()
_full = {}
_full_order = []
_ext_last = 0.0          # время последнего контакта хука (ping или кадр)

# Прямая пересылка из CDP-кадров (уведомления в новом профиле Edge не пишутся в базу)
_fwd_seen = set()        # msgid уже обработанных (дедуп)
_fwd_order = []
_out_q = []              # готовые тексты на отправку в Telegram
_pending = []            # (release_ts, text, att, sender, chat_id) — ждут ~2.5с имя
_out_lock = threading.Lock()
_fwd_since = [0.0]       # не форвардить до этого момента (пропуск истории при старте)
_recent_notifs = []      # недавние веб-уведомления MAX (ts, title, body) — запасной источник имени
_notif_lock = threading.Lock()


def _norm(s):
    """Для сопоставления: убрать хвостовое многоточие и схлопнуть пробелы."""
    s = (s or "").strip().rstrip("…").rstrip(".").strip()
    return " ".join(s.split())


# Заголовки уведомлений MAX, которые НЕ имя (звонки): их за имя не принимать
SYS_TITLE = re.compile(r"вызов|звонок", re.I)


TGNAMES = os.path.join(BASE, "tgnames.json")   # {последние 10 цифр номера: подпись в Telegram владельца}
_tgnames = {"mtime": None, "map": {}}


def tg_name_by_phone(phone):
    """Подпись человека из выгрузки контактов Telegram владельца (по номеру), или None."""
    digits = re.sub(r"\D", "", str(phone or ""))[-10:]
    if len(digits) < 10:
        return None
    try:
        mt = os.path.getmtime(TGNAMES)
    except OSError:
        return None
    if _tgnames["mtime"] != mt:                   # перечитываем, когда файл обновили
        try:
            with open(TGNAMES, encoding="utf-8") as f:
                _tgnames["map"] = json.load(f)
            _tgnames["mtime"] = mt
        except Exception as e:
            log(f"tgnames.json не прочитан: {e!r}")
            return None
    return _tgnames["map"].get(digits) or None


def chat_meta(chat_id):
    """{type: DIALOG/CHAT/CHANNEL, title: название группы} из кадров MAX (или {})."""
    c = _cdp[0]
    if not c or chat_id in (None, ""):
        return {}
    try:
        v = _cdp_eval(c, "JSON.stringify((()=>{const ch=(window.__maxfwd_chats||{})[%s]||{};"
                         "return {type:ch.type||'', title:ch.title||''};})())" % json.dumps(str(chat_id)), timeout=10)
        return json.loads(v or "{}")
    except Exception:
        return {}


def user_name(user_id):
    """Имя любого пользователя MAX по userId (автор пересланного): подпись из Telegram владельца
    по номеру, иначе из MAX. None — не нашли."""
    c = _cdp[0]
    if not c or user_id in (None, ""):
        return None
    try:
        info = json.loads(_cdp_eval(c, "(async()=>window.__maxfwd_contactInfo?JSON.stringify("
                                       "await window.__maxfwd_contactInfo(%s)):'{}')()"
                                    % json.dumps(str(user_id)), timeout=10) or "{}")
    except Exception:
        return None
    nm = tg_name_by_phone(info.get("phone")) or (info.get("name") or "").strip()
    return nm or None


ALIASES = os.path.join(BASE, "aliases.json")   # {chatId: подпись владельца} — «/name …» для тех, у кого MAX скрыл номер
_alias_lock = threading.Lock()


def alias_get(chat_id):
    try:
        with open(ALIASES, encoding="utf-8") as f:
            return (json.load(f).get(str(chat_id)) or "").strip() or None
    except Exception:
        return None


def alias_set(chat_id, name):
    with _alias_lock:
        try:
            with open(ALIASES, encoding="utf-8") as f:
                m = json.load(f)
        except Exception:
            m = {}
        if name:
            m[str(chat_id)] = name
        else:
            m.pop(str(chat_id), None)
        tmp = ALIASES + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(m, f, ensure_ascii=False, indent=1)
        os.replace(tmp, ALIASES)
    _people_cache["ts"] = 0.0                      # список контактов перечитать


def contact_for(chat_id, sender, display=True):
    """Имя собеседника личного чата по userId отправителя (уведомление может быть о звонке).
    display=True — как он подписан у владельца в Telegram (по номеру), если есть; иначе — из MAX.
    display=False — строго как в MAX (по нему ищется строка в списке чатов)."""
    c = _cdp[0]
    if not c or sender in (None, "") or chat_id in (None, ""):
        return None
    try:
        v = _cdp_eval(c, "(async()=>{const ch=(window.__maxfwd_chats||{})[%s];"
                         "if(!ch||ch.type!=='DIALOG'||!window.__maxfwd_contactInfo) return '{}';"
                         "return JSON.stringify(await window.__maxfwd_contactInfo(%s));})()"
                      % (json.dumps(str(chat_id)), json.dumps(str(sender))), timeout=10)
        info = json.loads(v or "{}")
    except Exception:
        return None
    if display:
        tg = alias_get(chat_id) or tg_name_by_phone(info.get("phone"))
        if tg:
            return tg
    nm = (info.get("name") or "").strip()
    return nm if nm and not SYS_TITLE.search(nm) else None


def name_for(text, chat_id=None):
    """Имя отправителя из недавнего уведомления, чьё тело — начало этого текста.
    Нет такого — имя, под которым этот chatId уже пересылался (MAX не показывает уведомление
    по ОТКРЫТОМУ чату, а после ответа из Telegram чат остаётся открытым)."""
    now = time.time()
    tn = _norm(text)
    with _notif_lock:
        for ts, title, body in reversed(_recent_notifs):
            if now - ts > 20:
                break
            if SYS_TITLE.search(title or ""):
                continue                              # «Входящий вызов» — не имя
            bn = _norm(body)
            if bn and (tn.startswith(bn) or bn.startswith(tn[:len(bn)])):
                return title.strip() or None
    known = name_by_chat(chat_id)
    if known:
        return known
    with _notif_lock:
        # если тел не совпали, но есть свежайшее уведомление — берём его заголовок
        if _recent_notifs and now - _recent_notifs[-1][0] < 8 and not SYS_TITLE.search(_recent_notifs[-1][1] or ""):
            return (_recent_notifs[-1][1] or "").strip() or None
    return None


def mark_ext():
    global _ext_last
    _ext_last = time.time()


def ext_active():
    """Расширение считается активным, если был контакт за последние 10 минут.
    Если нет — не ждём кадр и шлём текст уведомления сразу (без регрессии)."""
    return (time.time() - _ext_last) < 600


def log(msg):
    """Пишет в журнал без текста сообщений. Журнал не больше ~5 МБ."""
    try:
        if os.path.exists(LOG) and os.path.getsize(LOG) > 5_000_000:
            shutil.move(LOG, LOG + ".1")
        with open(LOG, "a", encoding="utf-8") as f:
            f.write(f"{dt.datetime.now():%Y-%m-%d %H:%M:%S} {msg}\n")
    except Exception:
        pass


def load_cfg():
    c = configparser.ConfigParser()
    c.read(CFG, encoding="utf-8")
    s = c["main"]
    return {
        "token": s.get("bot_token", "").strip(),
        "chat_id": s.get("chat_id", "").strip(),
        "proxy": s.get("proxy", "").strip(),
        "daily": s.get("daily_report", "07:30").strip(),
        "poll": s.getint("poll_seconds", 5),
        "cdp": s.get("cdp_enabled", "off").strip().lower() in ("on", "1", "true", "yes"),
        "login": s.get("cdp_login", "off").strip().lower() in ("on", "1", "true", "yes"),
        "replies": s.get("replies", "off").strip().lower() in ("on", "1", "true", "yes"),
        "transcribe": s.get("transcribe", "on").strip().lower() in ("on", "1", "true", "yes"),
        "whisper_model": s.get("whisper_model", "").strip(),
    }


def load_state():
    try:
        with open(STATE, encoding="utf-8") as f:
            st = json.load(f)
    except Exception:
        st = {}
    st.setdefault("seen", [])          # ключи уже обработанных уведомлений
    st.setdefault("queue", [])         # не отправленные (нет связи с Telegram)
    st.setdefault("waiting", {})       # ключ -> {title, body, first}: ждём кадр с полным текстом
    st.setdefault("sent_today", 0)
    st.setdefault("last_daily", "")
    st.setdefault("alerts", {})        # тип -> время последнего предупреждения
    st.setdefault("primed", False)     # при первом запуске старые уведомления не шлём
    return st


def save_state(st):
    st["seen"] = st["seen"][-3000:]
    tmp = STATE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(st, f, ensure_ascii=False)
    os.replace(tmp, STATE)


# ---------- Telegram ----------
def _tg_msgid(stdout):
    """message_id из ответа Telegram (int, всегда > 0) или False."""
    try:
        j = json.loads(stdout.decode("utf-8", "replace"))
        if j.get("ok"):
            return int(j["result"]["message_id"]) or True
    except Exception:
        pass
    return False


# ---------- темы в личном чате с ботом (Bot API 9.4: Threaded Mode у @BotFather) ----------
# У каждой переписки MAX своя тема; всё от человека — в его тему; текст владельца в теме — этому человеку.
# Текущая тема задаётся на поток работы (_tl.thread), tg_send/_tg_multipart берут её сами.
_tl = threading.local()
_topics_ok = [False]          # getMe.has_topics_enabled
TOPICS = os.path.join(BASE, "topics.json")   # {"by_chat": {chatId: thread}, "by_thread": {thread: {c, n}}}
_topics_lock = threading.Lock()


def _topics_load():
    try:
        with open(TOPICS, encoding="utf-8") as f:
            m = json.load(f)
    except Exception:
        m = {}
    m.setdefault("by_chat", {})
    m.setdefault("by_thread", {})
    return m


def topic_for(cfg, chat_id, name):
    """Тема этой переписки (создаётся при первом сообщении) или None (темы выключены/не вышло)."""
    if not _topics_ok[0] or chat_id in (None, ""):
        return None
    cid = str(chat_id)
    with _topics_lock:
        m = _topics_load()
        if cid in m["by_chat"]:
            th = m["by_chat"][cid]
            old = (m["by_thread"].get(str(th)) or {}).get("n", "")
            nm = (name or "").strip()
            # тема создалась безымянной («MAX») — переименовать, когда имя стало известно
            if old in ("", "MAX") and nm and nm != "MAX":
                try:
                    r = tg_api(cfg, "editForumTopic", {"chat_id": cfg["chat_id"], "message_thread_id": th,
                                                       "name": nm[:128]})
                    if r and r.get("ok"):
                        m["by_thread"][str(th)] = {"c": cid, "n": nm}
                        tmp = TOPICS + ".tmp"
                        with open(tmp, "w", encoding="utf-8") as f:
                            json.dump(m, f, ensure_ascii=False, indent=1)
                        os.replace(tmp, TOPICS)
                        log(f"темы: тема {th} переименована")
                except Exception as e:
                    log(f"темы: не переименовал {e!r}")
            return th
        r = None
        try:
            r = tg_api(cfg, "createForumTopic", {"chat_id": cfg["chat_id"],
                                                 "name": (name or "MAX").strip()[:128] or "MAX"})
            th = int(r["result"]["message_thread_id"]) if r and r.get("ok") else None
        except Exception as e:
            log(f"темы: не создал {e!r}")
            th = None
        if not th:
            log(f"темы: createForumTopic отказ {str(r)[:160]}")
            return None
        m["by_chat"][cid] = th
        m["by_thread"][str(th)] = {"c": cid, "n": (name or "").strip()}
        tmp = TOPICS + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(m, f, ensure_ascii=False, indent=1)
        os.replace(tmp, TOPICS)
        log(f"темы: создана тема {th} для чата {cid}")
        return th


def topic_target(thread):
    """Тема -> {c: chatId MAX, n: имя} или None."""
    if not thread:
        return None
    with _topics_lock:
        return _topics_load()["by_thread"].get(str(thread))


def tg_send(cfg, text, reply_to=None, markup=None):
    """message_id (истина) — доставлено, False — нет. Через curl.exe и SOCKS5 на ПК владельца."""
    if not cfg["token"] or not cfg["chat_id"]:
        log("нет bot_token / chat_id в config.ini")
        return False
    url = f"https://api.telegram.org/bot{cfg['token']}/sendMessage"
    cmd = ["curl.exe", "-s", "--max-time", "25", "-x", cfg["proxy"], url,
           "--data-urlencode", f"chat_id={cfg['chat_id']}",
           "--data-urlencode", f"text={text}",
           "--data-urlencode", "disable_web_page_preview=true"]
    if reply_to:
        cmd += ["--data-urlencode", f"reply_to_message_id={reply_to}",
                "--data-urlencode", "allow_sending_without_reply=true"]
    if markup:
        cmd += ["--data-urlencode", "reply_markup=" + json.dumps(markup, ensure_ascii=False)]
    th = getattr(_tl, "thread", None)
    if th:
        cmd += ["--data-urlencode", f"message_thread_id={th}"]
    try:
        r = subprocess.run(cmd, capture_output=True, timeout=40, creationflags=NO_WINDOW)
        mid = _tg_msgid(r.stdout)
        if not mid:
            log(f"telegram: не доставлено, curl={r.returncode}, ответ={r.stdout[:120]!r}")
        return mid
    except Exception as e:
        log(f"telegram: ошибка {e!r}")
        return False


def alert(cfg, st, kind, text, every_sec=3600):
    """Предупреждение не чаще раза в every_sec для каждого вида."""
    now = time.time()
    if now - st["alerts"].get(kind, 0) >= every_sec:
        if tg_send(cfg, text):
            st["alerts"][kind] = now


# ---------- пересылка входящих из кадров веб-сокета MAX (через CDP) ----------
def store_frame(body):
    """Входящее сообщение из кадра хука -> в очередь на отправку в Telegram.
    Уведомления Windows в новом профиле Edge в базу не пишутся, поэтому форвардим
    напрямую из кадров. Эта MAX-сессия только принимает (владелец отвечает в Telegram),
    поэтому все кадры opcode 128 — входящие."""
    if not isinstance(body, dict):
        return
    if body.get("hello"):
        mark_ext()
        log(f"CDP: хук на связи ({body.get('src')})")
        return
    if body.get("notif"):
        n = body["notif"]
        with _notif_lock:
            _recent_notifs.append((time.time(), str(n.get("t", "")), str(n.get("b", ""))))
            del _recent_notifs[:-50]
        mark_ext()
        return
    if body.get("error"):
        log("CDP: хук сообщил об ошибке разбора кадра")
        return
    if body.get("reaction"):
        on_reaction(body["reaction"])
        return
    if body.get("fdiag") is not None:
        try:
            log("FDIAG " + json.dumps(body["fdiag"], ensure_ascii=False)[:1800])
        except Exception:
            pass
        return
    msg = body.get("message") or {}
    mid = msg.get("id")
    if mid is None:
        return
    mid = str(mid)
    mark_ext()
    text = msg.get("text") or ""
    sender = msg.get("sender")
    chat_id = body.get("chatId")
    # Пересланное / ответ: у MAX содержимое во вложенном блоке message.link {type, message{...}}.
    # Без этого пересланное приходит «пустым» (нет text и attaches) и молча терялось.
    extra = {}
    link = msg.get("link")
    if isinstance(link, dict) and isinstance(link.get("message"), dict):
        lm = link["message"]
        ltype = str(link.get("type") or "").upper()
        if ltype == "REPLY" and (text.strip() or msg.get("attaches")):
            q = " ".join((lm.get("text") or "").split())
            if q:
                extra["reply_quote"] = q[:80] + ("…" if len(q) > 80 else "")
        else:                                   # FORWARD (или неизвестный тип при пустом сообщении)
            if not text.strip():
                text = lm.get("text") or ""
            if not [a for a in (msg.get("attaches") or []) if a]:
                msg = dict(msg, attaches=lm.get("attaches") or [])
            extra["fwd_from"] = lm.get("sender")
            extra["fwd"] = True
    if is_echo(chat_id, text):
        log(f"CDP: своё отправленное (ответ из Telegram) msgid={mid} — не пересылаю")
        return
    raw_att = [a for a in (msg.get("attaches") or []) if a]
    att = []        # фото (с URL) и лейблы прочих вложений
    media = []      # (kind, name) для видео/файлов -> отдельные воркеры (качаем сам файл)
    for a in raw_att:
        a = a or {}
        typ = str(a.get("_type", "")).upper()
        nm = a.get("name") or a.get("fileName") or a.get("title") or ""
        if typ in ("PHOTO", "IMAGE") and a.get("baseUrl"):
            att.append((typ, str(nm), str(a.get("baseUrl", ""))))   # фото — прямой URL
        elif typ in ("AUDIO", "VOICE") and a.get("url"):
            att.append((typ, str(nm), str(a.get("url", ""))))       # голосовое — прямой URL (OGG/Opus)
        elif typ in ("VIDEO", "VIDEO_MESSAGE"):
            media.append(("VIDEO", str(nm)))
        elif typ == "FILE":
            media.append(("FILE", str(nm)))
        else:
            att.append((typ, str(nm), ""))                          # голосовое/стикер/… — лейбл
    with _out_lock:
        if mid in _fwd_seen:
            return
        _fwd_seen.add(mid)
        _fwd_order.append(mid)
        while len(_fwd_order) > 3000:
            _fwd_seen.discard(_fwd_order.pop(0))
        if time.time() < _fwd_since[0]:
            log(f"CDP: пропуск истории msgid={mid}")   # стартовая синхронизация
            return
        # в текстовую очередь — только если есть что показать текстом (не чистое медиа);
        # у пересланного — всегда (строка «↪️ Переслано от …» перед видео/файлом)
        if (text or "").strip() or att or extra.get("fwd"):
            _pending.append((time.time() + 2.5, text, att, sender, chat_id, extra))
    for kind, nm in media:
        spawn_media(kind, nm, chat_id, sender)                      # видео/файл — отдельным потоком
    log(f"CDP: принято msgid={mid} textlen={len(text)} att={len(att)} медиа={len(media)}")


def drain_pending():
    """Переносит созревшие сообщения в очередь отправки, подставляя имя из уведомления MAX."""
    ready = []
    with _out_lock:
        now = time.time()
        keep = []
        for item in _pending:
            if now >= item[0]:
                ready.append(item)
            else:
                keep.append(item)
        _pending[:] = keep
    for rel, text, att, sender, chat_id, extra in ready:
        meta = chat_meta(chat_id)
        if meta.get("type") in ("CHAT", "CHANNEL") and meta.get("title"):
            # группа: вкладка/«кому» — название группы, в шапке — кто написал
            who = meta["title"]
            name = user_name(sender) or "участник"
        else:
            name = contact_for(chat_id, sender) or name_for(text, chat_id) or "MAX"
            who = name
        if extra.get("fwd"):
            src = user_name(extra.get("fwd_from")) if extra.get("fwd_from") not in (None, sender) else None
            head = "↪️ Переслано" + (f" от {src}" if src else "")
            text = f"{head}:\n{text}" if (text or "").strip() else head
        elif extra.get("reply_quote"):
            text = f"↩️ в ответ на «{extra['reply_quote']}»\n" + (text or "")
        photos = [a for a in att if a[0] in ("PHOTO", "IMAGE") and len(a) > 2 and a[2]]
        voices = [a for a in att if a[0] in ("AUDIO", "VOICE") and len(a) > 2 and a[2]]
        other = [(a[0], a[1]) for a in att if a not in photos and a not in voices]
        has_text = bool((text or "").strip())
        acts = []
        # Текстовое сообщение: если есть текст, прочие вложения, или нет ни фото, ни голосовых.
        if has_text or other or not (photos or voices):
            acts.append({"kind": "text", "text": format_full(name, {"text": text, "att": other}),
                         "who": who, "chat": chat_id})
        # Каждое фото — отдельной картинкой с короткой подписью (имя отправителя).
        for a in photos:
            acts.append({"kind": "photo", "url": a[2], "name": a[1] or "",
                         "caption": _cap_caption(f"💬 {name}"), "who": who, "chat": chat_id})
        # Голосовое — настоящим голосовым Telegram, следом расшифровка (локальный Whisper).
        for a in voices:
            acts.append({"kind": "voice", "url": a[2], "caption": _cap_caption(f"💬 {name}"),
                         "who": who, "chat": chat_id})
        with _out_lock:
            _out_q.extend(acts)
        log(f"CDP: в очередь (имя={'да' if name != 'MAX' else 'нет'}, "
            f"текст={'да' if (has_text or other or not photos) else 'нет'}, фото={len(photos)})")


def lookup_full(mid):
    if not mid:
        return None
    with _full_lock:
        return _full.get(mid)


_sw_pending = []         # sessionId service worker-ов на инъекцию хука уведомления
_sw_seen = set()
_sw_lock = threading.Lock()


_chooser = []      # события Page.fileChooserOpened
_net_seen = set()  # ВРЕМЕННО: дедуп URL медиа-запросов для диагностики


def _cdp_event(m):
    """События CDP. Биндинг __maxfwdSend (страница ИЛИ service worker) -> разбор кадра.
    attachedToTarget на service worker -> в очередь на инъекцию хука уведомления."""
    meth = m.get("method")
    if meth == "Runtime.bindingCalled" and m.get("params", {}).get("name") == "__maxfwdSend":
        try:
            store_frame(json.loads(m["params"]["payload"]))
        except Exception:
            log("CDP: не разобрал payload биндинга")
        return
    # ВРЕМЕННАЯ ДИАГНОСТИКА: какие URL MAX запрашивает под медиа (для скачивания файлов/видео)
    if meth == "Network.requestWillBeSent":
        try:
            url = m.get("params", {}).get("request", {}).get("url", "")
            low = url.lower()
            if (url[:5] == "https" and "websocket" not in low
                    and any(h in low for h in ("download", "/photo", "/video", "/file",
                                               "/attach", "/media", "/upload", "attach",
                                               "i.oneme", "files.oneme", "cdn", "/get"))):
                base = url.split("?", 1)[0]
                if base not in _net_seen:
                    _net_seen.add(base)
                    if len(_net_seen) > 200:
                        _net_seen.clear()
                    log("NET " + url[:180])
        except Exception:
            pass
        return
    if meth == "Page.fileChooserOpened":       # перехваченное окно выбора файла (отправка файла)
        _chooser.append(m.get("params", {}))
        return
    if meth == "Target.attachedToTarget":
        p = m.get("params", {})
        ti = p.get("targetInfo", {})
        sid = p.get("sessionId")
        if sid and ti.get("type") in ("service_worker", "worker", "shared_worker"):
            with _sw_lock:
                if sid not in _sw_seen:
                    _sw_seen.add(sid)
                    _sw_pending.append((sid, bool(p.get("waitingForDebugger"))))
            log(f"CDP: прицепился к {ti.get('type')} (имя из уведомления)")


def _cdp_find_target():
    for t in cdp.http_targets(CDP_PORT):
        if (t.get("type") == "page" and t.get("webSocketDebuggerUrl")
                and "max.ru" in (t.get("url") or "")):
            return t
    return None


def _cdp_attach_once(hook_src):
    """Находит вкладку MAX, цепляется по CDP, внедряет хук, слушает кадры до обрыва."""
    tgt = None
    for _ in range(40):
        try:
            tgt = _cdp_find_target()
        except Exception:
            tgt = None
        if tgt:
            break
        time.sleep(3)
    if not tgt:
        raise RuntimeError("вкладка MAX не найдена на отладочном порту")
    c = cdp.CDP(tgt["webSocketDebuggerUrl"])
    try:
        c.on_event = _cdp_event
        c.call("Runtime.enable")
        c.call("Page.enable")
        c.call("Runtime.addBinding", {"name": "__maxfwdSend"})
        c.call("Page.addScriptToEvaluateOnNewDocument", {"source": hook_src})
        # Перезагружаем вкладку ТОЛЬКО если хук ещё не стоит (иначе MAX уже обёрнут —
        # не дёргаем страницу при каждом переподключении).
        hooked = 0
        try:
            r = c.call("Runtime.evaluate", {"expression": "window.__maxfwd_hook||0", "returnByValue": True})
            hooked = r.get("result", {}).get("value", 0)
        except Exception:
            pass
        if not hooked:
            c.call("Page.reload", {})
            time.sleep(3)
        # Ловим service worker MAX (источник имени отправителя во всплывашке)
        with _sw_lock:
            _sw_seen.clear()
            _sw_pending.clear()
        try:
            c.call("Target.setAutoAttach", {"autoAttach": True, "waitForDebuggerOnStart": True,
                                            "flatten": True})
        except Exception as e:
            log(f"CDP: setAutoAttach не удался: {e}")
        log(f"CDP: подключён к вкладке MAX (хук {'уже стоял' if hooked else 'внедрён'})")
        _cdp[0] = c            # доступен медиа-воркерам (видео/файлы)
        while c._alive:
            # внедряем хук уведомления в появившиеся service worker-ы (вне приёмного потока)
            while True:
                with _sw_lock:
                    sw = _sw_pending.pop(0) if _sw_pending else None
                if not sw:
                    break
                sid, waiting = sw
                try:
                    c.call("Runtime.enable", session_id=sid)
                    c.call("Runtime.addBinding", {"name": "__maxfwdSend"}, session_id=sid)
                    c.call("Runtime.evaluate", {"expression": SW_HOOK}, session_id=sid)
                    log("CDP: хук уведомления внедрён в service worker")
                except Exception as e:
                    log(f"CDP: инъекция в SW не удалась: {e}")
                if waiting:
                    try:
                        c.call("Runtime.runIfWaitingForDebugger", {}, session_id=sid)
                    except Exception:
                        pass
            time.sleep(1)
    finally:
        _cdp[0] = None
        c.close()
    raise RuntimeError("соединение CDP закрыто")


def start_cdp():
    """Фоновый поток: держит соединение CDP с вкладкой MAX, переподключается при обрыве."""
    if cdp is None:
        log("CDP: модуль cdp.py не найден — полный текст недоступен")
        return
    try:
        with open(HOOK_FILE, encoding="utf-8") as f:
            hook_src = f.read()
    except Exception as e:
        log(f"CDP: не прочитал {HOOK_FILE}: {e}")
        return

    def loop():
        while True:
            try:
                _cdp_attach_once(hook_src)
            except Exception as e:
                log(f"CDP: {e} — переподключение через 10 с")
            time.sleep(10)

    threading.Thread(target=loop, daemon=True).start()
    log("CDP: поток полного текста запущен")


# ---------- уведомления Windows ----------
def read_max_notifications():
    """Список (ключ, заголовок, текст) из уведомлений web.max.ru."""
    tmpd = tempfile.mkdtemp(prefix="wpn")
    try:
        for ext in ("", "-wal", "-shm"):
            if os.path.exists(WPN + ext):
                shutil.copy2(WPN + ext, os.path.join(tmpd, "w.db" + ext))
        db = sqlite3.connect(os.path.join(tmpd, "w.db"))
        rows = db.execute(
            "select n.Id, n.ArrivalTime, n.Payload from Notification n "
            "join NotificationHandler h on n.HandlerId=h.RecordId "
            "where h.PrimaryId like '%web.max.ru%' order by n.ArrivalTime").fetchall()
        db.close()
    finally:
        shutil.rmtree(tmpd, ignore_errors=True)
    out = []
    for nid, arrival, payload in rows:
        x = payload.decode("utf-8", "replace") if isinstance(payload, bytes) else str(payload)
        m = re.search(r"#(\d*dlg_[0-9_-]+)", x)
        key = m.group(1) if m else f"id{nid}_{arrival}"
        texts = [unescape(t) for t in re.findall(r"<text[^>]*>(.*?)</text>", x, re.S)]
        title = texts[0] if texts else "MAX"
        body = "\n".join(texts[1:]) if len(texts) > 1 else ""
        out.append((key, title, body))
    return out


def key_msgid(key):
    """Из ключа уведомления dlg_<chat>_<msgid> достаёт msgid для сопоставления с кадром."""
    m = re.search(r"dlg_\d+_(\d+)", key)
    return m.group(1) if m else None


def unescape(s):
    return (s.replace("&lt;", "<").replace("&gt;", ">").replace("&quot;", '"')
             .replace("&apos;", "'").replace("&#39;", "'").replace("&amp;", "&"))


def _cap(text):
    text = text.strip()
    if len(text) > TG_LIMIT:
        text = text[:TG_LIMIT].rstrip() + " […]"
    return text


def format_msg(title, body):
    """Запасной формат — из обрезанного текста уведомления (кадр не пришёл)."""
    lines = [f"💬 {title}"]
    b = body.strip()
    low = b.lower()
    if not b:
        lines.append("📎 вложение")
    elif len(b) < 40 and any(w in low for w in ATTACH):
        lines.append(f"📎 вложение: {b}")
    else:
        lines.append(b)
    return _cap("\n".join(lines))


def format_full(title, full):
    """Основной формат — полный текст из кадра веб-сокета (вложения-пометки)."""
    lines = [f"💬 {title}"]
    t = (full.get("text") or "").strip()
    if t:
        lines.append(t)
    for item in full.get("att", []):
        typ, name = item[0], item[1]
        label = ATT_LABEL.get(typ, "вложение")
        lines.append(f"📎 {label}" + (f": {name}" if name else ""))
    if len(lines) == 1:
        lines.append("📎 вложение")
    return _cap("\n".join(lines))


def _cap_caption(text):
    text = (text or "").strip()
    if len(text) > CAPTION_LIMIT:
        text = text[:CAPTION_LIMIT].rstrip() + " […]"
    return text


def _http_get(url, cap=PHOTO_MAX, ctx=None):
    """Прямое скачивание (мимо SOCKS-прокси — он только к Telegram). Сеть ВМ = домашняя RU.
    ctx=_SSL — без проверки сертификата (CDN видео/файлов)."""
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Referer": "https://web.max.ru/"})
    with urllib.request.urlopen(req, timeout=90, context=ctx) as resp:
        data = resp.read(cap + 1)
    if len(data) > cap:
        raise ValueError(f"файл больше лимита {cap} б")
    return data


def _tg_multipart(cfg, method, field, filename, ctype, data, caption):
    """Отправка файла в Telegram (sendPhoto/sendDocument) через curl + SOCKS-прокси."""
    tmp = os.path.join(tempfile.gettempdir(),
                       f"mx_{int(time.time()*1000)}_{os.getpid()}_{threading.get_ident()}")
    with open(tmp, "wb") as f:
        f.write(data)
    try:
        api = f"https://api.telegram.org/bot{cfg['token']}/{method}"
        cmd = ["curl.exe", "-s", "--max-time", "90", "-x", cfg["proxy"], api,
               "-F", f"chat_id={cfg['chat_id']}"]
        th = getattr(_tl, "thread", None)
        if th:
            cmd += ["-F", f"message_thread_id={th}"]
        if caption:
            cmd += ["-F", f"caption={caption}"]
        cmd += ["-F", f"{field}=@{tmp};type={ctype};filename={filename}"]
        r = subprocess.run(cmd, capture_output=True, timeout=120, creationflags=NO_WINDOW)
        mid = _tg_msgid(r.stdout)
        if not mid:
            log(f"{method}: не ок, curl={r.returncode}, ответ={r.stdout[:160]!r}")
        return mid
    finally:
        try:
            os.remove(tmp)
        except Exception:
            pass


def send_photo(cfg, url, caption, name=""):
    """Качает фото по прямому URL и шлёт картинкой; при отказе Telegram — документом."""
    try:
        data = _http_get(url)
    except Exception as e:
        log(f"photo: не скачал {e!r}")
        return tg_send(cfg, (caption + "\n📎 фото (скачать не удалось)").strip())
    magic = data[:4]
    ct = ("image/webp" if magic == b"RIFF" else
          "image/jpeg" if magic[:3] == b"\xff\xd8\xff" else
          "image/png" if magic == b"\x89PNG" else "application/octet-stream")
    fname = name or ("photo.webp" if ct == "image/webp" else "photo.jpg")
    if ct != "application/octet-stream":
        if _tg_multipart(cfg, "sendPhoto", "photo", fname, ct, data, caption):
            return True
        log("photo: sendPhoto отклонён, пробую документом")
    return _tg_multipart(cfg, "sendDocument", "document", fname, ct, data, caption)


WHISPER_DIR = r"C:\whisper"
_whisper_lock = threading.Lock()     # у ВМ 2 ядра — расшифровки по одной


def transcribe(cfg, ogg):
    """OGG/Opus -> текст. Локально: ffmpeg (16 кГц моно WAV) + whisper.cpp; звук никуда не уходит.
    -> (текст | None, пояснение)."""
    exe = os.path.join(WHISPER_DIR, "whisper-cli.exe")
    ff = os.path.join(WHISPER_DIR, "ffmpeg.exe")
    model = os.path.join(WHISPER_DIR, cfg.get("whisper_model") or "ggml-large-v3-turbo-q5_0.bin")
    if not (os.path.exists(exe) and os.path.exists(ff) and os.path.exists(model)):
        return None, "Whisper не установлен"
    tmp = tempfile.mkdtemp(prefix="vox")
    try:
        src, wav = os.path.join(tmp, "in.ogg"), os.path.join(tmp, "in.wav")
        with open(src, "wb") as f:
            f.write(ogg)
        r = subprocess.run([ff, "-nostdin", "-loglevel", "error", "-y", "-i", src, "-ar", "16000",
                            "-ac", "1", "-c:a", "pcm_s16le", wav],
                           capture_output=True, timeout=120, creationflags=NO_WINDOW)
        if r.returncode != 0 or not os.path.exists(wav):
            return None, f"ffmpeg не перекодировал ({r.returncode})"
        with _whisper_lock:
            t0 = time.time()
            r = subprocess.run([exe, "-m", model, "-f", wav, "-l", "ru", "-nt", "-np",
                                "-t", str(os.cpu_count() or 2)],
                               capture_output=True, timeout=900, creationflags=NO_WINDOW)
            sec = time.time() - t0
        text = " ".join(l.strip() for l in r.stdout.decode("utf-8", "replace").splitlines() if l.strip())
        log(f"расшифровка: {sec:.0f} с, код {r.returncode}, длина {len(text)}")
        if r.returncode != 0:
            return None, f"Whisper завершился с кодом {r.returncode}"
        return text, ""
    except subprocess.TimeoutExpired:
        return None, "слишком долго"
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def send_voice(cfg, url, caption, who=None, chat=None):
    """Голосовое из MAX -> голосовое в Telegram (OGG/Opus как есть), следом — расшифровка ответом."""
    try:
        data = _http_get(url, MEDIA_MAX, _SSL)
    except Exception as e:
        log(f"голосовое: не скачал {e!r}")
        return tg_send(cfg, (caption + "\n🎤 голосовое (скачать не удалось)").strip())
    mid = _tg_multipart(cfg, "sendVoice", "voice", "voice.ogg", "audio/ogg", data, caption)
    if not mid:
        log("голосовое: sendVoice отклонён, шлю файлом")
        mid = _tg_multipart(cfg, "sendDocument", "document", "voice.ogg", "audio/ogg", data, caption)
    if mid and cfg.get("transcribe", True):
        th = getattr(_tl, "thread", None)             # расшифровка — в ту же тему, что и голосовое
        def work():
            _tl.thread = th
            text, why = transcribe(cfg, data)
            if text:
                body = _cap("📝 " + text)
            elif text is not None:
                body = "📝 (слов не разобрал)"
            else:
                body = f"📝 расшифровка не удалась: {why}"
            m2 = tg_send(cfg, body, reply_to=mid)
            remember(m2, who, chat)                   # на расшифровку тоже можно ответить
        threading.Thread(target=work, daemon=True).start()
    return mid


def send_action(cfg, act):
    """Единая отправка пунктов очереди CDP: текст / фото / голосовое — в тему этой переписки."""
    _tl.thread = topic_for(cfg, act.get("chat"), act.get("who"))
    try:
        if act.get("kind") == "photo":
            return send_photo(cfg, act["url"], act.get("caption", ""), act.get("name", ""))
        if act.get("kind") == "voice":
            return send_voice(cfg, act["url"], act.get("caption", ""), act.get("who"), act.get("chat"))
        return tg_send(cfg, act["text"], act.get("reply_to"))
    finally:
        _tl.thread = None


# ---------- видео и файлы: берём через саму страницу MAX (CDP) ----------
# Важно: клик открывает чат только по ГЛУБОКОМУ элементу (SPAN с текстом), не по контейнеру.
_media_busy = [False]        # пока идёт захват медиа — главный цикл не сворачивает окно

_JS_LIST_TOP = r"""(() => {
  let best=null,bh=0;
  [].slice.call(document.querySelectorAll('*')).forEach(e=>{const r=e.getBoundingClientRect();
    if(r.left<380 && r.width<430 && e.scrollHeight-e.clientHeight>150 && e.clientHeight>200){if(e.scrollHeight>bh){bh=e.scrollHeight;best=e;}}});
  if(best){best.scrollTop=0;return 'ok';} return 'nolist';
})()"""

_JS_OPEN_CHAT = r"""(() => {
  const nm = %s;
  // элемент строки чата в ЛЕВОЙ колонке, чей текст содержит префикс имени; берём самый глубокий
  let els = [].slice.call(document.querySelectorAll('*')).filter(e => {
    const t=(e.innerText||'').replace(/\s+/g,' ').trim(); const r=e.getBoundingClientRect();
    return t && t.indexOf(nm)!==-1 && r.left<340 && r.top>70 && r.width>25 && r.width<360 && r.height<120;
  });
  els.sort((a,b)=>a.getElementsByTagName('*').length - b.getElementsByTagName('*').length);
  if (!els.length) return 'NOCHAT';
  els[0].scrollIntoView({block:'center'}); els[0].click(); return 'ok';
})()"""

_JS_OPEN_TOP = r"""(() => {
  let rows = [].slice.call(document.querySelectorAll('*')).filter(e => {
    const t=(e.innerText||'').replace(/\s+/g,' ').trim(); const r=e.getBoundingClientRect();
    return t && t.length>2 && t.length<90 && t!=='Чаты' && t!=='Найти'
       && r.left>70 && r.left<210 && r.width>120 && r.height>44 && r.height<120 && r.top>80;
  });
  rows.sort((a,b)=>a.getBoundingClientRect().top - b.getBoundingClientRect().top);
  if (!rows.length) return 'NOROWS';
  let kids=[].slice.call(rows[0].querySelectorAll('*')).filter(e=>((e.innerText||'').trim().length>1));
  kids.sort((a,b)=>a.getElementsByTagName('*').length - b.getElementsByTagName('*').length);
  const tg = kids.length ? kids[0] : rows[0];
  tg.scrollIntoView({block:'center'}); tg.click(); return 'top';
})()"""

_JS_MSG_BOTTOM = r"""(() => {
  let best=null,bh=0;
  [].slice.call(document.querySelectorAll('*')).forEach(e=>{const r=e.getBoundingClientRect();
    if(r.left>380 && e.scrollHeight-e.clientHeight>120 && e.clientHeight>200){if(e.scrollHeight>bh){bh=e.scrollHeight;best=e;}}});
  if(best){best.scrollTop=best.scrollHeight;return 'ok';} return 'nomsg';
})()"""

_JS_CHAT_TITLE = r"""(() => {
  let el=[].slice.call(document.querySelectorAll('[aria-label]')).find(e=>/Окно чата с/i.test(e.getAttribute('aria-label')||''));
  if(el) return (el.getAttribute('aria-label')||'').replace(/^.*?чата с\s*/i,'').trim().slice(0,60);
  let hs=[].slice.call(document.querySelectorAll('*')).filter(e=>{const t=(e.innerText||'').trim();const r=e.getBoundingClientRect();
    return t && t.length>1 && t.length<60 && r.left>380 && r.top<70 && r.height>14 && r.height<50;});
  hs.sort((a,b)=>a.getElementsByTagName('*').length - b.getElementsByTagName('*').length);
  return hs.length ? (hs[0].innerText||'').replace(/\s+/g,' ').trim().slice(0,60) : '';
})()"""

_JS_READ_VIDEO = r"""(() => {
  const vs = document.querySelectorAll('video');
  if (!vs.length) return '';
  const v = vs[vs.length - 1];
  try { v.scrollIntoView({block:'center'}); } catch(_) {}
  return v.currentSrc || v.src || '';
})()"""

_JS_CLICK_FILE = r"""(() => {
  const nm = %s;
  let cards = [].slice.call(document.querySelectorAll('*')).filter(e => {
    const t = (e.innerText||'').replace(/\s+/g,' ').trim();
    return t && (nm==='' || t.indexOf(nm)!==-1) && t.indexOf('Скачать')!==-1 && t.length < 220;
  });
  cards.sort((a,b)=>a.getElementsByTagName('*').length - b.getElementsByTagName('*').length);
  if (!cards.length) return 'NOFILE';
  let dl = [].slice.call(cards[0].querySelectorAll('*')).filter(e => (e.innerText||'').indexOf('Скачать')!==-1);
  dl.sort((a,b)=>a.getElementsByTagName('*').length - b.getElementsByTagName('*').length);
  let el = dl.length ? dl[0] : cards[0], node = el;
  for (let i=0;i<7 && node;i++){ if (getComputedStyle(node).cursor==='pointer'){ node.scrollIntoView({block:'center'}); node.click(); return 'ok'; } node = node.parentElement; }
  el.scrollIntoView({block:'center'}); el.click(); return 'ok-fb';
})()"""


def _cdp_eval(c, expr, timeout=20):
    r = c.call("Runtime.evaluate", {"expression": expr, "returnByValue": True, "awaitPromise": True},
               timeout=timeout)
    return r.get("result", {}).get("value")


def latest_name():
    """Имя отправителя из самого свежего веб-уведомления MAX (запасной источник имени)."""
    now = time.time()
    with _notif_lock:
        if _recent_notifs and now - _recent_notifs[-1][0] < 30:
            return (_recent_notifs[-1][1] or "").strip() or None
    return None


def media_worker(kind, name, chat_id, sender_id=None):
    """Открывает чат в странице MAX, забирает видео/файл и шлёт в Telegram.
    Окно на время захвата делаем видимым БЕЗ фокуса (SW_SHOWNOACTIVATE) — лента рендерится,
    а имена из уведомлений не ломаются (окно не в фокусе). Медиа-воркеры — по одному."""
    # Имя отправителя захватываем СРАЗУ (до сериализации воркеров): уведомление приходит
    # в первые секунды после кадра. Иначе к моменту (задержанного) запуска «последним»
    # может стать другой чат — и воркер откроет не тот чат.
    # Если этот chatId уже пересылался — имя известно точно (уведомления по открытому чату нет).
    maxname = contact_for(chat_id, sender_id, display=False)     # как в списке MAX — искать строку
    display = contact_for(chat_id, sender_id)                    # как у владельца в Telegram — в шапку
    sender = maxname or name_by_chat(chat_id)
    for _ in range(0 if sender else 8):
        time.sleep(0.5)
        sender = latest_name()
        if sender:
            break
    with _media_lock:
        c = _cdp[0]
        cfg = _cfg[0]
        if not c or not cfg:
            log(f"медиа: нет CDP/cfg — {kind} '{name}' пропущен")
            return
        meta = chat_meta(chat_id)
        grp = meta.get("title") if meta.get("type") in ("CHAT", "CHANNEL") else None
        # видео/файл — в тему этой переписки (у группы тема = название группы, в подписи — кто прислал)
        _tl.thread = topic_for(cfg, chat_id, grp or display or sender)
        if grp:
            display = user_name(sender_id) or display
        _media_busy[0] = True
        try:
            set_edge_windows(SW_SHOWNOACTIVATE)  # показать окно без фокуса — чтобы лента рендерилась
            time.sleep(1.8)
            # открыть чат ОТПРАВИТЕЛЯ по префиксу имени (полное имя в списке усечено);
            # если имени нет — верхний чат (последняя надежда).
            pref = (sender or "")[:18]
            res = None
            if chat_id not in (None, "") and _cur_path(c) == f"/{chat_id}":
                res = "already"                       # нужный чат уже открыт
            elif chat_id not in (None, "") and max_open_chat(
                    c, chat_id, [n for n in (maxname, name_by_chat(chat_id), sender) if n]):
                res = "verified"                      # открыт и сверен по адресу /<chatId>
            elif pref:
                _cdp_eval(c, _JS_LIST_TOP); time.sleep(0.8)
                res = _cdp_eval(c, _JS_OPEN_CHAT % json.dumps(pref))
                if res == "NOCHAT":
                    _cdp_eval(c, _JS_LIST_TOP); time.sleep(1.0)
                    res = _cdp_eval(c, _JS_OPEN_CHAT % json.dumps(pref))
            else:
                _cdp_eval(c, _JS_LIST_TOP); time.sleep(0.8)
                res = _cdp_eval(c, _JS_OPEN_TOP)
            time.sleep(3.2)
            title = (_cdp_eval(c, _JS_CHAT_TITLE) or "").strip()
            # Защита: не пересылать из ЧУЖОГО чата. Если открыт не тот — пометка.
            if res not in ("already", "verified") and sender and title \
                    and sender[:10] not in title and title[:10] not in sender:
                log(f"медиа: открыт не тот чат (нужен {sender!r}, открыт {title!r}) — пометка")
                tg_send(cfg, _cap_caption(f"💬 {sender}") + f"\n📎 {kind.lower()}: {name} (чат не найден)")
                return
            if res in (None, "NOCHAT", "NOROWS"):
                log(f"медиа: чат не открыт (res={res}, имя={sender!r}) — пометка")
                tg_send(cfg, _cap_caption(f"💬 {sender or 'MAX'}") + f"\n📎 {kind.lower()}: {name} (чат не найден)")
                return
            title = display or title or sender or "MAX"
            cap = _cap_caption(f"💬 {title}")
            _cdp_eval(c, _JS_MSG_BOTTOM)
            time.sleep(2.0)
            log(f"медиа: чат открыт (откр={res}, имя={title!r})")
            if kind == "VIDEO":
                url = _cdp_eval(c, _JS_READ_VIDEO) or ""
                if not str(url).startswith("http"):
                    time.sleep(2.5)
                    url = _cdp_eval(c, _JS_READ_VIDEO) or ""
                log(f"медиа: видео src={'есть' if str(url).startswith('http') else 'нет'}")
                if str(url).startswith("http"):
                    data = _http_get(url, MEDIA_MAX, _SSL)
                    ok = _tg_multipart(cfg, "sendVideo", "video", name or "video.mp4", "video/mp4", data, cap)
                    log(f"медиа: видео -> {'ok' if ok else 'fail'} ({len(data)} б)")
                    if ok:
                        remember(ok, title, chat_id)
                        return
                tg_send(cfg, cap + "\n📎 видео (не удалось забрать)")
            else:  # FILE
                _cdp_eval(c, "window.__maxfwd_lastfileurl=null;'ok'")
                res2 = _cdp_eval(c, _JS_CLICK_FILE % json.dumps(name or ""))
                log(f"медиа: клик файла '{name}' -> {res2}")
                url = None
                for _ in range(24):
                    time.sleep(0.5)
                    v = _cdp_eval(c, "JSON.stringify(window.__maxfwd_lastfileurl||null)")
                    if v and v != "null":
                        try:
                            url = json.loads(v).get("url")
                        except Exception:
                            url = None
                        if url:
                            break
                if url:
                    data = _http_get(url, MEDIA_MAX, _SSL)
                    ok = _tg_multipart(cfg, "sendDocument", "document", name or "file",
                                       "application/octet-stream", data, cap)
                    log(f"медиа: файл -> {'ok' if ok else 'fail'} ({len(data)} б)")
                    if ok:
                        remember(ok, title, chat_id)
                        return
                tg_send(cfg, cap + f"\n📎 файл: {name} (не удалось забрать)")
        except Exception as e:
            log(f"медиа: ошибка {kind}: {e!r}")
            try:
                tg_send(cfg, _cap_caption(f"💬 {sender or 'MAX'}") + f"\n📎 {kind.lower()} (ошибка загрузки)")
            except Exception:
                pass
        finally:
            try:
                set_edge_windows(SW_MINIMIZE)    # снова свернуть
            except Exception:
                pass
            _media_busy[0] = False


def spawn_media(kind, name, chat_id, sender_id=None):
    threading.Thread(target=media_worker, args=(kind, name, chat_id, sender_id), daemon=True).start()


# ---------- ответы из Telegram в MAX ----------
# Владелец отвечает боту кнопкой «Ответить» на пересланное сообщение (или «@Имя» первой строкой)
# — текст уходит в MAX ТОМУ ЖЕ ЛИЧНОМУ чату. Защиты (ничего лишнего и никому другому):
#  • адресат — только chatId из кадра MAX, запомненный при пересылке (replymap.json); имя служит
#    лишь для поиска строки в списке; после клика адрес страницы ОБЯЗАН быть web.max.ru/<chatId>;
#  • только личные диалоги (тип DIALOG из кадров MAX); группа/канал/тип неизвестен — отказ;
#  • перед Enter в поле ввода должен быть ровно текст владельца, иначе поле чистим и отказ;
#  • команды только из лички владельца (chat и from = chat_id), каждая один раз, старые — нет.
REPLYMAP = os.path.join(BASE, "replymap.json")
TG_OFFSET = os.path.join(BASE, "tg_offset.txt")
REPLY_MAX_AGE = 1800     # команды старше 30 мин (пересыльщик был выключен) не выполняем
_rmap_lock = threading.Lock()
_rmap = [None]
_echo = []               # (ts, chatId, текст) — свои отправленные, чтобы не переслать обратно
_echo_lock = threading.Lock()
HELP = ("Переписки — по темам (вкладки наверху): что написал в теме человека, уходит ему.\n"
        "Новому собеседнику: «📇 Контакты» внизу → выбери человека → откроется его тема → пиши там. "
        "Или «✍️ Написать» → имя → выбери человека.\n"
        "Ответ в MAX: нажми «Ответить» на пересланном сообщении и напиши текст — он уйдёт "
        "этому человеку в личный чат MAX.\nИли первой строкой «@Имя» (как в шапке 💬), "
        "со второй — текст.\nТекст, фото, видео и файлы до 20 МБ (подпись к файлу уйдёт следом текстом); только личные чаты, в группы не отправляется.")


def _flat(s):
    return " ".join((s or "").split())


def _rmap_get():
    if _rmap[0] is None:
        try:
            with open(REPLYMAP, encoding="utf-8") as f:
                _rmap[0] = json.load(f)
        except Exception:
            _rmap[0] = {}
    return _rmap[0]


def remember(tg_mid, name, chat_id):
    """Связь «сообщение в Telegram -> чат MAX», по ней отвечаем."""
    if not tg_mid or tg_mid is True or chat_id in (None, ""):
        return
    with _rmap_lock:
        m = _rmap_get()
        m[str(tg_mid)] = {"n": (name or "").strip(), "c": str(chat_id), "t": int(time.time())}
        if len(m) > 5000:
            for k in sorted(m, key=lambda k: m[k].get("t", 0))[:len(m) - 4000]:
                del m[k]
        try:
            tmp = REPLYMAP + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(m, f, ensure_ascii=False)
            os.replace(tmp, REPLYMAP)
        except Exception as e:
            log(f"ответы: не сохранил связь {e!r}")


def recall(tg_mid):
    with _rmap_lock:
        v = _rmap_get().get(str(tg_mid))
        return dict(v) if v else None


def name_by_chat(chat_id):
    """Последнее имя, под которым пересылался этот chatId (или None)."""
    if chat_id in (None, ""):
        return None
    cid = str(chat_id)
    with _rmap_lock:
        best = None
        for v in _rmap_get().values():
            if v.get("c") == cid and v.get("n") and v["n"] != "MAX" and not SYS_TITLE.search(v["n"]):
                if best is None or v.get("t", 0) > best.get("t", 0):
                    best = v
        return best["n"] if best else None


def chats_by_name(name):
    """chatId известных чатов с ТОЧНО таким именем (для «@Имя»)."""
    nn = _flat(name).lower()
    with _rmap_lock:
        return sorted({v["c"] for v in _rmap_get().values() if _flat(v.get("n")).lower() == nn})


_sent_log = []           # (ts, chatId, текст, message_id ответа владельца в Telegram)
_react_seen = set()


def on_reaction(r):
    """Реакция в MAX -> строка в Telegram. Только личные диалоги, только на СВОИ сообщения
    (значит, поставил собеседник); снятие реакции не пересылаем."""
    chat = str(r.get("chatId"))
    if r.get("type") != "DIALOG":
        log(f"реакция: чат {chat} не личный — пропуск")
        return
    cnt = [x for x in (r.get("counters") or []) if isinstance(x, dict) and x.get("count")]
    if not cnt or not r.get("total"):
        return                                      # реакцию сняли
    msg = r.get("msg") or {}
    me = r.get("me")
    if msg.get("s") and me and msg["s"] != str(me):
        log("реакция: на сообщение собеседника (это своя реакция) — пропуск")
        return
    key = f"{r.get('messageId')}:" + ",".join(sorted(f"{x.get('reaction')}{x.get('count')}" for x in cnt))
    with _out_lock:
        if key in _react_seen:
            return
        _react_seen.add(key)
    emo = " ".join(str(x.get("reaction") or "") for x in cnt).strip() or "реакция"
    name = name_by_chat(chat) or "MAX"
    txt = (msg.get("t") or "").strip()
    line = (f"{emo} — реакция на: «{txt[:80]}{'…' if len(txt) > 80 else ''}»" if txt
            else f"{emo} — реакция на твоё сообщение")
    reply_to = None
    if txt:
        ft = _flat(txt)
        with _echo_lock:
            for ts, c, t, omid in reversed(_sent_log):
                if c == chat and t == ft:
                    reply_to = omid
                    break
    with _out_lock:
        _out_q.append({"kind": "text", "text": f"💬 {name}\n{line}", "who": name, "chat": chat,
                       "reply_to": reply_to})
    log(f"реакция: чат {chat} -> в очередь (своё сообщение {'известно' if txt else 'не в кэше'})")


def is_echo(chat_id, text):
    """Кадр нашего же отправленного (MAX может вернуть его как входящее) — не пересылать."""
    now = time.time()
    ft = _flat(text)
    with _echo_lock:
        _echo[:] = [e for e in _echo if now - e[0] < 120]
        for e in _echo:
            if e[1] == str(chat_id) and e[2] == ft:
                _echo.remove(e)
                return True
    return False


def tg_api(cfg, method, params, max_time=20):
    url = f"https://api.telegram.org/bot{cfg['token']}/{method}"
    cmd = ["curl.exe", "-s", "--max-time", str(max_time), "-x", cfg["proxy"], url]
    for k, v in params.items():
        cmd += ["--data-urlencode", f"{k}={v}"]
    r = subprocess.run(cmd, capture_output=True, timeout=max_time + 20, creationflags=NO_WINDOW)
    if not r.stdout:
        return None
    return json.loads(r.stdout.decode("utf-8", "replace"))


_JS_LIST_SCROLL = r"""(() => {
  const mode = %s;
  let best=null,bh=0;
  [].slice.call(document.querySelectorAll('*')).forEach(e=>{const r=e.getBoundingClientRect();
    if(r.left<380 && r.width<430 && e.scrollHeight-e.clientHeight>150 && e.clientHeight>200){if(e.scrollHeight>bh){bh=e.scrollHeight;best=e;}}});
  if(!best) return 'nolist';
  if(mode==='top'){best.scrollTop=0;return 'ok';}
  const before=best.scrollTop; best.scrollTop=before+Math.max(200,best.clientHeight*0.7);
  return best.scrollTop>before ? 'ok' : 'end';
})()"""

# Листья в списке чатов, чей текст = имя (или усечённое «…» начало имени). k<0 — вернуть число,
# иначе кликнуть k-й (клик только по глубокому элементу — иначе роутер MAX не срабатывает).
_JS_ROW_MATCH = r"""(() => {
  const nm = %s, k = %d;
  const norm = s => (s||'').replace(/\s+/g,' ').trim().toLowerCase();
  const n = norm(nm);
  // самый глубокий элемент, чей текст целиком = имени (в поиске MAX имя разбито подсветкой <mark>
  // на части — поэтому не «лист», а элемент, ни один ребёнок которого сам не совпадает)
  const ok = e => { const t = norm(e.innerText);
    return t && (t===n || (t.endsWith('…') && t.length>4 && n.startsWith(t.slice(0,-1).trim()))); };
  const els = [].slice.call(document.querySelectorAll('*')).filter(e => {
    const r = e.getBoundingClientRect();
    if (!(r.left<340 && r.top>90 && r.width>25 && r.height>0 && r.height<40)) return false;
    if (!ok(e)) return false;
    return ![].slice.call(e.children).some(ok);
  });
  if (k < 0) return els.length;
  if (k >= els.length) return 'NONE';
  els[k].scrollIntoView({block:'center'}); els[k].click(); return 'ok';
})()"""

_JS_TITLE2 = r"""(() => {
  const a=[].slice.call(document.querySelectorAll('[aria-label^="Открыть профиль"]'))
    .map(e=>(e.getAttribute('aria-label')||'').replace(/^Открыть профиль\s*/,'').trim()).filter(Boolean);
  return a.length ? a[0].slice(0,80) : '';
})()"""

_JS_COMPOSER = r"""(() => {
  const mode = %s;
  const ed = [].slice.call(document.querySelectorAll('[role=textbox][contenteditable]'))
    .filter(e=>{const r=e.getBoundingClientRect(); return r.left>380 && r.width>100;})[0];
  if (!ed) return JSON.stringify({ok:false});
  if (mode==='focus' || mode==='selectall') {
    ed.focus();
    try { const s=getSelection(), rg=document.createRange(); rg.selectNodeContents(ed);
          if (mode==='focus') rg.collapse(false); s.removeAllRanges(); s.addRange(rg); } catch(_) {}
  }
  // Текст поля С ЭМОДЗИ: MAX рисует эмодзи картинкой (data-lexical-emoji), innerText её не видит —
  // иначе эмодзи «невидим» и для сверки, и для проверки «поле пустое».
  let out = '';
  function walk(n){ if(n.nodeType===3){out+=n.nodeValue;return;} if(n.nodeType!==1) return;
    const em=n.getAttribute('data-lexical-emoji'); if(em){out+=em;return;}
    if(n.tagName==='BR'){out+='\n';return;}
    for(const ch of n.childNodes) walk(ch); }
  for (let i=0;i<ed.children.length;i++){ if(i) out+='\n'; walk(ed.children[i]); }
  return JSON.stringify({ok:true, text: out, path: location.pathname});
})()"""


def _key(c, key, code, vk, mods=0):
    for typ in ("keyDown", "keyUp"):
        c.call("Input.dispatchKeyEvent", {"type": typ, "key": key, "code": code,
                                          "windowsVirtualKeyCode": vk, "nativeVirtualKeyCode": vk,
                                          "modifiers": mods})


def _composer(c, mode="read"):
    try:
        return json.loads(_cdp_eval(c, _JS_COMPOSER % json.dumps(mode)) or "{}")
    except Exception:
        return {}


def _composer_clear(c):
    """Очистить поле ввода (выделить всё + Backspace). True — пусто (с учётом эмодзи).
    Пауза после выделения обязательна: редактор (Lexical) подхватывает выделение асинхронно,
    без неё Backspace стирает только часть."""
    for _ in range(8):
        if not _flat(_composer(c).get("text")):
            return True
        _composer(c, "selectall")
        time.sleep(0.3)
        _key(c, "Backspace", "Backspace", 8)
        time.sleep(0.3)
    return not _flat(_composer(c).get("text"))


def _cur_path(c):
    return str(_cdp_eval(c, "location.pathname") or "")


def _fold(s):
    return re.sub(r"[^\w]+", " ", (s or "").lower().replace("ё", "е")).strip()


# Уменьшительные -> корень полного имени: «Настя» находит «Анастасия», «Оля» — «Ольга» и т.д.
NICK = {
    "настя": "анастаси", "катя": "екатерин", "катюша": "екатерин", "даша": "дарь", "оля": "ольг",
    "саша": "александр", "маша": "мари", "лена": "елен", "таня": "татьян", "наташа": "натал",
    "юля": "юли", "женя": "евгени", "дима": "дмитри", "миша": "михаил", "сережа": "серге",
    "коля": "никола", "костя": "константин", "леша": "алексе", "алеша": "алексе", "ваня": "иван",
    "вова": "владимир", "володя": "владимир", "паша": "павел", "света": "светлан", "ира": "ирин",
    "аня": "анн", "люба": "любов", "галя": "галин", "валя": "валентин", "вера": "вер",
    "надя": "надежд", "люда": "людмил", "лиза": "елизавет", "соня": "софи", "поля": "полин",
    "ксюша": "ксени", "вика": "виктори", "витя": "виктор", "толя": "анатоли", "гена": "геннади",
    "петя": "петр", "гриша": "григори", "рома": "роман", "слава": "вячеслав", "стас": "станислав",
    "андрюша": "андре", "никитка": "никит", "тема": "артем", "егорка": "егор",
    "вася": "васили", "федя": "федор", "боря": "борис", "юра": "юри", "макс": "максим",
    "гоша": "георги", "жора": "георги", "митя": "дмитри", "леня": "леонид", "сеня": "семен",
    "тима": "тимофе", "даня": "данил", "влад": "владислав", "лера": "валери", "кира": "кир",
    "кирюша": "кирилл", "игорек": "игор", "олег": "олег", "лиля": "лили", "алена": "елен",
    "зина": "зинаид", "тамара": "тамар", "нина": "нин", "марина": "марин", "кристи": "кристин",
    "маргарита": "маргарит", "рита": "маргарит", "эля": "эльвир", "оксана": "оксан",
}


def _tok_ok(tok, hay):
    if tok in hay:
        return True
    root = NICK.get(tok)
    if root and root in hay:                       # «настя» -> в подписи «Анастасия»
        return True
    # и наоборот: «дарья» -> в подписи «Даша» (полное имя запроса -> уменьшительные)
    hw = hay.split()
    return any(tok.startswith(r) and len(r) >= 3 and any(w.startswith(nick) for w in hw)
               for nick, r in NICK.items())


def find_people(query):
    """Люди, с которыми УЖЕ есть личная переписка в MAX, по словам запроса — ищем и в имени из MAX,
    и в подписи из Telegram владельца. -> [{chat, max, tg, exact}] или None (нет связи с MAX)."""
    c = _cdp[0]
    if not c:
        return None
    try:
        lst = json.loads(_cdp_eval(c, "(async()=>JSON.stringify(window.__maxfwd_allContacts?"
                                      "await window.__maxfwd_allContacts():[]))()", timeout=30) or "[]")
    except Exception:
        return None
    toks = _fold(query).split()
    res = []
    for x in lst:
        if not x.get("dialog") or not x.get("chat") or x.get("svc"):
            continue                              # без переписки / служебные аккаунты MAX
        tg = alias_get(x["chat"]) or tg_name_by_phone(x.get("phone")) or ""   # подпись владельца
        hay = _fold((x.get("name") or "") + " " + tg)
        if not toks or all(_tok_ok(t, hay) for t in toks):     # пустой запрос = все
            exact = bool(toks) and _fold(query) in (_fold(tg), _fold(x.get("name")))
            res.append({"chat": str(x["chat"]), "max": x.get("name") or "", "tg": tg, "exact": exact,
                        "t": x.get("t") or 0, "lm": x.get("lm") or "",
                        "named": bool(tg or x.get("custom"))})   # подписан владельцем (Telegram / телефон / /name)
    res.sort(key=lambda r: (not r["exact"], -(r["t"] or 0)))      # точные, затем свежие переписки
    return res


# Кнопка «✍️ Написать» (постоянная клавиатура бота) → «Кого ищем?» → кнопки с людьми →
# нажал на человека → «Пиши для …» с уже включённым ответом → ответ уходит обычным путём (все сверки).
WRITE_BTN = "✍️ Написать"
CONTACTS_BTN = "📇 Контакты"
MAIN_KB = {"keyboard": [[{"text": CONTACTS_BTN}, {"text": WRITE_BTN}]],
           "resize_keyboard": True, "is_persistent": True}
_search_prompts = set()      # message_id вопросов «Кого ищем?» — ответ на них = строка поиска
_cards = {}                  # chatId -> подпись (для кнопок с людьми)
_pinfo = {}                  # chatId -> запись о человеке (подпись, имя в MAX, последнее сообщение, время)
PAGE = 16                    # контактов на странице (2 столбца × 8 строк)


_inline_ok = [None]          # включён ли у бота встроенный режим (getMe.supports_inline_queries)
_inline_ok_ts = [0.0]


def _short(s, n=24):
    s = " ".join((s or "").split())
    return s if len(s) <= n else s[:n - 1].rstrip() + "…"


def _people_rows(people):
    """Кнопки с людьми в 2 столбца, короткие имена."""
    rows, row = [], []
    for p in people:
        disp = p["tg"] or p["max"]
        _cards[p["chat"]] = disp
        _pinfo[p["chat"]] = p
        label = _short(disp)
        if not p.get("named") and p.get("t"):     # без подписи (MAX скрыл номер) — с датой, чтобы различать
            label = _short(disp, 16) + " · " + dt.datetime.fromtimestamp(p["t"] / 1000).strftime("%d.%m")
        row.append({"text": label, "callback_data": f"w:{p['chat']}"})
        if len(row) == 2:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    return rows


def ask_who(cfg, reply_to=None):
    mid = tg_send(cfg, "Кого ищем? Напиши имя или его часть.", reply_to=reply_to,
                  markup={"force_reply": True, "input_field_placeholder": "Имя или часть имени"})
    if mid:
        _search_prompts.add(mid)


def contacts_markup(page):
    """Страница списка контактов: свежие переписки сверху, листание ◀ ▶."""
    people = all_people() or []
    pages = max(1, (len(people) + PAGE - 1) // PAGE)
    page = max(0, min(page, pages - 1))
    rows = _people_rows(people[page * PAGE:(page + 1) * PAGE])
    nav = []
    if page > 0:
        nav.append({"text": "◀", "callback_data": f"p:{page - 1}"})
    if pages > 1:
        nav.append({"text": f"{page + 1}/{pages}", "callback_data": "noop"})
    if page < pages - 1:
        nav.append({"text": "▶", "callback_data": f"p:{page + 1}"})
    if nav:
        rows.append(nav)
    return {"inline_keyboard": rows}, len(people)


_search_until = [0.0]         # после «Контакты» обычный текст (без «Ответить») = строка поиска


def show_contacts(cfg, reply_to=None):
    markup, n = contacts_markup(0)
    if not n:
        tg_send(cfg, "❌ Список пуст — нет связи со страницей MAX?", reply_to=reply_to)
        return
    tg_send(cfg, "📇 Кому пишем?", reply_to=reply_to, markup=markup)


_people_cache = {"ts": 0.0, "list": []}


def all_people():
    """Все люди с личной перепиской в MAX (кэш 2 мин — встроенный поиск дёргается на каждую букву)."""
    if time.time() - _people_cache["ts"] < 120 and _people_cache["list"]:
        return _people_cache["list"]
    lst = find_people("")
    if lst is not None:
        _people_cache["list"], _people_cache["ts"] = lst, time.time()
    return _people_cache["list"] if lst is None else lst


def on_inline(cfg, iq):
    """Встроенный режим: список контактов, фильтр по набранному. Только для владельца."""
    owner = str(cfg["chat_id"])
    results = []
    # только владельцу и только в чате С САМИМ БОТОМ (chat_type "sender"): иначе выбор человека
    # отправил бы строку с его именем в чужой чат
    if str((iq.get("from") or {}).get("id")) == owner and iq.get("chat_type") == "sender":
        toks = _fold(iq.get("query") or "").split()
        for p in all_people():
            hay = _fold(p["max"] + " " + p["tg"])
            if toks and not all(_tok_ok(t, hay) for t in toks):
                continue
            disp = p["tg"] or p["max"]
            esc = disp.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            item = {"type": "article", "id": p["chat"], "title": disp,
                    "input_message_content": {
                        # номер чата спрятан в невидимой ссылке — по нему бот поймёт, кого выбрали
                        "message_text": f'✍️ {esc}<a href="https://web.max.ru/{p["chat"]}">​</a>',
                        "parse_mode": "HTML"}}
            results.append(item)                  # одна строка на человека — компактно
            if len(results) >= 50:
                break
    try:
        tg_api(cfg, "answerInlineQuery", {"inline_query_id": iq.get("id", ""), "cache_time": 0,
                                          "is_personal": "true",
                                          "results": json.dumps(results, ensure_ascii=False)})
    except Exception as e:
        log(f"встроенный поиск: ошибка ответа {e!r}")


def picked_from_inline(m):
    """Сообщение «✍️ Имя», отправленное выбором из встроенного списка -> (chatId, имя) или None."""
    if not m.get("via_bot"):
        return None
    for e in m.get("entities") or []:
        mm = re.match(r"https://web\.max\.ru/(\d+)$", str(e.get("url") or ""))
        if e.get("type") == "text_link" and mm:
            return mm.group(1), (m.get("text") or "").replace("✍️", "").replace("​", "").strip()
    return None


def show_people(cfg, query, people, reply_to):
    """Найденные люди — кнопками; нажатие = выбрать, кому писать."""
    if people is None:
        tg_send(cfg, "❌ Нет связи со страницей MAX — поиск не выполнен.", reply_to=reply_to)
        return
    if not people:
        tg_send(cfg, f"Никого не нашёл по «{query}» среди переписок в MAX "
                     "(ищу по именам в MAX и по твоим подписям в Telegram).", reply_to=reply_to)
        return
    shown = people[:PAGE]
    head = "Кому пишем?" + (f" ({len(shown)} из {len(people)} — уточни имя)" if len(people) > len(shown) else "")
    tg_send(cfg, head, reply_to=reply_to, markup={"inline_keyboard": _people_rows(shown)})
    log(f"поиск: {len(query)} симв. -> {len(people)} чел.")


def on_callback(cfg, cq):
    """Нажата кнопка с человеком: приглашение «Пиши для …» (ответ на него уйдёт этому человеку)."""
    owner = str(cfg["chat_id"])
    if str((cq.get("from") or {}).get("id")) != owner:
        return
    data = str(cq.get("data") or "")
    cmsg = cq.get("message") or {}
    _tl.thread = cmsg.get("message_thread_id") if cmsg.get("is_topic_message") else None
    if cq.get("id") and not (data.startswith("w:") and _topics_ok[0]):   # при темах ответ — ниже, с подсказкой
        try:
            tg_api(cfg, "answerCallbackQuery", {"callback_query_id": cq.get("id", "")})
        except Exception:
            pass
    if data.startswith("p:"):                     # листание списка контактов — правим то же сообщение
        msg = cq.get("message") or {}
        markup, _n = contacts_markup(int(data[2:] or 0))
        try:
            tg_api(cfg, "editMessageReplyMarkup", {"chat_id": (msg.get("chat") or {}).get("id", ""),
                                                   "message_id": msg.get("message_id", ""),
                                                   "reply_markup": json.dumps(markup, ensure_ascii=False)})
        except Exception:
            pass
        return
    if not data.startswith("w:"):
        return
    chat = data[2:]
    disp = _cards.get(chat) or name_by_chat(chat) or "собеседник"
    hint = ""
    p = _pinfo.get(chat) or {}
    if p and not p.get("named"):                  # MAX скрыл номер — помочь опознать и подписать
        when = dt.datetime.fromtimestamp(p["t"] / 1000).strftime("%d.%m.%Y") if p.get("t") else ""
        if p.get("lm"):
            hint += f"\nПоследнее в переписке ({when}): «{p['lm']}»"
        hint += "\nКто это? Подпиши: «/name Имя»."
    th = topic_for(cfg, chat, disp)
    if th:                                        # темы включены — карточка в теме человека, писать прямо там
        _tl.thread = th
        mid = tg_send(cfg, f"💬 {disp}{hint}\nПиши здесь, в этой теме — текст или файл.")
        _tl.thread = None
        try:
            tg_api(cfg, "answerCallbackQuery", {"callback_query_id": cq.get("id", ""),
                                                "text": f"Тема «{disp[:40]}» — пиши там"})
        except Exception:
            pass
    else:
        mid = tg_send(cfg, f"💬 {disp}{hint}\nНапиши ответом на это сообщение — текст или файл.",
                      markup={"force_reply": True, "input_field_placeholder": f"Сообщение для {disp}"[:64]})
    remember(mid, disp, chat)


_JS_SEARCH_SET = r"""((q)=>{const i=document.querySelector('input[placeholder="Найти"]'); if(!i) return 'noinput';
  i.focus(); const set=Object.getOwnPropertyDescriptor(HTMLInputElement.prototype,'value').set;
  set.call(i,q); i.dispatchEvent(new Event('input',{bubbles:true})); return 'ok';})(%s)"""


def _max_search_open(c, chat_id, names):
    """Чата нет в видимой части списка — ищем через строку «Найти» MAX; открытие сверяется по URL."""
    want = "/" + str(chat_id)
    try:
        for nm in names:
            if not _flat(nm):
                continue
            if _cdp_eval(c, _JS_SEARCH_SET % json.dumps(nm)) != "ok":
                return False
            time.sleep(2.5)
            cnt = _cdp_eval(c, _JS_ROW_MATCH % (json.dumps(nm), -1)) or 0
            for k in range(int(cnt) if isinstance(cnt, (int, float)) else 0):
                if _cdp_eval(c, _JS_ROW_MATCH % (json.dumps(nm), k)) != "ok":
                    continue
                time.sleep(2.0)
                if _cur_path(c) == want:
                    return True
                _cdp_eval(c, _JS_SEARCH_SET % json.dumps(nm)); time.sleep(2.0)   # вернуть результаты
        return False
    finally:
        try:
            _cdp_eval(c, _JS_SEARCH_SET % json.dumps(""))                      # очистить строку поиска
        except Exception:
            pass


def max_open_chat(c, chat_id, names):
    """Открыть чат chat_id: перебор строк списка с подходящим именем, пока адрес не станет
    /<chatId>. Чужие чаты при переборе только открываются, в них ничего не пишется."""
    want = "/" + str(chat_id)
    if _cur_path(c) == want:
        return True
    for nm in names:
        if not _flat(nm):
            continue
        _cdp_eval(c, _JS_LIST_SCROLL % json.dumps("top")); time.sleep(0.8)
        for _page in range(15):
            cnt = _cdp_eval(c, _JS_ROW_MATCH % (json.dumps(nm), -1)) or 0
            for k in range(int(cnt) if isinstance(cnt, (int, float)) else 0):
                if _cdp_eval(c, _JS_ROW_MATCH % (json.dumps(nm), k)) != "ok":
                    continue
                time.sleep(2.0)
                if _cur_path(c) == want:
                    return True
            if _cdp_eval(c, _JS_LIST_SCROLL % json.dumps("down")) != "ok":
                break
            time.sleep(0.7)
    # в списке не нашли (чат давний, глубоко) — через поиск MAX
    ok = _max_search_open(c, chat_id, names)
    if ok:
        _cdp_eval(c, _JS_LIST_SCROLL % json.dumps("top"))
    return ok


def _check_dialog_and_open(c, chat_id, names):
    """Тип чата = DIALOG и открыт именно /<chatId>. -> None (ок) или текст отказа."""
    info = None
    for _ in range(20):            # после перезагрузки страницы список чатов приходит не сразу
        try:
            info = json.loads(_cdp_eval(c, "JSON.stringify((window.__maxfwd_chats||{})[%s]||null)"
                                        % json.dumps(str(chat_id))) or "null")
        except Exception:
            info = None
        if info:
            break
        time.sleep(1)
    typ = str((info or {}).get("type") or "")
    if typ == "CHAT":                              # группа (с 09.10 владелец разрешил писать в группы)
        title = str((info or {}).get("title") or "").strip()
        if title:
            names = [title] + [n for n in names if n != title]
        if not max_open_chat(c, chat_id, names):
            return "не нашёл эту группу в списке MAX"
        return None
    if typ != "DIALOG":
        return ("это канал — туда не отправляю" if typ
                else "не знаю тип чата (личный или группа) — не отправляю")
    # имя собеседника из контактов MAX — первым кандидатом для поиска строки в списке
    # (шапка пересылки может быть «Входящий вызов»); адресат всё равно сверяется по chatId
    try:
        peer = _cdp_eval(c, "(async()=>{const ch=(window.__maxfwd_chats||{})[%s]||{};"
                            "const me=String(window.__maxfwd_me||'');"
                            "const u=(ch.p||[]).find(x=>String(x)!==me);"
                            "return u&&window.__maxfwd_contact?await window.__maxfwd_contact(u):'';})()"
                         % json.dumps(str(chat_id)), timeout=10) or ""
    except Exception:
        peer = ""
    if peer.strip() and not SYS_TITLE.search(peer):
        names = [peer.strip()] + [n for n in names if n != peer.strip()]
    if not max_open_chat(c, chat_id, names):
        return "не нашёл этот чат в списке MAX"
    return None


def _eval_gesture(c, expr):
    """evaluate «от имени пользователя» — иначе Chrome не откроет окно выбора файла."""
    r = c.call("Runtime.evaluate", {"expression": expr, "returnByValue": True,
                                    "awaitPromise": True, "userGesture": True})
    return r.get("result", {}).get("value")


_JS_MENU_ITEM = r"""((txt)=>{const it=[].slice.call(document.querySelectorAll('button,[role=button],[role=menuitem]'))
  .find(e=>(e.innerText||'').trim()===txt && e.getBoundingClientRect().width>0);
  if(!it) return 'noitem'; it.click(); return 'ok';})(%s)"""


_JS_SEND_BTN = r"""(()=>{const b=[].slice.call(document.querySelectorAll('button[aria-label="Отправить сообщение"]'))
  .find(e=>e.getBoundingClientRect().width>0 && !e.disabled); if(!b) return 'nobtn'; b.click(); return 'ok';})()"""


def max_send_file(c, chat_id, names, path, as_media=False, dry=False):
    """Отправить файл в личный чат chat_id. -> (ok, пояснение).
    MAX отправляет файл СРАЗУ после выбора (без предпросмотра), поэтому проверка — на самой
    команде: хук ДЕРЖИТ исходящую «отправить» (guard='hold'), мы сверяем chatId и что вложение
    одно, и только тогда выпускаем её. Иначе — уничтожаем и перезагружаем страницу (неотправленное
    MAX не хранит — проверено 06.10)."""
    err = _check_dialog_and_open(c, chat_id, names)
    if err:
        return False, err
    time.sleep(0.8)
    title = (_cdp_eval(c, _JS_TITLE2) or "").strip() or (names[0] if names else "")
    if _cur_path(c) != f"/{chat_id}":
        return False, "чат сменился перед отправкой файла"
    try:
        c.call("Emulation.setFocusEmulationEnabled", {"enabled": True})
    except Exception:
        pass
    selected = False
    try:
        _composer(c, "focus")
        if not _composer_clear(c):                 # чтобы к файлу не прилип чужой текст
            return False, "в поле ввода MAX черновик, не смог очистить"
        _cdp_eval(c, "window.__maxfwd_held=[];window.__maxfwd_ack=null;window.__maxfwd_guard='hold';'ok'")
        c.call("Page.setInterceptFileChooserDialog", {"enabled": True})
        del _chooser[:]
        _eval_gesture(c, "(()=>{const b=document.querySelector('button[aria-label=\"Загрузить файл\"]');"
                         "if(!b) return 'nobtn'; b.click(); return 'ok';})()")
        time.sleep(0.9)
        r = _eval_gesture(c, _JS_MENU_ITEM % json.dumps("Фото или видео" if as_media else "Файл"))
        for _ in range(24):
            if _chooser:
                break
            time.sleep(0.25)
        if r != "ok" or not _chooser:
            return False, "MAX не открыл выбор файла (меню «Загрузить файл»)"
        c.call("DOM.setFileInputFiles", {"files": [path], "backendNodeId": _chooser[-1]["backendNodeId"]})
        selected = True
        held = None
        clicks = 0
        for i in range(240):                       # загрузка до 20 МБ — ждём до 2 мин
            time.sleep(0.5)
            # «Фото или видео» не уходит сразу: прикрепляется к полю ввода, нужна кнопка отправки
            if as_media and clicks < 2 and i % 20 == 3:
                if _eval_gesture(c, _JS_SEND_BTN) == "ok":
                    clicks += 1
            v = _cdp_eval(c, "JSON.stringify((window.__maxfwd_held||[]).map(h=>h.p))")
            try:
                held = json.loads(v or "[]")
            except Exception:
                held = []
            if held:
                time.sleep(0.5)                    # вдруг следом вторая команда
                held = json.loads(_cdp_eval(c, "JSON.stringify((window.__maxfwd_held||[]).map(h=>h.p))") or "[]")
                break
        if not held:
            return False, "MAX не дошёл до отправки файла (загрузка не завершилась)"
        p = held[0] or {}
        att = ((p.get("message") or {}).get("attaches") or [])
        if len(held) != 1 or str(p.get("chatId")) != str(chat_id) or len(att) != 1 \
                or (p.get("message") or {}).get("text"):
            log(f"файл: команда не прошла сверку (команд {len(held)}, chat={p.get('chatId')}, вложений {len(att)})")
            return False, "команда отправки не совпала с ожидаемой — уничтожил, ничего не ушло"
        if dry:
            return True, f"{title} (проверка: команда сверена и уничтожена, ничего не ушло)"
        _cdp_eval(c, "window.__maxfwd_held[0].go();'ok'")    # выпускаем ровно проверенную команду
        for _ in range(60):
            time.sleep(0.5)
            ack = json.loads(_cdp_eval(c, "JSON.stringify(window.__maxfwd_ack||null)") or "null")
            if ack:
                if ack.get("chatId") == str(chat_id):
                    selected = False               # ушло как надо — страницу не трогаем
                    return True, title
                return False, f"сервер MAX подтвердил другой чат ({ack.get('chatId')}) — проверь!"
        selected = False
        return False, "MAX не подтвердил отправку за 30 с — проверь чат"
    finally:
        try:
            c.call("Page.setInterceptFileChooserDialog", {"enabled": False})
        except Exception:
            pass
        try:
            c.call("Emulation.setFocusEmulationEnabled", {"enabled": False})
        except Exception:
            pass
        if selected:
            # файл выбран, но не выпущен: держим блок и перезагружаем страницу — пузырь исчезнет
            try:
                _cdp_eval(c, "window.__maxfwd_guard=1;'ok'")
                c.call("Page.reload", {})
                log("файл: отправка отменена, страница MAX перезагружена (неотправленное сброшено)")
                time.sleep(6)
            except Exception:
                pass
        else:
            try:
                time.sleep(2)                      # после выпуска пару секунд гасим повторы
                _cdp_eval(c, "window.__maxfwd_guard=0;window.__maxfwd_held=[];'ok'")
            except Exception:
                pass


def max_send_text(c, chat_id, names, text, dry=False):
    """Отправить text в личный чат chat_id. -> (ok, пояснение). dry=True — всё, кроме Enter."""
    want = "/" + str(chat_id)
    err = _check_dialog_and_open(c, chat_id, names)
    if err:
        return False, err
    time.sleep(1.0)
    title = (_cdp_eval(c, _JS_TITLE2) or "").strip() or (names[0] if names else "")
    try:
        c.call("Emulation.setFocusEmulationEnabled", {"enabled": True})
    except Exception:
        pass
    try:
        _composer(c, "focus")
        if not _composer_clear(c):
            return False, "в поле ввода MAX остался черновик, не смог очистить"
        _composer(c, "focus")
        for i, line in enumerate(text.split("\n")):
            if i:
                _key(c, "Enter", "Enter", 13, 8)        # Shift+Enter — перенос строки
            if line:
                c.call("Input.insertText", {"text": line})
        time.sleep(0.4)
        st = _composer(c)
        if _flat(st.get("text")) != _flat(text) or st.get("path") != want:
            _composer_clear(c)
            return False, "в поле ввода оказалось не то, что ты написал — отменил"
        if dry:
            if not _composer_clear(c):
                return False, "проверка: поле не очистилось"
            return True, f"{title} (проверка, Enter не нажат)"
        with _echo_lock:
            _echo.append((time.time(), str(chat_id), _flat(text)))
        _key(c, "Enter", "Enter", 13)
        for _ in range(20):
            time.sleep(0.25)
            if not _flat(_composer(c).get("text")):
                return True, title
        _composer_clear(c)
        return False, "MAX не принял отправку (поле ввода не очистилось) — проверь чат"
    finally:
        try:
            c.call("Emulation.setFocusEmulationEnabled", {"enabled": False})
        except Exception:
            pass


OUTBOX = os.path.join(BASE, "outbox")
TG_FILE_MAX = 20 * 1024 * 1024     # бот Telegram скачивает файлы до 20 МБ


def _safe_name(name, default):
    n = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "_", (name or "").strip()).strip(" .")
    return (n[:150] or default)


def tg_file_of(m):
    """Вложение сообщения владельца -> {id, name, size, media} или {bad: причина} или None."""
    if m.get("photo"):
        p = max(m["photo"], key=lambda x: x.get("file_size") or x.get("width", 0) * x.get("height", 0))
        return {"id": p["file_id"], "name": "photo.jpg", "size": p.get("file_size") or 0, "media": True}
    if m.get("video"):
        v = m["video"]
        return {"id": v["file_id"], "name": _safe_name(v.get("file_name"), "video.mp4"),
                "size": v.get("file_size") or 0, "media": True}
    for key, default in (("document", "file"), ("audio", "audio.mp3")):
        if m.get(key):
            d = m[key]
            return {"id": d["file_id"], "name": _safe_name(d.get("file_name"), default),
                    "size": d.get("file_size") or 0, "media": False}
    for key, what in (("voice", "голосовые"), ("video_note", "кружки"), ("sticker", "стикеры"),
                      ("location", "геолокацию"), ("contact", "контакты"), ("poll", "опросы")):
        if m.get(key):
            return {"bad": f"{what} в MAX пока не отправляю — только текст, фото, видео и файлы"}
    return None


def tg_download(cfg, f, tag):
    """Скачать файл из Telegram (через прокси) в outbox. -> путь или текст ошибки (str с '!')."""
    if f["size"] and f["size"] > TG_FILE_MAX:
        return "!файл больше 20 МБ — Telegram не отдаёт его боту"
    r = tg_api(cfg, "getFile", {"file_id": f["id"]})
    fp = ((r or {}).get("result") or {}).get("file_path")
    if not fp:
        return f"!Telegram не отдал файл ({str(r)[:80]})"
    d = os.path.join(OUTBOX, str(tag))
    os.makedirs(d, exist_ok=True)
    dest = os.path.join(d, f["name"])
    url = f"https://api.telegram.org/file/bot{cfg['token']}/{fp}"
    rr = subprocess.run(["curl.exe", "-s", "-f", "--max-time", "300", "-x", cfg["proxy"], "-o", dest, url],
                        capture_output=True, timeout=330, creationflags=NO_WINDOW)
    size = os.path.getsize(dest) if os.path.exists(dest) else 0
    if rr.returncode != 0 or size == 0 or (f["size"] and size != f["size"]):
        return f"!не скачал файл из Telegram (curl={rr.returncode}, {size} б)"
    return dest


def tg_react(cfg, mid, emoji):
    """Реакция бота на сообщение владельца (emoji=None — снять). True — встала."""
    try:
        r = tg_api(cfg, "setMessageReaction", {
            "chat_id": cfg["chat_id"], "message_id": mid,
            "reaction": json.dumps([{"type": "emoji", "emoji": emoji}] if emoji else [], ensure_ascii=False)})
        ok = bool(r and r.get("ok"))
        if not ok:
            log(f"реакция {emoji!r}: не встала {str(r)[:120]}")
        return ok
    except Exception as e:
        log(f"реакция: ошибка {e!r}")
        return False


def reply_worker(cfg, owner_mid, chat_id, names, body, tgfile=None, th=None):
    _tl.thread = th                    # подтверждения — в ту же тему, где писал владелец
    tg_react(cfg, owner_mid, "✍")      # «отправляется…» — пометка на сообщении владельца
    path = None
    if tgfile:
        path = tg_download(cfg, tgfile, owner_mid)
        if path.startswith("!"):
            log(f"ответы: файл не скачан: {path[1:]}")
            tg_react(cfg, owner_mid, None)
            tg_send(cfg, f"❌ Не отправлено: {path[1:]}", reply_to=owner_mid)
            return
    for _ in range(90):            # сразу после старта CDP ещё не подключён — ждём, не отказываем
        if _cdp[0]:
            break
        time.sleep(1)
    sent_file = False
    with _media_lock:              # общий DOM с медиа-воркерами — по одному
        c = _cdp[0]
        ok, info = False, "нет связи со страницей MAX"
        if c:
            _media_busy[0] = True
            try:
                set_edge_windows(SW_SHOWNOACTIVATE)
                time.sleep(1.5)
                if path:
                    ok, info = max_send_file(c, chat_id, names, path, tgfile.get("media"))
                    sent_file = ok
                    if ok and body.strip():
                        ok2, info2 = max_send_text(c, chat_id, names, body)
                        if not ok2:
                            ok, info = False, f"файл ушёл, а подпись нет: {info2}"
                else:
                    ok, info = max_send_text(c, chat_id, names, body)
            except Exception as e:
                ok, info = False, f"ошибка {e!r}"[:200]
            finally:
                try:
                    set_edge_windows(SW_MINIMIZE)
                except Exception:
                    pass
                _media_busy[0] = False
    if path:
        shutil.rmtree(os.path.dirname(path), ignore_errors=True)
    log(f"ответы: chat={chat_id} {'файл ' if path else ''}-> {'ok' if ok else 'отказ'} "
        f"({info if not ok else 'отправлено'})")
    what = f" (файл «{tgfile['name']}»)" if path else ""
    if ok:
        if body.strip():
            with _echo_lock:
                _sent_log.append((time.time(), str(chat_id), _flat(body), owner_mid))
                del _sent_log[:-300]
        # успех — пометка на самом сообщении владельца (✍ → 👌); если реакция не встала — прежнее сообщение
        remember(owner_mid, info or (names[0] if names else ""), chat_id)
        if not tg_react(cfg, owner_mid, "👌"):
            mid = tg_send(cfg, f"✅ Отправлено в MAX → {info}{what}", reply_to=owner_mid)
            remember(mid, info or (names[0] if names else ""), chat_id)
    elif sent_file:
        tg_react(cfg, owner_mid, None)
        tg_send(cfg, f"⚠️ {info}", reply_to=owner_mid)
    else:
        tg_react(cfg, owner_mid, None)
        tg_send(cfg, f"❌ Не отправлено{what}: {info}", reply_to=owner_mid)


def handle_update(cfg, u):
    if u.get("callback_query"):
        on_callback(cfg, u["callback_query"])
        return
    if u.get("inline_query"):                     # встроенный поиск убран (не понравился владельцу) — пустой ответ
        try:
            tg_api(cfg, "answerInlineQuery", {"inline_query_id": u["inline_query"].get("id", ""),
                                              "results": "[]", "cache_time": 0})
        except Exception:
            pass
        return
    m = u.get("message")
    if not m:
        return
    owner = str(cfg["chat_id"])
    if str((m.get("chat") or {}).get("id")) != owner or str((m.get("from") or {}).get("id")) != owner:
        log("ответы: сообщение боту не от владельца — игнор")
        return
    # тема, в которой написал владелец: ответы бота — туда же; тема человека = адресат
    th = m.get("message_thread_id") if m.get("is_topic_message") else None
    _tl.thread = th
    mid = m.get("message_id")
    if time.time() - int(m.get("date") or 0) > REPLY_MAX_AGE:
        tg_send(cfg, "❌ Не отправлено: команда устарела (пришла, пока пересыльщик был выключен).",
                reply_to=mid)
        return
    tgfile = tg_file_of(m)
    if tgfile and tgfile.get("bad"):
        tg_send(cfg, f"❌ Не отправлено: {tgfile['bad']}.", reply_to=mid)
        return
    text = m.get("text") if not tgfile else (m.get("caption") or "")
    if text is None:
        tg_send(cfg, "❌ Не отправлено: такой тип сообщения в MAX не отправляю.", reply_to=mid)
        return
    low = text.strip().lower()
    rt = m.get("reply_to_message")
    if not tgfile and re.fullmatch(r"@\w*bot\s*", text.strip(), re.I):
        return                                   # набрал «@имя_бота» и отправил — это не «@Имя» человека
    picked = picked_from_inline(m) if not tgfile else None
    if picked:                                   # выбрали человека во встроенном списке контактов
        chat, disp = picked
        _cards[chat] = disp
        on_callback(cfg, {"from": m.get("from"), "data": f"w:{chat}"})
        return
    if not tgfile:
        # кнопка «✍️ Написать» / команды поиска
        if low in (CONTACTS_BTN.lower(), "/contacts", "/start"):
            show_contacts(cfg)
            return
        if low in (WRITE_BTN.lower(), "/write", "/find"):
            ask_who(cfg, reply_to=mid)
            return
        if low.startswith("/find ") or low.startswith("/write "):
            q = text.strip().split(None, 1)[1].strip()
            show_people(cfg, q, find_people(q), mid)
            return
        # ответ на «Кого ищем?» = строка поиска
        if rt and rt.get("message_id") in _search_prompts:
            show_people(cfg, text.strip(), find_people(text.strip()), mid)
            return
        # после «📇 Контакты» — обычный текст без «Ответить» = поиск (ничего не отправляет)
        if not rt and not low.startswith(("@", "/")) and time.time() < _search_until[0] \
                and len(text.strip()) <= 40:
            show_people(cfg, text.strip(), find_people(text.strip()), mid)
            return
        # «/name Имя» ответом на карточку/пересланное — своя подпись для этого чата (MAX скрыл номер)
        if low.startswith("/name"):
            ent = (recall(rt.get("message_id")) if rt else None) or topic_target(th)
            newname = text.strip()[5:].strip()
            if not ent:
                tg_send(cfg, "Напиши «/name Имя» в теме человека или ответом на его сообщение.", reply_to=mid)
                return
            alias_set(ent["c"], newname)
            remember(mid, newname or ent.get("n"), ent["c"])
            tg_send(cfg, f"✅ Подписал: {newname}" if newname else "✅ Подпись убрана.", reply_to=mid)
            return
        if low.startswith("/"):
            tg_send(cfg, HELP, markup=MAIN_KB)
            return
    tt = topic_target(th)
    if tt:                                       # написал в теме человека — адресат из темы, «Ответить» не нужен
        chat_id, body, names = tt["c"], text, [tt.get("n") or ""]
    elif rt:
        ent = recall(rt.get("message_id"))
        lines = [l.strip() for l in ((rt.get("text") or rt.get("caption") or "").split("\n"))]
        hdr = lines[0][1:].strip() if lines and lines[0].startswith("💬") else ""
        if not ent:
            # старая пересылка (до карты): как «@Имя» — имя из шапки, ровно один известный чат
            ids = chats_by_name(hdr) if hdr and hdr != "MAX" else []
            if len(ids) != 1:
                tg_send(cfg, "❌ Не отправлено: не знаю, из какого чата MAX это сообщение "
                             "(пришло до включения ответов или это не пересылка)."
                             + (" Чатов с таким именем несколько." if len(ids) > 1 else ""),
                        reply_to=mid)
                return
            ent = {"c": ids[0], "n": hdr}
        chat_id, body = ent["c"], text
        names = [ent.get("n", "")]
        if hdr:
            names.append(hdr)
            if len(lines) > 1 and 0 < len(lines[1]) < 50:
                names.append(lines[1])       # «💬 Входящий вызов» / имя второй строкой
        if (rt.get("text") or "").startswith("✅ Отправлено в MAX → "):
            names.append(rt["text"].split("→", 1)[1].split(" (файл «", 1)[0].strip())
    elif text.startswith("@"):
        first, _, body = text.partition("\n")
        name = first[1:].strip()
        if not name or (not body.strip() and not tgfile):
            tg_send(cfg, "❌ Формат: первая строка «@Имя», со второй — текст "
                         "(у файла — в подписи).", reply_to=mid)
            return
        ids = chats_by_name(name)
        if not ids:
            tg_send(cfg, f"❌ Не отправлено: не знаю чат «{name}». Ответь кнопкой «Ответить» "
                         "на его сообщение.", reply_to=mid)
            return
        if len(ids) > 1:
            tg_send(cfg, f"❌ Не отправлено: чатов с именем «{name}» несколько. Ответь кнопкой "
                         "«Ответить» на сообщение нужного человека.", reply_to=mid)
            return
        chat_id, names = ids[0], [name]
    else:
        if _topics_ok[0]:
            tg_send(cfg, "Не отправлено — это вне темы, бот не знает кому. Открой вкладку человека наверху "
                         "(или выбери его в «📇 Контакты») и напиши там.", reply_to=mid)
        else:
            tg_send(cfg, "Не отправлено.\n" + HELP, reply_to=mid)
        return
    body = body.strip("\n")
    if not body.strip() and not tgfile:
        tg_send(cfg, "❌ Пустой текст — нечего отправлять.", reply_to=mid)
        return
    if len(body) > 4000:
        tg_send(cfg, "❌ Слишком длинный текст (больше 4000 знаков).", reply_to=mid)
        return
    names = [n for i, n in enumerate(names) if n and n != "MAX" and n not in names[:i]]
    log(f"ответы: принят ответ для chat={chat_id} (текст {len(body)}"
        f"{', файл' if tgfile else ''})")
    threading.Thread(target=reply_worker, args=(cfg, mid, chat_id, names, body, tgfile, th),
                     daemon=True).start()


def reply_loop():
    """Фоновый поток: забирает сообщения владельца боту (getUpdates через тот же прокси)."""
    off = None
    try:
        with open(TG_OFFSET, encoding="utf-8") as f:
            off = int(f.read().strip())
    except Exception:
        pass

    def save_off(v):
        try:
            with open(TG_OFFSET, "w", encoding="utf-8") as f:
                f.write(str(v))
        except Exception:
            pass

    last_err = 0
    menu_set = False
    while True:
        cfg = _cfg[0]
        if not cfg or not cfg.get("replies"):
            time.sleep(10)
            continue
        if time.time() - _inline_ok_ts[0] > 600:  # включён ли встроенный режим (владелец включает у @BotFather)
            try:
                r = tg_api(cfg, "getMe", {})
                _inline_ok[0] = bool(r and r.get("ok") and r["result"].get("supports_inline_queries"))
                _topics_ok[0] = bool(r and r.get("ok") and r["result"].get("has_topics_enabled"))
                _inline_ok_ts[0] = time.time()
            except Exception:
                pass
        if not menu_set:                          # меню команд бота (кнопка «Меню» в Telegram)
            try:
                r = tg_api(cfg, "setMyCommands", {"commands": json.dumps([
                    {"command": "contacts", "description": "Контакты — выбрать, кому написать"},
                    {"command": "write", "description": "Написать — найти по имени"},
                    {"command": "help", "description": "Как отвечать в MAX"}], ensure_ascii=False)})
                menu_set = bool(r and r.get("ok"))
            except Exception:
                pass
        try:
            if off is None:
                # первый запуск: всё, что писали боту раньше, НЕ выполняем
                r = tg_api(cfg, "getUpdates", {"offset": -1, "timeout": 0})
                if r and r.get("ok"):
                    res = r.get("result") or []
                    off = (res[-1]["update_id"] + 1) if res else 0
                    save_off(off)
                    log(f"ответы: старт, старые сообщения боту пропущены (offset={off})")
                else:
                    raise RuntimeError(f"getUpdates: {str(r)[:120]}")
                continue
            r = tg_api(cfg, "getUpdates", {"offset": off, "timeout": 25,
                                           "allowed_updates": '["message","callback_query","inline_query"]'}, max_time=40)
            if not r or not r.get("ok"):
                raise RuntimeError(f"getUpdates: {str(r)[:160]}")
            for u in r.get("result") or []:
                off = u["update_id"] + 1
                save_off(off)                  # до выполнения: каждую команду — не больше раза
                try:
                    handle_update(cfg, u)
                except Exception:
                    log("ответы: ошибка разбора " + traceback.format_exc().replace("\n", " | ")[:500])
        except Exception as e:
            if time.time() - last_err > 600:
                log(f"ответы: {e}")
                last_err = time.time()
            time.sleep(15)


# ---------- Edge с web.max.ru ----------
user32 = ctypes.windll.user32


def edge_windows():
    """Видимые окна Edge (дескриптор, заголовок)."""
    res = []
    pids = edge_pids()

    @ctypes.WINFUNCTYPE(ctypes.c_bool, wt.HWND, wt.LPARAM)
    def cb(hwnd, _):
        if user32.IsWindowVisible(hwnd):
            pid = wt.DWORD()
            user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
            if pid.value in pids:
                n = user32.GetWindowTextLengthW(hwnd)
                b = ctypes.create_unicode_buffer(n + 1)
                user32.GetWindowTextW(hwnd, b, n + 1)
                if b.value:
                    res.append((hwnd, b.value))
        return True
    user32.EnumWindows(cb, 0)
    return res


def edge_pids():
    try:
        r = subprocess.run(["tasklist", "/fi", "imagename eq msedge.exe", "/fo", "csv", "/nh"],
                           capture_output=True, text=True, timeout=15, creationflags=NO_WINDOW)
        return {int(l.split('","')[1]) for l in r.stdout.splitlines() if l.startswith('"msedge')}
    except Exception:
        return set()


def launch_edge(cdp_mode):
    """Запускает Edge с MAX. В режиме CDP — с отладочным портом и отдельным профилем."""
    args = [EDGE, "--new-window"]
    if cdp_mode:
        args += [f"--remote-debugging-port={CDP_PORT}", "--remote-allow-origins=*",
                 f"--user-data-dir={CDP_PROFILE}", "--no-first-run", "--no-default-browser-check"]
    args.append(MAX_URL)
    subprocess.Popen(args, creationflags=NO_WINDOW)


SW_SHOWNOACTIVATE = 4    # показать окно без активации/фокуса (рендер есть, фокуса нет)
SW_MINIMIZE = 6


def set_edge_windows(cmd):
    """Применить ShowWindow(cmd) ко всем окнам Edge (для медиа-захвата)."""
    for hwnd, _ in edge_windows():
        try:
            user32.ShowWindow(hwnd, cmd)
        except Exception:
            pass


def minimize_edge(wins):
    for hwnd, title in wins:
        if not user32.IsIconic(hwnd):
            user32.ShowWindow(hwnd, 6)  # SW_MINIMIZE


def restore_edge(wins):
    """Разворачивает окно (режим QR-входа): чтобы на скриншоте был виден QR."""
    for hwnd, title in wins:
        user32.ShowWindow(hwnd, 9)  # SW_RESTORE
        try:
            user32.SetForegroundWindow(hwnd)
        except Exception:
            pass


def show_or_hide(cfg, wins):
    """В режиме входа окно развёрнуто, иначе свёрнуто (нужно для web-уведомлений).
    Во время захвата медиа окно не трогаем (его показывает/прячет медиа-воркер)."""
    if _media_busy[0]:
        return
    if cfg.get("login"):
        restore_edge(wins)
    else:
        minimize_edge(wins)


_edge_init = False


def ensure_edge(cfg, st):
    """Edge с MAX должен работать и быть свёрнут (иначе сайт не шлёт уведомления)."""
    global _edge_init
    cdp_mode = cfg.get("cdp")
    if not _edge_init:
        # Разово при старте: отладочный порт работает только на чистом запуске Edge,
        # поэтому гасим все msedge и поднимаем начисто.
        _edge_init = True
        if edge_pids():
            log("старт: чистый перезапуск Edge")
            try:
                subprocess.run(["taskkill", "/f", "/im", "msedge.exe"],
                               capture_output=True, timeout=25, creationflags=NO_WINDOW)
            except Exception:
                pass
            time.sleep(4)
        log("запускаю MAX" + (" (CDP)" if cdp_mode else ""))
        launch_edge(cdp_mode)
        time.sleep(25)
        wins = edge_windows()
        if not wins:
            alert(cfg, st, "edge", "⚠️ Пересыльщик MAX: не удалось запустить Edge с MAX.")
            return
        show_or_hide(cfg, wins)
        return

    wins = edge_windows()
    if not wins:
        log("Edge не запущен — запускаю MAX")
        launch_edge(cdp_mode)
        time.sleep(25)
        wins = edge_windows()
        if not wins:
            alert(cfg, st, "edge", "⚠️ Пересыльщик MAX: не удалось запустить Edge с MAX.")
            return
    show_or_hide(cfg, wins)


# ---------- основной цикл ----------
def main():
    # только один экземпляр
    ctypes.windll.kernel32.CreateMutexW(None, False, "Local\\maxfwd_single_instance")
    if ctypes.windll.kernel32.GetLastError() == 183:  # ERROR_ALREADY_EXISTS
        return
    log("старт")
    st = load_state()
    cfg = load_cfg()
    if cfg.get("cdp"):
        _fwd_since[0] = time.time() + 25   # первые 25 с — стартовая синхронизация MAX, не шлём
        start_cdp()
        threading.Thread(target=reply_loop, daemon=True).start()   # ответы из Telegram в MAX
    last_edge = 0
    started_msg = False
    while True:
        try:
            cfg = load_cfg()
            _cfg[0] = cfg            # снимок для медиа-воркеров
            if not started_msg and tg_send(cfg, "🔄 Пересыльщик MAX запущен.", markup=MAIN_KB if cfg.get("replies") else None):
                started_msg = True
            if time.time() - last_edge > 60:
                ensure_edge(cfg, st)
                last_edge = time.time()

            if not cfg.get("cdp"):
                # Старый путь (без CDP): триггер — уведомление Windows.
                notes = read_max_notifications()
                seen = set(st["seen"])
                waiting = st["waiting"]
                if not st["primed"]:
                    st["seen"].extend(k for k, _, _ in notes)
                    st["primed"] = True
                else:
                    for key, title, body in notes:
                        if key not in seen and key not in waiting:
                            waiting[key] = {"title": title, "body": body, "first": time.time()}
                    for key in list(waiting.keys()):
                        info = waiting[key]
                        full = lookup_full(key_msgid(key))
                        if full is not None:
                            text = format_full(info["title"], full)
                        elif (not ext_active()) or (time.time() - info.get("first", 0) > 12):
                            text = format_msg(info["title"], info["body"])
                        else:
                            continue
                        st["queue"].append({"key": key, "text": text})
                        st["seen"].append(key)
                        seen.add(key)
                        del waiting[key]
                while st["queue"]:
                    item = st["queue"][0]
                    if not tg_send(cfg, item["text"]):
                        alert(cfg, st, "tg", "⚠️ Пересыльщик MAX: нет связи с Telegram, копится.")
                        break
                    st["queue"].pop(0)
                    st["sent_today"] += 1
                    log(f"переслано {item['key']}")

            # Путь CDP: созревшие кадры -> очередь (с именем из уведомления) -> Telegram.
            drain_pending()
            while True:
                with _out_lock:
                    act = _out_q.pop(0) if _out_q else None
                if act is None:
                    break
                tmid = send_action(cfg, act)
                if tmid:
                    remember(tmid, act.get("who"), act.get("chat"))
                    st["sent_today"] += 1
                    log(f"CDP: переслано в Telegram ({act.get('kind', 'text')})")
                else:
                    with _out_lock:
                        _out_q.insert(0, act)
                    alert(cfg, st, "tg", "⚠️ Пересыльщик MAX: нет связи с Telegram, копится.")
                    break

            now = dt.datetime.now()
            if now.strftime("%H:%M") >= cfg["daily"] and st["last_daily"] != now.strftime("%Y-%m-%d"):
                if tg_send(cfg, f"✅ Пересыльщик MAX работает. За сутки переслано: {st['sent_today']}."):
                    st["last_daily"] = now.strftime("%Y-%m-%d")
                    st["sent_today"] = 0
            save_state(st)
        except Exception:
            log("ошибка цикла: " + traceback.format_exc().replace("\n", " | ")[:800])
        time.sleep(cfg.get("poll", 5))


if __name__ == "__main__":
    main()
