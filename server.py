"""Blackjack-Mehrspieler-Server (bis zu 4 Spieler pro Tisch, Beitritt per QR-Code).

Start:  python server.py   (oder Doppelklick auf start.bat)
Benoetigt nur Python 3 und das Paket "segno" (QR-Codes).
"""
import io
import json
import os
import queue
import random
import secrets
import socket
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

import segno

PORT = int(os.environ.get("PORT", "8765"))
HERE = os.path.dirname(os.path.abspath(__file__))

MAX_PLAYERS = 4
START_CHIPS = 100
MIN_BET = 1
OFFLINE_SECONDS = 30
RESULT_SECONDS = 7
DECKS = 6
EMOTE_COUNT = 18

LOCK = threading.RLock()
ROOMS = {}

RANKS = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]
SUITS = "SHDC"


# ---------------------------------------------------------------- Karten

def new_shoe():
    shoe = [{"r": r, "s": s} for _ in range(DECKS) for s in SUITS for r in RANKS]
    random.SystemRandom().shuffle(shoe)
    return shoe


def card_value(card):
    if card["r"] == "A":
        return 11
    if card["r"] in ("K", "Q", "J", "10"):
        return 10
    return int(card["r"])


def total(cards):
    t = sum(card_value(c) for c in cards)
    aces = sum(1 for c in cards if c["r"] == "A")
    while t > 21 and aces:
        t -= 10
        aces -= 1
    return t


# ---------------------------------------------------------------- Modell

class Player:
    def __init__(self, pid, name):
        self.pid = pid                      # geheim, identifiziert das Geraet
        self.pub = secrets.token_hex(4)     # oeffentliche Kennung
        self.name = name
        self.chips = START_CHIPS
        self.bet = 0
        self.hands = []
        self.net = None
        self.conns = set()
        self.disc_at = time.time()
        self.left = False
        self.last_emote = 0


class Room:
    def __init__(self, code):
        self.code = code
        self.players = []
        self.phase = "lobby"   # lobby | betting | playing | dealer | results
        self.round = 0
        self.dealer = []
        self.hide = True
        self.shoe = new_shoe()
        self.turn = None
        self.deadline = 0
        self.gen = 0
        self.timer = None
        self.active = time.time()


def draw(room):
    if not room.shoe:
        room.shoe = new_shoe()
    return room.shoe.pop()


def view(room):
    if room.hide and len(room.dealer) >= 2:
        dealer = [room.dealer[0], {"hidden": True}]
    else:
        dealer = room.dealer
    return {
        "code": room.code,
        "phase": room.phase,
        "round": room.round,
        "host": room.players[0].pub if room.players else None,
        "players": [
            {
                "id": p.pub,
                "name": p.name,
                "chips": p.chips,
                "bet": p.bet,
                "hands": p.hands,
                "net": p.net,
                "online": bool(p.conns),
                "left": p.left,
            }
            for p in room.players
        ],
        "dealer": dealer,
        "turn": room.turn,
        "ms": max(0, int((room.deadline - time.time()) * 1000)) if room.deadline else 0,
    }


def broadcast(room):
    room.active = time.time()
    data = json.dumps(view(room))
    for p in room.players:
        for q in p.conns:
            q.put(data)


def close_conns(player):
    for q in list(player.conns):
        q.put(None)


# ---------------------------------------------------------------- Timer

def cancel(room):
    room.gen += 1
    if room.timer:
        room.timer.cancel()
        room.timer = None


def schedule(room, delay, fn):
    cancel(room)
    gen = room.gen

    def run():
        with LOCK:
            if room.gen != gen or ROOMS.get(room.code) is not room:
                return
            fn(room)

    room.timer = threading.Timer(delay, run)
    room.timer.daemon = True
    room.timer.start()


# ---------------------------------------------------------------- Spielablauf

def start_betting(room):
    cancel(room)
    now = time.time()
    keep = []
    for p in room.players:
        if p.left or (p.disc_at and now - p.disc_at > 90):
            close_conns(p)
        else:
            keep.append(p)
    room.players = keep
    if not room.players:
        ROOMS.pop(room.code, None)
        return
    if len(room.shoe) < 78:
        room.shoe = new_shoe()
    room.phase = "betting"
    room.round += 1
    room.dealer = []
    room.hide = True
    room.turn = None
    room.deadline = 0
    for p in room.players:
        p.hands = []
        p.bet = 0
        p.net = None
        if p.chips < MIN_BET:
            p.chips = START_CHIPS
    broadcast(room)


def check_all_bet(room):
    if room.phase != "betting":
        return
    online = [p for p in room.players if p.conns]
    if online and all(p.bet > 0 for p in online):
        schedule(room, 1.0, deal)
    else:
        cancel(room)


def deal(room):
    if room.phase != "betting":
        return
    bettors = [p for p in room.players if p.bet > 0]
    if not bettors:
        return
    cancel(room)
    room.phase = "playing"
    for p in bettors:
        p.chips -= p.bet
        p.hands = [{"cards": [], "bet": p.bet, "done": False, "result": None,
                    "bj": False, "split": False, "doubled": False}]
    for _ in range(2):
        for p in bettors:
            p.hands[0]["cards"].append(draw(room))
        room.dealer.append(draw(room))
    for p in bettors:
        h = p.hands[0]
        if total(h["cards"]) == 21:
            h["bj"] = True
            h["done"] = True
    if total(room.dealer) == 21:
        room.hide = False
        settle(room)
    else:
        next_turn(room)


def next_turn(room):
    cancel(room)
    for p in room.players:
        for i, h in enumerate(p.hands):
            if not h["done"]:
                # Kein Zeitlimit: Nur wer die Verbindung verloren hat,
                # wird nach einer Weile uebersprungen, damit der Tisch nicht haengt.
                room.turn = {"id": p.pub, "hand": i}
                room.deadline = 0
                if not p.conns:
                    schedule(room, OFFLINE_SECONDS, turn_timeout)
                broadcast(room)
                return
    dealer_play(room)


def turn_timeout(room):
    if room.phase != "playing" or not room.turn:
        return
    for p in room.players:
        if p.pub == room.turn["id"]:
            p.hands[room.turn["hand"]]["done"] = True
    next_turn(room)


def live_hands(room):
    return any(not h["bj"] and h["result"] != "bust"
               for p in room.players for h in p.hands)


def dealer_play(room):
    room.phase = "dealer"
    room.turn = None
    room.deadline = 0
    room.hide = False
    broadcast(room)
    schedule(room, 1.0, dealer_step)


def dealer_step(room):
    if live_hands(room) and total(room.dealer) < 17:
        room.dealer.append(draw(room))
        broadcast(room)
        schedule(room, 0.9, dealer_step)
    else:
        settle(room)


def settle(room):
    cancel(room)
    dt = total(room.dealer)
    dealer_bj = dt == 21 and len(room.dealer) == 2
    for p in room.players:
        if not p.hands:
            continue
        staked = 0
        paid = 0
        for h in p.hands:
            h["done"] = True
            staked += h["bet"]
            pt = total(h["cards"])
            if h["result"] == "bust":
                pay = 0
            elif h["bj"] and not dealer_bj:
                h["result"] = "blackjack"
                pay = round(h["bet"] * 2.5)
            elif dealer_bj:
                h["result"] = "push" if h["bj"] else "lose"
                pay = h["bet"] if h["bj"] else 0
            elif dt > 21 or pt > dt:
                h["result"] = "win"
                pay = h["bet"] * 2
            elif pt == dt:
                h["result"] = "push"
                pay = h["bet"]
            else:
                h["result"] = "lose"
                pay = 0
            paid += pay
        p.chips += paid
        p.net = paid - staked
    room.phase = "results"
    room.turn = None
    room.deadline = time.time() + RESULT_SECONDS
    broadcast(room)
    schedule(room, RESULT_SECONDS, start_betting)


def handle_action(room, p, a):
    kind = a.get("type")
    is_host = bool(room.players) and room.players[0] is p

    if kind == "emote":
        try:
            e = int(a.get("e"))
        except (TypeError, ValueError):
            return
        now = time.time()
        if 0 <= e < EMOTE_COUNT and now - p.last_emote >= 0.8:
            p.last_emote = now
            data = json.dumps({"emote": {"id": p.pub, "e": e}})
            for other in room.players:
                for q in other.conns:
                    q.put(data)
        return

    if kind == "start":
        if room.phase == "lobby" and is_host:
            start_betting(room)
        return

    if kind == "bet":
        try:
            amount = int(a.get("amount", 0))
        except (TypeError, ValueError):
            return
        if room.phase == "betting" and MIN_BET <= amount <= p.chips:
            p.bet = amount
            broadcast(room)
            check_all_bet(room)
        return

    if kind == "unbet":
        if room.phase == "betting":
            p.bet = 0
            broadcast(room)
            check_all_bet(room)
        return

    if kind == "deal":
        if room.phase == "betting" and is_host:
            deal(room)
        return

    if kind == "leave":
        close_conns(p)
        if room.phase in ("playing", "dealer", "results") and p.hands:
            p.left = True
            for h in p.hands:
                h["done"] = True
            if room.phase == "playing" and room.turn and room.turn["id"] == p.pub:
                next_turn(room)
            else:
                broadcast(room)
        else:
            room.players.remove(p)
            if not room.players:
                cancel(room)
                ROOMS.pop(room.code, None)
            else:
                broadcast(room)
                check_all_bet(room)
        return

    if kind in ("hit", "stand", "double", "split"):
        if room.phase != "playing" or not room.turn or room.turn["id"] != p.pub:
            return
        h = p.hands[room.turn["hand"]]
        cards = h["cards"]
        if kind == "hit":
            cards.append(draw(room))
            t = total(cards)
            if t > 21:
                h["result"] = "bust"
                h["done"] = True
            elif t == 21:
                h["done"] = True
        elif kind == "stand":
            h["done"] = True
        elif kind == "double":
            if len(cards) != 2 or p.chips < h["bet"]:
                return
            p.chips -= h["bet"]
            h["bet"] *= 2
            h["doubled"] = True
            cards.append(draw(room))
            if total(cards) > 21:
                h["result"] = "bust"
            h["done"] = True
        elif kind == "split":
            if (len(cards) != 2 or len(p.hands) != 1 or p.chips < h["bet"]
                    or card_value(cards[0]) != card_value(cards[1])):
                return
            p.chips -= h["bet"]
            aces = cards[0]["r"] == "A"
            second = cards.pop()
            other = {"cards": [second], "bet": h["bet"], "done": False, "result": None,
                     "bj": False, "split": True, "doubled": False}
            h["split"] = True
            p.hands.append(other)
            for hand in (h, other):
                hand["cards"].append(draw(room))
                if aces or total(hand["cards"]) == 21:
                    hand["done"] = True
        next_turn(room)


# ---------------------------------------------------------------- Netzwerk

def lan_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("8.8.8.8", 80))   # sendet nichts, ermittelt nur die Route
        return s.getsockname()[0]
    except OSError:
        try:
            return socket.gethostbyname(socket.gethostname())
        except OSError:
            return "127.0.0.1"
    finally:
        s.close()


def join_url(handler, code):
    host = handler.headers.get("Host") or ""
    name = host.split(":")[0].lower()
    if not host or name in ("localhost", "127.0.0.1", "[::1]"):
        host = f"{lan_ip()}:{PORT}"
    # Hinter einem Hosting-Anbieter (https) liefert der Proxy das Protokoll mit
    proto = (handler.headers.get("X-Forwarded-Proto") or "http").split(",")[0].strip()
    if proto not in ("http", "https"):
        proto = "http"
    return f"{proto}://{host}/?room={code}"


def new_code():
    alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZ"
    while True:
        code = "".join(secrets.choice(alphabet) for _ in range(4))
        if code not in ROOMS:
            return code


def clean_name(raw):
    name = " ".join(str(raw or "").split())[:14]
    return name or "Spieler"


def find_player(room, pid):
    for p in room.players:
        if p.pid == pid:
            return p
    return None


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def send_json(self, obj, status=200):
        body = json.dumps(obj).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        url = urlparse(self.path)
        qs = parse_qs(url.query)
        if url.path in ("/", "/index.html"):
            with open(os.path.join(HERE, "index.html"), "rb") as f:
                body = f.read()
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)
        elif url.path == "/qr.svg":
            code = (qs.get("room") or [""])[0].upper()[:4]
            buf = io.BytesIO()
            segno.make(join_url(self, code), error="m").save(
                buf, kind="svg", scale=8, border=2)
            body = buf.getvalue()
            self.send_response(200)
            self.send_header("Content-Type", "image/svg+xml")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        elif url.path == "/events":
            self.events((qs.get("room") or [""])[0].upper(), (qs.get("pid") or [""])[0])
        else:
            self.send_error(404)

    def events(self, code, pid):
        q = queue.Queue()
        with LOCK:
            room = ROOMS.get(code)
            p = find_player(room, pid) if room else None
            if not p or p.left:
                self.send_error(404)
                return
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream")
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Accel-Buffering", "no")
            self.end_headers()
            p.conns.add(q)
            p.disc_at = None
            broadcast(room)
            check_all_bet(room)
            if room.phase == "playing" and room.turn and room.turn["id"] == p.pub:
                cancel(room)   # wieder da: kein Ueberspringen mehr
        try:
            while True:
                try:
                    msg = q.get(timeout=5)
                    if msg is None:
                        break
                    self.wfile.write(f"data: {msg}\n\n".encode())
                except queue.Empty:
                    self.wfile.write(b": ping\n\n")
                self.wfile.flush()
        except OSError:
            pass
        finally:
            with LOCK:
                p.conns.discard(q)
                if not p.conns:
                    p.disc_at = time.time()
                if ROOMS.get(code) is room and p in room.players:
                    broadcast(room)
                    check_all_bet(room)
                    if (not p.conns and room.phase == "playing" and room.turn
                            and room.turn["id"] == p.pub):
                        schedule(room, OFFLINE_SECONDS, turn_timeout)

    def do_POST(self):
        try:
            length = min(int(self.headers.get("Content-Length") or 0), 4096)
            data = json.loads(self.rfile.read(length) or b"{}")
            if not isinstance(data, dict):
                raise ValueError
        except (ValueError, OSError):
            self.send_json({"error": "Ungültige Anfrage"}, 400)
            return
        pid = str(data.get("pid") or "")
        if len(pid) < 8:
            self.send_json({"error": "Ungültige Anfrage"}, 400)
            return
        path = urlparse(self.path).path
        with LOCK:
            if path == "/api/create":
                room = Room(new_code())
                ROOMS[room.code] = room
                p = Player(pid, clean_name(data.get("name")))
                room.players.append(p)
                self.send_json({"room": room.code, "me": p.pub,
                                "url": join_url(self, room.code)})
                return
            code = str(data.get("room") or "").upper().strip()
            room = ROOMS.get(code)
            if not room:
                self.send_json({"error": "Diesen Tisch gibt es nicht (mehr)."}, 404)
                return
            p = find_player(room, pid)
            if path == "/api/join":
                if p:
                    p.left = False
                    if data.get("name"):
                        p.name = clean_name(data.get("name"))
                elif len(room.players) >= MAX_PLAYERS:
                    self.send_json({"error": "Der Tisch ist voll (4 Spieler)."}, 409)
                    return
                else:
                    p = Player(pid, clean_name(data.get("name")))
                    room.players.append(p)
                broadcast(room)
                self.send_json({"room": room.code, "me": p.pub,
                                "url": join_url(self, room.code)})
            elif path == "/api/action":
                if not p:
                    self.send_json({"error": "Nicht am Tisch."}, 403)
                    return
                handle_action(room, p, data)
                self.send_json({"ok": True})
            else:
                self.send_json({"error": "Unbekannt"}, 404)


def janitor():
    while True:
        time.sleep(60)
        with LOCK:
            now = time.time()
            for code, room in list(ROOMS.items()):
                if now - room.active > 900 and not any(p.conns for p in room.players):
                    cancel(room)
                    del ROOMS[code]


def main():
    try:
        server = ThreadingHTTPServer(("0.0.0.0", PORT), Handler)
    except OSError:
        print(f"Der Server läuft offenbar schon (Port {PORT} ist belegt).")
        print(f"Einfach im Browser öffnen: http://localhost:{PORT}")
        return
    server.daemon_threads = True
    threading.Thread(target=janitor, daemon=True).start()
    print("Blackjack läuft!")
    print(f"  Auf diesem PC:        http://localhost:{PORT}")
    print(f"  Im WLAN (Handys):     http://{lan_ip()}:{PORT}")
    print("Beenden mit Strg+C.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
