"""한자 변환 코어 — Qt 없이 쓰는 사전 조회와 후보 찾기.

사전은 libhangul 의 hanja.txt (`한글:한자:뜻풀이`, 파일 순서가 곧 빈도순)이다.
같은 꼴의 기호 사전 mssymbol.txt(`ㄱ:…:명칭`, 윈도 입력기의 ㄱ+한자 기호표)도 읽는다. 기호는
`kind = 1` 로 표시해 한자와 구별한다: 키는 자모(`ㄱ`)이고, 명칭(`로마숫자일` → ⅰ)은 훈음처럼
공백이 없어도 그대로 찾는다.
  · 음          `가`        → 可 家 加 歌 …
  · 단어        `국가`      → 國家 國歌
  · 훈음        `노래 가`   → 歌 哥          (뜻풀이가 `노래 가` 인 한자)

사전 DB(읽기 전용)와 사용자 DB(최근 기록)를 따로 둔다. 앱을 묶으면 설치 폴더는 읽기 전용이기
때문에, 만든 사전 DB 와 최근 기록은 쓸 수 있는 곳(사용자 폴더)에 둔다.

Copyright (c) 2005,2006 Choe Hwanjin (hanja.txt, BSD), 2005-2014 (mssymbol.txt, BSD) — 사전 파일 첫머리의 문구를 지우지 말 것.
"""
import os
import sqlite3

__version__ = "0.3.1"

SCHEMA_VERSION = 5
MAX_KEY = 12            # 커서 앞에서 거슬러 올라가 볼 최대 글자 수(공백 포함)


def _split_meanings(meaning):
    """`값 가, 값/성 가` → ["값 가", "값/성 가"]. 훈음 하나가 한 덩어리이다."""
    out = []
    for alt in meaning.split(","):
        alt = " ".join(alt.split())
        if alt:
            out.append(alt)
    return out


def dict_is_ready(db_path, want_symbols=False):
    """같은 버전의 사전 DB 가 있는지. want_symbols 인데 DB 에 기호가 없으면(기호 파일을 나중에
    둔 경우) 다시 만들어야 하므로 False."""
    if not os.path.isfile(db_path):
        return False
    try:
        conn = sqlite3.connect(db_path)
        try:
            if conn.execute("PRAGMA user_version").fetchone()[0] != SCHEMA_VERSION:
                return False
            if want_symbols:
                return conn.execute("SELECT COUNT(*) FROM hanja_dict WHERE kind = 1").fetchone()[0] > 0
            return True
        finally:
            conn.close()
    except sqlite3.Error:
        return False


def build_dict(txt_path, db_path, symbol_path=None):
    """hanja.txt → SQLite 사전 DB. 임시 파일에 만들고 끝나면 바꿔 치우므로, 만들다 멈춰도
    반쯤 만든 DB 가 남지 않는다. 별도 스레드에서 불러도 된다(자기 연결을 쓴다)."""
    os.makedirs(os.path.dirname(os.path.abspath(db_path)), exist_ok=True)
    tmp = db_path + ".building"
    if os.path.exists(tmp):
        os.remove(tmp)
    conn = sqlite3.connect(tmp)
    try:
        cur = conn.cursor()
        cur.executescript("""
            CREATE TABLE hanja_dict (id INTEGER PRIMARY KEY, hangul TEXT NOT NULL,
                                     hanja TEXT NOT NULL, meaning TEXT NOT NULL,
                                     kind INTEGER NOT NULL DEFAULT 0);
            CREATE TABLE hun (alt TEXT NOT NULL, hanja TEXT NOT NULL, id INTEGER NOT NULL,
                              kind INTEGER NOT NULL DEFAULT 0);
        """)
        rows = []
        for path, kind in ((txt_path, 0), (symbol_path, 1)):
            if not path:
                continue
            with open(path, "r", encoding="utf-8") as f:
                for line in f:
                    line = line.rstrip("\n")
                    if not line or line.startswith("#"):
                        continue
                    parts = line.split(":", 2)
                    if len(parts) < 3:
                        continue
                    # 기호 사전의 전각 공백(U+3000)처럼 "공백인 기호"가 있다 — str.strip() 은 이것까지
                    # 지워 빈 글자가 되므로, 기호는 ASCII 공백·탭만 다듬는다.
                    sym = parts[1].strip(" \t\r") if kind == 1 else parts[1].strip()
                    rows.append((parts[0].strip(), sym, parts[2].strip(), kind))
        cur.executemany("INSERT INTO hanja_dict (hangul, hanja, meaning, kind) VALUES (?, ?, ?, ?)", rows)
        huns = []
        for rid, hanja, meaning, kind in cur.execute(
                "SELECT id, hanja, meaning, kind FROM hanja_dict WHERE meaning != ''").fetchall():
            for alt in _split_meanings(meaning):
                huns.append((alt, hanja, rid, kind))
        cur.executemany("INSERT INTO hun (alt, hanja, id, kind) VALUES (?, ?, ?, ?)", huns)
        cur.execute("CREATE INDEX idx_hangul ON hanja_dict (hangul)")
        cur.execute("CREATE INDEX idx_hanja ON hanja_dict (hanja)")
        cur.execute("CREATE INDEX idx_hun ON hun (alt)")
        cur.execute(f"PRAGMA user_version = {SCHEMA_VERSION}")
        conn.commit()
    finally:
        conn.close()
    os.replace(tmp, db_path)
    return len(rows)


class Hanja:
    """사전 DB(읽기)와 사용자 DB(최근 기록)를 묶은 조회 객체. 쓰는 스레드에서 만들 것."""

    def __init__(self, db_path, user_path):
        self.conn = sqlite3.connect(db_path)
        os.makedirs(os.path.dirname(os.path.abspath(user_path)), exist_ok=True)
        self.user = sqlite3.connect(user_path)
        self.user.execute("""CREATE TABLE IF NOT EXISTS recent (
            hangul TEXT NOT NULL, hanja TEXT NOT NULL, last_used INTEGER NOT NULL,
            PRIMARY KEY (hangul, hanja))""")
        self.user.commit()
        self._tick = int(self.user.execute("SELECT COALESCE(MAX(last_used), 0) FROM recent").fetchone()[0])

    def close(self):
        for c in (self.conn, self.user):
            try:
                c.close()
            except sqlite3.Error:
                pass

    def lookup(self, key, recent_first=False):
        """key(한글·`훈 음`·기호 명칭) → [(한자, 읽기, 뜻풀이, kind)] — 사전 순(빈도순). kind 0 = 한자,
        1 = 기호. recent_first 이면 최근에 고른 것이 같은 읽기 안에서 앞선다."""
        c = self.conn
        out = []
        for hanja, meaning, rid, kind in c.execute(
                "SELECT hanja, meaning, id, kind FROM hanja_dict WHERE hangul = ? ORDER BY id", (key,)):
            out.append([hanja, key, meaning, rid, kind])
        # 훈음 `노래 가` 는 공백이 있는 키만, 기호 명칭 `로마숫자일` 은 공백이 없어도 찾는다.
        seen = {o[0] for o in out}
        for hanja, rid, kind in c.execute(
                "SELECT hanja, id, kind FROM hun WHERE alt = ? ORDER BY id", (key,)):
            if hanja in seen or (kind == 0 and " " not in key):
                continue
            seen.add(hanja)
            out.append([hanja, key.rsplit(" ", 1)[-1] if kind == 0 else key, key, rid, kind])
        if recent_first and out:
            readings = sorted({o[1] for o in out})
            used = {}
            for hangul, hanja, ts in self.user.execute(
                    "SELECT hangul, hanja, last_used FROM recent WHERE hangul IN (%s)"
                    % ",".join("?" * len(readings)), readings):
                used[(hangul, hanja)] = ts
            out.sort(key=lambda o: ((0, -used[(o[1], o[0])]) if (o[1], o[0]) in used else (1, 0), o[3]))
        return [(h, r, m, k) for h, r, m, _, k in out]

    def reverse(self, hanja):
        """한자(글자 또는 단어) → [(음/읽기, 훈음 뜻풀이)] — 사전 순. 없으면 []. 기호는 제외한다."""
        return [(h, m) for h, m in self.conn.execute(
            "SELECT hangul, meaning FROM hanja_dict WHERE hanja = ? AND kind = 0 ORDER BY id", (hanja,))]

    def remember(self, hangul, hanja):
        self._tick += 1
        self.user.execute("INSERT OR REPLACE INTO recent (hangul, hanja, last_used) VALUES (?, ?, ?)",
                          (hangul, hanja, self._tick))
        self.user.commit()

    def forget_recent(self):
        self.user.execute("DELETE FROM recent")
        self.user.commit()
        self._tick = 0


def is_key_char(ch):
    return ch == " " or "가" <= ch <= "힣" or "ㄱ" <= ch <= "ㆎ"


def find_candidates(h, text_before, selected="", recent_first=False):
    """후보 목록 [(바꿀 글자 수, 한자, 읽기, 뜻풀이, 뒤에 남는 글자 수, kind)] (kind 1 = 기호).
    선택이 있으면 선택 전체를 한 덩어리로 찾는다(뒤에 남는 글자 0).
    없으면 커서 앞의 한글 낱말(공백 없는 덩어리)을 **앞에서부터** 가장 긴 접두부터 한 글자까지 줄여 가며
    찾는다: `한자입력` 이면 `한자` 를 먼저 보이고(뒤의 `입력` 은 그대로 남는다), 바꾼 뒤 다시 누르면
    `입력` 차례가 된다. 낱말이 한 글자이고 앞에 낱말이 있으면 훈음(`노래 가`)을 가장 먼저 보인다."""
    if selected:
        key = " ".join(selected.split())
        return [(len(selected), hj, r, m, 0, k) for hj, r, m, k in h.lookup(key, recent_first)]
    run = []
    for ch in reversed(text_before):
        if not is_key_char(ch) or len(run) >= MAX_KEY:
            break
        run.append(ch)
    run = "".join(reversed(run))
    word = run.split(" ")[-1]
    out, seen = [], set()

    def add(key, n, tail):
        for hj, r, m, k in h.lookup(key, recent_first):
            if (hj, n, tail) in seen:
                continue
            seen.add((hj, n, tail))
            out.append((n, hj, r, m, tail, k))

    if len(word) == 1 and len(run) > 2 and run[-2] == " ":
        prev = run[:-2].split(" ")[-1]
        if prev:                                   # 훈음: `노래 가`
            add(prev + " " + word, len(prev) + 2, 0)
    for end in range(len(word), 0, -1):
        add(word[:end], end, len(word) - end)
    return out


def is_hanja_char(ch):
    """BMP 의 한자(CJK 통합·확장 A·호환)."""
    return "\u4e00" <= ch <= "\u9fff" or "\u3400" <= ch <= "\u4dbf" or "\uf900" <= ch <= "\ufaff"


def find_reverse(h, text_before, selected=""):
    """한자 → 음 후보 [(글자 수, 한자, 음, 훈음, 뒤에 남는 글자 수, 2)]  (kind 2 = 역조회).
    선택이 있으면 선택 전체(한자로만 이뤄졌을 때), 없으면 커서 앞의 한자 낱말을 **앞에서부터**
    가장 긴 접두부터 한 글자까지 줄여 가며 찾는다(`漢字入力` 이면 `漢字` 먼저, 뒤의 `入力` 은 남는다). 한자가 아니면 None(= 역조회 대상이 아님),
    한자인데 사전에 없으면 [] 를 돌려준다."""
    if selected:
        txt = selected.strip()
        if not txt or not all(is_hanja_char(c) for c in txt):
            return None
        run = txt
        exact = True
    else:
        r = []
        for ch in reversed(text_before):
            if not is_hanja_char(ch) or len(r) >= MAX_KEY:
                break
            r.append(ch)
        if not r:
            return None
        run = "".join(reversed(r))
        exact = False
    out = []
    if exact:
        ends = [len(run)]
    else:                                    # 한자 변환과 같게: 낱말 앞에서부터 가장 긴 접두부터
        ends = range(len(run), 0, -1)
    for end in ends:
        key = run[:end]
        for reading, meaning in h.reverse(key):
            out.append((end, key, reading, meaning, len(run) - end, 2))
    return out
