#!/usr/bin/env python3
"""
tools/font.py -- 폰트 도구: XeLaTeX/LuaLaTeX fontspec 명령 구성기 (oblivoir styler 의 다섯 번째 도구).

독립 실행하던 fontselector.py 를 styler 도구로 옮긴 것이다. 하는 일은 같다:
  * TeX Live 와 시스템의 폰트(.ttf .otf .ttc .otc)를 훑어 목록으로 보여 주고,
  * 고른 폰트로 \\setmainfont · \\setmainhangulfont · \\newfontfamily … 같은 fontspec 명령을 만들고,
  * 고른 폰트로 조판한 모양을 xelatex/lualatex 로 미리 보여 준다.

styler 안에서는
  * 화면은 3단: [무엇을/글꼴] [공통 옵션 + 미리보기] [생성된 LaTeX]
  * export_section() 으로 스타일 파일(.sty)의 한 구역이 된다 (\\fontspec 처럼 본문에서 쓰는 명령은 .sty 에 넣지 못해 뺀다).
  * 미리보기 엔진(xelatex/lualatex)은 이 도구 안에서 고른다: 문서 바의 '엔진'(pdflatex 가 기본)과는 따로다.
    문서 바의 'TeX 폴더'는 그대로 따른다.
  * 화면에 보일 때만 미리보기를 컴파일한다.
  * 설정은 .json 으로 저장/열기 (state / load_state).

ndhmdWriter 와 함께 쓸 때 (Writer 모드, 0.11.x 의 [설정 ▶ 글꼴 설정]):
  python font.py --out 결과.json [--scripts latin|all] [--engine xelatex|lualatex] [--class oblivoir]
                 [--state 이전설정.json] [--texdir TeX폴더]
  전역 글꼴 선언 \\set{main,sans,mono}[hangul|hanja]font 만 다루고(\\newfontfamily · \\fontspec 은 숨김),
  [Writer 로 보내기]를 누르면 결과(.tex 코드 + 다시 열 설정)를 --out 파일에 쓰고 종료코드 0 으로 닫는다.
  인자 없이 실행하거나 styler 안에서 쓰면 예전과 똑같다 (Writer 모드는 writer= 로 켠다).

필요한 것: PySide6. 있으면 좋은 것: fontTools(폰트 내부 이름), kpsewhich(TeX Live 폰트 위치).
폰트 목록 캐시: ~/.ndhmd_font_scan_cache.json  (🔄 스캔 단추로 갱신)
설정(엔진·문서 클래스·미리보기 문장): QSettings("oblivoir-tools", "fontselector")
"""
import sys
import os
import platform
import glob
import subprocess
import json
import re
import shutil
import tempfile
from pathlib import Path

from PySide6.QtWidgets import (QApplication, QWidget, QVBoxLayout,
                               QHBoxLayout, QLabel, QComboBox, QLineEdit,
                               QPlainTextEdit, QGroupBox, QCheckBox, QPushButton,
                               QRadioButton, QGridLayout, QButtonGroup,
                               QScrollArea, QFileDialog, QMessageBox,
                               QCompleter, QSplitter, QSizePolicy, QToolButton)
from PySide6.QtCore import Qt, QThread, Signal, QTimer, QSettings, QSize
from PySide6.QtGui import (QColor, QBrush, QStandardItemModel, QStandardItem,
                           QFontDatabase, QImage, QPainter, QPixmap, QFont)

try:
    from fontTools.ttLib import TTFont, TTCollection
    HAS_FONTTOOLS = True
except ImportError:
    HAS_FONTTOOLS = False

try:
    from PySide6.QtPdf import QPdfDocument
    HAS_QTPDF = True
except ImportError:                      # 드물다: 미리보기만 못 그린다
    HAS_QTPDF = False

#: 폰트 목록 캐시. 옛 fontselector.py 가 같은 이름의 파일을 다른 형식으로 써서 서로 덮어쓰던 것을 이름으로 갈랐다.
CACHE_FILE = Path.home() / ".ndhmd_font_scan_cache.json"
SETTINGS_ORG, SETTINGS_APP = "oblivoir-tools", "fontselector"
ENGINES = ("xelatex", "lualatex")          # 미리보기 컴파일러 (pdflatex 는 fontspec 을 못 쓴다)
DEFAULT_ENGINE = "xelatex"
DOC_CLASSES = ("article", "oblivoir", "memoir", "book")
DEFAULT_CLASS = "article"
#: luatexko(lualatex)만 아는 글꼴 옵션. xelatex(xetexko)에는 이 키가 없어서 fontspec 오류가 난다.
LUATEXKO_ONLY_OPTIONS = ("CompressPunctuations",)
PREVIEW_DELAY_MS = 700                      # 입력이 멈춘 뒤 컴파일 (타이핑 중 컴파일 방지)
PREVIEW_TIMEOUT_S = 180                     # lualatex 는 처음에 폰트 캐시를 만드느라 오래 걸릴 수 있다
VERSION = "1.1.1"                             # 이 도구의 버전 (styler 전체 버전과 따로)
CACHE_VERSION = 4                           # 캐시 형식이 바뀌면 올린다 (2: ttc/otc 포함, 3: 서체 번호 추가)
import logging
logging.getLogger("fontTools").setLevel(logging.ERROR)    # "skipping malformed name record" 같은 경고가 터미널을 덮지 않게
FONT_PATTERNS = ('*.ttf', '*.otf', '*.ttc', '*.otc', '*.TTF', '*.OTF', '*.TTC', '*.OTC')
TTC_COLOR = QColor(200, 0, 0)               # 콤보에서 ttc/otc 를 알리는 빨간색
TTC_COLOR_DARK = QColor(255, 120, 120)      # 어두운 배경(다크 모드)에서는 밝은 빨강: 어두운 빨강은 거기서 읽히지 않는다


def find_tex_exe(name, texdir=""):
    """TeX 실행 파일 찾기. 문서 바의 'TeX 폴더'가 있으면 거기를 먼저, 없으면 PATH 에서."""
    if texdir:
        for cand in (name + ".exe", name) if sys.platform == "win32" else (name,):
            p = Path(texdir) / cand
            if p.is_file():
                return str(p)
    return shutil.which(name)


def get_font_index(feats):
    """Features 문자열에서 FontIndex=N 의 N (없으면 None)."""
    m = re.search(r"(?:^|,)\s*FontIndex\s*=\s*(\d+)\s*(?=,|$)", feats or "")
    return int(m.group(1)) if m else None


def set_font_index(feats, idx):
    """Features 문자열의 FontIndex 를 idx 로 바꾼다. idx 가 None 이면 지운다. 나머지 옵션은 그대로."""
    parts, depth, cur = [], 0, ""
    for ch in (feats or ""):                     # {…} 안의 쉼표는 나누지 않는다 (Numbers={OldStyle,Lining})
        depth += (ch == "{") - (ch == "}")
        if ch == "," and depth <= 0:
            parts.append(cur); cur = ""
        else:
            cur += ch
    parts.append(cur)
    parts = [p.strip() for p in parts]
    parts = [p for p in parts if p and not re.fullmatch(r"FontIndex\s*=\s*\d+", p)]
    if idx is not None:
        parts.append(f"FontIndex={int(idx)}")
    return ",".join(parts)


REGULAR_LIKE = ("", "regular", "book", "roman", "normal")


def _clean_name(text):
    """name 레코드 글자: 앞뒤 공백을 없애고, 제어 문자(널 등)가 섞인 깨진 값은 None."""
    if not text:
        return None
    text = str(text).strip()
    if not text or any(ord(ch) < 32 for ch in text):
        return None
    return text


def _postscript_like(name):
    """PostScript 이름처럼 생겼나: 공백이 없고 하이픈이 있다 (TeXGyrePagella-Regular)."""
    return bool(name) and not re.search(r"\s", name) and "-" in name


def portable_font_name(full, family, sub, typo_family=None, typo_sub=None):
    """폰트 이름 하나를 고른다: 풀 네임(ID 4)이 정상적인 이름이면 그대로, PostScript 이름처럼 보일 때만
    Family(ID 16, 없으면 1) 로 바꾼다 — 기본 서체(Regular·Book…)면 Family 만, 아니면 'Family Subfamily'.
    Family·Subfamily 가 비었거나 깨졌거나 그것도 PostScript 이름 같으면 풀 네임(없으면 ID 1) 그대로."""
    full = _clean_name(full)
    if full and not _postscript_like(full):
        return full
    fam = _clean_name(typo_family) or _clean_name(family)
    st = _clean_name(typo_sub) or _clean_name(sub) or ""
    if not fam or _postscript_like(fam):
        return full or _clean_name(family)
    if st.lower() in REGULAR_LIKE:
        return fam
    if _postscript_like(st) or not st:
        return full or fam
    return f"{fam} {st}"


def is_collection(file_name):
    """ttc/otc (여러 서체가 든 묶음 파일) 인가."""
    return str(file_name).lower().endswith((".ttc", ".otc"))


CREATE_NO_WINDOW = 0x08000000               # Windows 에서 콘솔 창이 깜박이지 않게 (subprocess.CREATE_NO_WINDOW)

#: 미리보기 기본 문장 — 문자(script)마다 하나씩
DEFAULT_SAMPLES = {
    "latin":  "The quick brown fox jumps over the lazy dog",
    "hangul": "하수는 두 산 틈에서 나와 돌과 부딪쳐 싸우며",
    "hanja":  "河出兩山間 觸石鬪狠 其驚濤駭浪",    # 狠(U+72E0)은 1수준 한자가 아니다 — 폰트가 한자를 얼마나 지원하는지 가늠하는 데 쓴다
}
#: 예전 버전의 기본 문장 (저장된 설정에 남아 있으면 새 기본값으로 바꿔 읽는다)
LEGACY_SAMPLES = {"hanja": ("河出兩山間 觸石鬪狼 其驚濤駭浪",)}


class FontScannerThread(QThread):
    fonts_found = Signal(list)

    def __init__(self, force_rescan=False, texdir=""):
        super().__init__()
        self.force_rescan = force_rescan
        self.texdir = texdir

    def run(self):
        if not self.force_rescan and CACHE_FILE.exists():
            try:
                with open(CACHE_FILE, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    cached_fonts = data.get('fonts', [])
                    if data.get('version') == CACHE_VERSION and cached_fonts and len(cached_fonts[0]) in (3, 4):
                        self.fonts_found.emit([tuple(f) + (None,) * (4 - len(f)) for f in cached_fonts])
                        return
            except Exception as e:
                print(f"캐시 읽기 실패: {e}")

        texmf_paths, sys_paths = self.get_search_directories()
        texlive_fonts, system_fonts = set(), set()

        for path in texmf_paths: self._scan_dir(path, texlive_fonts)
        for path in sys_paths: self._scan_dir(path, system_fonts)

        system_fonts = system_fonts - texlive_fonts

        result_list = [(fname, file_n, True, idx) for fname, file_n, idx in list(texlive_fonts)] + \
                      [(fname, file_n, False, idx) for fname, file_n, idx in list(system_fonts)]

        try:
            with open(CACHE_FILE, 'w', encoding='utf-8') as f:
                json.dump({'version': CACHE_VERSION, 'fonts': result_list}, f, ensure_ascii=False)
        except Exception as e:
            print(f"캐시 저장 실패: {e}")

        self.fonts_found.emit(result_list)

    def _scan_dir(self, path_str, target_set):
        p = Path(path_str)
        if not p.exists() or not p.is_dir(): return
        for ext in FONT_PATTERNS:
            for font_file in p.rglob(ext):
                target_set.update(self.extract_font_infos(font_file))

    def get_search_directories(self):
        system = platform.system()
        texmf_paths, sys_paths = [], []

        try:
            kpse = find_tex_exe('kpsewhich', self.texdir) or 'kpsewhich'
            result = subprocess.check_output([kpse, '-expand-path', '$TEXMF'], text=True, encoding='utf-8', **no_window_kwargs())
            sep = ';' if system == 'Windows' else ':'
            raw_paths = result.strip().split(sep)
            for p in raw_paths:
                p = p.strip()
                if p.startswith('!!'): p = p[2:]
                if p and os.path.exists(p):
                    texmf_paths.append(os.path.join(p, 'fonts', 'truetype'))
                    texmf_paths.append(os.path.join(p, 'fonts', 'opentype'))
        except Exception:
            pass

        if not texmf_paths:
            base_dirs = [r'C:\texlive'] if system == 'Windows' else ['/usr/local/texlive', '/usr/share/texlive']
            for base in base_dirs:
                if os.path.exists(base):
                    for year_dir in glob.glob(os.path.join(base, '20*')):
                        texmf_paths.append(os.path.join(year_dir, 'texmf-dist', 'fonts', 'truetype'))
                        texmf_paths.append(os.path.join(year_dir, 'texmf-dist', 'fonts', 'opentype'))

        if system == 'Windows':
            sys_paths.append(r'C:\Windows\Fonts')
            local_app_data = os.environ.get('LOCALAPPDATA', '')
            if local_app_data: sys_paths.append(os.path.join(local_app_data, 'Microsoft', 'Windows', 'Fonts'))
        elif system == 'Darwin':
            sys_paths.extend(['/System/Library/Fonts', '/Library/Fonts', os.path.expanduser('~/Library/Fonts')])
        elif system == 'Linux':
            sys_paths.extend(['/usr/share/fonts', '/usr/local/share/fonts', os.path.expanduser('~/.fonts'), os.path.expanduser('~/.local/share/fonts')])

        return texmf_paths, sys_paths

    def extract_font_info(self, filepath):
        n, f, _i = self.extract_font_infos(filepath)[0]
        return n, f

    def extract_font_infos(self, filepath):
        """[(폰트 이름, 파일 이름, 서체 번호), ...]. ttc/otc 는 안에 든 서체마다 하나씩(번호 0, 1, …), 나머지는 하나(번호 None)."""
        file_name = filepath.name
        if not HAS_FONTTOOLS:
            return [(filepath.stem, file_name, 0 if is_collection(file_name) else None)]
        faces = []
        try:
            if is_collection(file_name):
                n = len(TTCollection(filepath, lazy=True).fonts)
            else:
                n = 1
            for i in range(n):
                font = TTFont(filepath, fontNumber=i, lazy=True)
                nm = font['name']
                rec = portable_font_name(nm.getDebugName(4), nm.getDebugName(1), nm.getDebugName(2),
                                         nm.getDebugName(16), nm.getDebugName(17))
                if rec: faces.append((rec, file_name, i if is_collection(file_name) else None))
        except Exception:
            pass
        return faces or [(filepath.stem, file_name, 0 if is_collection(file_name) else None)]


# ---------------------------------------------------------------------
# 명령 이름 규칙 — 방식 × 계열 × 문자  →  fontspec 명령
# ---------------------------------------------------------------------
MODES = [
    ("set",  "기본 글꼴 설정", r"문서 전체의 글꼴을 바꾼다:  \setmainfont 따위"),
    ("new",  "새 글꼴 패밀리", r"이름을 붙여 두고 필요할 때 쓴다:  \newfontfamily\이름{…}"),
    ("spec", "즉석 적용",     r"그 자리에서 한 번만 쓴다:  \fontspec{…}"),
]
FAMILIES = [
    ("main", "본문 main",    "바탕이 되는 글꼴 (roman, 명조/바탕)"),
    ("sans", "산세리프 sans", "\\sffamily 가 쓰는 글꼴 (고딕)"),
    ("mono", "고정폭 mono",  "\\ttfamily 가 쓰는 글꼴"),
]
SCRIPTS = [
    ("latin",  "라틴 latin",   "알파벳 · 숫자 · 일반 문장부호"),
    ("hangul", "한글 hangul",  "한글 (xetexko / luatexko)"),
    ("hanja",  "한자 hanja",   "한자 (xetexko / luatexko)"),
]


def compose(mode, family, script):
    """(방식, 계열, 문자) → fontspec 명령.  예) ('set','main','hangul') → \\setmainhangulfont"""
    s = "" if script == "latin" else script
    if mode == "set":
        return rf"\set{family}{s}font"
    if mode == "new":
        return rf"\new{s}fontfamily"
    return rf"\{s}fontspec"


#: 명령 문자열 -> (방식, 계열, 문자).  '새 패밀리'와 '즉석 적용'에는 계열이 없다(None).
CMD_INFO = {}
for _m in ("set", "new", "spec"):
    for _f in (("main", "sans", "mono") if _m == "set" else (None,)):
        for _s in ("latin", "hangul", "hanja"):
            CMD_INFO[compose(_m, _f or "main", _s)] = (_m, _f, _s)

FAMILY_SWITCH = {"main": r"\rmfamily", "sans": r"\sffamily", "mono": r"\ttfamily"}
STYLE_SWITCH = {"Bold": r"\bfseries", "Italic": r"\itshape", "BoldItalic": r"\bfseries\itshape", "SmallCaps": r"\scshape"}
PREVIEW_STYLES = ("Bold", "Italic", "BoldItalic", "SmallCaps")
SCALE_OPTIONS = ("Scale=MatchLowercase", "Scale=MatchUppercase")      # 둘 중 하나만
RENDERER_OPTIONS = ("Renderer=Node", "Renderer=OpenType", "Renderer=Base", "Renderer=HarfBuzz", "Renderer=Graphite")   # 하나만, Node 가 맨 위
VERTICAL_OPT = "Vertical=Alternates,RawFeature=vertical"    # '세로쓰기' 체크칸이 내보내는 옵션
PRESET_TIPS = {
    "CompressPunctuations": "luatexko(lualatex)가 아는 옵션입니다. xelatex 로 컴파일하는 문서에서는 fontspec 오류가 납니다.\n"
                            "(미리보기는 xelatex 일 때 이 옵션만 빼고 그립니다.)",
    VERTICAL_OPT: "세로쓰기: " + VERTICAL_OPT,
}
PRESET_ORDER = ("Ligatures=TeX",) + RENDERER_OPTIONS + ("Scale=MatchLowercase", "Scale=MatchUppercase",
                "Script=Hangul", "CompressPunctuations", VERTICAL_OPT)                # 결과 코드에 나오는 순서
AUTO_FAMILY_STYLES = ("Bold", "Italic", "BoldItalic")
AUTO_FAMILY_STYLES_CJK = ("Bold",)                         # 한글·한자 폰트: 기울임은 시험하지 않는다     # 본문만 폰트 이름으로 줬을 때 fontspec 이 가족에서 찾아 줄 수 있는 것들


def looks_like_file(name):
    """폰트 '파일' 이름처럼 보이는가 (.ttf .otf .ttc .otc). 이름으로 가족을 찾을 수 없는 경우를 가려내는 데 쓴다."""
    return str(name).strip().lower().endswith((".ttf", ".otf", ".ttc", ".otc"))


def normalize_newlines(text):
    """줄바꿈을 모두 \\n 하나로: \\r\\n · \\r\\r\\n · 외톨이 \\r 을 한 줄바꿈으로 합친다.
    (Qt 는 '\\r\\r\\n' 을 줄바꿈 두 개로 읽어 줄 사이에 빈 줄이 생긴다 — 폰트 이름·붙여넣은 글에 \\r 이 섞이면 Windows 에서 이런 일이 생길 수 있다.)"""
    return re.sub(r"\r*\n|\r", "\n", text)


def tidy_block(text):
    """명령 하나의 코드: 줄바꿈을 통일하고, 블록 안에는 빈 줄을 두지 않는다 (빈 줄은 명령과 명령 사이에만 들어간다)."""
    return "\n".join(ln for ln in normalize_newlines(text).split("\n") if ln.strip())


def monospace_font(point_size=10):
    """코드 칸용 고정폭 글꼴: 흔한 고정폭 글꼴을 이름으로 먼저 찾고, 없으면 시스템의 고정폭 글꼴."""
    fams = set(QFontDatabase.families())
    for name in ("Consolas", "Menlo", "DejaVu Sans Mono", "Liberation Mono", "Courier New"):
        if name in fams:
            f = QFont(name, point_size)
            f.setStyleHint(QFont.Monospace)
            f.setFixedPitch(True)
            return f
    f = QFontDatabase.systemFont(QFontDatabase.FixedFont)
    f.setPointSize(point_size)
    return f


def tex_escape(text):
    """미리보기 문장·이름을 TeX 에 그대로 넣을 수 있게 특수 문자를 이스케이프한다."""
    out = []
    for ch in text:
        if ch == "\\":
            out.append(r"\textbackslash{}")
        elif ch in "_&%#${}":
            out.append("\\" + ch)
        elif ch == "^":
            out.append(r"\textasciicircum{}")
        elif ch == "~":
            out.append(r"\textasciitilde{}")
        else:
            out.append(ch)
    return "".join(out)


def build_preview_tex(items, doc_class, samples, kotex=True):
    """미리보기용 .tex 와 경고 목록을 만든다.  (Qt 없이 시험할 수 있는 순수 함수)

    items    지정된 명령들: {'cmd_id', 'block', 'styles': ['Bold', ...], 'macro': '\\kor' 또는 None}
             block 은 결과 칸에 나오는 그 명령의 코드 그대로다 — 미리보기는 결과와 같은 코드를 쓴다.
    samples  {'latin': ..., 'hangul': ..., 'hanja': ...}
    kotex    False 면 kotex 를 불러오지 않고 fontspec 만 부른다(한글·한자를 안 쓰는 문서의 모양).

    구조: 클래스 + kotex + (\\set…font, \\new…fontfamily 블록들) + 명령마다 한 묶음의 본문.
      * \\set…font       계열 전환(\\rmfamily/\\sffamily/\\ttfamily) 안에서 그 문자의 문장
      * \\new…fontfamily  정의한 매크로로 그 문자의 문장
      * \\fontspec 류    본문 안에서 그 자리에 써서 그 문자의 문장 (프리앰블에 둘 수 없다)
      * 굵게/기울임/굵은 기울임/작은 대문자는 지정한 것만 줄을 더한다.
    """
    warnings, pre, body, macros = [], [], [], {}
    for it in items:
        mode, fam, script = CMD_INFO[it["cmd_id"]]
        if mode in ("set", "new"):
            pre.append(it["block"])
        if mode == "new":
            m = it["macro"]
            if m in macros:
                warnings.append("매크로 이름 %s 이(가) %s 와 %s 에 겹쳐 쓰였습니다 — 서로 다른 이름을 주세요." % (m, macros[m], it["cmd_id"]))
            macros[m] = it["cmd_id"]
        sample = tex_escape(samples.get(script, DEFAULT_SAMPLES[script]))
        label = tex_escape(it["cmd_id"] + (it["macro"] or ""))
        if it.get("auto"):
            label += " \\textperiodcentered{} 굵게/기울임: 폰트 가족에서 자동 검출"
        body.append("{\\footnotesize %s}\\par\\nopagebreak" % label)
        for style in ("Upright (Main)",) + tuple(it["styles"]):
            sw = STYLE_SWITCH.get(style, "")
            if mode == "set":
                inner = "%s%s %s" % (FAMILY_SWITCH[fam], sw, sample)
            elif mode == "new":
                inner = "%s%s %s" % (it["macro"], sw, sample)
            else:
                inner = "%s\n%s %s" % (it["block"], sw, sample)
            body.append("{%s}\\par" % inner)
        body.append("\\medskip")
    cls = (doc_class or "").strip() or DEFAULT_CLASS
    tex = "\n".join([
        "\\documentclass{%s}" % cls,
        "\\usepackage{kotex}" if kotex else "\\IfPackageLoadedTF{fontspec}{}{\\usepackage{fontspec}}",
        "\n\n".join(pre),
        "\\pagestyle{empty}",
        "\\setlength{\\parindent}{0pt}",
        "\\begin{document}",
        "\\large",
        "\n".join(body),
        "\\end{document}",
    ]) + "\n"
    return tex, warnings


def no_window_kwargs():
    """subprocess 에 줄 인자: Windows 에서만 콘솔 창을 만들지 않는다."""
    return {"creationflags": CREATE_NO_WINDOW} if sys.platform == "win32" else {}


_MISSING_RE = re.compile(r"Missing character: There is no (\S+) \(U\+([0-9A-Fa-f]+)\) in font ([^/\n]*?)(?:/|\s*$|!)")


def missing_glyphs(log_text):
    """TeX 로그에서 '글자가 폰트에 없다'는 경고를 모은다: [(글자, 코드포인트, 폰트 이름)] (중복 없이, 나온 순서대로).
    미리보기가 그려지긴 했어도 빈 칸(또는 대체 글꼴)으로 나온 글자를 알려 주는 데 쓴다 — 폰트의 한자 지원 범위를 가늠할 수 있다."""
    seen, out = set(), []
    for m in _MISSING_RE.finditer(log_text):
        ch, cp, font = m.group(1), int(m.group(2), 16), m.group(3).strip()
        if (cp, font) in seen:
            continue
        seen.add((cp, font))
        out.append((ch, cp, font))
    return out


def extract_error(log_text, tail=14):
    """TeX 로그에서 사용자에게 보여 줄 오류 부분: 처음 '!' 줄부터 몇 줄, 없으면 로그의 끝."""
    lines = log_text.splitlines()
    for i, ln in enumerate(lines):
        if ln.startswith("!"):
            return "\n".join(lines[i:i + 8])
    return "\n".join(lines[-tail:])


class PreviewThread(QThread):
    """TeX 를 한 번 돌려 PDF 를 만든다. (job 번호는 낡은 결과를 가려내는 데 쓴다)"""
    done = Signal(int, bool, str, str)         # job, 성공?, pdf 경로, (오류면) 설명

    def __init__(self, job, engine, workdir, texdir=""):
        super().__init__()
        self.job, self.engine, self.workdir, self.texdir = job, engine, workdir, texdir
        self._proc = None
        self._cancel = False

    def cancel(self):
        self._cancel = True
        p = self._proc
        if p is not None:
            try:
                p.kill()
            except Exception:
                pass

    def command(self, exe):
        return [exe, "-interaction=nonstopmode", "-halt-on-error", "preview.tex"]

    def run(self):
        exe = find_tex_exe(self.engine, self.texdir)
        if not exe:
            self.done.emit(self.job, False, "", "%s 을(를) 찾을 수 없습니다.\nTeX Live 를 설치했는지, PATH 에 있는지 확인하세요." % self.engine)
            return
        try:
            self._proc = subprocess.Popen(self.command(exe), cwd=self.workdir, stdin=subprocess.DEVNULL,
                                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, **no_window_kwargs())
            try:
                out, _ = self._proc.communicate(timeout=PREVIEW_TIMEOUT_S)
            except subprocess.TimeoutExpired:
                self._proc.kill()
                self._proc.communicate()
                self.done.emit(self.job, False, "", "시간 초과(%d초): 컴파일이 끝나지 않아 멈췄습니다." % PREVIEW_TIMEOUT_S)
                return
        except OSError as e:
            self.done.emit(self.job, False, "", "컴파일러를 실행하지 못했습니다: %s" % e)
            return
        if self._cancel:
            return
        pdf = os.path.join(self.workdir, "preview.pdf")
        log = ""
        try:
            log = Path(self.workdir, "preview.log").read_text(encoding="utf-8", errors="replace")
        except OSError:
            pass
        if self._proc.returncode == 0 and os.path.exists(pdf):
            # 성공이면 message 에는 '글자 없음' 경고 줄들만 싣는다
            self.done.emit(self.job, True, pdf, "\n".join(ln for ln in log.splitlines() if "Missing character:" in ln))
            return
        self.done.emit(self.job, False, "", extract_error(log or out.decode("utf-8", errors="replace")))


def crop_whitespace(img, margin=10):
    """이미지의 흰 여백을 잘라 낸다 (글이 있는 부분 + margin)."""
    img = img.convertToFormat(QImage.Format_RGB32)
    w, h, bpl = img.width(), img.height(), img.bytesPerLine()
    data = bytes(img.constBits())
    white = b"\xff" * (w * 4)
    top = bottom = None
    left, right = w * 4, 0
    for y in range(h):
        row = data[y * bpl:y * bpl + w * 4]
        if row != white:
            if top is None:
                top = y
            bottom = y
            left = min(left, len(row) - len(row.lstrip(b"\xff")))
            right = max(right, len(row.rstrip(b"\xff")))
    if top is None:
        return img
    x0, x1 = max(0, left // 4 - margin), min(w, (right + 3) // 4 + margin)
    y0, y1 = max(0, top - margin), min(h, bottom + 1 + margin)
    return img.copy(x0, y0, x1 - x0, y1 - y0)


def render_pdf(path, scale=1.6, max_pages=4):
    """PDF 의 앞쪽 쪽들을 하나의 QImage 로 세로로 이어 붙인다 (여백은 잘라 낸다). 못 그리면 None."""
    if not HAS_QTPDF:
        return None
    doc = QPdfDocument()
    if doc.load(path) != QPdfDocument.Error.None_:
        return None
    try:
        pages = []
        for n in range(min(doc.pageCount(), max_pages)):
            sz = doc.pagePointSize(n)
            size = QSize(max(1, int(sz.width() * scale)), max(1, int(sz.height() * scale)))
            raw = doc.render(n, size)
            canvas = QImage(size, QImage.Format_RGB32)
            canvas.fill(QColor("white"))
            pt = QPainter(canvas)
            pt.drawImage(0, 0, raw)
            pt.end()
            pages.append(crop_whitespace(canvas))
        if not pages:
            return None
        gap = 14
        out = QImage(max(p.width() for p in pages), sum(p.height() for p in pages) + gap * (len(pages) - 1), QImage.Format_RGB32)
        out.fill(QColor("white"))
        pt = QPainter(out)
        y = 0
        for p in pages:
            pt.drawImage(0, y, p)
            y += p.height() + gap
        pt.end()
        return out
    finally:
        doc.close()


class Segmented(QWidget):
    """서로 배타적인 단추 한 줄(라디오 대신). 선택된 것이 강조색으로 보인다."""
    changed = Signal(object)

    _CSS = ("QPushButton[seg='true'] { padding: 5px 12px; border: 1px solid palette(mid);"
            " background: palette(button); color: palette(button-text); }"
            "QPushButton[seg='true']:hover { border-color: palette(highlight); }"
            "QPushButton[seg='true']:checked { background: palette(highlight);"
            " color: palette(highlighted-text); border-color: palette(highlight); font-weight: bold; }"
            "QPushButton[seg='true']:disabled { color: palette(mid); background: palette(window); }")

    def __init__(self, items, min_width=0, parent=None):
        super().__init__(parent)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(0)
        self._group = QButtonGroup(self)
        self._group.setExclusive(True)
        self._buttons = {}
        for i, (value, text, tip) in enumerate(items):
            b = QPushButton(text)
            b.setCheckable(True)
            b.setProperty("seg", True)
            b.setToolTip(tip)
            b.setMinimumWidth(min_width)
            b.setFocusPolicy(Qt.TabFocus)
            if i == 0:
                b.setChecked(True)
            self._group.addButton(b)
            lay.addWidget(b)
            self._buttons[value] = b
        lay.addStretch(1)
        self.setStyleSheet(self._CSS)
        self._notify = True
        self._group.buttonToggled.connect(self._on_toggled)

    def _on_toggled(self, button, checked):
        if checked and self._notify:
            self.changed.emit(self.value())

    def value(self):
        for v, b in self._buttons.items():
            if b.isChecked():
                return v
        return None

    def set_value(self, value, notify=True):
        self._notify = notify
        try:
            self._buttons[value].setChecked(True)
        finally:
            self._notify = True

    def button(self, value):
        return self._buttons[value]


class _FocusEdit(QLineEdit):
    """포커스를 받으면 알려 주는 입력칸 — 이 칸을 누르면 그 줄이 "받는 줄"이 된다."""
    focused = Signal()

    def focusInEvent(self, e):
        super().focusInEvent(e)
        self.focused.emit()


class FontPage(QWidget):
    """fontspec 설정(\\setmainfont 등)을 스캔한 폰트 목록에서 골라 구성하는 창.

    결과는 아래 "생성된 LaTeX" 칸에 누적되며, 복사해서 YAML frontmatter 의
    preamble: 이나 .tex 프리앰블에 붙여 쓴다.
    """

    #: \newfontfamily 계열은 이름을 새로 붙여야 하고, \fontspec 계열은
    #: 그 자리에서 바로 쓰는 것이라 이름이 필요 없다.
    NEEDS_MACRO_NAME = (r"\newfontfamily", r"\newhangulfontfamily", r"\newhanjafontfamily")

    #: 한글/한자 문자에서만 뜻이 있는 공통 옵션 — 라틴 명령에서는 고를 수 없다.
    HANGUL_ONLY_PRESETS = ("CompressPunctuations", VERTICAL_OPT)

    STYLE_LABELS = {
        "Upright (Main)": "본문 Upright",
        "Bold": "굵게 Bold",
        "Italic": "기울임 Italic",
        "BoldItalic": "굵은 기울임 BoldItalic",
        "SmallCaps": "작은 대문자 SmallCaps",
    }

    status = Signal(str)                     # 셸의 상태줄로 보낼 메시지

    def __init__(self, parent=None, embedded=False, writer=None):
        super().__init__(parent)
        self.embedded = bool(embedded)
        #: ndhmdWriter 모드 (None 이면 예전과 똑같다): {"scripts": "latin"|"all", "engine": …, "class": …, "out": 경로}
        self.writer = dict(writer) if writer else None
        self._sent = False                   # [Writer 로 보내기]를 눌렀는가
        self.pdf_off = False                 # 문서 바의 엔진이 pdflatex 이면 True: 도구를 흐리게 하고 내보내지 않는다
        self._active = not self.embedded     # 셸 안에서는 화면에 보일 때만 컴파일·스캔한다 (set_active)
        self._dirty = False                  # 숨어 있는 동안 미리보기를 다시 만들 일이 생겼는가
        self._scan_started = False
        self.tex_dir = ""                    # 문서 바의 'TeX 폴더' (set_tex_dir)

        self.font_styles = ["Upright (Main)", "Bold", "Italic", "BoldItalic", "SmallCaps"]
        # 출력 순서: 기본 9개(문자별로 main·sans·mono) → 새 패밀리 3개 → 즉석 3개
        self.cmd_order = [compose("set", f, s) for s in ("latin", "hangul", "hanja")
                          for f in ("main", "sans", "mono")]
        self.cmd_order += [compose(m, "main", s) for m in ("new", "spec")
                           for s in ("latin", "hangul", "hanja")]
        self.states = {cmd: self.empty_state() for cmd in self.cmd_order}
        self.current_cmd_id = r"\setmainfont"
        self.target_style = "Upright (Main)"
        self._is_loading_state = False
        self.full_font_data = []
        self.scanner = None
        self._shown_mode = "name"            # 콤보 목록이 지금 보여 주는 기준: "name"(폰트 이름) | "file"(파일 이름)
        self._pending_sel = None             # 다시 스캔하는 동안 기억해 둘 선택
        self._picked = {}                    # (명령, 줄) -> (목록 항목, 넣은 글자): 콤보에서 골라 넣은 칸들. 기준을 바꾸면 이 칸들도 바꾼다
        self.qs = QSettings(SETTINGS_ORG, SETTINGS_APP)
        self._pv_job = 0                     # 미리보기 컴파일 번호 (낡은 결과를 버리는 데 쓴다)
        self._pv_threads = set()
        self._pv_tmp = None
        self._pv_last_key = None             # 마지막으로 성공한 (엔진, 소스) — 같으면 다시 컴파일하지 않는다
        self.preview_image = None
        self.preview_missing = []            # 마지막 성공한 미리보기에서 폰트에 글리프가 없던 글자들
        self._pv_timer = QTimer(self)
        self._pv_timer.setSingleShot(True)
        self._pv_timer.setInterval(PREVIEW_DELAY_MS)
        self._pv_timer.timeout.connect(self._preview_timeout)

        outer = QVBoxLayout(self)
        outer.setContentsMargins(10, 10, 10, 10)
        outer.setSpacing(8)

        # ---------------------------------------------------------
        # 맨 위: 폰트 고르기 (캐시한 폰트 이름 목록)
        # ---------------------------------------------------------
        top = QVBoxLayout()
        top.setSpacing(3)
        row = QHBoxLayout()
        lbl = QLabel("<b>폰트</b>")
        row.addWidget(lbl)

        self.font_model = QStandardItemModel(self)
        self.font_combo = QComboBox()
        self.font_combo.setEditable(True)
        self.font_combo.setInsertPolicy(QComboBox.NoInsert)
        self.font_combo.setModel(self.font_model)
        self.font_combo.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.font_combo.setMaxVisibleItems(18)
        self.font_combo.setMinimumContentsLength(24)
        completer = QCompleter(self.font_model, self)
        completer.setCaseSensitivity(Qt.CaseInsensitive)
        completer.setFilterMode(Qt.MatchContains)
        completer.setCompletionMode(QCompleter.PopupCompletion)
        self.font_combo.setCompleter(completer)
        self.font_combo.lineEdit().setClearButtonEnabled(True)
        self.font_combo.lineEdit().setPlaceholderText("폰트를 고르거나, 이름 일부를 쳐서 찾기 (예: noto, 바탕, gothic)")
        self.font_combo.activated.connect(self._on_font_picked)
        row.addWidget(self.font_combo, 1)
        self.fill_btn = QPushButton("↳ 받는 줄에 넣기")
        self.fill_btn.setToolTip("지금 위 칸에 골라 둔 폰트를 '받는 줄'(아래에서 눌러 둔 줄)에 넣는다.\n"
                                 "이미 골라 둔 폰트를 Bold·Italic 등에도 쓸 때 — 콤보에서 Enter 를 쳐도 같다.")
        self.fill_btn.clicked.connect(self.fill_selected)
        row.addWidget(self.fill_btn)
        self.font_combo.lineEdit().returnPressed.connect(self.fill_selected)

        self.seg_view = Segmented([("name", "폰트 이름", "폰트 내부 이름으로 보인다 (fontspec 에 이름으로 넘길 때)"),
                                   ("file", "파일 이름", "파일 이름으로 보인다 (fontspec 에 파일로 넘길 때)")])
        row.addWidget(self.seg_view)
        self.seg_view.changed.connect(self._on_view_changed)

        self.refresh_btn = QPushButton("🔄 스캔")
        self.refresh_btn.setToolTip("디스크를 다시 훑어 폰트 목록(캐시)을 새로 만든다")
        self.refresh_btn.clicked.connect(self.force_rescan_fonts)
        row.addWidget(self.refresh_btn)
        top.addLayout(row)

        self.scan_status = QLabel("폰트 목록을 불러오는 중…")
        self.scan_status.setEnabled(False)   # 흐린 글씨(테마 색을 따른다)
        top.addWidget(self.scan_status)
        outer.addLayout(top)

        # ---------------------------------------------------------
        # 스크롤 영역: 무엇을 지정할까 / 글꼴 / 공통 옵션
        # ---------------------------------------------------------
        scroll_host = QWidget()
        main_layout = QVBoxLayout(scroll_host)
        main_layout.setContentsMargins(0, 0, 4, 0)
        main_layout.setSpacing(8)

        # ---- 1. 무엇을 지정할까 ---------------------------------
        cmd_group = QGroupBox("1. 무엇을 지정할까요")
        g = QGridLayout(cmd_group)
        g.setHorizontalSpacing(10)
        g.setVerticalSpacing(6)

        self.lbl_mode = QLabel("방식")
        g.addWidget(self.lbl_mode, 0, 0)
        self.seg_mode = Segmented([(k, t, tip) for k, t, tip in MODES], min_width=110)
        g.addWidget(self.seg_mode, 0, 1)

        g.addWidget(QLabel("계열"), 1, 0)
        self.seg_family = Segmented([(k, t, tip) for k, t, tip in FAMILIES], min_width=110)
        g.addWidget(self.seg_family, 1, 1)

        g.addWidget(QLabel("문자"), 2, 0)
        self.seg_script = Segmented([(k, t, tip) for k, t, tip in SCRIPTS], min_width=110)
        g.addWidget(self.seg_script, 2, 1)

        self.macro_row = QWidget()
        mr = QHBoxLayout(self.macro_row)
        mr.setContentsMargins(0, 0, 0, 0)
        mr.addWidget(QLabel("매크로 이름"))
        self.macro_edit = QLineEdit()
        self.macro_edit.setPlaceholderText(r"\myfont   (비우면 \myfont)")
        self.macro_edit.setMaximumWidth(220)
        self.macro_edit.textChanged.connect(self.update_output)
        mr.addWidget(self.macro_edit)
        mr.addWidget(QLabel("← 본문에서 이 이름으로 부른다"))
        mr.addStretch(1)
        g.addWidget(self.macro_row, 3, 1)

        self.cmd_label = QLabel()
        self.cmd_label.setTextFormat(Qt.RichText)
        g.addWidget(QLabel("만들 명령"), 4, 0)
        g.addWidget(self.cmd_label, 4, 1)

        self.done_label = QLabel()
        self.done_label.setEnabled(False)
        self.done_label.setWordWrap(True)
        g.addWidget(QLabel("지정한 것"), 5, 0)
        g.addWidget(self.done_label, 5, 1)
        g.setColumnStretch(1, 1)
        main_layout.addWidget(cmd_group)

        self.seg_mode.changed.connect(self._on_selector_changed)
        self.seg_family.changed.connect(self._on_selector_changed)
        self.seg_script.changed.connect(self._on_selector_changed)
        if self.writer:
            # Writer 모드: 전역 선언(\set…font)만. 새 패밀리·즉석 적용은 숨긴다(코드에는 그대로 남아 있다).
            self.lbl_mode.setVisible(False)
            self.seg_mode.setVisible(False)
            if self.writer.get("scripts") == "latin":
                for sc in ("hangul", "hanja"):
                    self.seg_script.button(sc).setVisible(False)

        # ---- 2. 글꼴 (본문/굵게/기울임…) ------------------------
        font_group = QGroupBox("2. 글꼴  —  줄을 눌러 두면 위 목록에서 고른 폰트가 그 줄에 들어갑니다")
        fg = QGridLayout(font_group)
        fg.setHorizontalSpacing(8)
        fg.setVerticalSpacing(4)

        self.style_edits = {}
        self.style_feat_edits = {}
        self.style_radios = {}
        self.style_radio_group = QButtonGroup(self)
        self._feat_widgets = []

        fg.addWidget(QLabel("<b>글꼴</b>"), 0, 1)
        hdr_feat = QLabel("<b>Features</b>")
        fg.addWidget(hdr_feat, 0, 2)
        self._feat_widgets.append(hdr_feat)

        for r, style in enumerate(self.font_styles, start=1):
            rb = QRadioButton(self.STYLE_LABELS[style])
            rb.setProperty("style_id", style)
            if style == self.target_style:
                rb.setChecked(True)
            self.style_radio_group.addButton(rb)
            self.style_radios[style] = rb
            fg.addWidget(rb, r, 0)

            le = _FocusEdit()
            le.setClearButtonEnabled(True)
            le.setPlaceholderText("(비워 두면 자동)" if style != "Upright (Main)" else "폰트 이름")
            le.textChanged.connect(self.update_output)
            le.focused.connect(lambda s=style: self.style_radios[s].setChecked(True))
            self.style_edits[style] = le
            fg.addWidget(le, r, 1)

            lf = _FocusEdit()
            lf.setPlaceholderText("예: Color=AA0000")
            lf.textChanged.connect(self.update_output)
            lf.focused.connect(lambda s=style: self.style_radios[s].setChecked(True))
            self.style_feat_edits[style] = lf
            fg.addWidget(lf, r, 2)
            self._feat_widgets.append(lf)
        fg.setColumnStretch(1, 3)
        fg.setColumnStretch(2, 2)
        self.style_radio_group.buttonToggled.connect(self._on_target_style)

        self.chk_feats = QCheckBox("줄마다 Features 옵션 따로 주기 (고급)")
        self.chk_feats.toggled.connect(self._on_feats_toggled)
        fg.addWidget(self.chk_feats, len(self.font_styles) + 1, 0, 1, 3)
        main_layout.addWidget(font_group)
        self._set_feats_visible(False)

        # ---- 3. 공통 옵션 ---------------------------------------
        feature_group = QGroupBox("3. 공통 옵션  —  지금 고른 명령에 붙습니다")
        fl = QVBoxLayout(feature_group)
        pg = QGridLayout()
        self.presets = {
            "Ligatures=TeX": QCheckBox("Ligatures=TeX"),
            "Script=Hangul": QCheckBox("Script=Hangul"),
            "CompressPunctuations": QCheckBox("CompressPunctuations"),
            VERTICAL_OPT: QCheckBox("세로쓰기"),         # 옵션 이름이 길어서 이름표만 짧게
        }
        self.scale_combo = QComboBox()             # Scale 은 둘 중 하나만 쓸 수 있으므로 체크칸 대신 고르는 칸
        self.scale_combo.addItem("Scale: 지정 안 함", "")
        self.scale_combo.addItem("Scale=MatchLowercase", "Scale=MatchLowercase")
        self.scale_combo.addItem("Scale=MatchUppercase", "Scale=MatchUppercase")
        self.scale_combo.setToolTip("라틴 글자 크기를 한글 쪽에 맞춘다.\n"
                                    "MatchLowercase: 소문자(x-height) 높이를 맞춘다\n"
                                    "MatchUppercase: 대문자 높이를 맞춘다 — 한글과 섞어 쓸 때 더 어울리는 경우가 많다")
        self.scale_combo.currentIndexChanged.connect(self.on_preset_changed)
        self.renderer_combo = QComboBox()          # Renderer 도 하나만 고른다. Node 가 맨 위.
        self.renderer_combo.addItem("Renderer: 지정 안 함", "")
        for opt in RENDERER_OPTIONS:
            self.renderer_combo.addItem(opt, opt)
        self.renderer_combo.setToolTip("글자를 짜는 엔진을 고른다 (lualatex: Node · Base · HarfBuzz, xelatex: OpenType · Graphite).\n"
                                       "OpenType 과 HarfBuzz 는 사실상 같지만 입력 관행대로 둘 다 둔다.")
        self.renderer_combo.currentIndexChanged.connect(self.on_preset_changed)
        for cb in self.presets.values():
            cb.stateChanged.connect(self.on_preset_changed)
        r = c = 0
        grid_widgets = [self.presets["Ligatures=TeX"], self.renderer_combo, self.scale_combo,
                        self.presets["Script=Hangul"], self.presets["CompressPunctuations"], self.presets[VERTICAL_OPT]]
        for cb in grid_widgets:
            pg.addWidget(cb, r, c)
            c += 1
            if c > 2:
                c = 0
                r += 1
        fl.addLayout(pg)
        self.index_row = QWidget()                     # ttc/otc 를 골랐을 때만 보인다
        ir = QHBoxLayout(self.index_row); ir.setContentsMargins(0, 0, 0, 0)
        ir.addWidget(QLabel("FontIndex"))
        self.index_combo = QComboBox()
        self.index_combo.setMinimumWidth(240)
        self.index_combo.activated.connect(self._on_index_chosen)
        ir.addWidget(self.index_combo)
        self.index_hint = QLabel("")
        ir.addWidget(self.index_hint, 1)
        fl.addWidget(self.index_row)
        self.index_row.setVisible(False)
        add = QHBoxLayout()
        add.addWidget(QLabel("추가 옵션"))
        self.feature_edit = QLineEdit()
        self.feature_edit.setPlaceholderText("직접 입력, 예: LetterSpace=2.0")
        self.feature_edit.textChanged.connect(self.update_output)
        add.addWidget(self.feature_edit)
        fl.addLayout(add)
        main_layout.addStretch(1)

        scroll = QScrollArea()
        scroll.setWidget(scroll_host)
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QScrollArea.NoFrame)

        # ---------------------------------------------------------
        # 결과
        # ---------------------------------------------------------
        output_group = QGroupBox("생성된 LaTeX  (지정한 명령이 모두 차례로 쌓입니다)")
        ol = QVBoxLayout(output_group)
        self.output_text = QPlainTextEdit()           # 코드 칸: 문단 간격 없이 줄 그대로
        self.output_text.setReadOnly(True)
        self.output_text.setLineWrapMode(QPlainTextEdit.NoWrap)
        self.output_text.setPlaceholderText("폰트를 고르면 여기에 LaTeX 코드가 나옵니다")   # 흐린 안내글: 내용이 아니라서 복사·저장되지 않는다
        self.output_text.setFont(monospace_font())
        self.output_text.setMinimumHeight(70)
        ol.addWidget(self.output_text)
        bl = QGridLayout()
        clear_btn = QPushButton("🗑 모두 지우기")
        clear_btn.clicked.connect(self.clear_all)
        copy_btn = QPushButton("📋 복사")
        copy_btn.clicked.connect(lambda: QApplication.clipboard().setText(self.output_text.toPlainText()))
        save_btn = QPushButton("💾 .tex 저장…")
        save_btn.setToolTip("결과 코드를 .tex 파일로 저장")
        save_btn.clicked.connect(self._save_to_file)
        load_json_btn = QPushButton("📂 설정 열기…")
        load_json_btn.setToolTip("저장해 둔 설정(.json)을 불러온다 — 명령마다의 폰트·옵션이 모두 돌아온다")
        load_json_btn.clicked.connect(self.open_file)
        save_json_btn = QPushButton("💾 설정 저장…")
        save_json_btn.setToolTip("지금의 모든 설정을 .json 으로 저장한다 (나중에 다시 열어 고칠 수 있다)")
        save_json_btn.clicked.connect(self.save_file)
        bl.addWidget(copy_btn, 0, 0)
        bl.addWidget(save_btn, 0, 1)
        bl.addWidget(clear_btn, 0, 2)
        bl.addWidget(load_json_btn, 1, 0, 1, 1)
        bl.addWidget(save_json_btn, 1, 1, 1, 1)
        ol.addLayout(bl)
        if self.writer:
            self.send_btn = QPushButton("✔ Writer 로 보내기")
            self.send_btn.setToolTip("지금 설정을 ndhmdWriter 에 넘기고 이 창을 닫는다.\n"
                                     "Writer 가 원고의 front matter(preamble+:)에 글꼴 블록으로 써 넣는다.")
            self.send_btn.setDefault(True)
            self.send_btn.clicked.connect(self.send_to_writer)
            ol.addWidget(self.send_btn)
            # Ctrl+W(맥은 ⌘W) — 보내지 않고 그냥 닫는다. 보내지 않았으니 Writer 는 아무것도 바꾸지 않는다.
            from PySide6.QtGui import QShortcut, QKeySequence
            self._close_sc = QShortcut(QKeySequence("Ctrl+W"), self)
            self._close_sc.activated.connect(self.close)
        self.status_label = QLabel("")
        self.status_label.setEnabled(False)
        ol.addWidget(self.status_label)

        # 세 컬럼: [1·2 무엇을/글꼴] [3 공통 옵션 + 미리보기] [생성된 LaTeX]
        preview_group = self._build_preview_group()
        middle = QWidget()
        ml = QVBoxLayout(middle); ml.setContentsMargins(0, 0, 0, 0); ml.setSpacing(8)
        ml.addWidget(feature_group)
        ml.addWidget(preview_group, 1)
        scroll.setMinimumWidth(380)
        middle.setMinimumWidth(360)
        output_group.setMinimumWidth(300)
        split = QSplitter(Qt.Horizontal)
        split.addWidget(scroll)
        split.addWidget(middle)
        split.addWidget(output_group)
        split.setStretchFactor(0, 4)
        split.setStretchFactor(1, 4)
        split.setStretchFactor(2, 3)
        split.setSizes([470, 470, 360])
        split.setChildrenCollapsible(False)
        self.split = split
        self.pdf_banner = QLabel("pdflatex 는 fontspec 을 쓸 수 없어 이 도구를 쓰지 않습니다. "
                                 "위 문서 바의 '엔진'을 xelatex 나 lualatex 로 바꾸면 켜집니다. (입력한 설정은 그대로 보관됩니다.)")
        self.pdf_banner.setWordWrap(True)
        self.pdf_banner.setMargin(6)
        self.pdf_banner.setStyleSheet("QLabel { border: 1px solid palette(mid); background: palette(alternate-base); }")
        self.pdf_banner.setVisible(False)
        outer.addWidget(self.pdf_banner)
        outer.addWidget(split, 1)

        self.font_combo.setEnabled(False)
        self.load_state_to_ui(self.current_cmd_id)
        self._refresh_selector_ui()
        self.update_output()
        if not self.embedded:
            self.start_font_scan(force_rescan=False)     # 셸 안에서는 처음 화면에 보일 때 (시동이 느려지지 않게)

    # ---------------------------------------------------------
    # 미리보기
    # ---------------------------------------------------------
    def _build_preview_group(self):
        g = QGroupBox("미리보기  (XeLaTeX/LuaLaTeX + kotex)")
        v = QVBoxLayout(g)
        bar = QHBoxLayout()
        self.pv_engine_label = QLabel("엔진")
        bar.addWidget(self.pv_engine_label)
        self.pv_engine = QComboBox()
        self.pv_engine.addItems(ENGINES)
        eng = str(self.qs.value("engine", DEFAULT_ENGINE))
        self.pv_engine.setCurrentText(eng if eng in ENGINES else DEFAULT_ENGINE)
        self.pv_engine.setToolTip("pdflatex 는 fontspec 을 쓸 수 없어 고를 수 없습니다.")
        bar.addWidget(self.pv_engine)
        if self.embedded:                                   # 셸 안에서는 문서 바의 '엔진'이 이것을 정한다 (set_engine)
            self.pv_engine_label.setVisible(False)
            self.pv_engine.setVisible(False)
        if self.writer:                                     # Writer 모드: 문서의 엔진을 따른다 (바꾸면 코드가 어긋난다)
            eng = self.writer.get("engine")
            if eng in ENGINES:
                self.pv_engine.setCurrentText(eng)
            self.pv_engine.setEnabled(False)
            self.pv_engine.setToolTip("문서 엔진은 Writer 의 설정을 따릅니다.")
        bar.addWidget(QLabel("문서 클래스"))
        self.pv_class = QComboBox()
        self.pv_class.setEditable(True)
        self.pv_class.addItems(DOC_CLASSES)
        self.pv_class.setCurrentText(str(self.qs.value("docclass", DEFAULT_CLASS)) or DEFAULT_CLASS)
        self.pv_class.setMinimumWidth(110)
        self.pv_class.setToolTip("미리보기 문서는 이 클래스와 kotex 패키지만 씁니다.")
        if self.writer:
            if self.writer.get("class"):
                self.pv_class.setCurrentText(str(self.writer["class"]))
            self.pv_class.setEnabled(False)
            self.pv_class.setToolTip("문서 클래스는 원고의 class: 를 따릅니다.")
        bar.addWidget(self.pv_class)
        self.pv_auto = QCheckBox("자동 갱신")
        self.pv_auto.setChecked(str(self.qs.value("auto", "true")).lower() not in ("false", "0"))
        bar.addWidget(self.pv_auto)
        self.pv_btn = QPushButton("갱신")
        self.pv_btn.clicked.connect(lambda: self.refresh_preview(force=True))
        bar.addWidget(self.pv_btn)
        bar.addStretch(1)
        v.addLayout(bar)

        self.pv_status = QLabel("")
        v.addWidget(self.pv_status)
        self.pv_note = QLabel("")                  # 미리보기에서 뺀 옵션 안내 (있을 때만 보인다)
        self.pv_note.setVisible(False)
        v.addWidget(self.pv_note)

        self.pv_label = QLabel()
        self.pv_label.setAlignment(Qt.AlignLeft | Qt.AlignTop)
        self.pv_label.setTextInteractionFlags(Qt.TextSelectableByMouse)
        self.pv_label.setWordWrap(True)
        self.pv_scroll = QScrollArea()
        self.pv_scroll.setWidget(self.pv_label)
        self.pv_scroll.setWidgetResizable(True)
        v.addWidget(self.pv_scroll, 1)

        self.pv_samples_btn = QToolButton()
        self.pv_samples_btn.setText("미리보기 문장 고치기")
        self.pv_samples_btn.setCheckable(True)
        self.pv_samples_btn.setArrowType(Qt.RightArrow)
        self.pv_samples_btn.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        v.addWidget(self.pv_samples_btn)
        self.pv_samples_box = QWidget()
        sg = QGridLayout(self.pv_samples_box)
        sg.setContentsMargins(0, 0, 0, 0)
        self.pv_sample_edits = {}
        for r, (script, label) in enumerate((("latin", "라틴"), ("hangul", "한글"), ("hanja", "한자"))):
            sg.addWidget(QLabel(label), r, 0)
            saved = str(self.qs.value("sample_" + script, DEFAULT_SAMPLES[script]))
            if not saved or saved in LEGACY_SAMPLES.get(script, ()):
                saved = DEFAULT_SAMPLES[script]
            e = QLineEdit(saved)
            e.textChanged.connect(self._preview_params_changed)
            self.pv_sample_edits[script] = e
            sg.addWidget(e, r, 1)
        reset = QPushButton("기본 문장으로")
        reset.clicked.connect(self._reset_samples)
        sg.addWidget(reset, 3, 1, alignment=Qt.AlignLeft)
        sg.setColumnStretch(1, 1)
        self.pv_samples_box.setVisible(False)
        self.pv_samples_btn.toggled.connect(self._toggle_samples)
        v.addWidget(self.pv_samples_box)

        self.pv_engine.currentTextChanged.connect(self._preview_params_changed)
        self.pv_class.currentTextChanged.connect(self._preview_params_changed)
        self.pv_auto.toggled.connect(self._preview_params_changed)
        return g

    def _toggle_samples(self, on):
        self.pv_samples_box.setVisible(on)
        self.pv_samples_btn.setArrowType(Qt.DownArrow if on else Qt.RightArrow)

    def _reset_samples(self):
        for k, e in self.pv_sample_edits.items():
            e.setText(DEFAULT_SAMPLES[k])

    def preview_samples(self):
        return {k: (e.text().strip() or DEFAULT_SAMPLES[k]) for k, e in self.pv_sample_edits.items()}

    def _preview_params_changed(self, *_):
        if not self.writer:                                 # Writer 모드의 엔진·클래스는 문서가 정한 것이라 기억하지 않는다
            self.qs.setValue("engine", self.pv_engine.currentText())
            self.qs.setValue("docclass", self.pv_class.currentText().strip() or DEFAULT_CLASS)
        self.qs.setValue("auto", self.pv_auto.isChecked())
        for k, e in self.pv_sample_edits.items():
            self.qs.setValue("sample_" + k, e.text())
        self._schedule_preview()

    def set_engine(self, name):
        """셸의 문서 바 '엔진'. xelatex/lualatex 면 미리보기 컴파일러가 되고, pdflatex 면 fontspec 을 쓸 수 없으니
        도구 전체를 흐리게 하고(입력은 보관) 미리보기·내보내기를 멈춘다."""
        off = (name == "pdflatex")
        if name in ENGINES and self.pv_engine.currentText() != name:
            self.pv_engine.setCurrentText(name)             # -> _preview_params_changed -> 미리보기 예약
        if off == self.pdf_off:
            return
        self.pdf_off = off
        self.split.setEnabled(not off)
        self.pdf_banner.setVisible(off)
        if off:
            self._pv_timer.stop()
            self._pv_cancel_all()
            self._pv_job += 1                               # 돌던 컴파일의 결과는 버린다
            self._pv_last_key = None
            self._dirty = False
        else:
            self._schedule_preview()
        self._say("pdflatex: 폰트 도구를 쓰지 않음" if off else "")

    def _schedule_preview(self):
        if getattr(self, "_is_loading_state", False) or self.pdf_off:
            return
        if not self._active:
            self._dirty = True               # 숨은 동안은 컴파일하지 않는다: 다시 보일 때 한 번
            return
        self._pv_timer.start()

    def set_active(self, on):
        """셸이 부른다: 화면에 보이는가. 처음 보일 때 폰트를 스캔하고, 숨은 동안 바뀐 것은 다시 보일 때 미리보기에 반영한다."""
        self._active = bool(on)
        if not on:
            if self._pv_timer.isActive():
                self._pv_timer.stop()
                self._dirty = True
            return
        if not self._scan_started:
            self.start_font_scan(force_rescan=False)
        if self._dirty:
            self._dirty = False
            self._schedule_preview()

    def set_tex_dir(self, texdir):
        """문서 바의 'TeX 폴더'. 컴파일러(xelatex/lualatex)와 kpsewhich 를 여기서 먼저 찾는다."""
        self.tex_dir = (texdir or "").strip()

    def _preview_timeout(self):
        if self.pv_auto.isChecked():
            self.refresh_preview()
        else:
            self._pv_pending_note()

    def _pv_pending_note(self):
        if self._preview_items():
            self.pv_status.setText("내용이 바뀌었습니다 — [갱신]을 누르세요 (자동 갱신이 꺼져 있습니다).")

    def _skip_note(self):
        sk = self.preview_skipped()
        return ("※ 미리보기에서 뺀 옵션: %s (luatexko 전용)" % ", ".join(sk)) if sk else ""

    def _missing_note(self):
        """폰트에 없는 글자 안내 (폰트별 한 줄). 없으면 ''."""
        by_font = {}
        for ch, _cp, font in self.preview_missing:
            by_font.setdefault(font, []).append(ch)
        lines = []
        for font, chars in list(by_font.items())[:3]:
            shown = " ".join(chars[:12]) + (" …" if len(chars) > 12 else "")
            lines.append("※ %s 에 없는 글자 %d개: %s" % (font, len(chars), shown))
        return "\n".join(lines)

    def _show_notes(self):
        skip, miss = self._skip_note(), self._missing_note()
        self.pv_note.setText("\n".join(x for x in (skip, miss) if x))
        tips = []
        if skip:
            tips.append("luatexko(lualatex)만 아는 옵션이라 xelatex 로는 컴파일되지 않습니다.\n"
                        "생성된 LaTeX 에는 그대로 들어 있고, 엔진을 lualatex 로 바꾸면 미리보기에도 적용됩니다.")
        if miss:
            tips.append("그려지긴 했지만 이 글자들은 지정한 폰트에 글리프가 없어 빈 칸이거나 다른 폰트로 대체됩니다.\n"
                        + "\n".join("U+%04X %s (%s)" % (cp, ch, font) for ch, cp, font in self.preview_missing[:40]))
        self.pv_note.setToolTip("\n\n".join(tips))
        self.pv_note.setVisible(bool(skip or miss))
    def preview_skipped(self):
        """이 엔진의 미리보기에서 빼야 하는, 지금 체크된 옵션들 (xelatex 에서는 luatexko 전용 옵션)."""
        if self.pv_engine.currentText() == "lualatex":
            return []
        used = set()
        for cmd_id, st in self.states.items():
            if st["fonts"]["Upright (Main)"].strip():
                used.update(n for n in st.get("checked_presets", []) if n in LUATEXKO_ONLY_OPTIONS
                            and not (n in self.HANGUL_ONLY_PRESETS and self._is_latin(cmd_id)))
        return sorted(used)

    def _preview_items(self):
        """폰트를 실제로 지정한 명령들."""
        items = []
        skip = () if self.pv_engine.currentText() == "lualatex" else LUATEXKO_ONLY_OPTIONS
        for cmd_id, text, placeholder in self._build_blocks(skip=skip):
            if placeholder:
                continue
            st = self.states[cmd_id]
            up = st["fonts"]["Upright (Main)"].strip()
            styles = [name for name in PREVIEW_STYLES
                      if (st["fonts"][name].strip() and st["fonts"][name].strip() != up) or st["feats"][name].strip()]
            # 본문만, 그것도 폰트 이름으로 줬고 굵게·기울임 등은 아무것도 지정하지 않았으면: fontspec 이 가족에서 찾아 줄 수 있으니 시험해 본다.
            # 하나라도 따로 지정했으면(폰트이든 Features 이든) 이 자동 시도는 하지 않는다.
            any_given = any(st["fonts"][n].strip() or st["feats"][n].strip() for n in PREVIEW_STYLES)
            auto = bool(up) and not any_given and not looks_like_file(up)
            if auto:
                # 한글·한자는 기울임이 뜻이 없다: 본문과 굵게만. 라틴은 굵게·기울임·굵은 기울임.
                styles = list(AUTO_FAMILY_STYLES if CMD_INFO[cmd_id][2] == "latin" else AUTO_FAMILY_STYLES_CJK)
            macro = None
            if cmd_id in self.NEEDS_MACRO_NAME:
                macro = st["macro"].strip() or r"\myfont"
                if not macro.startswith("\\"):
                    macro = "\\" + macro
            items.append({"cmd_id": cmd_id, "block": text, "styles": styles, "macro": macro, "auto": auto})
        return items

    def preview_tex(self):
        """지금 화면의 설정으로 만들어질 미리보기 소스와 경고. (지정한 명령이 없으면 ('', []))"""
        items = self._preview_items()
        if not items:
            return "", []
        kotex = not (self.writer and self.writer.get("scripts") == "latin")
        return build_preview_tex(items, self.pv_class.currentText(), self.preview_samples(), kotex=kotex)

    def preview_busy(self):
        return self._pv_timer.isActive() or any(t.isRunning() for t in self._pv_threads)

    def _pv_show_text(self, text):
        self.pv_note.setVisible(False)
        self.preview_missing = []
        self.preview_image = None
        self.pv_label.setStyleSheet("")
        self.pv_label.setPixmap(QPixmap())
        self.pv_label.setText(text)

    def _pv_cancel_all(self):
        for t in list(self._pv_threads):
            t.cancel()

    def refresh_preview(self, force=False):
        """미리보기를 (필요하면) 다시 컴파일한다."""
        self._pv_timer.stop()
        if self.pdf_off:
            return
        tex, warns = self.preview_tex()
        if not tex:
            self._pv_cancel_all()
            self._pv_job += 1
            self._pv_last_key = None
            self.pv_status.setText("")
            self._pv_show_text("폰트를 고르면 여기에 미리보기가 나타납니다.")
            return
        if warns:
            self._pv_cancel_all()
            self._pv_job += 1
            self._pv_last_key = None
            self.pv_status.setText("미리보기를 만들 수 없습니다.")
            self._pv_show_text("\n".join(warns))
            return
        engine = self.pv_engine.currentText()
        key = (engine, tex)
        if not force and key == self._pv_last_key and self.preview_image is not None:
            return
        self._pv_cancel_all()
        self._pv_job += 1
        if self._pv_tmp is None:
            self._pv_tmp = tempfile.mkdtemp(prefix="fontsel_")
        workdir = os.path.join(self._pv_tmp, "job%d" % self._pv_job)
        os.makedirs(workdir, exist_ok=True)
        Path(workdir, "preview.tex").write_text(tex, encoding="utf-8")
        self._pv_key_pending = key
        self.pv_status.setText("%s 로 컴파일하는 중…" % engine)
        t = PreviewThread(self._pv_job, engine, workdir, self.tex_dir)
        t.done.connect(self._on_preview_done)
        t.finished.connect(lambda t=t: self._pv_threads.discard(t))
        self._pv_threads.add(t)
        t.start()

    def _on_preview_done(self, job, ok, pdf, message):
        workdir = os.path.join(self._pv_tmp or "", "job%d" % job)
        try:
            if job != self._pv_job:
                return                                  # 그 사이에 더 새 요청이 있었다
            if not ok:
                self._pv_last_key = None
                self.pv_status.setText("컴파일 오류")
                self._pv_show_text(message)
                return
            img = render_pdf(pdf)
            if img is None:
                self.pv_status.setText("PDF 를 그릴 수 없습니다 (QtPdf 없음?)")
                self._pv_show_text("미리보기 PDF 는 만들어졌지만 이 PySide6 에는 QtPdf 가 없어 화면에 그릴 수 없습니다.")
                return
            self.preview_image = img
            self._pv_last_key = self._pv_key_pending
            self.pv_label.setText("")
            self.pv_label.setStyleSheet("background: white;")
            self.pv_label.setPixmap(QPixmap.fromImage(img))
            self.pv_status.setText("%s · %d × %d" % (self.pv_engine.currentText(), img.width(), img.height()))
            self.preview_missing = missing_glyphs(message)
            self._show_notes()
        finally:
            shutil.rmtree(workdir, ignore_errors=True)

    # ---------------------------------------------------------
    # 공개 도우미 (다른 창에 끼워 쓸 때)
    # ---------------------------------------------------------
    def preamble(self):
        """지금까지 지정한 내용의 LaTeX 문자열."""
        return self.output_text.toPlainText()

    def select_target(self, mode, family, script):
        """코드에서 "무엇을 지정할까" 를 고른다. (테스트·연동용)"""
        self.seg_mode.set_value(mode, notify=False)
        self.seg_family.set_value(family, notify=False)
        self.seg_script.set_value(script, notify=False)
        self._on_selector_changed()

    def select_command(self, cmd_id):
        """명령 문자열(예: \\setmainhangulfont)로 고른다."""
        for m in ("set", "new", "spec"):
            for f in (("main", "sans", "mono") if m == "set" else ("main",)):
                for s in ("latin", "hangul", "hanja"):
                    if compose(m, f, s) == cmd_id:
                        self.select_target(m, f, s)
                        return True
        return False

    def pick_font(self, name):
        """위 콤보에서 폰트를 골랐을 때와 같은 효과. 목록에 있는 폰트면 어느 칸에 넣었는지 기억해 두었다가,
        [폰트 이름]/[파일 이름] 기준을 바꾸면 그 칸도 같이 바꾼다."""
        if not name:
            return
        style = self.target_style
        feat = self.style_feat_edits[style]
        feat.blockSignals(True)
        feat.setText(set_font_index(feat.text(), None))        # 이전 폰트의 서체 번호가 남지 않게
        feat.blockSignals(False)
        self.style_edits[style].setText(name)
        key = (self.current_cmd_id, style)
        entry = self._find_entry(name.strip(), self._shown_mode)
        if entry is not None:
            self._picked[key] = (entry, name.strip())
            if self._shown_mode == "name" and len(entry) > 3 and entry[3] is not None:
                self._write_font_index(style, entry[3])        # ttc/otc 에서 서체를 골랐으면 그 번호를 같이 넣는다
        else:
            self._picked.pop(key, None)
        self._refresh_index_row()

    # ---- ttc/otc: FontIndex ------------------------------------
    def _faces_of(self, text):
        """text(폰트 이름 또는 파일 이름) 가 ttc/otc 면 그 파일에 든 서체들 [(번호, 폰트 이름)], 아니면 []."""
        e = self._find_entry(text, self._shown_mode) or self._find_entry(text, "file" if self._shown_mode == "name" else "name")
        if e is None or not is_collection(e[1]):
            return []
        faces = {(x[3], x[0]) for x in self.full_font_data if x[1] == e[1] and len(x) > 3 and x[3] is not None}
        return sorted(faces)

    def _write_font_index(self, style, idx):
        """그 줄의 Features 칸에 FontIndex=idx 를 넣거나(None 이면 지운다). 값이 생기면 Features 칸을 보이게 한다."""
        feat = self.style_feat_edits[style]
        feat.setText(set_font_index(feat.text(), idx))          # textChanged -> update_output
        if idx is not None and not self.chk_feats.isChecked():
            self.chk_feats.setChecked(True)

    def _on_index_chosen(self, i):
        idx = self.index_combo.itemData(i)
        self._write_font_index(self.target_style, idx)

    def _refresh_index_row(self):
        style = self.target_style
        faces = self._faces_of(self.style_edits[style].text().strip())
        self.index_row.setVisible(bool(faces))
        if not faces:
            return
        cur = get_font_index(self.style_feat_edits[style].text())
        self.index_combo.blockSignals(True)
        self.index_combo.clear()
        self.index_combo.addItem("(지정 안 함)", None)
        for idx, nm in faces:
            self.index_combo.addItem(f"{idx}  {nm}", idx)
        pos = self.index_combo.findData(cur)
        self.index_combo.setCurrentIndex(pos if pos >= 0 else 0)
        self.index_combo.blockSignals(False)
        label = self.STYLE_LABELS[style]
        self.index_hint.setText(f"← '{label}' 줄의 폰트는 ttc/otc 입니다. 서체를 번호로 고릅니다.")

    def _save_to_file(self):
        text = self.output_text.toPlainText().strip()
        if not text:
            return
        name, _ = QFileDialog.getSaveFileName(
            self, "프리앰블로 저장", str(Path.home() / "fonts-preamble.tex"),
            "TeX 파일 (*.tex);;텍스트 (*.txt);;모든 파일 (*)")
        if not name:
            return
        try:
            Path(name).write_text(text + "\n", encoding="utf-8")
        except OSError as e:
            QMessageBox.warning(self, "저장 실패", str(e))

    # ---------------------------------------------------------
    # 선택 UI
    # ---------------------------------------------------------
    def _selector_id(self):
        return compose(self.seg_mode.value(), self.seg_family.value(), self.seg_script.value())

    def _on_selector_changed(self, *_):
        new_id = self._selector_id()
        if new_id != self.current_cmd_id:
            self.save_current_state()          # 떠나는 명령의 입력을 먼저 보관
            self.current_cmd_id = new_id
            self.load_state_to_ui(new_id)
            # 명령을 바꾸면 받는 줄은 늘 "본문"부터 다시 시작 — 가장 흔한 순서다.
            self.style_radios["Upright (Main)"].setChecked(True)
        self._refresh_selector_ui()
        self.update_output()

    def _refresh_selector_ui(self):
        mode = self.seg_mode.value()
        self.seg_family.setEnabled(mode == "set")   # 새 패밀리/즉석 적용은 계열이 없다
        cid = self.current_cmd_id
        needs_macro = cid in self.NEEDS_MACRO_NAME
        self.macro_row.setVisible(needs_macro)
        latin = self._is_latin(cid)
        for name in self.HANGUL_ONLY_PRESETS:
            cb = self.presets[name]
            cb.setEnabled(not latin)
            cb.setToolTip("한글·한자 명령에서만 쓸 수 있습니다 (문자를 '한글'이나 '한자'로 고르세요)" if latin else
                          PRESET_TIPS.get(name, ""))
        if self.writer and self._luatexko_blocked():
            for name in LUATEXKO_ONLY_OPTIONS:               # 문서가 xelatex 면 fontspec 오류가 나는 옵션
                cb = self.presets[name]
                cb.setChecked(False)
                cb.setEnabled(False)
                cb.setToolTip(PRESET_TIPS.get(name, ""))
        shown = cid
        if needs_macro:
            macro = self.macro_edit.text().strip() or r"\myfont"
            if not macro.startswith("\\"):
                macro = "\\" + macro
            shown = cid + macro
        self.cmd_label.setText(f"<b><tt style='font-size:13pt'>{shown.replace('<', '&lt;')}</tt></b>")
        done = [c for c in self.cmd_order if self._cmd_allowed(c) and self.states[c]["fonts"]["Upright (Main)"].strip()]
        self.done_label.setText("   ".join(done) if done else "아직 없음")

    def _cmd_allowed(self, cmd_id):
        """Writer 모드에서는 전역 선언(\\set…font)만, 그것도 --scripts 가 허락한 문자만 낸다. 평소에는 모두."""
        if not self.writer:
            return True
        mode, _fam, script = CMD_INFO[cmd_id]
        return mode == "set" and (self.writer.get("scripts") != "latin" or script == "latin")

    def _luatexko_blocked(self):
        return bool(self.writer) and self.pv_engine.currentText() != "lualatex"

    def _output_skip(self):
        """결과 코드에서 뺄 옵션: Writer 모드에서 문서가 xelatex 면 luatexko 전용 옵션."""
        return LUATEXKO_ONLY_OPTIONS if self._luatexko_blocked() else ()

    @staticmethod
    def _is_latin(cmd_id):
        return cmd_id not in {compose(m, f, s) for m in ("set", "new", "spec")
                              for f in ("main", "sans", "mono") for s in ("hangul", "hanja")}

    def _on_target_style(self, button, checked):
        if checked:
            self.target_style = button.property("style_id")
            self._refresh_index_row()

    def _set_feats_visible(self, on):
        for w in self._feat_widgets:
            w.setVisible(on)

    def _on_feats_toggled(self, on):
        if not on and any(e.text().strip() for e in self.style_feat_edits.values()):
            # 값이 들어 있는 칸을 숨기면 결과에 왜 들어가는지 알 수 없게 된다 — 못 숨긴다.
            self.chk_feats.blockSignals(True)
            self.chk_feats.setChecked(True)
            self.chk_feats.blockSignals(False)
            return
        self._set_feats_visible(on)

    # ---------------------------------------------------------
    # 상태 관리(State Management)
    # ---------------------------------------------------------
    def empty_state(self):
        return {
            "fonts": {style: "" for style in self.font_styles},
            "feats": {style: "" for style in self.font_styles},
            "checked_presets": [],
            "general_features": "",
            "macro": "",
        }

    def save_current_state(self):
        st = self.states[self.current_cmd_id]
        for style in self.font_styles:
            st["fonts"][style] = self.style_edits[style].text()
            st["feats"][style] = self.style_feat_edits[style].text()
        st["general_features"] = self.feature_edit.text()
        st["checked_presets"] = [name for name in PRESET_ORDER
                                 if (self.scale_combo.currentData() == name if name in SCALE_OPTIONS
                                     else self.renderer_combo.currentData() == name if name in RENDERER_OPTIONS
                                     else self.presets[name].isChecked())]
        st["macro"] = self.macro_edit.text()

    def load_state_to_ui(self, cmd_id):
        self._is_loading_state = True
        st = self.states[cmd_id]
        for style in self.font_styles:
            self.style_edits[style].setText(st["fonts"][style])
            self.style_feat_edits[style].setText(st["feats"][style])
        self.feature_edit.setText(st["general_features"])
        scale = next((n for n in st.get("checked_presets", []) if n in SCALE_OPTIONS), "")
        self.scale_combo.blockSignals(True)
        self.scale_combo.setCurrentIndex(max(0, self.scale_combo.findData(scale)))
        self.scale_combo.blockSignals(False)
        renderer = next((n for n in st.get("checked_presets", []) if n in RENDERER_OPTIONS), "")
        self.renderer_combo.blockSignals(True)
        self.renderer_combo.setCurrentIndex(max(0, self.renderer_combo.findData(renderer)))
        self.renderer_combo.blockSignals(False)
        for name, cb in self.presets.items():
            cb.blockSignals(True)
            cb.setChecked(name in st.get("checked_presets", [])
                          and not (name in self.HANGUL_ONLY_PRESETS and self._is_latin(cmd_id)))
            cb.blockSignals(False)
        self.macro_edit.setText(st["macro"])
        if any(v.strip() for v in st["feats"].values()) and not self.chk_feats.isChecked():
            self.chk_feats.blockSignals(True)
            self.chk_feats.setChecked(True)
            self.chk_feats.blockSignals(False)
            self._set_feats_visible(True)
        self._is_loading_state = False
        self._refresh_index_row()

    # ---- 설정 저장 · 불러오기 (.json) ---------------------------
    STATE_VERSION = 1

    def state(self):
        """화면의 모든 설정 (저장용): 명령마다의 폰트·Features·공통 옵션·매크로 이름과 지금 고른 명령, 보기 기준."""
        self.save_current_state()
        return {"tool": "fontselector", "version": self.STATE_VERSION,
                "current": self.current_cmd_id, "view": self.seg_view.value(),
                "states": json.loads(json.dumps(self.states))}

    def _sanitize_state(self, raw):
        """저장된 명령 하나 -> 알려진 키만 남긴 상태. 빠진 키는 빈 값."""
        st = self.empty_state()
        if not isinstance(raw, dict):
            return st
        for key in ("fonts", "feats"):
            src = raw.get(key)
            if isinstance(src, dict):
                for style in self.font_styles:
                    if isinstance(src.get(style), str):
                        st[key][style] = src[style]
        known = set(PRESET_ORDER) | set(self.presets)
        if isinstance(raw.get("checked_presets"), list):
            st["checked_presets"] = [n for n in raw["checked_presets"] if isinstance(n, str) and n in known]
        for key in ("general_features", "macro"):
            if isinstance(raw.get(key), str):
                st[key] = raw[key]
        return st

    def load_state(self, data):
        """state() 가 만든 설정을 화면에 복원한다. 알 수 없는 명령·키는 버리고 빠진 것은 비운다. 형식이 틀리면 ValueError."""
        if not isinstance(data, dict) or not isinstance(data.get("states"), dict):
            raise ValueError("폰트 설정 파일이 아닙니다")
        states = {cmd: self._sanitize_state(data["states"].get(cmd)) for cmd in self.cmd_order}
        cur = data.get("current") if data.get("current") in self.cmd_order else self.current_cmd_id
        self._picked.clear()
        self.states = states
        view = data.get("view")
        if view in ("name", "file") and view != self.seg_view.value():
            self.seg_view.set_value(view, notify=False)
            self.refresh_combo_model()
        self.current_cmd_id = cur
        for m in ("set", "new", "spec"):                       # 선택 칸을 그 명령에 맞춘다 (알림 없이)
            for f in (("main", "sans", "mono") if m == "set" else ("main",)):
                for sc in ("latin", "hangul", "hanja"):
                    if compose(m, f, sc) == cur:
                        self.seg_mode.set_value(m, notify=False); self.seg_family.set_value(f, notify=False)
                        self.seg_script.set_value(sc, notify=False)
        self.load_state_to_ui(cur)
        self.style_radios["Upright (Main)"].setChecked(True)
        self._refresh_selector_ui()
        self.update_output()

    def _say(self, msg):
        self.status_label.setText(msg)
        self.status.emit(msg)

    def save_file(self):
        name, _ = QFileDialog.getSaveFileName(self, "폰트 설정 저장", str(Path.home() / "fonts.json"), "폰트 설정 (*.json)")
        if not name:
            return
        try:
            Path(name).write_text(json.dumps(self.state(), ensure_ascii=False, indent=1), encoding="utf-8")
        except OSError as e:
            QMessageBox.warning(self, "저장 실패", str(e))
            return
        self._say("설정을 저장했습니다: %s" % name)

    def open_file(self):
        name, _ = QFileDialog.getOpenFileName(self, "폰트 설정 열기", "", "폰트 설정 (*.json)")
        if not name:
            return
        try:
            self.load_state(json.loads(Path(name).read_text(encoding="utf-8")))
        except (OSError, ValueError, KeyError, TypeError) as e:
            QMessageBox.warning(self, "열기", "설정을 읽지 못했습니다: %s" % e)
            return
        self._say("설정을 열었습니다: %s" % name)

    # ---------- 프로젝트 ----------
    def project_state(self):
        return self.state()

    def load_project_state(self, d):
        """빈 dict/None 이면 시작 상태. 형식이 틀리면 시작 상태로 두고 ValueError."""
        if isinstance(d, dict) and d:
            self.load_state(d)
        else:
            self.clear_all()

    def project_cleanup(self):
        pass

    def clear_all(self):
        self._picked.clear()
        for cmd in self.states:
            self.states[cmd] = self.empty_state()
        self.load_state_to_ui(self.current_cmd_id)
        self.update_output()

    def on_preset_changed(self):
        self.update_output()

    # ---------------------------------------------------------
    # 폰트 목록 (스레드 · 콤보)
    # ---------------------------------------------------------
    def start_font_scan(self, force_rescan=False):
        self.refresh_btn.setEnabled(False)
        self._scan_started = True
        self.scanner = FontScannerThread(force_rescan=force_rescan, texdir=self.tex_dir)
        self.scanner.fonts_found.connect(self.on_scan_finished)
        self.scanner.start()

    def force_rescan_fonts(self):
        self._pending_sel = self._selected_entry()         # 새로 훑은 뒤에도 같은 폰트를 고른 채로 둔다
        self.font_model.clear()
        self.font_combo.setEnabled(False)
        self.scan_status.setText("디스크를 훑는 중입니다. 잠시만 기다려 주세요…")
        self.start_font_scan(force_rescan=True)

    def on_scan_finished(self, font_data_list):
        self.full_font_data = font_data_list
        self.refresh_combo_model()

    @staticmethod
    def _clean(text):
        t = text.strip()
        return t[2:].strip() if t.startswith("★ ") else t

    def refresh_combo_model(self):
        if not self.full_font_data:
            self.scan_status.setText("폰트를 하나도 찾지 못했습니다. 🔄 스캔을 눌러 다시 훑거나, 아래 칸에 이름을 직접 쓰세요.")
            self.refresh_btn.setEnabled(True)
            return

        typed = self.font_combo.lineEdit().text()
        # 지금 골라 둔 폰트를 (이전 표시 기준으로) 먼저 알아 둔다 — 기준을 바꾸거나 목록을 새로 채운 뒤에도 같은 폰트를 고른 채로 둔다
        selected = self._pending_sel or self._selected_entry()
        self._pending_sel = None
        self.font_model.clear()
        show_filename = (self.seg_view.value() == "file")
        self._shown_mode = self.seg_view.value()

        items = []
        for font_name, file_name, is_texlive, *_rest in self.full_font_data:
            items.append((file_name if show_filename else font_name, bool(is_texlive), is_collection(file_name)))
        texlive_items = sorted([it for it in items if it[1]], key=lambda x: x[0].lower())
        system_items = sorted([it for it in items if not it[1]], key=lambda x: x[0].lower())

        seen = set()
        n_tex = 0
        n_ttc = 0
        for display_text, is_texlive, is_ttc in (texlive_items + system_items):
            if display_text in seen:
                continue
            seen.add(display_text)
            item = QStandardItem(f"★ {display_text}" if is_texlive else display_text)
            item.setData(display_text, Qt.UserRole)
            if is_texlive:
                n_tex += 1
                item.setBackground(QBrush(QColor(230, 245, 255)))
                item.setForeground(QBrush(QColor(0, 50, 150)))
            if is_ttc:
                n_ttc += 1
                dark_bg = (not is_texlive) and self.palette().base().color().lightness() < 128      # TeX Live 줄은 밝은 파랑 배경을 따로 칠한다
                item.setForeground(QBrush(TTC_COLOR_DARK if dark_bg else TTC_COLOR))
            self.font_model.appendRow(item)

        self.font_combo.setEnabled(True)
        self.font_combo.setCurrentIndex(-1)
        self.font_combo.lineEdit().setText(typed)
        if selected is not None:
            target = selected[1] if show_filename else selected[0]
            for row in range(self.font_model.rowCount()):
                if self.font_model.item(row).data(Qt.UserRole) == target:
                    self.font_combo.setCurrentIndex(row)       # activated 는 내보내지 않으므로 글꼴 칸은 건드리지 않는다
                    break
        self.scan_status.setText(f"폰트 {len(seen)}개  ·  ★ = TeX Live 에 들어 있는 것({n_tex}개)  ·  "
                                 f"{'빨강 = ttc/otc 묶음 파일(' + str(n_ttc) + '개)  ·  ' if n_ttc else ''}고르면 아래 '받는 줄'에 들어갑니다")
        self.refresh_btn.setEnabled(True)

    def _selected_entry(self):
        """콤보에서 지금 고른(또는 이름 전체를 친) 폰트의 (폰트 이름, 파일 이름, TeX Live 인가). 없으면 None.
        이전에 보여 준 기준(self._shown_mode)으로 목록에서 찾는다. 같은 이름이 여럿이면 TeX Live 것을 먼저 쓴다."""
        idx = self.font_combo.currentIndex()
        key = self.font_combo.itemData(idx, Qt.UserRole) if idx >= 0 else None
        if not key:
            key = self._clean(self.font_combo.lineEdit().text())
        return self._find_entry(key, self._shown_mode)

    def _find_entry(self, text, mode):
        """목록에서 text(mode 기준의 이름)에 해당하는 항목. 없으면 None. 같은 이름이 여럿이면 TeX Live 것."""
        if not text:
            return None
        pos = 1 if mode == "file" else 0
        hits = [e for e in self.full_font_data if e[pos] == text]
        if not hits:
            return None
        hits.sort(key=lambda e: not e[2])          # TeX Live(True) 먼저. sort 는 안정적이라 나머지 순서는 그대로
        return tuple(hits[0])

    def _on_view_changed(self, value):
        """[폰트 이름] <-> [파일 이름]: 콤보의 선택뿐 아니라, 콤보에서 골라 넣은 칸들도 새 기준의 이름으로 바꾼다."""
        old = self._shown_mode
        self.refresh_combo_model()
        if value != old:
            self._convert_picked(value)

    def _convert_picked(self, mode):
        """콤보에서 골라 넣었고 그 뒤로 손대지 않은 칸을 mode 기준 이름으로 바꾼다. 손으로 고친 칸은 건드리지 않고 추적도 그만둔다."""
        changed_other = False
        for key, (entry, inserted) in list(self._picked.items()):
            cmd, style = key
            current = (self.style_edits[style].text() if cmd == self.current_cmd_id
                       else self.states[cmd]["fonts"][style])
            if current.strip() != inserted:
                del self._picked[key]
                continue
            feats = (self.style_feat_edits[style].text() if cmd == self.current_cmd_id
                     else self.states[cmd]["feats"][style])
            fi = get_font_index(feats)
            if fi is not None and is_collection(entry[1]):         # ttc/otc: FontIndex 가 가리키는 서체의 이름으로
                same = [x for x in self.full_font_data if x[1] == entry[1] and len(x) > 3 and x[3] == fi]
                if same:
                    entry = tuple(same[0])
            new_text = entry[1] if mode == "file" else entry[0]
            self._picked[key] = (entry, new_text)
            if cmd == self.current_cmd_id:
                self.style_edits[style].setText(new_text)          # textChanged -> update_output
            else:
                self.states[cmd]["fonts"][style] = new_text
                changed_other = True
        if changed_other:
            self.update_output()

    def fill_selected(self):
        """콤보에 지금 골라 둔(또는 이름을 끝까지 친) 폰트를 받는 줄에 넣는다. 목록에 없는 이름이면 아무것도 안 한다."""
        idx = self.font_combo.currentIndex()
        name = self.font_combo.itemData(idx, Qt.UserRole) if idx >= 0 else None
        if not name:
            name = self._clean(self.font_combo.lineEdit().text())
        if name and self._find_entry(name, self._shown_mode) is not None:
            self.pick_font(name)

    def _on_font_picked(self, idx):
        if idx < 0:
            return
        name = self.font_combo.itemData(idx, Qt.UserRole) or self._clean(self.font_combo.itemText(idx))
        self.pick_font(name)

    # ---------------------------------------------------------
    # styler 셸과의 접점: 메뉴 · 내보내기
    # ---------------------------------------------------------
    # ---------- ndhmdWriter 모드 ----------
    def compact_state(self):
        """Writer 가 블록 머리줄에 적어 둘 작은 설정: 허락된 명령 중 뭔가 들어 있는 것만, 빈 칸은 뺀다."""
        self.save_current_state()
        out = {}
        for cmd in self.cmd_order:
            if not self._cmd_allowed(cmd):
                continue
            st = self.states[cmd]
            c = {}
            fonts = {k: v for k, v in st["fonts"].items() if v.strip()}
            feats = {k: v for k, v in st["feats"].items() if v.strip()}
            if fonts:
                c["fonts"] = fonts
            if feats:
                c["feats"] = feats
            if st["checked_presets"]:
                c["checked_presets"] = list(st["checked_presets"])
            if st["general_features"].strip():
                c["general_features"] = st["general_features"]
            if c and fonts.get("Upright (Main)"):
                out[cmd] = c
        return {"states": out}

    def writer_result(self):
        """Writer 에 넘길 결과: 코드(\\set…font 블록들)와 다시 열 설정."""
        self.update_output()
        blocks = self._build_blocks(skip=self._output_skip())
        return {"tool": "ndhmdfont", "version": 1, "font_py": VERSION,
                "engine": self.pv_engine.currentText(), "scripts": (self.writer or {}).get("scripts", "all"),
                "commands": [c for c, _t, _p in blocks],
                "tex": "\n\n".join(t for _c, t, _p in blocks),
                "state": self.compact_state()}

    def send_to_writer(self):
        out = (self.writer or {}).get("out")
        if not out:
            return
        try:
            Path(out).write_text(json.dumps(self.writer_result(), ensure_ascii=False), encoding="utf-8")
        except OSError as e:
            QMessageBox.warning(self, "보내기 실패", str(e))
            return
        self._sent = True
        self.close()

    def tool_menus(self):
        """셸이 메뉴바에 올려 쓸 이 도구의 메뉴."""
        from PySide6.QtWidgets import QMenu
        m = QMenu("폰트", self)
        m.addAction("설정 열기…", self.open_file, "Ctrl+O")
        m.addAction("설정 저장…", self.save_file, "Ctrl+S")
        m.addSeparator()
        m.addAction("LaTeX 복사", lambda: QApplication.clipboard().setText(self.output_text.toPlainText()))
        m.addAction(".tex 로 저장…", self._save_to_file)
        m.addSeparator()
        m.addAction("모두 지우기", self.clear_all)
        m.addAction("폰트 목록 다시 훑기", self.force_rescan_fonts)
        self._menu = m
        return [m]

    def export_section(self):
        """스타일 파일(.sty)의 한 구역 (common/export.py). 지정한 폰트 명령이 하나라도 있으면 변경된 것이다.
        \\setmainfont 류와 \\newfontfamily 류만 넣는다: \\fontspec 류는 본문 안에서 쓰는 명령이라 프리앰블(.sty)에 둘 수 없다."""
        from ..common import export as ex
        if self.pdf_off:                                    # pdflatex 에서는 fontspec 이 오류를 내므로 기본으로는 내보내지 않는다 (체크하면 나간다)
            blocks = [(c, t) for c, t, _ph in self._build_blocks() if CMD_INFO[c][0] in ("set", "new")]
            sec = ex.Section("font", changed=False)
            if blocks:
                sec.full_tex = "\n\n".join(t for _c, t in blocks)
                sec.full_requires = ["\\RequirePackage{fontspec}"]
                sec.notes.append("폰트 명령(fontspec)은 XeLaTeX 또는 LuaLaTeX 로 컴파일할 때만 쓸 수 있습니다. 문서 바의 엔진이 지금 pdflatex 라 기본으로는 체크하지 않았습니다.")
            return sec
        blocks = self._build_blocks()
        keep = [(c, t) for c, t, _ph in blocks if CMD_INFO[c][0] in ("set", "new")]
        spec = [c for c, _t, _ph in blocks if CMD_INFO[c][0] == "spec"]
        tex = "\n\n".join(t for _c, t in keep)
        details = []
        for c, _t in keep:
            st = self.states[c]
            shown = c
            if c in self.NEEDS_MACRO_NAME:
                mac = st["macro"].strip() or r"\myfont"
                shown = c + (mac if mac.startswith("\\") else "\\" + mac)
            details.append("%s  %s" % (shown, st["fonts"]["Upright (Main)"].strip()))
        notes, skipped = [], []
        if keep:
            notes.append("폰트 명령(fontspec)은 XeLaTeX 또는 LuaLaTeX 로 컴파일할 때만 쓸 수 있습니다 (pdflatex 에서는 오류가 납니다).")
            if any(o in t for _c, t in keep for o in LUATEXKO_ONLY_OPTIONS):
                notes.append("CompressPunctuations 는 LuaLaTeX(luatexko) 전용 옵션입니다. XeLaTeX 로 컴파일하면 fontspec 오류가 납니다.")
        if spec:
            skipped.append("%s — 본문 안에서 쓰는 명령이라 스타일 파일에 넣지 못했습니다. 이 도구의 결과 칸에서 복사해 본문에 쓰세요." % ", ".join(spec))
        return ex.Section("font", changed=bool(keep), tex=tex, requires=["\\RequirePackage{fontspec}"] if keep else [],
                          notes=notes, details=details, skipped=skipped)

    def closeEvent(self, e):
        self._pv_timer.stop()
        self._pv_cancel_all()
        for t in list(self._pv_threads):
            t.wait(15000)
        if self._pv_tmp:
            shutil.rmtree(self._pv_tmp, ignore_errors=True)
            self._pv_tmp = None
        if self.scanner is not None and self.scanner.isRunning():
            self.scanner.wait(15000)
        super().closeEvent(e)

    # ---------------------------------------------------------
    # 출력 생성 (최종 조합)
    # ---------------------------------------------------------
    def _build_blocks(self, skip=()):
        """[(명령, 코드, 자리표시자인가)] — 결과 칸과 미리보기가 같은 코드를 쓰도록 한 곳에서 만든다.
        skip: 코드에서 뺄 공통 옵션 이름들 (미리보기가 xelatex 로 컴파일되지 못하는 옵션을 뺄 때만 쓴다)."""
        blocks = []
        for cmd_id in self.cmd_order:
            st = self.states[cmd_id]
            upright = st["fonts"]["Upright (Main)"].strip()
            placeholder = False

            if not self._cmd_allowed(cmd_id):
                continue
            if not upright:
                continue            # 폰트를 안 고른 명령은 아예 내지 않는다 (\setmainfont 없이 \setmainhangulfont 만 쓰는 경우도 있다)

            if cmd_id in self.NEEDS_MACRO_NAME:
                macro = st["macro"].strip() or r"\myfont"
                if not macro.startswith("\\"): macro = "\\" + macro
                cmd_str = f"{cmd_id}{macro}"
            else:
                cmd_str = cmd_id

            options = []

            up_feat = st["feats"]["Upright (Main)"].strip()
            if up_feat: options.append(f"UprightFeatures={{{up_feat}}}")

            def differs(font, feat):
                # 폰트가 윗줄과 같아도 FontIndex 가 있으면 (같은 ttc 의 다른 서체) 폰트를 적어야 한다
                return font and (font != upright or get_font_index(feat) is not None)

            bold = st["fonts"]["Bold"].strip()
            bold_feat = st["feats"]["Bold"].strip()
            if differs(bold, bold_feat): options.append(f"BoldFont={{{bold}}}")
            if bold_feat: options.append(f"BoldFeatures={{{bold_feat}}}")

            italic = st["fonts"]["Italic"].strip()
            it_feat = st["feats"]["Italic"].strip()
            if differs(italic, it_feat): options.append(f"ItalicFont={{{italic}}}")
            if it_feat: options.append(f"ItalicFeatures={{{it_feat}}}")

            bi = st["fonts"]["BoldItalic"].strip()
            bi_feat = st["feats"]["BoldItalic"].strip()
            if differs(bi, bi_feat): options.append(f"BoldItalicFont={{{bi}}}")
            if bi_feat: options.append(f"BoldItalicFeatures={{{bi_feat}}}")

            sc = st["fonts"]["SmallCaps"].strip()
            sc_feat = st["feats"]["SmallCaps"].strip()
            if differs(sc, sc_feat): options.append(f"SmallCapsFont={{{sc}}}")
            if sc_feat: options.append(f"SmallCapsFeatures={{{sc_feat}}}")

            for preset in st.get("checked_presets", []):
                if preset in self.HANGUL_ONLY_PRESETS and self._is_latin(cmd_id):
                    continue
                if preset in skip:
                    continue
                options.append(preset)

            gen_feat = st["general_features"].strip()
            if gen_feat: options.append(gen_feat)

            if options:
                opt_str = "[\n  " + ",\n  ".join(options) + "\n]"
                blocks.append((cmd_id, tidy_block(f"{cmd_str}{{{upright}}}{opt_str}"), placeholder))
            else:
                blocks.append((cmd_id, tidy_block(f"{cmd_str}{{{upright}}}"), placeholder))
        return blocks

    def update_output(self, *args):
        if getattr(self, '_is_loading_state', False): return
        self.save_current_state()
        self.output_text.setPlainText("\n\n".join(text for _cmd, text, _ph in self._build_blocks(skip=self._output_skip())))
        self._refresh_selector_ui()
        self._refresh_index_row()
        self._schedule_preview()


FontSelectorWindow = FontPage                # 독립 실행하던 이름 (호환)


def main(argv=None):
    """이 도구만 따로 띄운다. 인자가 없으면 예전과 같고, --out 이 있으면 ndhmdWriter 모드다 (종료코드: 보냈으면 0, 아니면 1)."""
    import argparse
    ap = argparse.ArgumentParser(description="폰트 도구 (fontspec 명령 구성기)")
    ap.add_argument("--out", help="Writer 모드: [Writer 로 보내기]가 결과를 쓸 .json 경로")
    ap.add_argument("--scripts", choices=("latin", "all"), default="all", help="Writer 모드: latin 이면 한글·한자 칸을 숨긴다")
    ap.add_argument("--engine", choices=ENGINES, help="문서의 엔진 (미리보기와 옵션 걸러내기)")
    ap.add_argument("--class", dest="klass", help="문서 클래스 (미리보기용)")
    ap.add_argument("--state", help="Writer 모드: 이전에 보낸 설정(.json 의 state 또는 결과 전체)")
    ap.add_argument("--texdir", default="", help="TeX 실행 파일이 있는 폴더")
    args, rest = ap.parse_known_args(argv[1:] if argv else sys.argv[1:])
    app = QApplication([sys.argv[0]] + rest)
    app.setStyle("Fusion")
    writer = None
    if args.out:
        writer = {"out": args.out, "scripts": args.scripts, "engine": args.engine, "class": args.klass}
    w = FontPage(writer=writer)
    if args.texdir:
        w.set_tex_dir(args.texdir)
    if writer and args.state:
        try:
            data = json.loads(Path(args.state).read_text(encoding="utf-8"))
            w.load_state(data.get("state", data) if isinstance(data, dict) else data)
        except (OSError, ValueError, KeyError, TypeError) as e:
            print("이전 설정을 읽지 못했습니다:", e, file=sys.stderr)
    w.setWindowTitle("폰트 도구 v%s%s" % (VERSION, " — ndhmdWriter" if writer else ""))
    w.resize(1340, 820)
    w.show()
    code = app.exec()
    if writer:
        return 0 if w._sent else 1
    return code


if __name__ == "__main__":
    sys.exit(main())
