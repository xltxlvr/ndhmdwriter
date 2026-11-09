#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ndhmd 저술 앱 — 첫 수직 슬라이스: 편집창 + 문법 하이라이터.

이 단계에서 세우는 것은 셋이다.

  1. QPlainTextEdit 기반 편집창 — 긴 글을 오래 보는 화면이므로 타이포그래피
     (행간, 단 너비, 여백, 커서)에 예산을 몰아준다.
  2. ndhmd4tex 방언의 신택스 하이라이터 — 정규식은 짐작하지 않고
     ndhmd4tex.py 에 정의된 것을 그대로 옮겼다(§문법 상수).
  3. `:::` 중첩 깊이를 블록 상태에 싣고 세로 가이드로 그리는 구조.

서랍/컴파일/sync 는 아직 없다. 다만 나중에 붙을 자리는 비워 뒀다:
  - Editor.file_line() / goto_file_line() 은 "편집창 행 <-> 파일 행" 변환을
    이미 통과시킨다. 지금은 항등이지만, front matter 를 숨기게 되면
    Editor.fm_offset 만 채우면 sync 배선 전체가 그대로 맞아 들어간다.
  - 하이라이터가 계산한 블록 상태에는 `:::` 깊이가 들어 있어서, 나중에
    린트 패널이나 접기(folding)가 같은 값을 재사용할 수 있다.

Python 3.9+ / PySide6.
"""

from __future__ import annotations

#: semver. 도움말(F1)에 그대로 보여준다. 수정이 있을 때마다 마지막
#: 자리(patch)를 하나씩 올린다 — CHANGELOG.md 에 그 기록을 남긴다.
__version__ = "0.5.7"

from contextlib import contextmanager

import configparser
import glob
import hashlib
import unicodedata
import json
import os
import platform
import re
import textwrap
import difflib
import shlex
import shutil
import signal
import subprocess
import sys
import html as _html
import tempfile
import time
import urllib.parse
import urllib.request
from dataclasses import dataclass
from pathlib import Path

from PySide6.QtCore import (QObject, QPoint, QRect, QRectF, QRunnable, QSettings, QSize, Qt,
                            QThreadPool, QTimer, Signal, Slot)
from PySide6.QtCore import QFileInfo
from PySide6.QtCore import QEvent, QProcess, QProcessEnvironment, QUrl
from PySide6.QtCore import QThread, QSortFilterProxyModel
from PySide6.QtGui import QFontMetrics, QDrag
from PySide6.QtCore import QMimeData
from PySide6.QtWidgets import QStyle, QStyleOptionViewItem
from PySide6.QtNetwork import QLocalServer, QLocalSocket
from PySide6.QtSvg import QSvgRenderer
from PySide6.QtGui import (
    QAction,
    QActionGroup,
    QDesktopServices,
    QGuiApplication,
    QIcon,
    QColor,
    QFont,
    QImage,
    QFontDatabase,
    QFontMetricsF,
    QKeySequence,
    QPainter,
    QPolygon,
    QPalette,
    QPixmap,
    QStandardItem,
    QStandardItemModel,
    QBrush,
    QTextBlockFormat,
    QTextCharFormat,
    QTextCursor,
    QTextDocument,
    QTextFormat,
    QSyntaxHighlighter,
)
from PySide6.QtCore import QRegularExpression
from PySide6.QtWidgets import (
    QAbstractItemDelegate,
    QApplication,
    QCheckBox,
    QComboBox,
    QDialog,
    QDialogButtonBox,
    QListView,
    QListWidget,
    QListWidgetItem,
    QDoubleSpinBox,
    QFileDialog,
    QFileIconProvider,
    QFrame,
    QFontComboBox,
    QFormLayout,
    QGridLayout,
    QGroupBox,
    QButtonGroup,
    QHBoxLayout,
    QInputDialog,
    QLabel,
    QLineEdit,
    QMainWindow,
    QMenu,
    QMessageBox,
    QPlainTextDocumentLayout,
    QPlainTextEdit,
    QPushButton,
    QScrollArea,
    QSizePolicy,
    QSpinBox,
    QStatusBar,
    QTabWidget,
    QTableWidget,
    QTableWidgetItem,
    QHeaderView,
    QTextEdit,
    QToolButton,
    QSplitter,
    QTreeWidget,
    QTreeWidgetItem,
    QTreeWidgetItemIterator,
    QVBoxLayout,
    QWidget,
    QRadioButton,
)
# 수식 편집기(ndhmdMath)가 쓰는 Qt 이름들 — 위와 겹쳐도 해가 없다.
from PySide6.QtCore import (QObject, QRegularExpression, QSettings, QSize, QStringListModel,
                            Qt, QStandardPaths, QThread, QTimer, Signal, QCoreApplication)
from PySide6.QtGui import (QAction, QColor, QFont, QFontDatabase, QGuiApplication, QImage,
                           QIcon, QKeySequence, QShortcut, QPainter, QPalette, QPixmap, QStandardItem,
                           QPen, QStandardItemModel, QSyntaxHighlighter, QTextCharFormat,
                           QTextCursor, QTextFormat)
from PySide6.QtWidgets import QTextBrowser
from PySide6.QtWidgets import (QAbstractItemView, QApplication, QCheckBox, QComboBox, QCompleter,
                               QDialog, QDialogButtonBox, QFileDialog, QFormLayout, QHBoxLayout,
                               QHeaderView, QLabel, QMainWindow, QMenu, QMessageBox,
                               QPlainTextEdit, QPushButton, QScrollArea, QSpinBox, QSplitter, QStyledItemDelegate, QDockWidget, QLineEdit, QListWidget, QListWidgetItem,
                               QTableWidget, QTableWidgetItem, QTextEdit, QToolBar, QToolButton, QVBoxLayout,
                               QWidget)

# ===========================================================================
# 1. 문법 상수 — ndhmd4tex.py 에서 그대로 가져온 것
# ===========================================================================
#
# 하이라이터가 변환기와 다른 정규식을 쓰면 "화면에서는 초록인데 PDF 에는
# 안 나오는" 종류의 버그가 생긴다. 그래서 짐작해서 새로 쓰지 않고 원본의
# 정의를 옮겼다. 원본이 바뀌면 여기도 같이 고쳐야 한다.

# 문서 전체에서 프론트매터 블록을 통째로 잡는다 — ndhmd4tex 와 같은 정규식.
FRONTMATTER_RE = re.compile(r"^---\s*\n(.*?)\n---\s*(?:\n|$)", re.DOTALL)
FRONTMATTER_OPEN_RE = re.compile(r"^---\s*$")
FRONTMATTER_CLOSE_RE = re.compile(r"^(?:---|\.\.\.)\s*$")

FENCE_OPEN_RE = re.compile(r"^ {0,3}(`{3,})[ \t]*([a-zA-Z0-9_-]*)[ \t]*$")
FENCE_OPEN_LOOSE_RE = re.compile(r"^ {0,3}(`{3,})[ \t]*([^`]*)$")   # showexam 용
FENCE_CLOSE_RE = re.compile(r"^ {0,3}(`{3,})[ \t]*$")

ENV_OPEN_RE = re.compile(r"^:::\{([a-zA-Z][\w-]*)\s*(.*)\}\s*$")
ENV_CLOSE_RE = re.compile(r"^:::\s*$")

#: :::{thebibliography ...} 를 다른 환경과 구분해서 찾는다. 정확히
#: 이 이름이어야 한다 — ndhmd4tex 의 환경 표에 등록된 이름 그대로다.
#: "bibliography"(the 없이)로 쓰면 등록되지 않은 환경으로 취급되어
#: widest 속성이 통째로 무시되고 기본 템플릿(\begin{bibliography}, 인자
#: 없음)으로 떨어진다 — 실제로 한 번 이렇게 잘못 냈던 버그였다.
BIBLIOGRAPHY_OPEN_RE = re.compile(r"^:::\{thebibliography(?:\s+.*)?\}\s*$")
#: \bibitem[option]{citekey} author, others 형태. option 은 있을 수도
#: 없을 수도 있다.
BIBITEM_RE = re.compile(r"^\\bibitem(?:\[(.*?)\])?\{([^}]*)\}\s*(.*)$")
FRAME_OPEN_RE = re.compile(r"^={4,}\{(.*)\}\s*$")
FRAME_CLOSE_RE = re.compile(r"^={4,}\s*$")

HEADING_RE = re.compile(r"^(#{1,6})\s+(.*?)(?:\s+\{(.*?)\})?$")
#: [편집] ▸ 스마트 문장부호 가 고를 수 있는 따옴표 짝들. "off" 는
#: 메뉴에는 있지만 여기엔 없다 — Editor.keyPressEvent 가 "off" 면
#: 아예 이 표를 안 보고 기본 입력으로 넘긴다. ndhmd4tex 가 스트레이트
#: 따옴표를 TeX 따옴표로 알아서 바꿔 주므로, TeX 짝은 따로 없다 —
#: 이건 순전히 편집 중 눈에 보이는 모양을 위한 것이다(출력에 영향
#: 없음).
SMART_QUOTE_PAIRS = {
    "curly":  {'"': ("\u201c", "\u201d"), "'": ("\u2018", "\u2019")},
    "cjk":    {'"': ("\u300e", "\u300f"), "'": ("\u300c", "\u300d")},
    "french": {'"': ("\u00ab", "\u00bb"), "'": ("\u2039", "\u203a")},
}
#: 스마트 문장부호의 마침표·쉼표 쪽 — 고리점(。)·모점(、). 따옴표
#: 짝과 별개로 켜고 끌 수 있다. 한국어식(cjk) 따옴표를 고르면 편의상
#: 같이 켜 주지만, 그 뒤로는 각자 독립적으로 바꿀 수 있다.
SMART_PUNCTUATION_PAIRS = {".": "\u3002", ",": "\u3001"}
HR_STAR_RE = re.compile(r"^\*{3,}\s*$")
HR_DASH_RE = re.compile(r"^-{3,}\s*$")

UL_RE = re.compile(r"^(\s*)[-*+](?:\s+|(?=\[))(.*)$")
OL_RE = re.compile(r"^(\s*)(\d+)[.)](?:\s+|(?=\[))(.*)$")
DESC_RE = re.compile(r"^(\s*)(\S.*?)\s+::(?!:)(?:\s+(.*?))?\s*$")
DESC_BRACE_RE = re.compile(r"^(\s*)\{([^{}]+)\}[ \t]*::(?:[ \t]{2,}(.*?))?[ \t]*$")
QUOTE_RE = re.compile(r"^>\s?(.*)$")
#: 파이프 표 바로 아래 줄에 오는 옵션 줄 — `{env=long,caption="…"}` (헤딩의 `{…}` 와 같은 속성 문법).
#: 앞 줄이 표 행일 때만 옵션 줄로 본다.
TABLE_OPT_RE = re.compile(r"^\s*\{(.*)\}\s*$")


def _is_table_row_text(line: str) -> bool:
    l = line.strip()
    return l.startswith("|") and l.endswith("|") and len(l) > 1


TABLE_SEP_RE = re.compile(r"^\s*\|?\s*:?-{2,}:?\s*(\|\s*:?-{2,}:?\s*)*\|?\s*$")
# ---------------------------------------------------------------------------
# pandoc grid table (ndhmd4tex 0.20)
# ---------------------------------------------------------------------------
#
# 아래 해석기는 ndhmd4tex 0.20 의 grid 표 해석기(parse_grid_table)를 그대로 옮긴 것이다
# (열 경계를 "화면 칸"으로 맞추는 방식까지 같다). 변환기의 규칙이 바뀌면 같이 고친다.
# 이 앱은 표를 칠하고(하이라이트), 미리보기를 그리고, 간단한 표를 표 편집기로
# 불러오고 내보내는 데에만 쓴다 — LaTeX 로 바꾸는 일은 ndhmd4tex 가 한다.

#: 표 바로 아래 줄의 속성 줄 `{env=long, caption="…"}` (ndhmd4tex 의 _TABLE_ATTR_LINE_RE 와 같다).
_TABLE_ATTR_LINE_RE = re.compile(r"^\{((?:[^{}|]|\{[^{}]*\})*)\}$")
#: grid 표의 가로 테두리 한 줄(머리글 구분 `+===+`, 정렬 `+:==:+` 포함).
GRID_BORDER_RE = re.compile(r"^\s*\+(?:[-=:]+\+)+\s*$")
#: 내용 줄 안에 섞인 가로 테두리 조각 `+-----+` (병합 셀 옆 줄).
GRID_PART_RE = re.compile(r"(?<![^\s|+])(?:\+[-=:]{2,})+\+?")

class GridTableError(ValueError):
    pass


_GRID_TOP_RE = re.compile(r"^\+(?:[-:]+\+)+$")
_GRID_H = set("-=:+")      # 가로 테두리에 올 수 있는 글자
_GRID_V = set("|+")        # 세로 테두리에 올 수 있는 글자
_GRID_WIDE = "\x00"        # 전각 글자의 둘째 칸 표시


def _grid_lines(blk):
    """(표 줄 목록, 속성 줄 또는 None). 공통 들여쓰기는 뗀다."""
    lines = [ln.rstrip() for ln in blk]
    attr = None
    if len(lines) >= 4 and _TABLE_ATTR_LINE_RE.match(lines[-1].strip()):
        attr = lines[-1].strip()
        lines = lines[:-1]
    ind = min(len(l) - len(l.lstrip()) for l in lines if l.strip())
    return [l[ind:] for l in lines], attr


def _is_grid_table(blk):
    """첫 줄이 `+----+----+` 꼴이면 grid 표 후보다. 해석 가능 여부는 따로 본다."""
    return len(blk) >= 3 and bool(_GRID_TOP_RE.match(blk[0].strip()))


def _grid_matrix(lines, by_width):
    rows = []
    for ln in lines:
        r = []
        for ch in ln:
            r.append(ch)
            if by_width and unicodedata.east_asian_width(ch) in ("W", "F"):
                r.append(_GRID_WIDE)
        rows.append(r)
    w = max(len(r) for r in rows)
    for r in rows:
        r.extend(" " * (w - len(r)))
    return rows


def _parse_grid_once(lines, by_width):
    g = _grid_matrix(lines, by_width)
    n, w = len(g), len(g[0])

    def ch(r, c):
        return g[r][c] if 0 <= r < n and 0 <= c < w else " "

    if ch(0, 0) != "+":
        raise GridTableError("첫 줄이 `+` 로 시작하지 않습니다")
    # 모서리에서 사각형을 찾는다(docutils 방식): 왼쪽 위 모서리에서 오른쪽으로
    # 가장 가까운 `+`, 거기서 아래로 가장 가까운 `+` 를 잡고 아래·왼쪽 테두리를
    # 확인한다. 못 닫으면 더 먼 모서리를 시도한다.
    cells, seen, queue = [], set(), [(0, 0)]
    while queue:
        r, c = queue.pop(0)
        if (r, c) in seen or ch(r, c) != "+":
            continue
        seen.add((r, c))
        found = None
        for c2 in range(c + 1, w):
            if ch(r, c2) not in _GRID_H:
                break
            if ch(r, c2) != "+":
                continue
            for r2 in range(r + 1, n):
                if ch(r2, c2) not in _GRID_V:
                    break
                if ch(r2, c2) != "+":
                    continue
                if (all(ch(r2, x) in _GRID_H for x in range(c, c2 + 1))
                        and all(ch(y, c) in _GRID_V for y in range(r, r2 + 1))):
                    found = (r, c, r2, c2)
                    break
            if found:
                break
        if not found:
            continue  # 오른쪽·아래 가장자리의 모서리: 셀의 시작점이 아니다
        cells.append(found)
        r, c, r2, c2 = found
        queue += [(r, c2), (r2, c), (r2, c2)]
    if not cells:
        raise GridTableError("닫힌 셀을 찾지 못했습니다")

    # 검증: 셀 안쪽은 겹치지 않고, 글자는 모두 어떤 셀 안쪽에 있어야 하며,
    # 테두리 글자는 어떤 셀의 테두리여야 한다.
    for y in range(n):
        for x in range(w):
            c_ = g[y][x]
            if c_ == " " or c_ == _GRID_WIDE:
                inner = sum(1 for (r, c, r2, c2) in cells if r < y < r2 and c < x < c2)
                if inner == 0 and c_ == " ":
                    # 셀 밖의 공백: 표 오른쪽 바깥의 여백이면 허용
                    on_edge = any(r <= y <= r2 and c <= x <= c2 for (r, c, r2, c2) in cells)
                    if not on_edge and x < max(c2 for (_, _, _, c2) in cells):
                        raise GridTableError(
                            f"표의 {y + 1}째 줄 {x + 1}칸 근처가 어느 셀에도 속하지 않습니다 "
                            f"— 이 줄의 `|` 위치가 위아래 줄과 맞는지 확인하십시오")
                continue
            inner = [1 for (r, c, r2, c2) in cells if r < y < r2 and c < x < c2]
            edge = [1 for (r, c, r2, c2) in cells
                    if r <= y <= r2 and c <= x <= c2 and not (r < y < r2 and c < x < c2)]
            if len(inner) > 1:
                raise GridTableError(f"{y + 1}째 줄에서 셀이 겹칩니다")
            if not inner and not edge:
                raise GridTableError(
                    f"표의 {y + 1}째 줄 {x + 1}칸 `{c_}` 이(가) 어느 셀의 테두리와도 이어지지 않습니다 "
                    f"— 모서리 `+` 나 세로선 `|` 가 어긋났거나 줄이 모자란지 확인하십시오")

    xs = sorted({x for (_, a, _, b) in cells for x in (a, b)})
    ys = sorted({y for (a, _, b, _) in cells for y in (a, b)})
    if ys[0] != 0 or ys[-1] != n - 1:
        raise GridTableError("표의 첫 줄과 끝 줄이 가로 테두리가 아닙니다")

    def border(y):
        return "".join(c_ for c_ in g[y] if c_ != _GRID_WIDE)

    out = []
    for (r, c, r2, c2) in cells:
        rows_txt = ["".join(c_ for c_ in g[y][c + 1:c2] if c_ != _GRID_WIDE).strip()
                    for y in range(r + 1, r2)]
        paras, cur = [], []
        for t in rows_txt:
            if t:
                cur.append(t)
            elif cur:
                paras.append(" ".join(cur))
                cur = []
        if cur:
            paras.append(" ".join(cur))
        out.append({"row": ys.index(r), "col": xs.index(c),
                    "rs": ys.index(r2) - ys.index(r), "cs": xs.index(c2) - xs.index(c),
                    "paras": paras})
    nrows, ncols = len(ys) - 1, len(xs) - 1
    eq = [i for i, y in enumerate(ys) if "=" in border(y)]
    header_rows = eq[0] if eq else 0
    footer_start = eq[1] if len(eq) > 1 else None

    def seg(y, j):
        return "".join(c_ for c_ in g[y][xs[j] + 1:xs[j + 1]] if c_ != _GRID_WIDE)

    aline = ys[eq[0]] if eq else 0
    aligns = []
    for j in range(ncols):
        sg = seg(aline, j)
        if sg.startswith(":") and sg.endswith(":") and len(sg) > 1:
            aligns.append("c")
        elif sg.endswith(":"):
            aligns.append("r")
        else:
            aligns.append("l")
    # 머리글 안쪽의 부분 구분선 -> \cmidrule 범위(1-based, 닫힌 구간)
    cmid = {}
    for i in range(1, header_rows):
        y = ys[i]
        cols = [j + 1 for j in range(ncols)
                if seg(y, j) and set(seg(y, j)) <= set("-=:")]
        ranges = []
        for j in cols:
            if ranges and ranges[-1][1] == j - 1:
                ranges[-1][1] = j
            else:
                ranges.append([j, j])
        if ranges:
            cmid[i - 1] = ranges
    dash_w = [xs[j + 1] - xs[j] - 1 for j in range(ncols)]
    return {"cells": out, "nrows": nrows, "ncols": ncols, "header_rows": header_rows,
            "footer_start": footer_start, "aligns": aligns, "cmid": cmid,
            "dash_widths": dash_w}


def parse_grid_table(blk):
    """grid 표 블록을 해석한다. 화면 칸 기준으로 먼저, 안 되면 문자 번호 기준으로."""
    lines, attr = _grid_lines(blk)
    try:
        return _parse_grid_once(lines, True), attr
    except GridTableError as e1:
        if not any(unicodedata.east_asian_width(c) in ("W", "F") for ln in lines for c in ln):
            raise
        try:
            return _parse_grid_once(lines, False), attr
        except GridTableError:
            raise e1


def grid_display_width(text: str) -> int:
    """고정폭 편집창에서 차지하는 칸 수(전각 2칸). ndhmd4tex 가 열을 맞추는 방식과 같다."""
    return sum(2 if unicodedata.east_asian_width(ch) in ("W", "F") else 1 for ch in text)


def parse_grid_simple(lines):
    """grid 표를 표 편집기용 (정렬 목록, 행 목록)으로 읽는다.

    편집기가 다룰 수 있는 표만 받는다 — 병합 셀·바닥글·두 줄 이상 머리글이 없고 머리글이
    정확히 한 줄(`=` 줄 하나)인 표. 여러 줄 셀은 ndhmd4tex 와 같이 줄을 공백으로 이어 한 줄로
    읽고(빈 줄이 든 여러 문단 셀은 안 받는다), 못 받는 표는 GridTableError 로 이유를 알린다.
    """
    tbl, _attr = parse_grid_table([l for l in lines])
    for cl in tbl["cells"]:
        if cl["rs"] > 1 or cl["cs"] > 1:
            raise GridTableError("병합된 셀이 있는 grid 표는 편집기에서 다룰 수 없습니다")
        if len(cl["paras"]) > 1:
            raise GridTableError("한 셀에 문단이 여럿인 grid 표는 편집기에서 다룰 수 없습니다")
    if tbl["footer_start"] is not None:
        raise GridTableError("바닥글(두 번째 `=` 줄)이 있는 grid 표는 편집기에서 다룰 수 없습니다")
    if tbl["header_rows"] != 1:
        raise GridTableError("머리글이 정확히 한 줄인 grid 표만 편집기에서 다룰 수 있습니다 "
                             "(첫 행 아래에 `+===+` 줄이 하나 있어야 합니다)")
    nrows, ncols = tbl["nrows"], tbl["ncols"]
    grid = [[""] * ncols for _ in range(nrows)]
    for cl in tbl["cells"]:
        grid[cl["row"]][cl["col"]] = cl["paras"][0] if cl["paras"] else ""
    return list(tbl["aligns"]), grid


def grid_to_tsv(lines) -> str:
    """grid 표 → TSV(탭으로 나뉜 글). 병합 셀은 왼쪽 위 칸에만 글을 두고 가려진 칸은 비운다
    (TSV 는 병합을 표현할 수 없다). 한 셀의 여러 줄·문단은 공백으로 잇는다."""
    tbl, _attr = parse_grid_table(lines)
    grid = [[""] * tbl["ncols"] for _ in range(tbl["nrows"])]
    for cl in tbl["cells"]:
        grid[cl["row"]][cl["col"]] = " ".join(" ".join(cl["paras"]).split())
    return "\n".join("\t".join(row) for row in grid)


def format_grid_table(aligns, rows) -> list:
    """(정렬 `l`/`c`/`r` 목록, 행 목록 — 첫 행이 머리글) → grid 표의 줄 목록.

    칸 너비는 전각을 2칸으로 세어 맞춘다. 셀 안의 줄바꿈은 공백으로 바꾼다.
    """
    ncols = len(aligns)
    clean = [[" ".join(str(c).split()) for c in (list(r) + [""] * ncols)[:ncols]] for r in rows]
    widths = [max([3] + [grid_display_width(r[j]) for r in clean]) for j in range(ncols)]

    def border(fill, marks=None):
        parts = []
        for j, w in enumerate(widths):
            seg = fill * (w + 2)
            if marks:
                a = aligns[j]
                if a == "c":
                    seg = ":" + seg[1:-1] + ":"
                elif a == "r":
                    seg = seg[:-1] + ":"
                else:
                    seg = ":" + seg[1:]
            parts.append(seg)
        return "+" + "+".join(parts) + "+"

    def line(r):
        cells = []
        for j, w in enumerate(widths):
            pad = w - grid_display_width(r[j])
            cells.append(" " + r[j] + " " * (pad + 1))
        return "|" + "|".join(cells) + "|"

    out = [border("-")]
    for i, r in enumerate(clean):
        out.append(line(r))
        out.append(border("=", marks=True) if i == 0 else border("-"))
    return out


def grid_table_html(lines, fg: str = "#222222", inline=None) -> str:
    """grid 표 원문 줄 → 미리보기용 HTML(병합 셀 포함). 해석이 안 되면 ""."""
    import html as _html
    try:
        tbl, _attr = parse_grid_table(lines)
    except (GridTableError, ValueError):
        return ""
    grid = [[None] * tbl["ncols"] for _ in range(tbl["nrows"])]
    for cl in tbl["cells"]:
        grid[cl["row"]][cl["col"]] = cl
    names = {"l": "left", "c": "center", "r": "right"}
    out = [f'<table border="1" cellspacing="0" cellpadding="5" '
           f'style="color:{fg}; border-collapse:collapse;">']
    for r in range(tbl["nrows"]):
        tag = "th" if r < tbl["header_rows"] else "td"
        row = []
        for c in range(tbl["ncols"]):
            cl = grid[r][c]
            if cl is None:
                continue
            txt = "<br>".join(_html.escape(p) for p in cl["paras"])
            if inline:
                txt = inline(txt)
            span = (f' rowspan="{cl["rs"]}"' if cl["rs"] > 1 else "") + \
                   (f' colspan="{cl["cs"]}"' if cl["cs"] > 1 else "")
            row.append(f'<{tag} align="{names[tbl["aligns"][c]]}"{span}>{txt or "&nbsp;"}</{tag}>')
        out.append("<tr>" + "".join(row) + "</tr>")
    out.append("</table>")
    return "".join(out)


LINECOMMENT_RE = re.compile(r"^//.*$")
FOOTNOTE_DEF_RE = re.compile(r"^\[\^([A-Za-z0-9_\-가-힣]+)\]:\s?(.*)$")

INCLUDE_RE = re.compile(r"(?<!`)\{\{([^{}\n]+?)\}\}(?!`)")
INLINE_CODE_RE = re.compile(r"`([^`\n]+)`")
INLINE_MATH_RE = re.compile(r"(\$[^$\n]+?\$|\\\([^)]*?\\\))")
FIGURE_RE = re.compile(
    r"!\[((?:[^\[\]]|\[[^\[\]]*\])*)\]\(([^)\s]+)\)"
    r"(?:\{((?:[^{}]|\{[^{}]*\})*)\})?")
#: ndhmd4tex 0.12 의 참조 스타일 그림: ![캡션][표지] + 별도 줄의
#: [표지]: 경로 속성... 정의. FIGURE_RE 와 달리 경로가 이 줄에 없다 —
#: PreviewScanner 가 문서 전체에서 정의를 따로 찾아야 한다.
FIGURE_REF_RE = re.compile(r"!\[((?:[^\[\]]|\[[^\[\]]*\])*)\]\[([^\]]+)\]")
#: 그 정의 줄 자체: [표지]: 경로 [속성...]. 속성은 미리보기에 안 쓴다.
#: 각주 정의([^note]: ...)와 구분해야 하므로 ^ 로 시작하는 표지는
#: 제외한다.
FIGURE_DEF_RE = re.compile(r"^\[(?!\^)([^\]]+)\]:\s*(\S+)")
LINK_RE = re.compile(r"\[([^\]]*)\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)")
#: 참조 스타일 링크 [글자][표지] (표지는 비어 있지 않아야 한다 — [글자][]는 ndhmd4tex 이 참조로 보지 않는다). 앞에 !(그림)나 [([[색인]])가 오면 아니다.
REFLINK_RE = re.compile(r"(?<![!\[\\])\[((?:[^\[\]]|\[[^\[\]]*\])*)\]\[([^\]\n]+)\]")
#: 맨 주소(링크 문법 없이 쓴 http(s)/ftp 주소). 끝의 문장부호는 _trim_url 이 뗀다.
BARE_URL_RE = re.compile(r"(?:https?|ftp)://[^\s<>\[\]{}\"'`|\\^]+")
FOOTNOTE_REF_RE = re.compile(r"\[\^([^\]\n]+)\]")
INLINE_FOOTNOTE_RE = re.compile(r"(?<!\^)\^\[([^\]\n]+)\]")
#: 칠하기 전용. ndhmd4tex 0.19 와 같이 대괄호 안에 대괄호 한 겹까지 허용한다(`^[각주에 [#sec:a] 참조]`).
#: 이동·점검용 FOOTNOTE_REF_RE 는 그대로 두었다 — 거기서는 식별자만 필요하다.
_HL_BRACKET_BODY = r"(?:[^\[\]\n]|\[[^\[\]\n]*\])+"
HL_INLINE_FOOTNOTE_RE = re.compile(r"(?<!\^)\^\[(" + _HL_BRACKET_BODY + r")\]")
HL_FOOTNOTE_REF_RE = re.compile(r"\[\^(" + _HL_BRACKET_BODY + r")\]")
#: 각주 꼬리표 `^[본문]{side}` `[^id]{sym opt=3}` — 각주 바로 뒤의 `{…}`. ndhmd4tex 의 _NOTE_TAGLIKE_RE 와 같은
#: 글자만 꼬리표로 본다(`#`·`=` 로 시작하는 `{#라벨}` `{=latex}` 와 구별된다).
NOTE_TAG_RE = re.compile(r"\{([\w \t=,.\"'\[\]+-]+)\}")
INDEX_RE = re.compile(r"\[\[(.*?)(?:\|(.*?))?\]\]")
INLINE_LABEL_RE = re.compile(r"\{#([A-Za-z0-9:_.-]+)\}")
#: 인용·참조 뒤에 붙는 선택 인자 블록 `[@키]{rawopt="[see][p.~23]"}` 의 `{…}` 부분(그룹 1).
#: 프리픽스는 ndhmd4tex 기본 refcite 의 것(@ @t: @p: @a: @y: # C: E: F: T: title: name: page:).
CITE_RAWOPT_RE = re.compile(
    r"\[(?:@[tpay]:|@|#|C:|E:|F:|T:|title:|name:|page:)[^\]\n]+\]"
    r"(\{\s*rawopt\s*=\s*(?:\"[^\"\n]*\"|'[^'\n]*')\s*\})")
RAW_ATTR_RE = re.compile(r"\{=([a-zA-Z][a-zA-Z0-9_+-]*)\}")
# ndhmd4tex 의 INLINE 규칙표를 그대로 옮긴 것. 순서까지 같아야 한다.
#
# 이 방언의 핵심은 짝맞는 델리미터의 **뒤쪽을 검사하지 않는** 것이다.
# 한국어는 "*강조어구*가" 처럼 닫는 표지 바로 뒤에 조사가 공백 없이 붙는
# 일이 흔한데, pandoc 처럼 "닫는 쪽 뒤에 공백/구두점이 오는가"를 보면
# 이런 것이 전부 강조로 인식되지 않는다. 그래서 경계 가드가 앞뒤 어디에도
# 없고, `_` 는 강조 표지가 아니다(`*` 만 쓴다).
#
# 표지 길이를 같이 들고 다니는 이유는 아래 _paint_emphasis 주석에 있다.
EMPHASIS_RULES = (
    (re.compile(r"\*\*\*(.+?)\*\*\*"), "f_bold_italic", 3),
    (re.compile(r"\*\*(.+?)\*\*"), "f_bold", 2),
    (re.compile(r"\*(.+?)\*"), "f_italic", 1),
    (re.compile(r"~~(.+?)~~"), "f_strike", 2),
    (re.compile(r"\^\^(.+?)\^\^"), "f_dotemph", 2),
)

# 여러 줄에 걸치는 스팬의 여닫는 표지
# 여러 줄 스팬을 통째로 잡는 것들 — 미리보기가 커서 위치로 범위를 찾을 때 쓴다.
CODE_FENCE_RE = re.compile(r"```([a-zA-Z0-9_-]*)\n(.*?)\n```", re.DOTALL)
DISPLAY_MATH_RE = re.compile(r"(?<!`)(\$\$.*?\$\$|\\\[.*?\\\])(?!`)", re.DOTALL)
MATH_ENV_RE = re.compile(
    r"(?<!`)(\\begin\{(equation\*?|align\*?|gather\*?|multline\*?|eqnarray\*?)\}"
    r".*?\\end\{\2\})(?!`)", re.DOTALL)
TABLE_ENV_RE = re.compile(
    r"(?<!`)(\\begin\{(tabular|tabularx|tabulary|tblr|longtblr)\}"
    r".*?\\end\{\2\})(?!`)", re.DOTALL)

DISPLAY_MATH_OPEN_RE = re.compile(r"(?<!`)(\$\$|\\\[)")
MATH_ENV_OPEN_RE = re.compile(
    r"(?<!`)\\begin\{(equation\*?|align\*?|gather\*?|multline\*?|eqnarray\*?)\}")
TABLE_ENV_OPEN_RE = re.compile(
    r"(?<!`)\\begin\{(tabular|tabularx|tabulary|tblr|longtblr)\}")
COMMENT_OPEN_RE = re.compile(r"(?<!`)<!--")

# 린트에 걸릴 흔한 오타 — 빨간 밑줄 대신 조용한 경고색으로만 표시한다.
LINT_ENV_LOOSE_RE = re.compile(r"^:::\s+\{")
LINT_FRAME_LOOSE_RE = re.compile(r"^={4,}\s+\{")


# ===========================================================================
# 2. 블록 상태 비트 배분
# ===========================================================================
#
# QSyntaxHighlighter 는 줄 단위로만 돌기 때문에, 여러 줄에 걸치는 구조는
# 직접 상태를 이어 날라야 한다. 32비트 정수 하나에 다음을 나눠 싣는다.
#
#   bits  0-2   SPAN   현재 열려 있는 여러 줄 스팬의 종류 (0 = 없음)
#   bits  3-7   ENV    ::: 중첩 깊이 (0-31)
#   bits  8-12  FRAME  ==== 중첩 깊이 (0-31)
#   bits 13-16  FENCE  열린 코드펜스의 백틱 개수 - 3 (0-15)
#   bit  17     SEXAM  그 펜스가 showexam 인가
#   bit  24     SENT   센티널 — 상태값이 -1(미설정)과 충돌하지 않게 한다
#
# ENV 깊이를 세는 비용은 사실상 0인데, 이걸 실어 두면 나중에 접기·린트·
# 구조 패널이 같은 값을 공짜로 재사용할 수 있다.

SPAN_SHIFT, SPAN_MASK = 0, 0b111
ENV_SHIFT, ENV_MASK = 3, 0b11111
FRAME_SHIFT, FRAME_MASK = 8, 0b11111
FENCE_SHIFT, FENCE_MASK = 13, 0b1111
SEXAM_BIT = 1 << 17
ITEM_BIT = 1 << 18        # 이 줄이 (간격 대상) 목록 항목 줄이다 — 다음 줄이 "첫 항목인가"를 알기 위한 것
SENTINEL = 1 << 24

SPAN_NONE = 0
SPAN_FRONTMATTER = 1
SPAN_FENCE = 2
SPAN_DISPLAY_MATH = 3
SPAN_MATH_ENV = 4
SPAN_TABLE_ENV = 5
SPAN_COMMENT = 6

MAX_GUIDE_DEPTH = 4   # 가이드를 그릴 최대 중첩 — 그 이상은 가장 안쪽에 겹쳐 그린다


def env_depth(state: int) -> int:
    """블록 상태에서 `:::` 깊이만 꺼낸다. 상태가 없으면 0."""
    if state < 0:
        return 0
    return (state >> ENV_SHIFT) & ENV_MASK


def frame_depth(state: int) -> int:
    if state < 0:
        return 0
    return (state >> FRAME_SHIFT) & FRAME_MASK


# ===========================================================================
# 3. 테마
# ===========================================================================
#
# 글 쓰는 화면이므로 채도를 낮게 잡는다. 레인보우 브래킷처럼 화려하게
# 칠하면 정작 읽어야 할 본문이 뒤로 밀린다. 구조 기호(`:::`, `#`, 백틱)는
# 오히려 흐리게 — 그것들은 읽을 대상이 아니라 위치 표시다.

@dataclass(frozen=True)
class Theme:
    name: str
    bg: str
    fg: str
    marker: str          # 구조 기호. 본문보다 흐리다
    heading: str
    env_name: str
    math: str
    code_fg: str
    code_bg: str
    link: str
    include: str
    comment: str
    frontmatter: str
    frontmatter_bg: str
    warn: str
    current_line: str
    match_bg: str
    match_active_bg: str
    panel_bg: str
    gutter_fg: str
    gutter_fg_active: str
    guides: tuple

    def qcolor(self, key: str) -> QColor:
        return QColor(getattr(self, key))


def _render_branch_arrow(color: str, points: list, kind: str) -> str:
    """작은 삼각형 화살표를 color 로 채워 그린 뒤 임시 PNG 파일로
    저장하고 그 경로를 돌려준다. Qt 스타일시트의 url() 은 실제
    파일(또는 Qt 리소스) 경로를 기대하지, data: 인라인 URI 는
    조용히 무시한다(오류 없이 그냥 아무것도 안 그려진다) — 그래서
    매번 진짜 파일로 써 둬야 한다. 색·모양(kind)마다 다른 파일
    이름을 써서 테마가 바뀌거나 접힘/펼침 모양이 서로 안 겹친다."""
    pix = QPixmap(10, 10)
    pix.fill(Qt.transparent)
    painter = QPainter(pix)
    painter.setRenderHint(QPainter.Antialiasing)
    painter.setBrush(QColor(color))
    painter.setPen(Qt.NoPen)
    painter.drawPolygon(QPolygon([QPoint(x, y) for x, y in points]))
    painter.end()
    safe_color = re.sub(r"[^0-9a-zA-Z]", "", color)
    path = Path(tempfile.gettempdir()) / f"ndhmdwriter_branch_{kind}_{safe_color}.png"
    pix.save(str(path), "PNG")
    return str(path).replace("\\", "/")   # 윈도우 경로 구분자는 QSS url() 이 못 받는다


def tree_branch_css(color: str) -> str:
    """QTreeWidget 접기/펼치기 화살표를 지정한 색으로 직접 그린 작은
    PNG 로 바꿔 끼우는 스타일시트 조각을 돌려준다.

    운영체제 기본 스타일이 그리는 화살표는 OS의 라이트/다크 모드를
    따라가는데, 이 앱 자신의 테마 선택과는 무관하게 색이 고정돼
    있어서 — 예컨대 OS가 다크 모드면 화살표가 흰색으로 그려지는데,
    이 앱에서 밝은 테마를 고르면 그 흰 화살표가 밝은 배경 위에서
    안 보이는 — 조합에 따라 안 보이는 경우가 있었다. 화살표 자체를
    이 테마의 글자색으로 직접 그려서 그 문제를 피한다.
    """
    closed_path = _render_branch_arrow(color, [(3, 2), (3, 8), (8, 5)], "closed")  # ▶
    open_path = _render_branch_arrow(color, [(2, 3), (8, 3), (5, 8)], "open")      # ▼
    return f"""
        QTreeWidget::branch:has-children:closed {{
            image: url({closed_path});
        }}
        QTreeWidget::branch:has-children:open {{
            image: url({open_path});
        }}
    """


LIGHT = Theme(
    name="light",
    bg="#FAF7F0",
    fg="#23211E",
    marker="#B7AE9E",
    heading="#1A4F63",
    env_name="#7C5480",
    math="#3C5A8C",
    code_fg="#4A6138",
    code_bg="#F1ECE0",
    link="#2C6B5D",
    include="#9A5B2E",
    comment="#A49E92",
    frontmatter="#8A8274",
    frontmatter_bg="#F3EFE4",
    warn="#B4552F",
    current_line="#F3EFE4",
    match_bg="#E4DCC4",
    match_active_bg="#D6C79A",
    panel_bg="#F3EFE4",
    gutter_fg="#C8C0B0",
    gutter_fg_active="#8A8274",
    guides=("#C9C0AE", "#B9C4BC", "#CCBEC4", "#BDC2CE", "#C7C6B4"),
)

DARK = Theme(
    name="dark",
    bg="#1C1B19",
    fg="#E3DFD6",
    marker="#5A554B",
    heading="#7FB0C2",
    env_name="#BE9BC0",
    math="#8FA6D2",
    code_fg="#A6C288",
    code_bg="#252320",
    link="#7FC0AB",
    include="#D19A6B",
    comment="#6B665D",
    frontmatter="#7E7768",
    frontmatter_bg="#222020",
    warn="#D4795A",
    current_line="#232120",
    match_bg="#3B372B",
    match_active_bg="#544C33",
    panel_bg="#222020",
    gutter_fg="#45413A",
    gutter_fg_active="#8A8274",
    guides=("#3E3A33", "#3A423D", "#413A3E", "#383B42", "#403F36"),
)

#: 커뮤니티 피드백 — "전체적으로 색감이 노랑 계통"이라는 지적에서 나왔다.
#: LIGHT/DARK 는 그대로 두고, 순백 고대비 하나와 빨강·노랑·초록·파랑 색조
#: 넷을 더한다. 전부 bg/fg 대비 12:1 이상(WCAG AAA 인 7:1 을 넉넉히
#: 넘긴다), 강조색도 배경 대비 4.5:1(WCAG AA 본문 기준) 이상 나오도록
#: 손으로 하나씩 확인해서 골랐다 — 짐작으로 예쁜 색만 고르면 정작 읽기
#: 힘든 조합이 나오기 쉽다.

HIGH_CONTRAST = Theme(
    name="high_contrast",
    bg="#FFFFFF",
    fg="#000000",
    marker="#707070",
    heading="#0B4D8C",
    env_name="#6A1B9A",
    math="#0B4D8C",
    code_fg="#1B5E20",
    code_bg="#F0F0F0",
    link="#0B4D8C",
    include="#B34700",
    comment="#5A5A5A",
    frontmatter="#5A5A5A",
    frontmatter_bg="#EFEFEF",
    warn="#C62828",
    current_line="#EFEFEF",
    match_bg="#FFF176",
    match_active_bg="#FFD54F",
    panel_bg="#F5F5F5",
    gutter_fg="#B0B0B0",
    gutter_fg_active="#000000",
    guides=("#B0B0B0", "#B0B0B0", "#B0B0B0", "#B0B0B0", "#B0B0B0"),
)

RED = Theme(
    name="red",
    bg="#FBF1F1",
    fg="#2E1A1A",
    marker="#C9A8A8",
    heading="#8C2F3A",
    env_name="#8C4F6B",
    math="#7A4A55",
    code_fg="#6B4A3A",
    code_bg="#F3E4E4",
    link="#A13A3A",
    include="#9A5B2E",
    comment="#B08A8A",
    frontmatter="#9C7A7A",
    frontmatter_bg="#F5E8E8",
    warn="#994827",
    current_line="#F5E8E8",
    match_bg="#EBC9C9",
    match_active_bg="#DDA3A3",
    panel_bg="#F5E8E8",
    gutter_fg="#D8BFBF",
    gutter_fg_active="#9C7A7A",
    guides=("#D8B8B8", "#C9C4BC", "#D0BEC4", "#C2BECE", "#D2C6B4"),
)

YELLOW = Theme(
    name="yellow",
    bg="#FDF6DC",
    fg="#3A3018",
    marker="#C9BC8E",
    heading="#775C16",
    env_name="#8C5D3A",
    math="#6B5A2E",
    code_fg="#5A6B2E",
    code_bg="#F5EAC0",
    link="#775C16",
    include="#885316",
    comment="#AD9E70",
    frontmatter="#96895A",
    frontmatter_bg="#F7EEC8",
    warn="#994827",
    current_line="#F7EEC8",
    match_bg="#EEDB8E",
    match_active_bg="#E0C463",
    panel_bg="#F7EEC8",
    gutter_fg="#DDCB8E",
    gutter_fg_active="#96895A",
    guides=("#D8CC8E", "#C4CC9E", "#D4C4A0", "#C0C2A8", "#D0C88E"),
)

GREEN = Theme(
    name="green",
    bg="#F1F7EF",
    fg="#1A2E1A",
    marker="#A8C9A8",
    heading="#2F6B3A",
    env_name="#4F7C55",
    math="#3A6B4A",
    code_fg="#3A6B2E",
    code_bg="#E4F3E0",
    link="#2F7A4A",
    include="#617024",
    comment="#8AAE8A",
    frontmatter="#7A9C7A",
    frontmatter_bg="#E8F5E4",
    warn="#994827",
    current_line="#E8F5E4",
    match_bg="#C9EBC9",
    match_active_bg="#A3DDA3",
    panel_bg="#E8F5E4",
    gutter_fg="#BFD8BF",
    gutter_fg_active="#7A9C7A",
    guides=("#B8D8B8", "#BCC9C4", "#BED0C4", "#BECED2", "#C6D2B4"),
)

BLUE = Theme(
    name="blue",
    bg="#EFF3F9",
    fg="#1A222E",
    marker="#A8B8D8",
    heading="#2F4F8C",
    env_name="#4F5F9C",
    math="#3A4F8C",
    code_fg="#2E5A6B",
    code_bg="#E0E8F3",
    link="#2F6B8C",
    include="#775C27",
    comment="#8A9AB0",
    frontmatter="#7A8C9C",
    frontmatter_bg="#E4EAF5",
    warn="#994827",
    current_line="#E4EAF5",
    match_bg="#C9D8EB",
    match_active_bg="#A3C0DD",
    panel_bg="#E4EAF5",
    gutter_fg="#BFCBD8",
    gutter_fg_active="#7A8C9C",
    guides=("#B8C4D8", "#BCC9CC", "#C4C0D0", "#B0C0DE", "#C0C6D4"),
)

#: 테마 이름(prefs/theme 에 저장되는 문자열) → Theme 객체. "system" 은
#: 여기 없고 Prefs.resolved_theme() 에서 따로 푼다 — 그건 OS 설정을
#: 봐야 하는, 이름 하나로 안 끝나는 특별한 경우이기 때문이다.
THEMES = {
    "light": LIGHT,
    "dark": DARK,
    "high_contrast": HIGH_CONTRAST,
    "red": RED,
    "yellow": YELLOW,
    "green": GREEN,
    "blue": BLUE,
}


# ===========================================================================
# 4. 하이라이터
# ===========================================================================

#: .bib 한 줄 안의 `@종류{citekey,` (종류=1, citekey=2). 줄머리의 항목 시작만 본다.
BIB_LINE_ENTRY_RE = re.compile(r"^\s*@(\w+)\s*\{\s*([^,\s}]+)\s*,")


class NdhmdHighlighter(QSyntaxHighlighter):
    """ndhmd4tex 방언 하이라이터.

    한 줄을 처리하는 순서는 이렇다.

      (a) 이전 줄에서 넘어온 스팬이 열려 있으면 그것부터 닫는다. 닫히는
          위치가 줄 중간이면 그 뒤는 (b) 로 이어서 처리한다.
      (b) 줄 전체가 하나의 구조인 것들(헤딩, `:::`, `====`, 펜스, 인용,
          목록 표지)을 본다.
      (c) 남은 본문에 인라인 규칙을 얹는다. 단 인라인 코드 안쪽은
          보호 구간으로 잡아 두고 건너뛴다 — 원본 정규식들이 백틱 옆을
          `(?<!`)` 로 피해 가는 것과 같은 취지다.
    """

    def __init__(self, document, theme: Theme):
        super().__init__(document)
        self._theme = theme
        #: 목록 항목 사이를 화면에서만 벌리는 장치(0.4.116). 0 = 꺼짐.
        self._gap_scale = 0.0
        self._gap_bullets = False
        self._gap_fmt = None
        #: 문서 종류: "md"(원고) · "yaml" · "bib". 부속 파일은 원고 문법이 아니므로
        #: 줄머리 `#` 가 제목으로 칠해지는 일이 없도록 따로 칠한다(0.5beta26).
        self._kind = "md"
        self._build_formats()

    def set_kind(self, kind: str, rehighlight: bool = False):
        kind = kind if kind in ("yaml", "bib") else "md"
        if kind != self._kind:
            self._kind = kind
            if rehighlight:
                self.rehighlight()

    @staticmethod
    def kind_for_path(path) -> str:
        suffix = Path(path).suffix.lower() if path else ""
        return {".yaml": "yaml", ".yml": "yaml", ".bib": "bib"}.get(suffix, "md")

    def _highlight_aux(self, text: str):
        """yaml: `#` 주석만 칠한다(줄머리이거나 앞이 공백인 `#` 부터 줄 끝까지;
        따옴표 안의 `#` 는 제외). bib: `@종류{citekey,` 의 종류는 표지색, citekey 는 굵게."""
        self.setCurrentBlockState(0)
        if self._kind == "yaml":
            quote = ""
            for i, ch in enumerate(text):
                if quote:
                    if ch == quote:
                        quote = ""
                elif ch in "\"'":
                    quote = ch
                elif ch == "#" and (i == 0 or text[i - 1] in " \t"):
                    self.setFormat(i, len(text) - i, self.f_comment)
                    break
            return
        m = BIB_LINE_ENTRY_RE.match(text)
        if m:
            self.setFormat(m.start(1) - 1, len(m.group(1)) + 1, self.f_marker)
            self.setFormat(m.start(2), len(m.group(2)), self.f_bib_key)

    def set_item_gap(self, scale: float, bullets: bool = False, force: bool = False):
        """항목 사이 간격(표시 전용). scale 은 간격 공백 글꼴의 본문 대비 배율
        (1.0 이하면 끔). bullets 가 참이면 `- `/`1. ` 목록에도 적용한다."""
        scale = float(scale) if scale and scale > 1.0 else 0.0
        changed = (scale != self._gap_scale or bool(bullets) != self._gap_bullets)
        self._gap_scale, self._gap_bullets = scale, bool(bullets)
        self._gap_fmt = None          # 글꼴이 바뀌었을 수 있으니 서식을 새로 만든다
        if changed or (force and scale):
            self.rehighlight()

    def _gap_format(self):
        """큰 공백 한 글자에 줄 서식. 공백이 넓어진 만큼 음수 자간으로 되돌려
        뒤따르는 글이 밀리지 않게 한다."""
        if self._gap_fmt is None:
            font = QFont(self.document().defaultFont())
            base = font.pointSizeF()
            if base <= 0:
                base = 12.0
            font.setPointSizeF(base)
            w0 = QFontMetricsF(font).horizontalAdvance(" ")
            big = QFont(font)
            big.setPointSizeF(base * self._gap_scale)
            w1 = QFontMetricsF(big).horizontalAdvance(" ")
            cf = QTextCharFormat()
            cf.setFontPointSize(base * self._gap_scale)
            cf.setFontLetterSpacingType(QFont.AbsoluteSpacing)
            cf.setFontLetterSpacing(-(w1 - w0))
            self._gap_fmt = cf
        return self._gap_fmt

    def _is_gap_item(self, text: str) -> bool:
        if DESC_BRACE_RE.match(text) or DESC_RE.match(text):
            return True
        return self._gap_bullets and bool(UL_RE.match(text) or OL_RE.match(text))

    def _paint_item_gap(self, text: str, idx: int):
        """text[idx] 가 공백이면 그 한 글자를 키운다(앞 줄도 항목일 때만)."""
        if getattr(self, "_prev_item", False) and 0 <= idx < len(text) and text[idx] in " \t":
            self.setFormat(idx, 1, self._gap_format())

    def set_theme(self, theme: Theme):
        self._theme = theme
        self._build_formats()
        self.rehighlight()

    # -- 포맷 ---------------------------------------------------------------

    def _build_formats(self):
        t = self._theme

        def fmt(color=None, *, bold=False, italic=False, bg=None,
                size=None, mono=False):
            f = QTextCharFormat()
            if color:
                f.setForeground(QColor(color))
            if bg:
                f.setBackground(QColor(bg))
            if bold:
                f.setFontWeight(QFont.Bold)
            if italic:
                f.setFontItalic(True)
            if size:
                f.setProperty(QTextFormat.FontSizeAdjustment, size)
            return f

        self.f_marker = fmt(t.marker)
        self.f_heading = [
            fmt(t.heading, bold=True, size=3),
            fmt(t.heading, bold=True, size=2),
            fmt(t.heading, bold=True, size=1),
            fmt(t.heading, bold=True),
            fmt(t.heading, bold=True),
            fmt(t.heading, bold=True),
        ]
        self.f_heading_attr = fmt(t.marker, italic=True)
        self.f_env_name = fmt(t.env_name, bold=True)
        self.f_env_attr = fmt(t.env_name)
        self.f_frame = fmt(t.env_name, italic=True)
        self.f_code = fmt(t.code_fg, bg=t.code_bg)
        self.f_code_inline = fmt(t.code_fg, bg=t.code_bg)
        self.f_fence_info = fmt(t.marker, italic=True)
        self.f_showexam = fmt(t.env_name, bold=True)
        self.f_math = fmt(t.math)
        self.f_link_text = fmt(t.link)
        #: 인터넷 주소(링크·참조 링크·맨 주소) — 그림 문법과 구별되게 밑줄을 친다.
        self.f_url = fmt(t.link)
        self.f_url.setFontUnderline(True)
        self.f_link_url = fmt(t.link, italic=True)
        self.f_include = fmt(t.include, bold=True)
        self.f_comment = fmt(t.comment, italic=True)
        self.f_bib_key = fmt(t.heading, bold=True)
        self.f_frontmatter = fmt(t.frontmatter, bg=t.frontmatter_bg)
        self.f_frontmatter_key = fmt(t.frontmatter, bold=True, bg=t.frontmatter_bg)
        #: 인용문을 이탤릭으로 칠하면 그 안의 *강조*가 구별되지 않는다.
        #: 여는 `>` 를 흐리게 하는 것만으로 인용은 충분히 드러난다.
        self.f_quote = fmt(t.fg)
        self.f_label = fmt(t.marker, italic=True)
        self.f_footnote = fmt(t.link, italic=True)
        self.f_index = fmt(t.env_name)
        self.f_bold = fmt(bold=True)
        self.f_italic = fmt(italic=True)
        self.f_bold_italic = fmt(bold=True, italic=True)
        self.f_strike = QTextCharFormat()
        self.f_strike.setFontStrikeOut(True)
        self.f_strike.setForeground(QColor(t.comment))
        # ^^방점^^ — 전통 한국어 편집물의 방점. 점선 밑줄로 흉내 낸다.
        self.f_dotemph = QTextCharFormat()
        self.f_dotemph.setFontUnderline(True)
        self.f_dotemph.setUnderlineStyle(QTextCharFormat.DotLine)
        self.f_dotemph.setUnderlineColor(QColor(t.env_name))
        self.f_warn = fmt(t.warn, italic=True)
        self.f_hr = fmt(t.marker, bold=True)

    # -- 상태 인코딩 --------------------------------------------------------

    @staticmethod
    def _decode(state: int):
        if state < 0:
            state = 0
        return {
            "span": (state >> SPAN_SHIFT) & SPAN_MASK,
            "env": (state >> ENV_SHIFT) & ENV_MASK,
            "frame": (state >> FRAME_SHIFT) & FRAME_MASK,
            "fence": (state >> FENCE_SHIFT) & FENCE_MASK,
            "sexam": bool(state & SEXAM_BIT),
        }

    @staticmethod
    def _encode(s) -> int:
        v = SENTINEL
        v |= (s["span"] & SPAN_MASK) << SPAN_SHIFT
        v |= (min(s["env"], ENV_MASK)) << ENV_SHIFT
        v |= (min(s["frame"], FRAME_MASK)) << FRAME_SHIFT
        v |= (min(s["fence"], FENCE_MASK)) << FENCE_SHIFT
        if s["sexam"]:
            v |= SEXAM_BIT
        return v

    # -- 본체 ---------------------------------------------------------------

    def highlightBlock(self, text: str):
        if self._kind != "md":
            self._highlight_aux(text)
            return
        prev = self.previousBlockState()
        s = self._decode(prev)
        first_block = self.currentBlock().blockNumber() == 0

        pos = 0

        # (a) 열려 있는 스팬 닫기 -------------------------------------------
        if s["span"] == SPAN_FRONTMATTER:
            self._paint_frontmatter(text)
            if FRONTMATTER_CLOSE_RE.match(text):
                s["span"] = SPAN_NONE
            self.setCurrentBlockState(self._encode(s))
            return

        if s["span"] == SPAN_FENCE:
            m = FENCE_CLOSE_RE.match(text)
            if m and len(m.group(1)) >= s["fence"] + 3:
                self.setFormat(0, len(text), self.f_marker)
                s["span"] = SPAN_NONE
                s["fence"] = 0
                s["sexam"] = False
            else:
                self.setFormat(0, len(text), self.f_code)
            self.setCurrentBlockState(self._encode(s))
            return

        if s["span"] in (SPAN_DISPLAY_MATH, SPAN_MATH_ENV,
                         SPAN_TABLE_ENV, SPAN_COMMENT):
            end = self._find_span_end(text, s["span"])
            if end is None:
                self.setFormat(0, len(text), self._span_format(s["span"]))
                self.setCurrentBlockState(self._encode(s))
                return
            self.setFormat(0, end, self._span_format(s["span"]))
            s["span"] = SPAN_NONE
            pos = end

        # (b) 줄 전체가 하나의 구조인 것들 -----------------------------------
        if pos == 0:
            if first_block and FRONTMATTER_OPEN_RE.match(text):
                self.setFormat(0, len(text), self.f_marker)
                s["span"] = SPAN_FRONTMATTER
                self.setCurrentBlockState(self._encode(s))
                return

            # 펜스는 여는 표지와 닫는 표지가 같은 모양이라, 줄만 봐서는
            # 구분되지 않는다. 다만 여기까지 왔다는 건 열려 있는 펜스가
            # 없다는 뜻이므로(있었다면 위에서 이미 return 했다) 이 줄은
            # 반드시 여는 쪽이다. ```` 처럼 정보 문자열이 없어도 그렇다.
            m = FENCE_OPEN_LOOSE_RE.match(text)
            if m:
                info = m.group(2).strip()
                self.setFormat(0, len(m.group(1)) + m.start(1), self.f_marker)
                if info:
                    is_sexam = info.split()[0] == "showexam"
                    self.setFormat(m.start(2), len(m.group(2)),
                                   self.f_showexam if is_sexam else self.f_fence_info)
                    s["sexam"] = is_sexam
                s["span"] = SPAN_FENCE
                s["fence"] = len(m.group(1)) - 3
                self.setCurrentBlockState(self._encode(s))
                return

            if self._paint_block_level(text, s):
                self.setCurrentBlockState(self._encode(s))
                return

        # (c) 인라인 -----------------------------------------------------------
        # 간격은 "앞 줄도 항목인" 항목에만 준다(목록의 첫 항목 제외). 앞 줄의
        # 항목 여부는 블록 상태 비트로 건네받으므로, 앞 줄이 바뀌면 이 줄도 자동으로 다시 칠해진다.
        self._prev_item = prev >= 0 and bool(prev & ITEM_BIT)
        self._paint_inline(text, pos, s)
        st = self._encode(s)
        if self._gap_scale and s["span"] == SPAN_NONE and self._is_gap_item(text):
            st |= ITEM_BIT
        self.setCurrentBlockState(st)

    # -- (b) 줄 단위 구조 ---------------------------------------------------

    def _paint_block_level(self, text: str, s) -> bool:
        """줄 전체를 소비하는 구조면 칠하고 True 를 돌려준다."""

        # ::: 환경 — 깊이를 세는 곳
        m = ENV_OPEN_RE.match(text)
        if m:
            # 여는 `:::{` 를 통째로 표지색으로. `:::` 만 칠하고 `{` 를 빼면
            # 닫는 `}` 와 색이 어긋나 짝이 맞지 않아 보인다.
            self.setFormat(0, m.start(1), self.f_marker)
            self.setFormat(m.start(1), len(m.group(1)), self.f_env_name)
            if m.group(2):
                self.setFormat(m.start(2), len(m.group(2)), self.f_env_attr)
            brace = text.rfind("}")
            if brace >= 0:
                self.setFormat(brace, 1, self.f_marker)
            s["env"] += 1
            return True

        if ENV_CLOSE_RE.match(text):
            self.setFormat(0, len(text), self.f_marker)
            if s["env"] > 0:
                s["env"] -= 1
            else:
                # 열린 적 없는 `:::` — 린트가 잡을 것이지만 눈으로도 보이게.
                self.setFormat(0, len(text), self.f_warn)
            return True

        if LINT_ENV_LOOSE_RE.match(text) or LINT_FRAME_LOOSE_RE.match(text):
            # `::: {table}` 처럼 공백이 끼면 환경으로 인식되지 않는다.
            self.setFormat(0, len(text), self.f_warn)
            return True

        m = FRAME_OPEN_RE.match(text)
        if m:
            self.setFormat(0, len(text), self.f_frame)
            s["frame"] += 1
            return True

        if FRAME_CLOSE_RE.match(text):
            self.setFormat(0, len(text), self.f_frame)
            if s["frame"] > 0:
                s["frame"] -= 1
            return True

        m = HEADING_RE.match(text)
        if m:
            level = len(m.group(1))
            self.setFormat(0, level, self.f_marker)
            self.setFormat(m.start(2), len(m.group(2)), self.f_heading[level - 1])
            if m.group(3) is not None:
                self.setFormat(m.start(3) - 1, len(m.group(3)) + 2, self.f_heading_attr)
            return True

        if LINECOMMENT_RE.match(text):
            self.setFormat(0, len(text), self.f_comment)
            return True

        if HR_STAR_RE.match(text) or HR_DASH_RE.match(text):
            self.setFormat(0, len(text), self.f_hr)
            return True

        if TABLE_SEP_RE.match(text) and "-" in text:
            self.setFormat(0, len(text), self.f_marker)
            return True

        # grid 표의 가로 테두리 `+----+====+` 줄 전체를 표지색으로.
        if GRID_BORDER_RE.match(text):
            self.setFormat(0, len(text), self.f_marker)
            return True

        # 파이프 표 바로 아래의 옵션 줄 `{env=long,caption="…"}` — 헤딩 속성과 같은 모양으로 칠한다.
        if TABLE_OPT_RE.match(text):
            prev = self.currentBlock().previous()
            if prev.isValid() and (_is_table_row_text(prev.text())
                                   or GRID_BORDER_RE.match(prev.text())):
                self.setFormat(0, len(text), self.f_heading_attr)
                return True

        return False

    def _dim_table_pipes(self, text: str, protected):
        """표 행의 `|` 만 흐리게 한다. 셀 내용이 먼저 읽히도록."""
        if not text.lstrip().startswith("|"):
            return
        for i, ch in enumerate(text):
            if ch == "|" and not protected[i] and (i == 0 or text[i - 1] != "\\"):
                self.setFormat(i, 1, self.f_marker)
        # grid 표의 병합 셀 줄(`|    +------+------+`)에 섞인 가로 테두리 조각도 흐리게.
        for m in GRID_PART_RE.finditer(text):
            self.setFormat(m.start(), m.end() - m.start(), self.f_marker)

    # -- (c) 인라인 ---------------------------------------------------------

    def _paint_inline(self, text: str, pos: int, s):
        """pos 부터 줄 끝까지 인라인 규칙을 얹는다."""
        n = len(text)
        if pos >= n:
            return

        # 줄머리 표지(인용/목록/설명목록/각주정의)는 흐리게, 내용은 본문색으로.
        opt_start = -1          # 목록 옵션 블록 `{!…}` 의 시작 위치(없으면 -1)
        if pos == 0:
            m = QUOTE_RE.match(text)
            if m:
                self.setFormat(0, m.start(1), self.f_marker)
                self.setFormat(m.start(1), n - m.start(1), self.f_quote)
            else:
                for rx in (UL_RE, OL_RE):
                    mm = rx.match(text)
                    if mm:
                        self.setFormat(len(mm.group(1)),
                                       mm.start(len(mm.groups())) - len(mm.group(1)),
                                       self.f_marker)
                        if self._gap_scale and self._gap_bullets:
                            self._paint_item_gap(text, mm.start(len(mm.groups())) - 1)
                        opt_start = mm.start(len(mm.groups()))
                        break
                else:
                    mm = DESC_BRACE_RE.match(text) or DESC_RE.match(text)
                    if mm:
                        self.setFormat(mm.start(2), len(mm.group(2)), self.f_bold)
                        if self._gap_scale:
                            k = text.find("::", mm.end(2))
                            if k > 0:
                                self._paint_item_gap(text, k - 1)
                        if mm.group(3) is not None:
                            opt_start = mm.start(3)
                    else:
                        mm = FOOTNOTE_DEF_RE.match(text)
                        if mm:
                            self.setFormat(0, mm.start(2), self.f_footnote)

        # 보호 구간: 인라인 코드 안쪽은 다른 규칙을 적용하지 않는다.
        protected = bytearray(n)

        for m in INLINE_CODE_RE.finditer(text, pos):
            self.setFormat(m.start(), m.end() - m.start(), self.f_code_inline)
            for i in range(m.start(), m.end()):
                protected[i] = 1

        # 여러 줄로 이어질 수 있는 스팬의 "여는 쪽"을 찾는다. 줄 안에서
        # 닫히면 그대로 칠하고, 안 닫히면 상태에 실어 다음 줄로 넘긴다.
        for rx, kind in ((COMMENT_OPEN_RE, SPAN_COMMENT),
                         (MATH_ENV_OPEN_RE, SPAN_MATH_ENV),
                         (TABLE_ENV_OPEN_RE, SPAN_TABLE_ENV),
                         (DISPLAY_MATH_OPEN_RE, SPAN_DISPLAY_MATH)):
            m = rx.search(text, pos)
            if not m or protected[m.start()]:
                continue
            end = self._find_span_end(text, kind, m.end(), opener=m)
            if end is None:
                self.setFormat(m.start(), n - m.start(), self._span_format(kind))
                for i in range(m.start(), n):
                    protected[i] = 1
                s["span"] = kind
                break
            self.setFormat(m.start(), end - m.start(), self._span_format(kind))
            for i in range(m.start(), end):
                protected[i] = 1

        #: 강조 규칙이 들여다보면 안 되는 것들. ndhmd4tex 도 수식·코드 등을
        #: 먼저 자리표로 빼내어 인라인 규칙을 통째로 우회시킨다. 예컨대
        #: `$a*b*c$` 의 별표가 기울임으로 잡히면 안 된다.
        opaque = {INCLUDE_RE, INLINE_MATH_RE, INLINE_LABEL_RE, RAW_ATTR_RE}

        simple = (
            (INCLUDE_RE, self.f_include),
            (INLINE_MATH_RE, self.f_math),
            (FIGURE_RE, self.f_link_text),
            (FIGURE_REF_RE, self.f_link_text),
            (HL_INLINE_FOOTNOTE_RE, self.f_footnote),
            (HL_FOOTNOTE_REF_RE, self.f_footnote),
            (INDEX_RE, self.f_index),
            (INLINE_LABEL_RE, self.f_label),
            (RAW_ATTR_RE, self.f_label),
        )
        self._dim_table_pipes(text, protected)

        for rx, f in simple:
            for m in rx.finditer(text, pos):
                if any(protected[i] for i in range(m.start(), m.end())):
                    continue
                self.setFormat(m.start(), m.end() - m.start(), f)
                if rx in opaque:
                    for i in range(m.start(), m.end()):
                        protected[i] = 1
                if rx is HL_INLINE_FOOTNOTE_RE or rx is HL_FOOTNOTE_REF_RE:
                    tag = NOTE_TAG_RE.match(text, m.end())
                    if tag and not tag.group(1).lstrip().startswith("="):
                        # 각주 꼬리표 — 본문이 아니라 각주 종류·번호를 고르는 설정이라 흐린 이탤릭으로.
                        self.setFormat(tag.start(), tag.end() - tag.start(), self.f_heading_attr)
                        for i in range(tag.start(), tag.end()):
                            protected[i] = 1

        # 인용·참조 뒤의 `{rawopt="[see][p.~23]"}` — 그대로 \cite[…]{키} 의 선택 인자로
        # 나가는 값이라 본문이 아니다. 안쪽 `[a][b]`·`*`·URL 이 다른 규칙에 걸리지 않게
        # 먼저 막아 두고, 칠은 강조 뒤에 `{!…}` 처럼 흐린 이탤릭으로 한다.
        rawopts = []
        for m in CITE_RAWOPT_RE.finditer(text, pos):
            if any(protected[i] for i in range(m.start(1), m.end(1))):
                continue
            rawopts.append((m.start(1), m.end(1)))
            for i in range(m.start(1), m.end(1)):
                protected[i] = 1

        self._paint_urls(text, pos, protected)

        # 강조는 맨 나중에. 위 규칙들은 setFormat 으로 구간을 갈아치우지만
        # 강조는 _merge_format 으로 덧씌우므로, 순서를 뒤집으면 지워진다.
        self._paint_emphasis(text, pos, protected)

        for st, en in rawopts:
            self.setFormat(st, en - st, self.f_heading_attr)

        # 목록 옵션 블록 `{!…}` — ndhmd4tex 가 마커(설명 목록은 `::`) 바로 뒤에서 떼어
        # \begin{itemize}[…] 등에 쓰는 설정 구문이다. 본문이 아니므로 제목 줄 끝의
        # `{#…}` 처럼 흐린 이탤릭으로, 안쪽의 다른 칠을 모두 덮어 칠한다.
        if opt_start >= 0 and text.startswith("{!", opt_start):
            depth = 0
            for i in range(opt_start, n):
                ch = text[i]
                if ch == "{":
                    depth += 1
                elif ch == "}":
                    depth -= 1
                    if depth == 0:
                        self.setFormat(opt_start, i + 1 - opt_start, self.f_heading_attr)
                        break

    def _paint_emphasis(self, text: str, pos: int, protected):
        """강조 규칙을 ndhmd4tex 의 순서대로, 같은 방식으로 얹는다.

        변환기는 규칙표를 순서대로 re.sub 한다. 즉 `**굵게**` 가 먼저
        `\\textbf{굵게}` 로 바뀌므로 그 다음 italic 규칙은 그 `**` 를 다시
        볼 수 없다. 반면 **내용은 그대로 남으므로** 안쪽의 `*기울임*` 은
        여전히 매치된다.

        그래서 여기서도 매치 전체가 아니라 **델리미터만** 소비 처리한다.
        전체를 소비하면 중첩 강조가 죽고, 아무것도 소비하지 않으면
        `**굵게**` 의 별표들이 italic 규칙에 걸려 엉뚱하게 잘린다.
        """
        consumed = bytearray(len(text))
        for rx, fmt_name, marker in EMPHASIS_RULES:
            fmt = getattr(self, fmt_name)
            i = pos
            while True:
                m = rx.search(text, i)
                if m is None:
                    break
                start, end = m.start(), m.end()
                ok = (not any(protected[k] for k in range(start, end))
                      and not any(consumed[k] for k in range(start, start + marker))
                      and not any(consumed[k] for k in range(end - marker, end)))
                if not ok:
                    # 거절한 매치에서 이터레이터를 끝까지 밀면 안 된다.
                    # `**굵은 *기울임* 포함**` 에서 italic 의 첫 매치는
                    # `**굵은 *` 인데, 이걸 버리면서 뒤로 건너뛰면 진짜
                    # 짝인 5번째 `*` 를 영영 못 본다. 한 칸만 전진한다.
                    i = start + 1
                    continue
                self._merge_format(start, end - start, fmt)
                for k in range(start, start + marker):
                    consumed[k] = 1
                for k in range(end - marker, end):
                    consumed[k] = 1
                i = end

    def _paint_urls(self, text: str, pos: int, protected):
        """[글자](주소) · [글자][표지] · 맨 주소에 밑줄과 링크 색을 준다.
        그림(![..](..), ![..][..])과 그림 정의 줄은 그대로 둔다."""
        occupied = [(m.start(), m.end()) for rx in (FIGURE_RE, FIGURE_REF_RE)
                    for m in rx.finditer(text)]

        def free(a, b):
            return not any(protected[i] for i in range(a, b)) and \
                not any(x <= a < y for x, y in occupied)

        for rx in (LINK_RE, REFLINK_RE):
            for m in rx.finditer(text, pos):
                if m.start() > 0 and text[m.start() - 1] == "!":
                    continue
                if not free(m.start(), m.end()):
                    continue
                # 명칭([글자])은 색만, 밑줄은 주소 쪽((주소) / [표지])에만.
                a = m.start(2) - 1
                self.setFormat(m.start(), a - m.start(), self.f_link_text)
                # [글자](#라벨) 은 \hyperref — 인터넷 주소가 아니라 \ref 류의
                # 상호참조이므로 밑줄 없이 기울임(각주·참조와 같은 계열)으로 칠한다.
                is_xref = rx is LINK_RE and m.group(2).startswith("#")
                self.setFormat(a, m.end() - a,
                               self.f_link_url if is_xref else self.f_url)
                occupied.append((m.start(), m.end()))
        if FIGURE_DEF_RE.match(text):
            return                       # 정의 줄은 그림일 수도 — 칠하지 않는다
        for m in BARE_URL_RE.finditer(text, pos):
            u = trim_url(m.group(0))
            if u and free(m.start(), m.start() + len(u)):
                self.setFormat(m.start(), len(u), self.f_url)

    def _merge_format(self, start: int, count: int, extra: QTextCharFormat):
        """기존 포맷 위에 덧씌운다.

        setFormat 은 구간의 포맷을 통째로 갈아치우므로, 그냥 쓰면
        `**굵은 *기울임* 포함**` 에서 안쪽이 굵기를 잃는다.
        """
        merged = QTextCharFormat(self.format(start))
        merged.merge(extra)
        self.setFormat(start, count, merged)

    # -- 스팬 보조 ----------------------------------------------------------

    def _span_format(self, kind: int) -> QTextCharFormat:
        return {
            SPAN_DISPLAY_MATH: self.f_math,
            SPAN_MATH_ENV: self.f_math,
            SPAN_TABLE_ENV: self.f_math,
            SPAN_COMMENT: self.f_comment,
        }[kind]

    def _find_span_end(self, text: str, kind: int, start: int = 0, opener=None):
        """줄 안에서 스팬이 닫히는 위치(끝 인덱스)를 찾는다. 없으면 None."""
        if kind == SPAN_COMMENT:
            i = text.find("-->", start)
            return i + 3 if i >= 0 else None
        if kind == SPAN_DISPLAY_MATH:
            for closer in ("$$", "\\]"):
                i = text.find(closer, start)
                if i >= 0:
                    return i + len(closer)
            return None
        if kind in (SPAN_MATH_ENV, SPAN_TABLE_ENV):
            i = text.find("\\end{", start)
            if i < 0:
                return None
            j = text.find("}", i)
            return j + 1 if j >= 0 else None
        return None

    def _paint_frontmatter(self, text: str):
        self.setFormat(0, len(text), self.f_frontmatter)
        if FRONTMATTER_CLOSE_RE.match(text):
            self.setFormat(0, len(text), self.f_marker)
            return
        m = re.match(r"^([A-Za-z_][\w+-]*)\s*:", text)
        if m:
            self.setFormat(0, m.end(), self.f_frontmatter_key)


# ===========================================================================
# 5. 행번호 게이터
# ===========================================================================

class LineNumberArea(QWidget):
    def __init__(self, editor: "Editor"):
        super().__init__(editor)
        self._editor = editor

    def sizeHint(self) -> QSize:
        return QSize(self._editor.gutter_width(), 0)

    def paintEvent(self, event):
        self._editor.paint_gutter(event)

    def mousePressEvent(self, event):
        """첫 줄 게이터를 누르면 프론트매터를 접거나 편다."""
        block = self._editor.firstVisibleBlock()
        top = self._editor.blockBoundingGeometry(block).translated(
            self._editor.contentOffset()).top()
        y = event.position().y()
        while block.isValid():
            height = self._editor.blockBoundingRect(block).height()
            if top <= y < top + height:
                if block.blockNumber() == 0 and self._editor.frontmatter_range():
                    self._editor.toggle_frontmatter_fold()
                elif self._editor.fence_is_open_line(block):
                    self._editor.toggle_fence(block)
                return
            block = block.next()
            top += height
        super().mousePressEvent(event)


# ===========================================================================
# 6. 편집창
# ===========================================================================

class Editor(QPlainTextEdit):
    """긴 글을 오래 보는 화면.

    타이포그래피에 예산을 몰아준다. 행간 1.6, 단 너비 상한, 좌우 대칭 여백,
    두꺼운 커서, 절제된 현재 줄 표시. 화려한 효과보다 이쪽이 체감 품질을
    훨씬 많이 올린다.
    """

    #: 한 줄의 목표 글자 수. 이보다 넓어지면 여백으로 흡수한다.
    COLUMN_TARGET = 82         # 평소(창 모드) 목표 자수 — 상한이 있어 아주
                               # 넓은 창에서는 완전히 지켜지지 않는다.
    MAX_MARGIN = 96
    GUIDE_STEP = 9        # 중첩 한 단계당 가이드 간격(px)
    GUIDE_GAP = 11        # 본문 왼쪽 끝에서 가장 안쪽 가이드까지
    #: 가장 바깥 가이드까지 들어갈 자리를 본문 왼쪽에 반드시 남긴다.
    MIN_MARGIN = GUIDE_GAP + (MAX_GUIDE_DEPTH - 1) * GUIDE_STEP + 8
    #: 접힌 :::{thebibliography} 가 버튼처럼 보일 때 그 안에 쓸 글자.
    BIB_BUTTON_LABEL = "\U0001F4DA 참고문헌"

    def __init__(self, theme: Theme):
        super().__init__()
        self._theme = theme

        #: front matter 를 편집창에서 숨기게 되면 이 값이 채워진다.
        #: sync 배선은 전부 file_line()/goto_file_line() 을 거치므로,
        #: 여기만 바뀌면 나머지는 손대지 않아도 된다.
        self.fm_offset = 0

        self.setLineWrapMode(QPlainTextEdit.WidgetWidth)
        self.setCursorWidth(2)
        self.setFrameStyle(0)
        self.setAttribute(Qt.WidgetAttribute.WA_InputMethodEnabled, True)
        #: 버튼을 안 누르고 있어도 mouseMoveEvent 가 오게 한다 —
        #: Ctrl+호버로 링크 위에서 커서 모양을 바꿔 주는 데 필요하다.
        self.viewport().setMouseTracking(True)

        #: 한글 IME 조합 중인 글자 수. Qt 의 내장 조합 렌더링에 기대지
        #: 않고 진짜 텍스트로 임시 삽입해 두는 방식이라 필요하다 —
        #: inputMethodEvent() 참고.
        self._preedit_length = 0

        self._apply_font()
        self.apply_tab_spaces(4)
        #: Tab 키를 누르면 탭 문자 대신 스페이스를 넣을지. 기본 켜짐 —
        #: YAML 프론트매터에 탭 문자가 섞이면 파서가 바로 오류를 낸다.
        self.tab_to_spaces_enabled = True
        #: 스트레이트 따옴표(" ')를 어떤 짝으로 바꿔 넣을지 — "off"면
        #: 안 건드린다.
        self.smart_quotes_style = "off"
        #: 마침표·쉼표를 고리점(。)·모점(、)으로 바꿔 넣을지.
        self.smart_punctuation = False

        self._gutter = LineNumberArea(self)
        self.blockCountChanged.connect(self._update_gutter_width)
        self.updateRequest.connect(self._on_update_request)
        self.cursorPositionChanged.connect(self._highlight_current_line)
        self.cursorPositionChanged.connect(self._nudge_cursor_out)
        self.cursorPositionChanged.connect(self._unfold_if_cursor_hidden)
        self.textChanged.connect(self._schedule_fence_check)

        self._matches = []          # 검색어에 걸린 커서들
        self._scope_range = None    # 찾기 범위 "선택 범위"의 (시작, 끝) — 은은하게 칠한다
        self._active_match = -1

        #: 전체화면 여부와, 그때 적용할 목표 자수. 전체화면은 모니터
        #: 폭이 그대로 편집 폭이 되기 쉬워서 한 줄이 지나치게 길어지는데,
        #: 창 모드의 MAX_MARGIN 상한을 그대로 쓰면 그 상한에 막혀 실제로는
        #: 제한이 안 걸린다. 그래서 전체화면일 때는 상한 없이 정확히
        #: fullscreen_column 자수에 맞춰 여백을 계산한다.
        self._is_fullscreen = False
        self.fullscreen_column = 120

        #: 프론트매터 접기 상태. 여는 `---` 줄만 남기고 나머지를 숨긴다.
        #: 텍스트를 문서에서 빼는 게 아니라 "그리지 않는" 것이므로 블록
        #: 번호가 그대로 유지된다 — 그래서 file_line() 이 접힘 여부와
        #: 무관하게 옳고, fm_offset 보정도 필요 없다.
        self._fm_folded = False
        self._fm_last = -1          # 닫는 `---` 의 블록 번호
        #: :::{thebibliography} 블록 — 문서에 하나 있다고 가정한다(책 한
        #: 권에 참고문헌 하나가 보통이다). 여는 줄만 남기고 접어서
        #: [참고문헌] 버튼처럼 그린다. 여는/닫는 줄 번호는 저장해 두지
        #: 않는다 — 앞에 텍스트가 늘거나 줄면 번호가 밀려서 엉뚱한 줄을
        #: 가리키게 된다. _bib_marker_rect() 가 매번 화면에 보이는
        #: 것만 다시 찾는다.
        self._bib_folded = False
        #: 코드 펜스(```) 접기 — 여러 개를 따로 접을 수 있어 개별 상태는 저장하지 않고,
        #: 블록의 보임/숨김과 "여는 줄의 다음 블록이 숨겨져 있는가"로 그때그때 알아낸다.
        self._fence_folded_any = False
        self._fence_check_timer = QTimer(self)
        self._fence_check_timer.setSingleShot(True)
        self._fence_check_timer.setInterval(250)
        self._fence_check_timer.timeout.connect(self._validate_fence_folds)
        #: 편집 메뉴의 다섯 변형(목록·펜스·환경·풀기)을 우클릭 메뉴에도
        #: 똑같이 노출하기 위한 창 참조. MainWindow 가 생성 직후 채워 준다.
        #: None 이면(단독 사용·테스트) 표준 메뉴만 나온다.
        self._host = None

        # 하이라이터는 문서가 아니라 편집창 자신을 부모로 둔다. 문서를
        # 부모로 주면(QSyntaxHighlighter(document) 오버로드) 그 문서가
        # 하이라이터의 소유자가 되어, 나중에 다른 파일로 옮기며 문서를
        # 통째로 갈아 끼울 때 옛 문서가 정리되면서 하이라이터까지 같이
        # 죽는다. setDocument() 로 따로 붙이면 문서를 몇 번을 바꿔도
        # 하이라이터 자신은 편집창과 함께 계속 살아있다.
        self.highlighter = NdhmdHighlighter(self, theme)
        self.highlighter.setDocument(self.document())
        self.apply_theme(theme)
        self._update_gutter_width()

    # -- 폰트 ---------------------------------------------------------------

    #: 한글이 라틴 문자의 정확히 2배폭인 고정폭 폰트를 우선한다. 이게
    #: 아니면 표나 코드에서 열이 어긋나 보인다. 3개 OS 를 다 지원해야 하므로
    #: 있을 법한 것을 순서대로 훑고, 하나도 없으면 시스템 고정폭으로 떨어진다.
    FONT_CANDIDATES = [
        "D2Coding", "Sarasa Mono K", "Sarasa Term K",
        "NanumGothicCoding", "나눔고딕코딩",
        "JetBrains Mono", "IBM Plex Mono", "Cascadia Code",
        "Menlo", "Consolas", "DejaVu Sans Mono",
    ]

    def _apply_font(self, family: str = "", size: float = 12.5):
        """편집창 폰트를 건다.

        setFont() 는 지금 위젯 폰트와 값이 같으면 문서 쪽 동기화까지
        건너뛴다 — QPlainTextEdit.setFont() 가 내부적으로 "현재 문서의
        defaultFont 도 맞춰 준다"는 동작을 하는데, 이게 "값이 바뀌었을
        때만" 일어난다. 그런데 파일을 전환할 때마다 prefs 의 같은
        값으로 다시 이 메서드를 부르니(파일이 바뀌어도 설정은 그대로),
        위젯 입장에선 "안 바뀌었다"고 보고 건너뛴다 — 그 사이 setDocument()
        로 방금 새로 붙은 문서는 자기 나름의(보통 훨씬 작은) 기본 폰트를
        그대로 들고 있어서, 서식이 없는 일반 본문 줄이 그 문서의 기본
        폰트로 그려진다. 그래서 문서의 defaultFont() 는 위젯의 판단과
        무관하게 매번 직접 건다.
        """
        if family:
            font = QFont(family)
        else:
            families = set(QFontDatabase.families())
            chosen = next((f for f in self.FONT_CANDIDATES if f in families), None)
            font = QFont(chosen) if chosen else QFontDatabase.systemFont(
                QFontDatabase.FixedFont)
        font.setPointSizeF(size)
        font.setStyleStrategy(QFont.PreferAntialias)
        self.setFont(font)
        self.document().setDefaultFont(font)
        self.font_name = font.family()

    def apply_tab_spaces(self, spaces: int):
        self.tab_spaces_count = spaces
        width = QFontMetricsF(self.font()).horizontalAdvance(" ") * spaces
        self.setTabStopDistance(width)

    @contextmanager
    def _suppress_dirty(self):
        """포맷팅 전용 변경(여백 재계산, 행간 등)이 진짜 편집처럼 보이는
        걸 막는다.

        setDocumentMargin() 이나 블록 서식 병합처럼 글자 하나 안 건드리는
        조작도 Qt 내부적으로는 "다시 흘려 넣기"를 하면서 textChanged 뿐
        아니라 isModified() 와 contentsChange 까지 전부 진짜 편집과
        똑같이 쏜다 — 이 셋 중 뭘 봐도 구분이 안 된다. 그래서 신호
        자체를 막는 대신, MainWindow 의 _switching_document 플래그를
        빌려 "지금은 무시해도 된다"고 알려 둔다. _host 가 없는 독립
        실행(테스트 등)에서는 조용히 아무 일도 안 한다.
        """
        host = getattr(self, "_host", None)
        if host is not None:
            host._switching_document = True
        try:
            yield
        finally:
            if host is not None:
                host._switching_document = False

    # -- 테마 ---------------------------------------------------------------

    def apply_theme(self, theme: Theme):
        """편집창 배경·글자색을 스타일시트 *와* 팔레트 양쪽에 건다.

        스타일시트만 걸었던 이유는 따로 있다 — QPalette 만 쓰면 MainWindow
        가 나중에 자기 스타일시트를 다시 적용할 때(테마 전환은 창을 새로
        만드는 게 아니라 기존 창의 스타일시트를 갈아 끼우는 것이다) Qt 가
        스타일 재적용(polish) 과정에서 자식의 팔레트를 되돌리는 경우가
        있다. 위젯 자신에게 건 스타일시트는 조상의 재적용 순서와 무관하게
        확정적으로 적용되므로 그 문제는 해결됐다.

        그런데 스타일시트만 걸면 Windows 에서 한글 입력 중 미완성자(조합
        중인 글자)가 안 보이는 부작용이 있다. Windows 의 IME 조합 문자열
        렌더링이 스타일시트가 아니라 팔레트 쪽 값을 참조하는 것으로
        보인다 — macOS 는 조합 중 텍스트를 OS 차원에서 다르게 그려서 이
        영향을 덜 받는다. 그래서 팔레트도 같은 색으로 같이 걸어 둔다.
        둘 다 같은 값이라 시각적으로 충돌하지 않고, 어느 쪽을 보는
        코드든 옳은 색을 얻는다.
        """
        self._theme = theme

        pal = self.palette()
        pal.setColor(QPalette.Base, QColor(theme.bg))
        pal.setColor(QPalette.Text, QColor(theme.fg))
        # 텍스트 선택/IME 조합 렌더링이 참조하는 색이라 대비가 확실해야
        # 한다. marker(구조 표시용으로 일부러 채도를 낮춘 색)를 쓰면
        # 한글 입력 중 조합 문자가 거의 안 보일 만큼 흐려진다 — 이미
        # "눈에 띄어야 하는" 용도로 쓰는 match_active_bg 와 fg 로 바꾼다.
        pal.setColor(QPalette.Highlight, QColor(theme.match_active_bg))
        pal.setColor(QPalette.HighlightedText, QColor(theme.fg))
        self.setPalette(pal)

        self.setStyleSheet(f"""
            QPlainTextEdit {{
                background: {theme.bg}; color: {theme.fg}; border: none;
                selection-background-color: {theme.match_active_bg};
                selection-color: {theme.fg};
            }}
        """)
        self.highlighter.set_theme(theme)
        self._refresh_extra_selections()
        self._gutter.update()

    # -- 레이아웃 -----------------------------------------------------------

    def gutter_width(self) -> int:
        digits = max(3, len(str(max(1, self.blockCount()))))
        return 30 + QFontMetricsF(self.font()).horizontalAdvance("9") * digits

    @Slot()
    def _update_gutter_width(self):
        w = int(self.gutter_width())
        self.setViewportMargins(w, 0, 0, 0)
        self._relayout_text_column()

    def _relayout_text_column(self):
        """본문 단 너비를 목표 자수에 맞춰 좌우 여백으로 흡수한다.

        창 모드에서는 여백에 상한(MAX_MARGIN)을 두어, 창을 아주 넓게 늘려도
        여백이 화면을 우스꽝스럽게 잡아먹지 않게 한다 — 대신 아주 넓은
        창에서는 목표 자수가 정확히 지켜지지 않을 수 있다.

        전체화면에서는 그 상한이 오히려 문제다. 모니터 폭 전체가 편집
        폭이 되어 한 줄이 한없이 길어지는데, 정확히 이 상황을 막으려고
        전체화면 자수 제한을 두는 것이므로 여기서는 상한을 걸지 않는다.
        """
        fm = QFontMetricsF(self.font())
        ch = fm.horizontalAdvance("0")
        avail = self.viewport().width()
        if self._is_fullscreen:
            target = ch * self.fullscreen_column
            margin = max(self.MIN_MARGIN, (avail - target) / 2)
        else:
            target = ch * self.COLUMN_TARGET
            margin = (avail - target) / 2
            margin = max(self.MIN_MARGIN, min(self.MAX_MARGIN, margin))
        if abs(self.document().documentMargin() - margin) > 0.5:
            with self._suppress_dirty():
                self.document().setDocumentMargin(margin)

    def set_fullscreen(self, on: bool):
        if on != self._is_fullscreen:
            self._is_fullscreen = on
            self._relayout_text_column()

    def set_fullscreen_column(self, n: int):
        self.fullscreen_column = max(20, n)
        if self._is_fullscreen:
            self._relayout_text_column()

    def resizeEvent(self, event):
        super().resizeEvent(event)
        cr = self.contentsRect()
        self._gutter.setGeometry(
            QRect(cr.left(), cr.top(), int(self.gutter_width()), cr.height()))
        self._relayout_text_column()

    @Slot()
    def _on_update_request(self, rect, dy):
        if dy:
            self._gutter.scroll(0, dy)
        else:
            self._gutter.update(0, rect.y(), self._gutter.width(), rect.height())

    # -- 현재 줄 -------------------------------------------------------------

    @Slot()
    def _highlight_current_line(self):
        self._refresh_extra_selections()
        self._gutter.update()

    def set_search_matches(self, cursors, active: int = -1):
        """검색어에 걸린 구간 전체를 은은하게 칠한다.

        현재 줄 강조와 같은 ExtraSelection 목록을 쓰므로 한곳에서 합쳐야
        한다. 따로 setExtraSelections 를 부르면 서로를 지운다.
        """
        self._matches = list(cursors)
        self._active_match = active
        self._refresh_extra_selections()

    def clear_search_matches(self):
        self.set_search_matches([], -1)

    def set_scope_range(self, rng):
        """찾기 범위가 "선택 범위"일 때 그 구간을 옅게 칠한다. None 이면 지운다."""
        self._scope_range = rng
        self._refresh_extra_selections()

    def _refresh_extra_selections(self):
        sels = []

        line = QTextEdit.ExtraSelection()
        line.format.setBackground(QColor(self._theme.current_line))
        line.format.setProperty(QTextFormat.FullWidthSelection, True)
        line.cursor = self.textCursor()
        line.cursor.clearSelection()
        sels.append(line)

        if self._scope_range:
            lo, hi = self._scope_range
            rc = QTextCursor(self.document())
            rc.setPosition(max(0, min(lo, self.document().characterCount() - 1)))
            rc.setPosition(max(0, min(hi, self.document().characterCount() - 1)), QTextCursor.KeepAnchor)
            rs = QTextEdit.ExtraSelection()
            tint = QColor(self._theme.fg)
            tint.setAlpha(22)
            rs.format.setBackground(tint)
            rs.cursor = rc
            sels.append(rs)

        for i, cur in enumerate(self._matches):
            sel = QTextEdit.ExtraSelection()
            sel.format.setBackground(QColor(
                self._theme.match_active_bg if i == self._active_match
                else self._theme.match_bg))
            sel.cursor = cur
            sels.append(sel)

        self.setExtraSelections(sels)

    # -- 그리기 --------------------------------------------------------------

    def paintEvent(self, event):
        """본문을 그린 뒤 `:::` 중첩 가이드를 얹는다.

        배경 틴트 대신 세로선을 쓰는 이유는 두 가지다. QTextCharFormat 의
        배경은 글자가 있는 만큼만 칠해져서 오른쪽 끝이 들쭉날쭉해지고,
        중첩이 깊어져도 세로선은 화면을 탁하게 만들지 않는다.
        """
        super().paintEvent(event)

        painter = QPainter(self.viewport())
        margin = self.document().documentMargin()
        block = self.firstVisibleBlock()
        top = self.blockBoundingGeometry(block).translated(
            self.contentOffset()).top()

        while block.isValid() and top <= event.rect().bottom():
            height = self.blockBoundingRect(block).height()
            if block.isVisible() and top + height >= event.rect().top():
                # 여는 줄과 닫는 줄에도 선이 이어지도록, 그 줄 전후의
                # 깊이 중 큰 쪽을 쓴다.
                prev_state = block.previous().userState() if block.previous().isValid() else 0
                depth = max(env_depth(prev_state), env_depth(block.userState()))
                for d in range(min(depth, MAX_GUIDE_DEPTH)):
                    x = margin - self.GUIDE_GAP - (MAX_GUIDE_DEPTH - 1 - d) * self.GUIDE_STEP
                    if x < 2:
                        continue
                    painter.fillRect(
                        QRect(int(x), int(top), 2, int(height) + 1),
                        QColor(self._theme.guides[d % len(self._theme.guides)]))
                if self._fence_folded_any and self.fence_is_folded(block):
                    close = self.fence_close_block(block)
                    n = close.blockNumber() - block.blockNumber() - 1
                    if self._span_of(block.userState()) == SPAN_FENCE:
                        info = FENCE_OPEN_LOOSE_RE.match(block.text())
                        kind = (info.group(2).strip() if info else "") or "코드"
                    else:
                        info = ENV_OPEN_RE.match(block.text())
                        kind = info.group(1) if info else "환경"
                    fmx = QFontMetricsF(self.font())
                    x = margin + fmx.horizontalAdvance(block.text()) + 12
                    painter.setPen(QColor(self._theme.frontmatter))
                    f = QFont(self.font())
                    f.setItalic(True)
                    painter.setFont(f)
                    painter.drawText(
                        QRect(int(x), int(top), max(0, int(self.viewport().width() - x - 8)), int(height)),
                        Qt.AlignLeft | Qt.AlignVCenter, f"▸ {kind} · {n}줄 접힘")
            block = block.next()
            top += height

        geo = self._fold_marker_rect()
        if geo is not None:
            fm = QFontMetricsF(self.font())
            x = self.document().documentMargin() + fm.horizontalAdvance("---")
            painter.setPen(QColor(self._theme.frontmatter))
            f = QFont(self.font())
            f.setItalic(True)
            painter.setFont(f)
            painter.drawText(
                QRect(int(x), int(geo.top()),
                      int(self.viewport().width() - x - 8), int(geo.height())),
                Qt.AlignLeft | Qt.AlignVCenter, self.frontmatter_summary())

        bib_rect = self._bib_marker_rect()
        if bib_rect is not None:
            # 원문(:::{thebibliography ...})을 지우고 그 자리에 버튼처럼
            # 채워 그린다 — 프론트매터 요약과 달리 이건 원문 옆에
            # 덧붙이는 게 아니라 통째로 덮는다. LyX 의 WYSIWYM 버튼을
            # 흉내 낸 것이다. 그 줄 전체 폭을 배경색으로 먼저 지운
            # 다음, 버튼만 그 위에 얹는다.
            line_rect = QRect(0, int(bib_rect.top()),
                              self.viewport().width(), int(bib_rect.height()))
            painter.fillRect(line_rect, QColor(self._theme.bg))
            radius = min(8.0, bib_rect.height() / 2)
            painter.setBrush(QColor(self._theme.env_name))
            painter.setPen(Qt.NoPen)
            painter.drawRoundedRect(bib_rect, radius, radius)
            painter.setPen(QColor(self._theme.bg))
            f = QFont(self.font())
            f.setBold(True)
            painter.setFont(f)
            painter.drawText(bib_rect, Qt.AlignCenter, self.BIB_BUTTON_LABEL)

        painter.end()

    def paint_gutter(self, event):
        painter = QPainter(self._gutter)
        painter.fillRect(event.rect(), QColor(self._theme.bg))

        current = self.textCursor().blockNumber()
        block = self.firstVisibleBlock()
        top = self.blockBoundingGeometry(block).translated(
            self.contentOffset()).top()
        fm = QFontMetricsF(self.font())

        while block.isValid() and top <= event.rect().bottom():
            height = self.blockBoundingRect(block).height()
            if block.isVisible() and top + height >= event.rect().top():
                active = block.blockNumber() == current
                painter.setPen(QColor(self._theme.gutter_fg_active if active
                                      else self._theme.gutter_fg))
                painter.drawText(
                    QRect(0, int(top), self._gutter.width() - 10, int(fm.height() * 1.62)),
                    Qt.AlignRight | Qt.AlignVCenter,
                    str(block.blockNumber() + 1))
                if block.blockNumber() == 0 and self.frontmatter_range():
                    painter.setPen(QColor(self._theme.gutter_fg_active))
                    painter.drawText(
                        QRect(2, int(top), 12, int(fm.height() * 1.62)),
                        Qt.AlignLeft | Qt.AlignVCenter,
                        "▸" if self._fm_folded else "▾")
                elif self.fence_is_open_line(block) and self.fence_close_block(block) is not None:
                    painter.setPen(QColor(self._theme.gutter_fg_active if active
                                          else self._theme.gutter_fg))
                    painter.drawText(
                        QRect(2, int(top), 12, int(fm.height() * 1.62)),
                        Qt.AlignLeft | Qt.AlignVCenter,
                        "▸" if self.fence_is_folded(block) else "▾")
            block = block.next()
            top += height
        painter.end()

    # -- 프론트매터 접기 -------------------------------------------------------

    def frontmatter_range(self):
        """(여는 줄, 닫는 줄) 블록 번호. 프론트매터가 없으면 None.

        ndhmd4tex 의 FRONTMATTER_RE 와 같은 조건이다 — 첫 줄이 정확히
        `---` 이고 그 뒤에 닫는 줄이 있어야 한다.
        """
        doc = self.document()
        first = doc.firstBlock()
        if not first.isValid() or not FRONTMATTER_OPEN_RE.match(first.text()):
            return None
        block = first.next()
        while block.isValid():
            if FRONTMATTER_CLOSE_RE.match(block.text()):
                return (0, block.blockNumber())
            block = block.next()
        return None

    def frontmatter_summary(self) -> str:
        """접었을 때 `---` 오른쪽에 덧그릴 한 줄 요약."""
        rng = self.frontmatter_range()
        if not rng:
            return ""
        _, last = rng
        doc = self.document()
        title = None
        for n in range(1, last):
            text = doc.findBlockByNumber(n).text()
            m = re.match(r"^\s*([A-Za-z_][\w+-]*)\s*:\s*(.*)$", text)
            if not m:
                continue
            key, value = m.group(1), m.group(2).strip()
            if key == "title" and value:
                title = value.strip("\"'")
                break
            if title is None and value:
                title = f"{key}: {value}"
        hidden = last  # 숨긴 줄 수 = 1..last
        head = title or "프론트매터"
        return f"  {head}   ·   {hidden}줄 접힘"

    @property
    def frontmatter_folded(self) -> bool:
        return self._fm_folded

    def set_frontmatter_folded(self, folded: bool):
        rng = self.frontmatter_range()
        if rng is None:
            self._fm_folded = False
            self._fm_last = -1
            return False
        _, last = rng
        doc = self.document()

        block = doc.findBlockByNumber(1)
        while block.isValid() and block.blockNumber() <= last:
            block.setVisible(not folded)
            block = block.next()

        self._fm_folded = folded
        self._fm_last = last

        # 레이아웃에 다시 계산하라고 알린다. 이게 없으면 높이가 갱신되지 않는다.
        start = doc.findBlockByNumber(0).position()
        end_block = doc.findBlockByNumber(last)
        doc.markContentsDirty(start, end_block.position() + end_block.length() - start)
        self.viewport().update()
        self._gutter.update()

        if folded:
            self._nudge_cursor_out()
        return True

    def toggle_frontmatter_fold(self) -> bool:
        return self.set_frontmatter_folded(not self._fm_folded)

    def _nudge_cursor_out(self):
        """커서가 숨은 줄에 들어가 있으면 보이는 줄로 밀어낸다.

        숨긴 블록에도 커서는 갈 수 있다(↑↓, Ctrl+Home). 거기서 타이핑하면
        보이지 않는 곳이 고쳐지므로 반드시 막아야 한다.
        """
        if not self._fm_folded:
            return
        cursor = self.textCursor()
        n = cursor.blockNumber()
        if not (1 <= n <= self._fm_last):
            return
        target = self.document().findBlockByNumber(self._fm_last + 1)
        if not target.isValid():
            target = self.document().findBlockByNumber(0)
        cursor = QTextCursor(target)
        self.setTextCursor(cursor)

    def ensure_visible(self, block_number: int):
        """그 줄이 접혀 있으면 펼친다. 검색·sync 가 숨은 줄로 뛸 때 쓴다."""
        if self._fm_folded and 1 <= block_number <= self._fm_last:
            self.set_frontmatter_folded(False)

    def _fold_marker_rect(self):
        """접힌 프론트매터의 여는 `---` 줄이 화면에서 차지하는 사각형."""
        if not self._fm_folded:
            return None
        block = self.document().findBlockByNumber(0)
        if not block.isValid() or not block.isVisible():
            return None
        geo = self.blockBoundingGeometry(block).translated(self.contentOffset())
        return geo

    # -- :::{thebibliography} 접기 ----------------------------------------------
    #
    # 프론트매터 접기와 똑같은 메커니즘이다 — 여는 줄만 남기고 나머지를
    # setVisible(False) 로 숨긴다. 다른 점은 그 남은 줄을 원문 그대로
    # 두지 않고 paintEvent 에서 버튼처럼 덮어 그린다는 것뿐이다.

    def bibliography_range(self):
        """문서 안 첫 :::{thebibliography ...} ~ ::: 블록의 (여는 줄 번호,
        닫는 줄 번호). 없거나 닫는 ::: 를 못 찾으면 None."""
        doc = self.document()
        block = doc.firstBlock()
        fence = 0                  # 코드 펜스 안의 예시(매뉴얼 등)는 참고문헌 블록이 아니다
        while block.isValid():
            raw = block.text()
            if fence:
                m = FENCE_CLOSE_RE.match(raw)
                if m and len(m.group(1)) >= fence:
                    fence = 0
                block = block.next()
                continue
            m = FENCE_OPEN_LOOSE_RE.match(raw)
            if m:
                fence = len(m.group(1))
                block = block.next()
                continue
            if BIBLIOGRAPHY_OPEN_RE.match(raw):
                open_n = block.blockNumber()
                b2 = block.next()
                while b2.isValid():
                    if ENV_CLOSE_RE.match(b2.text()):
                        return (open_n, b2.blockNumber())
                    b2 = b2.next()
                return None          # 닫는 ::: 를 못 찾음 — 깨진 블록
            block = block.next()
        return None

    def set_bibliography_folded(self, folded: bool) -> bool:
        rng = self.bibliography_range()
        if rng is None:
            self._bib_folded = False
            return False
        open_n, close_n = rng
        doc = self.document()
        # 여는 줄 자신은 항상 보여야 한다(버튼처럼 덮어 그려지는 자리라서) —
        # 명시적으로 켜 둔다. 참고문헌을 고쳐 쓸 때(write_bibliography)
        # 여는 줄부터 닫는 줄까지를 통째로 지우고 새로 넣는데, 그 지워지는
        # 범위가 "보이는 여는 줄"에서 "숨겨진 나머지 줄"까지 걸쳐 있어서,
        # Qt 가 지우고 합치는 과정에서 새로 생긴 블록이 숨김 쪽 상태를
        # 물려받는 경우가 있다(실제로 보고된 버그다: 참고문헌 버튼이
        # 고친 직후 사라지고 F5 를 눌러야 돌아왔다). 아래 줄이 그 상태를
        # 매번 바로잡는다.
        doc.findBlockByNumber(open_n).setVisible(True)
        block = doc.findBlockByNumber(open_n + 1)
        while block.isValid() and block.blockNumber() <= close_n:
            block.setVisible(not folded)
            block = block.next()

        self._bib_folded = folded

        start = doc.findBlockByNumber(open_n).position()
        end_block = doc.findBlockByNumber(close_n)
        doc.markContentsDirty(start, end_block.position() + end_block.length() - start)
        self.viewport().update()
        self._gutter.update()

        if folded:
            self._nudge_cursor_out_of_bibliography()
        return True

    def _nudge_cursor_out_of_bibliography(self):
        """커서가 방금 숨긴 줄에 있으면 보이는 줄로 밀어낸다.

        블록 번호 범위를 저장해 두고 비교하지 않는다 — 커서 자신이
        지금 있는 블록의 가시성만 본다. 그래야 이 문서 어디에 텍스트가
        늘거나 줄어도 항상 옳다.
        """
        cursor = self.textCursor()
        if cursor.block().isVisible():
            return
        block = cursor.block().next()
        while block.isValid() and not block.isVisible():
            block = block.next()
        if not block.isValid():
            block = cursor.block().previous()
            while block.isValid() and not block.isVisible():
                block = block.previous()
        if block.isValid():
            self.setTextCursor(QTextCursor(block))

    def _bib_marker_rect(self):
        """지금 화면에 [참고문헌] 버튼이 있으면 그 사각형, 없으면 None.

        여는 줄의 블록 번호를 저장해 두고 쓰지 않는다 — 앞에 텍스트를
        써넣거나 지우면 그 번호가 밀려서 엉뚱한 줄을 가리키게 된다
        (실제로 보고된 버그다: 박스가 화면의 고정된 자리에 붙박여
        앞뒤 편집을 따라가지 못했다). 대신 지금 화면에 "보이는" 블록
        중에서 :::{thebibliography 로 시작하면서 바로 다음 블록이
        숨겨져 있는(=접힌 상태) 것을 그때그때 찾는다 — 화면에 보이는
        범위만 훑으므로 문서가 커도 비용이 작고, 텍스트가 얼마나
        밀리든 항상 맞는 줄을 가리킨다.
        """
        if not self._bib_folded:
            return None
        block = self.firstVisibleBlock()
        bottom = self.viewport().rect().bottom()
        top = self.blockBoundingGeometry(block).translated(self.contentOffset()).top()
        while block.isValid() and top <= bottom:
            height = self.blockBoundingRect(block).height()
            if (block.isVisible() and self._span_of(block.userState()) != SPAN_FENCE
                    and BIBLIOGRAPHY_OPEN_RE.match(block.text())):
                nxt = block.next()
                if nxt.isValid() and not nxt.isVisible():
                    geo = self.blockBoundingGeometry(block).translated(self.contentOffset())
                    fm = QFontMetricsF(self.font())
                    label_w = fm.horizontalAdvance(self.BIB_BUTTON_LABEL) + 24
                    margin = self.document().documentMargin()
                    return QRectF(margin, geo.top(), label_w, geo.height())
            block = block.next()
            top += height
        return None

    # -- 코드 펜스(```) 접기 --------------------------------------------------------
    #
    # 프론트매터·참고문헌 접기와 같은 방식(블록을 setVisible(False) 로 숨기고 여는 줄만 남긴다)이다.
    # 펜스의 여는·닫는 줄은 하이라이터가 블록 상태에 실어 둔 SPAN_FENCE 로, `:::{환경}` 은 같은 상태의
    # ENV 깊이로 판단한다(thebibliography 는 자기 전용 접기가 있어 뺀다). 닫는 줄이 없는 구조는
    # 접지 않는다(뒤의 글을 통째로 숨기게 되므로). 중첩이면 가장 안쪽이 대상이다.

    @staticmethod
    def _span_of(state: int) -> int:
        return (state >> SPAN_SHIFT) & SPAN_MASK if state >= 0 else SPAN_NONE

    def fence_is_open_line(self, block) -> bool:
        """접을 수 있는 구조(코드 펜스 또는 `:::{환경}`)의 여는 줄인가. (이름은 펜스로 시작했지만 둘 다 다룬다.)
        thebibliography 는 자기 전용 접기가 있으므로 뺀다."""
        if not block.isValid():
            return False
        sp = self._span_of(block.userState())
        prev = block.previous()
        pst = prev.userState() if prev.isValid() else -1
        if sp == SPAN_FENCE:
            return self._span_of(pst) != SPAN_FENCE
        if sp != SPAN_NONE or self._span_of(pst) == SPAN_FENCE:
            return False
        text = block.text()
        if not text.startswith(":::") or BIBLIOGRAPHY_OPEN_RE.match(text) or not ENV_OPEN_RE.match(text):
            return False
        return env_depth(block.userState()) > env_depth(pst)

    def fence_close_block(self, open_block):
        """여는 줄에 짝이 맞는 닫는 줄 블록. 닫는 줄이 없으면 None."""
        b = open_block.next()
        if self._span_of(open_block.userState()) == SPAN_FENCE:
            while b.isValid():
                if self._span_of(b.userState()) != SPAN_FENCE:
                    return b
                b = b.next()
            return None
        depth = env_depth(open_block.userState())      # 닫는 줄에서 이 값보다 작아진다
        while b.isValid():
            if env_depth(b.userState()) < depth:
                return b
            b = b.next()
        return None

    def fence_is_folded(self, open_block) -> bool:
        if not (open_block.isValid() and open_block.isVisible()):
            return False
        nxt = open_block.next()
        return nxt.isValid() and not nxt.isVisible() and self.fence_is_open_line(open_block)

    def fence_open_for(self, block):
        """block 이 접을 수 있는 구조(펜스·환경) 안(여는 줄·내용·닫는 줄)이면 가장 안쪽 구조의 여는 줄 블록, 아니면 None."""
        if not block.isValid():
            return None
        n = block.blockNumber()
        b = block
        while b.isValid():
            if self.fence_is_open_line(b):
                close = self.fence_close_block(b)
                if close is not None and close.blockNumber() >= n:
                    return b
            b = b.previous()
        return None

    def set_fence_folded(self, open_block, folded: bool) -> bool:
        close = self.fence_close_block(open_block)
        if close is None:
            return False
        doc = self.document()
        b = open_block.next()
        while b.isValid() and b.blockNumber() <= close.blockNumber():
            b.setVisible(not folded)
            b = b.next()
        start = open_block.position()
        doc.markContentsDirty(start, close.position() + close.length() - start)
        if folded:
            self._fence_folded_any = True
            cur = self.textCursor()
            if not cur.block().isVisible():
                self.setTextCursor(QTextCursor(open_block))
        self.viewport().update()
        self._gutter.update()
        return True

    def toggle_fence(self, open_block) -> bool:
        return self.set_fence_folded(open_block, not self.fence_is_folded(open_block))

    def toggle_fence_at_cursor(self) -> bool:
        ob = self.fence_open_for(self.textCursor().block())
        return ob is not None and self.toggle_fence(ob)

    def set_all_fences_folded(self, folded: bool) -> int:
        """문서의 모든 코드 펜스를 접거나 편다. 바꾼 개수를 돌려준다."""
        n, b = 0, self.document().firstBlock()
        while b.isValid():
            if self.fence_is_open_line(b) and b.isVisible():
                close = self.fence_close_block(b)
                if close is not None:
                    if self.fence_is_folded(b) != folded and self.set_fence_folded(b, folded):
                        n += 1
                    b = close
            b = b.next()
        return n

    def _unfold_if_cursor_hidden(self):
        """커서가 접힌 펜스 안으로 들어가면(찾기·줄 이동·오류 목록 등) 그 펜스를 편다."""
        if not self._fence_folded_any:
            return
        block = self.textCursor().block()
        if block.isVisible():
            return
        owner = block.previous()
        while owner.isValid() and not owner.isVisible():
            owner = owner.previous()
        if owner.isValid() and self.fence_is_open_line(owner):
            self.set_fence_folded(owner, False)

    def _schedule_fence_check(self):
        if self._fence_folded_any:
            self._fence_check_timer.start()

    def _validate_fence_folds(self):
        """고치다가 여는 줄이 망가져 숨은 줄의 주인이 없어진 곳을 다시 보이게 한다.
        프론트매터·참고문헌 접기가 숨긴 줄은 건드리지 않는다."""
        any_fold, owner = False, None
        b = self.document().firstBlock()
        while b.isValid():
            if b.isVisible():
                owner = b
            elif owner is not None:
                n = b.blockNumber()
                if owner.blockNumber() == 0 and self._fm_folded and n <= self._fm_last:
                    pass
                elif BIBLIOGRAPHY_OPEN_RE.match(owner.text()):
                    pass
                elif self.fence_is_open_line(owner):
                    close = self.fence_close_block(owner)
                    if close is not None and n <= close.blockNumber():
                        any_fold = True
                    else:
                        b.setVisible(True)
                else:
                    b.setVisible(True)
            b = b.next()
        self._fence_folded_any = any_fold
        self.document().markContentsDirty(0, self.document().characterCount())
        self.viewport().update()
        self._gutter.update()

    # -- 목록 Enter 이어쓰기 -----------------------------------------------------
    #
    # 탭으로 들여쓴 목록에서 Enter 를 치면 새 줄이 들여쓰기 없이 맨 앞으로
    # 가 버리는 것이 불편하다는 요청에서 나왔다. 들여쓰기(공백이든 탭이든)
    # 를 그대로 복사해 다음 줄에 물려주면 해결된다. 표지 없이 빈 항목만
    # 남았을 때 Enter 를 한 번 더 치면 표지를 지우고 평문으로 나간다 —
    # 리스트 안에서만 일어나는 일이라 다른 곳의 Enter 는 건드리지 않는다.

    # -- Ctrl+클릭으로 링크 열기 ----------------------------------------------
    #
    # [글자](URL) 에서 Ctrl 을 누른 채 클릭하면 기본 브라우저로 그 URL 을
    # 연다. 그림 참조(![대체글](경로))는 URL 여는 대상이 아니므로 앞에
    # '!' 가 붙은 것은 건너뛴다.

    def _link_index(self):
        """문서 전체에서 한 번 구해 두는 것: (펜스 안을 비운 본문, {표지: 주소}).
        문서가 바뀔 때(revision)만 다시 만든다 — Ctrl 을 누른 채 마우스를 움직일
        때마다 불리므로 매번 문서를 훑으면 큰 원고에서 느려진다."""
        rev = self.document().revision()
        cached = getattr(self, "_link_index_cache", None)
        if cached is not None and cached[0] == rev:
            return cached[1], cached[2]
        masked = PreviewScanner._fence_mask(self.toPlainText())
        defs = {}
        for line in masked.split("\n"):
            m = FIGURE_DEF_RE.match(line)
            if m:
                defs.setdefault(m.group(1).strip().lower(), m.group(2))
        self._link_index_cache = (rev, masked, defs)
        return masked, defs

    def _link_at(self, point):
        """그 화면 좌표가 인터넷 주소(링크·참조 링크·맨 주소)이면 그 주소를, 아니면
        None 을 준다. 그림은 주소로 치지 않는다(url_in_line 참고)."""
        return self._url_at_cursor(self.cursorForPosition(point))

    def _url_at_cursor(self, cursor):
        block = cursor.block()
        masked, defs = self._link_index()
        start = block.position()
        line = masked[start:start + block.length() - 1]
        text = None

        def resolve(key):
            return defs.get(key.strip().lower())

        def is_fig(key):
            nonlocal text
            if text is None:
                text = masked
            return PreviewScanner._is_figure_label(text, key)

        return url_in_line(line, cursor.positionInBlock(), resolve, is_fig)

    def _xref_at(self, point):
        """그 화면 좌표가 [글자](#라벨) 위이면 라벨을, 아니면 None."""
        cursor = self.cursorForPosition(point)
        block = cursor.block()
        masked, _ = self._link_index()
        start = block.position()
        line = masked[start:start + block.length() - 1]
        return xref_in_line(line, cursor.positionInBlock())

    def _ref_at(self, point):
        """그 화면 좌표가 참조·정의 표지(각주·상호참조·인용·이름 붙은 그림) 위이면 (종류, 키, 정의인가), 아니면 None."""
        cursor = self.cursorForPosition(point)
        block = cursor.block()
        return ref_token_at(block.text(), cursor.positionInBlock())

    def mousePressEvent(self, event):
        if (event.button() == Qt.LeftButton
                and event.modifiers() & Qt.ControlModifier
                and self._host is not None):
            label = self._xref_at(event.position().toPoint())
            if label:
                self._host.jump_to_label(label)
                return
        if event.button() == Qt.LeftButton and not (event.modifiers() & Qt.ControlModifier):
            bib_rect = self._bib_marker_rect()
            if bib_rect is not None and bib_rect.contains(event.position()):
                if self._host is not None:
                    self._host.open_bibliography_editor()
                return
        if (event.button() == Qt.LeftButton
                and event.modifiers() & Qt.ControlModifier):
            url = self._link_at(event.position().toPoint())
            if url:
                QDesktopServices.openUrl(QUrl(url))
                return
            tok = self._ref_at(event.position().toPoint()) if self._host is not None else None
            if tok:
                self._host.jump_reference(*tok)
                return
        super().mousePressEvent(event)
        if event.button() == Qt.LeftButton and self._host is not None:
            # 의도적으로 편집창을 눌렀다 — 서랍의 선택(자료 창고·컴파일 참고 항목 등)을
            # 지금 편집 중인 파일로 되돌린다.
            self._host.sync_drawer_selection()

    def mouseMoveEvent(self, event):
        if event.modifiers() & Qt.ControlModifier:
            pt = event.position().toPoint()
            is_link = self._link_at(pt) is not None or self._ref_at(pt) is not None
            self.viewport().setCursor(
                Qt.PointingHandCursor if is_link else Qt.IBeamCursor)
        else:
            bib_rect = self._bib_marker_rect()
            if bib_rect is not None and bib_rect.contains(event.position()):
                self.viewport().setCursor(Qt.PointingHandCursor)
            else:
                self.viewport().setCursor(Qt.IBeamCursor)
        super().mouseMoveEvent(event)

    def keyPressEvent(self, event):
        if event.key() in (Qt.Key_Return, Qt.Key_Enter):
            if event.modifiers() == Qt.NoModifier:
                if self._continue_list():
                    return
            elif event.modifiers() == Qt.ShiftModifier:
                if self._soft_break_in_list():
                    return
        if event.key() == Qt.Key_Tab and event.modifiers() == Qt.NoModifier:
            if self._list_indent(1):
                return
            if self.tab_to_spaces_enabled:
                self.textCursor().insertText(" " * self.tab_spaces_count)
                return
        if event.key() == Qt.Key_Backtab or (
                event.key() == Qt.Key_Tab and event.modifiers() == Qt.ShiftModifier):
            if self._list_indent(-1):
                return
        if event.key() == Qt.Key_BracketRight and event.modifiers() == Qt.ControlModifier:
            self._block_indent(1)
            return
        if event.key() == Qt.Key_BracketLeft and event.modifiers() == Qt.ControlModifier:
            self._block_indent(-1)
            return
        if (event.key() in (Qt.Key_Period, Qt.Key_Comma)
                and event.modifiers() in (Qt.AltModifier, Qt.AltModifier | Qt.ShiftModifier)):
            # 스마트 문장부호가 켜져 있어도 이걸로는 항상 키보드
            # 마침표/쉼표를 그대로 찍는다 — Alt 단축키가 시스템에
            # 막혀 있을 수도 있어 Shift+Alt 쪽도 똑같이 받아 준다.
            self.textCursor().insertText("." if event.key() == Qt.Key_Period else ",")
            return
        if (event.key() in (Qt.Key_Apostrophe, Qt.Key_QuoteDbl)
                and event.modifiers() in (Qt.AltModifier, Qt.AltModifier | Qt.ShiftModifier)):
            # 스마트 따옴표가 켜져 있어도 이걸로는 항상 곧은 따옴표를
            # 찍는다(마크다운 인자 등). 키 코드로 판별한다 — macOS 의
            # Option 은 event.text() 를 바꿔 버릴 수 있다. Shift 가
            # 눌렸거나 키 자체가 QuoteDbl 이면 큰따옴표, 아니면 작은따옴표.
            dbl = (event.key() == Qt.Key_QuoteDbl
                   or bool(event.modifiers() & Qt.ShiftModifier))
            self.textCursor().insertText('"' if dbl else "'")
            return
        if self.smart_quotes_style != "off" and event.text() in SMART_QUOTE_PAIRS.get(
                self.smart_quotes_style, {}):
            open_q, close_q = SMART_QUOTE_PAIRS[self.smart_quotes_style][event.text()]
            cursor = self.textCursor()
            if cursor.hasSelection():
                selected = cursor.selectedText().replace("\u2029", "\n")
                cursor.insertText(open_q + selected + close_q)
            else:
                before = cursor.block().text()[:cursor.positionInBlock()]
                cursor.insertText(open_q if self._smart_quote_is_opening(before) else close_q)
            return
        if self.smart_punctuation and event.text() in SMART_PUNCTUATION_PAIRS:
            self.textCursor().insertText(SMART_PUNCTUATION_PAIRS[event.text()])
            return
        super().keyPressEvent(event)

    @staticmethod
    def _smart_quote_is_opening(text_before: str) -> bool:
        """커서 앞 글자를 보고 여는 따옴표를 넣을 자리인지 판단한다 —
        비어 있거나(줄 시작) 공백 뒤, 또는 다른 여는 문장부호(괄호나
        이미 연 다른 따옴표) 바로 뒤라면 여는 쪽이다."""
        if not text_before:
            return True
        last = text_before[-1]
        if last.isspace():
            return True
        return last in "([{\u201c\u2018\u00ab\u2039\u300e\u300c"

    # -- 한글 IME 조합 -----------------------------------------------------------
    #
    # Qt 의 내장 조합(preedit) 렌더링이 Windows 에서 팔레트/스타일시트가
    # 얽힌 QPlainTextEdit 에서 유난히 흐리게(때로는 안 보이게) 나오는
    # 문제가 있다. 색을 맞추는 것만으로 안전하다고 장담할 수 없어서,
    # 아예 조합 중인 글자를 진짜 텍스트로 임시 삽입해 버린다 — 그러면
    # 우리 하이라이터·팔레트로 정상 렌더링되는 일반 텍스트와 완전히
    # 같은 경로를 타므로, Qt 의 preedit 그리기 자체를 신경 쓸 필요가
    # 없어진다. super().inputMethodEvent() 는 일부러 안 부른다 — 그걸
    # 부르면 Qt 가 자기 preedit 표시를 또 그리려 해서 이중으로 겹친다.

    def inputMethodEvent(self, event):
        cursor = self.textCursor()
        if self._preedit_length > 0:
            cursor.movePosition(QTextCursor.Left, QTextCursor.KeepAnchor,
                               self._preedit_length)
            cursor.removeSelectedText()
            self._preedit_length = 0
        if event.preeditString():
            cursor.insertText(event.preeditString())
            self._preedit_length = len(event.preeditString())
        if event.commitString():
            cursor.insertText(event.commitString())
        self.setTextCursor(cursor)

    def _continue_list(self) -> bool:
        cursor = self.textCursor()
        if cursor.hasSelection():
            return False
        block = cursor.block()
        text = block.text()
        m = LIST_PREFIX_RE.match(text)
        if not m:
            return False

        indent, marker, spacing = m.group(1), m.group(2), m.group(3)
        prefix_end = m.end()
        pos = cursor.positionInBlock()
        if pos < prefix_end:
            return False                     # 표지 위에서의 Enter 는 평범하게

        before = text[prefix_end:pos]
        after = text[pos:]
        if not before.strip() and not after.strip():
            # 표지만 있고 내용이 없는 항목 — 여기서 한 번 더 Enter 를 친
            # 것이므로 표지를 지우고 평문 줄로 나간다.
            cursor.movePosition(QTextCursor.StartOfBlock)
            cursor.movePosition(QTextCursor.EndOfBlock, QTextCursor.KeepAnchor)
            cursor.insertText(indent)
            cursor.movePosition(QTextCursor.EndOfBlock)
            cursor.insertText("\n")
            self.setTextCursor(cursor)
            return True

        if marker[-1] in ".)":
            new_marker = f"{int(marker[:-1]) + 1}{marker[-1]}"
        else:
            new_marker = marker
        cursor.insertText("\n" + indent + new_marker + spacing)
        self.setTextCursor(cursor)
        return True

    def _soft_break_in_list(self) -> bool:
        """리스트 항목 안에서 Shift+Enter — 새 항목을 만들지 않고 줄만
        바꾸되, 커서를 표지 밖(그 항목의 내용이 시작하는 칸)에 맞춰
        둔다. 그냥 두면 1번 칸으로 가 버려서, 아직 리스트를 벗어난
        게 아닌데도 한참 다시 들여써야 하는 게 불편하다는 데서 나왔다.

        표지 위에서 치면(아직 항목 내용이 시작되기 전) 평범하게
        처리되도록 False 를 돌려준다.
        """
        cursor = self.textCursor()
        if cursor.hasSelection():
            return False
        block = cursor.block()
        text = block.text()
        m = LIST_PREFIX_RE.match(text)
        if not m:
            return False
        indent, prefix_end = m.group(1), m.end()
        if cursor.positionInBlock() < prefix_end:
            return False
        # indent 는 원래 쓰던 문자(스페이스든 탭이든) 그대로 두고, 표지
        # 자체(marker+spacing) 자리만 같은 폭의 스페이스로 채운다 —
        # 표지를 새로 만드는 게 아니라 그 칸까지만 맞추면 되기 때문이다.
        pad = indent + " " * (prefix_end - len(indent))
        cursor.insertText("\n" + pad)
        self.setTextCursor(cursor)
        return True

    def _reindent_lines(self, first_block, last_block, direction: int) -> dict:
        """[first_block, last_block] 범위의 각 줄 맨 앞에 공백을 더하거나
        뺀다. 실제 들여쓰기/내어쓰기 작업 본체 — _list_indent() 와
        _block_indent() 가 공유한다. 블록 번호 -> 그 줄 맨 앞에서
        늘어나거나(양수) 줄어든(음수) 글자 수를 돌려준다(커서 복원에
        쓴다).
        """
        doc = self.document()
        unit_len = self.tab_spaces_count
        unit = " " * unit_len
        deltas = {}

        edit = QTextCursor(doc)
        edit.beginEditBlock()
        n = first_block.blockNumber()
        last_n = last_block.blockNumber()
        while True:
            block = doc.findBlockByNumber(n)
            line = block.text()
            pos = block.position()
            if direction > 0:
                edit.setPosition(pos)
                edit.insertText(unit)
                deltas[n] = unit_len
            else:
                remove_n = 0
                for ch in line[:unit_len]:
                    if ch != " ":
                        break
                    remove_n += 1
                if remove_n == 0 and line.startswith("\t"):
                    remove_n = 1
                if remove_n:
                    edit.setPosition(pos)
                    edit.setPosition(pos + remove_n, QTextCursor.KeepAnchor)
                    edit.removeSelectedText()
                deltas[n] = -remove_n
            if n == last_n:
                break
            n += 1
        edit.endEditBlock()
        return deltas

    def _restore_cursor_after_reindent(self, first_block, last_block, sel_start,
                                       had_selection: bool, deltas: dict):
        """_reindent_lines() 뒤에 커서/선택을 같은 자리로 되돌린다.
        그대로 두면 위젯이 알아서 옮겨 주는 자리가 방금 늘어나거나
        줄어든 부분과 어긋난다."""
        doc = self.document()
        new_cursor = self.textCursor()
        if had_selection:
            new_first = doc.findBlockByNumber(first_block.blockNumber())
            new_last = doc.findBlockByNumber(last_block.blockNumber())
            new_cursor.setPosition(new_first.position())
            new_cursor.setPosition(
                new_last.position() + new_last.length() - 1, QTextCursor.KeepAnchor)
        else:
            delta = deltas.get(first_block.blockNumber(), 0)
            offset_in_block = sel_start - first_block.position()
            new_offset = max(0, offset_in_block + delta)
            new_block = doc.findBlockByNumber(first_block.blockNumber())
            new_pos = min(new_block.position() + new_offset,
                         new_block.position() + new_block.length() - 1)
            new_cursor.setPosition(new_pos)
        self.setTextCursor(new_cursor)

    @staticmethod
    def _reindent_selection_range(cursor: QTextCursor, doc: QTextDocument):
        """커서/선택 기준으로 (first_block, last_block, sel_start,
        had_selection) 을 계산한다 — _list_indent() 와 _block_indent()
        가 똑같이 하던 일이다."""
        had_selection = cursor.hasSelection()
        sel_start = min(cursor.selectionStart(), cursor.selectionEnd())
        sel_end = max(cursor.selectionStart(), cursor.selectionEnd())
        first_block = doc.findBlock(sel_start)
        last_block = doc.findBlock(sel_end)
        if last_block.blockNumber() != first_block.blockNumber() and \
                sel_end == last_block.position():
            # 선택이 다음 줄 맨 앞에서 끝나면(줄 전체를 고른 흔한 모양)
            # 그 다음 줄까지 들여쓰기 대상으로 삼지 않는다.
            prev = last_block.previous()
            if prev.isValid():
                last_block = prev
        return first_block, last_block, sel_start, had_selection

    def _list_indent(self, direction: int) -> bool:
        """리스트 항목이면 표지째로 들여쓰기/내어쓰기 한다.

        표지 앞에 공백을 더하거나 빼는 것뿐이다 — 그래서 표지 자체가
        줄과 함께 통째로 움직인다. 이 줄이 리스트가 아니면 아무 일도
        안 하고 False 를 돌려준다 — 호출한 쪽이 다른 Tab 동작(스페이스
        삽입 등)으로 넘어갈 수 있게 하기 위해서다.

        선택 영역이 여러 줄에 걸쳐 있으면 그 줄들 전부에 적용한다.
        커서만 있으면(선택 없음) 그 줄 하나에만 적용한다.
        """
        cursor = self.textCursor()
        doc = self.document()
        first_block, last_block, sel_start, had_selection = \
            self._reindent_selection_range(cursor, doc)

        if not LIST_PREFIX_RE.match(first_block.text()):
            return False

        deltas = self._reindent_lines(first_block, last_block, direction)
        self._restore_cursor_after_reindent(
            first_block, last_block, sel_start, had_selection, deltas)
        return True

    def _block_indent(self, direction: int):
        """리스트인지 아닌지 가리지 않고, 선택한 줄들을 통째로
        들여쓰기/내어쓰기 한다. 붙여넣은 LaTeX 코드처럼 순수한 텍스트
        블록(예: frontmatter 의 preamble:)에 쓰기 위한 것이다 —
        Ctrl+]/Ctrl+[ 에 물린다. 선택이 없으면 커서가 있는 줄 하나에만
        적용한다.
        """
        cursor = self.textCursor()
        doc = self.document()
        first_block, last_block, sel_start, had_selection = \
            self._reindent_selection_range(cursor, doc)

        deltas = self._reindent_lines(first_block, last_block, direction)
        self._restore_cursor_after_reindent(
            first_block, last_block, sel_start, had_selection, deltas)

    # -- 우클릭 메뉴 ------------------------------------------------------------

    def _table_for_tblrdoumi_at(self, pos: int):
        """pos 가 파이프 표·grid 표 안이면 ("grid"|"pipe", 원문), 아니면 None."""
        target = PreviewScanner.find(self.toPlainText(), pos)
        if target is None or target.kind != "table":
            return None
        src = "\n".join(l for l in target.source.splitlines() if not TABLE_OPT_RE.match(l.strip()))
        if GRID_BORDER_RE.match(src.lstrip().split("\n", 1)[0]):
            try:
                parse_grid_table(src.splitlines())
            except (GridTableError, ValueError):
                return None
            return "grid", src
        fmt, _a, _r = TableEditorDialog.parse_table_text(src)
        return ("pipe", src) if fmt == "markdown" else None

    def _grid_table_source_at(self, pos: int):
        """pos 가 해석 가능한 grid 표 안이면 그 표의 줄 목록, 아니면 None."""
        target = PreviewScanner.find(self.toPlainText(), pos)
        if target is None or target.kind != "table":
            return None
        lines = target.source.splitlines()
        if not lines or not GRID_BORDER_RE.match(lines[0]):
            return None
        lines = [l for l in lines if not TABLE_OPT_RE.match(l.strip())]
        try:
            parse_grid_table(lines)
        except (GridTableError, ValueError):
            return None
        return lines

    def _build_context_menu(self) -> "QMenu":
        menu = self.createStandardContextMenu()
        host = self._host
        if host is not None:
            menu.addSeparator()

            # -- 표 편집기 연동 메뉴 동적 생성 --
            cursor = self.textCursor()
            selected_text = cursor.selectedText()
            # Qt는 단락 구분자로 \u2029를 쓰므로 일반 \n으로 변환하여 검사
            normalized_text = selected_text.replace("\u2029", "\n")
            
            # 표 형태인지 사전 검사
            is_valid_table = False
            error_msg = ""
            if normalized_text.strip():
                fmt, aligns, err = TableEditorDialog.parse_table_text(normalized_text)
                if fmt is not None:
                    is_valid_table = True
                else:
                    error_msg = err

            table_action = menu.addAction("간단 표 편집기에서 편집…")
            if is_valid_table:
                table_action.setEnabled(True)
                table_action.triggered.connect(lambda: host.open_table_editor_with_text(normalized_text))
            else:
                table_action.setEnabled(False)
                if selected_text.strip():
                    # 무언가 선택은 했으나 표가 아닐 때, 안내 메시지 툴팁 설정
                    table_action.setToolTip(error_msg if error_msg else "더 복잡한 표는 전용 표 편집 프로그램을 이용하셔요")
                else:
                    table_action.setToolTip("표를 선택해 주세요.")

            # grid 표 위에서: 표 편집기로 못 보내는(병합 셀 등) 표를 TSV 로 복사해 tblrDoumi 에 붙이게 한다.
            grid_src = self._grid_table_source_at(
                self.cursorForPosition(self._ctx_pos).position()
                if getattr(self, "_ctx_pos", None) is not None else self.textCursor().position())
            tbl_here = self._table_for_tblrdoumi_at(
                self.cursorForPosition(self._ctx_pos).position()
                if getattr(self, "_ctx_pos", None) is not None else self.textCursor().position())
            if tbl_here is not None:
                menu.addAction("tblrDoumi로 보내기 (병합·정렬 유지)",
                               lambda t=tbl_here: host.send_table_to_tblrdoumi(*t))
            if grid_src is not None:
                menu.addAction("grid 표를 TSV로 복사하고 tblrDoumi 열기",
                               lambda src=grid_src: host.grid_table_to_tblrdoumi(src))

            jig = host.jigsaw_target_at_cursor()
            if jig is not None:
                menu.addAction("조각 그림 편집…", lambda: host.open_jigsaw_dialog(jig))

            at = self.cursorForPosition(self._ctx_pos) if getattr(
                self, "_ctx_pos", None) is not None else self.textCursor()
            on_ref = ref_at_position(at.block().text(), at.positionInBlock())
            menu.addAction("상호참조 점검… (이 참조로)" if on_ref else "상호참조 점검…",
                           lambda c=QTextCursor(at): host.open_crossref_check_at_cursor(c))

            fence_ob = self.fence_open_for(at.block())
            if fence_ob is not None and self.fence_close_block(fence_ob) is not None:
                menu.addAction("접기 풀기(펴기)" if self.fence_is_folded(fence_ob) else "이 펜스·환경 접기",
                               lambda o=fence_ob: self.toggle_fence(o))

            menu.addAction("글머리 기호 목록으로",
                lambda: host._transform(SelectionTransform.to_bullet_list))
            menu.addAction("번호 매긴 목록으로",
                lambda: host._transform(SelectionTransform.to_numbered_list))
            menu.addAction("코드펜스로 감싸기",
                lambda: host._transform(SelectionTransform.to_code_fence))
            menu.addAction("인용문으로 감싸기",
                lambda: host._transform(SelectionTransform.to_blockquote))
            menu.addAction("환경으로 감싸기…", host.wrap_in_environment)
            menu.addAction("감싼 것 풀기", host.unwrap_selection)
            menu.addAction("문단 재배열", host.reflow_selection)
            menu.addAction("한자 변환\tF9", host.convert_hanja)
            if load_pmime_core() is not None:
                pm_at = QTextCursor(at)
                has_target = host._pm_target(pm_at) is not None
                a1 = menu.addAction("pm 입력기로 보내기" + ("" if cursor.hasSelection() else " (커서 위 단어)"),
                                    lambda c=pm_at: host.send_selection_to_pmime(c))
                a2 = menu.addAction(
                    "pm 변환 (현재 설정으로 바로)\t"
                    + QKeySequence("Ctrl+Shift+H").toString(QKeySequence.NativeText),
                    lambda c=pm_at: host.convert_selection_pmime(c))
                a1.setEnabled(has_target)
                a2.setEnabled(has_target)
            host.add_heading_shift_menus(menu, has_selection=cursor.hasSelection())
            menu.addSeparator()

            host.add_ai_menu(menu, cursor)
            host.add_ext_tool_menu(menu, cursor)
            lookup_text = selected_text.replace("\u2029", " ").strip()
            lookup_menu = menu.addMenu("찾아보기…")
            google_action = lookup_menu.addAction("Google에서 찾기")
            wiki_action = lookup_menu.addAction("위키백과에서 찾기")
            dict_menu = lookup_menu.addMenu("사전에서 찾기")
            for d in load_dictionaries(host._settings):
                act = dict_menu.addAction(d["name"].replace("&", "&&"))
                if lookup_text:
                    act.triggered.connect(
                        lambda checked=False, u=d["url"]: host.dict_lookup(lookup_text, u))
                else:
                    act.setEnabled(False)
            if dict_menu.actions():
                dict_menu.addSeparator()
            dict_menu.addAction("사전 설정…", host.open_dictionary_settings)
            if lookup_text:
                google_action.triggered.connect(
                    lambda: host.web_lookup(lookup_text, "google"))
                wiki_action.triggered.connect(
                    lambda: host.web_lookup(lookup_text, "wikipedia"))
            else:
                google_action.setEnabled(False)
                wiki_action.setEnabled(False)

            menu.addSeparator()
            menu.addAction("이 위치로 PDF 열기", host.forward_search)
        return menu

    def contextMenuEvent(self, event):
        self._ctx_pos = event.pos()
        menu = self._build_context_menu()
        menu.exec(event.globalPos())
        menu.deleteLater()
        self._ctx_pos = None

    # -- 행번호 변환 (sync 가 붙을 자리) --------------------------------------

    def file_line(self) -> int:
        """현재 커서의 **파일 기준** 1-based 행번호.

        .nmdsync 는 언제나 파일 절대 행번호를 기록하므로, 나중에 정방향
        sync 를 붙일 때 이 값을 그대로 넘기면 된다.
        """
        return self.textCursor().blockNumber() + 1 + self.fm_offset

    def goto_file_line(self, line: int):
        """파일 기준 행번호로 커서를 옮긴다(역방향 sync 진입점)."""
        target = max(0, line - 1 - self.fm_offset)
        block = self.document().findBlockByNumber(target)
        if not block.isValid():
            return
        self.ensure_visible(target)
        if not block.isVisible():
            # 접힌 :::{thebibliography} 안의 줄이면 숨은 줄에 커서를 두지 않고, 버튼처럼
            # 그려진 여는 줄(📚 참고문헌)로 간다.
            rng = self.bibliography_range()
            if rng is not None and rng[0] < target <= rng[1]:
                block = self.document().findBlockByNumber(rng[0])
        cursor = QTextCursor(block)
        self.setTextCursor(cursor)
        self.centerCursor()


# ===========================================================================
# 7. 작업공간
# ===========================================================================

class Workspace:
    """모든 원고가 사는 폴더 하나.

    열기·저장·찾기는 전부 이 안쪽에서만 일어난다. 밖으로 새는 경로를
    막아 두면, 나중에 서랍(계층·태그·출판 순서)이 붙을 때 "서랍에 없는
    파일"이라는 예외 상태를 아예 안 만들 수 있다.

    파일은 물리적으로 평평하게 두는 것이 원칙이다(책 하나 = 폴더 하나).
    계층은 나중에 SQLite 인덱스가 담당하고, 드래그로 순서를 바꿔도
    경로는 그대로여서 .nmdsync 의 절대경로 레코드가 깨지지 않는다.
    """

    #: 편집 대상으로 인정하는 확장자. 목록·검색·열기·저장이 모두 이걸 따른다.
    #: .tex 는 여기 없다 — 산출물이지 원고가 아니고, 편집은 외부 프로그램에
    #: 맡긴다(컴파일 ▸ 결과 tex 열기).
    SUFFIXES = (".txt", ".md", ".nmd", ".mmd")
    #: "부속 파일" — 원고는 아니지만 워크스페이스 안에 같이 두고 참조하는
    #: 것들. {{}} 로 포함되지도, 서랍의 부모-자식 트리에 들어가지도 않는다
    #: (BookIndex 는 SUFFIXES 만 훑으므로 자동으로 빠진다) — 서랍 맨 아래
    #: 접히는 별도 구역에서 평평하게 보여준다.
    AUX_SUFFIXES = (".yaml", ".yml", ".bib")
    #: 빌드 산출물과 숨김 폴더는 목록에서 뺀다.
    SKIP_DIRS = {".git", ".svn", "__pycache__", "_build", ".ndhmd",
                 "_images",   # ndhmd4tex 이 원격 그림을 캐싱해 두는 자리
                 "_assets",   # 컴파일에 관여하지 않는 참고자료 창고
                 "_export"}   # [파일] ▸ 내보내기 의 기본 목적지
    #: 자료 창고 — 원고도 부속 파일도 아니다. 컴파일·BookIndex·
    #: 부속 파일 목록 전부 이 폴더를 안 본다(SKIP_DIRS 에 있어서
    #: source_files()/aux_files() 가 자동으로 건너뛴다). 서랍에서
    #: 목록만 보여주고, 열기·다른 폴더로 옮기기만 지원한다 — 저장·
    #: 미리보기·편집은 전부 시스템에 맡긴다.
    ASSETS_DIR = "_assets"
    #: 내보내기 목적지로 작업공간 "안"을 고르면 이 폴더 밑으로
    #: 돌린다 — 내보낸 결과물이 원고 파일들 사이에 흩어지지 않게.
    EXPORT_DIR = "_export"

    def __init__(self, root: Path | None = None):
        self.root = Path(root).resolve() if root else None

    def __bool__(self) -> bool:
        return self.root is not None and self.root.is_dir()

    @property
    def name(self) -> str:
        return self.root.name if self.root else "(작업공간 없음)"

    def contains(self, path: Path) -> bool:
        if not self:
            return False
        try:
            Path(path).resolve().relative_to(self.root)
        except ValueError:
            return False
        return True

    def relative(self, path: Path) -> str:
        try:
            return str(Path(path).resolve().relative_to(self.root))
        except (ValueError, OSError):
            return str(path)

    @classmethod
    def name_filter(cls) -> str:
        pattern = " ".join(f"*{s}" for s in cls.SUFFIXES)
        aux_pattern = " ".join(f"*{s}" for s in cls.AUX_SUFFIXES)
        return f"원고 ({pattern});;부속 파일 ({aux_pattern});;모든 파일 (*)"

    def _files_with(self, suffixes):
        """작업공간 "최상위"에 있는 파일만 훑는다 — 하위 폴더는 안
        본다. 하위 폴더 파일은 서랍의 별도 구역("하위 폴더")에서
        다룬다(책 구조에 자동으로 섞이지 않게)."""
        if not self:
            return
        for path in sorted(self.root.iterdir()):
            if not path.is_file() or path.suffix.lower() not in suffixes:
                continue
            if path.name.startswith("."):
                continue
            yield path

    #: 컴파일러가 작업 폴더에 남기는 참고용 파일. .txt 이지만 원고가 아니다 —
    #: 원고 목록·책 구조·작업공간 찾기/바꾸기에서 빠지고, 서랍의 `컴파일 참고` 구역에
    #: 따로 보인다. (ksruncltex rev5 의 --missingchar 가 만드는 누락 글자 보고.)
    COMPILE_NOTE_NAMES = ("ksruncltex_missingchar.txt",)

    def source_files(self):
        """작업공간 최상위의 원고 파일을 정렬된 순서로 훑는다(하위
        폴더는 안 본다 — 위 _files_with() 참고). 컴파일 참고 파일은 뺀다."""
        for path in self._files_with(self.SUFFIXES):
            if path.name not in self.COMPILE_NOTE_NAMES:
                yield path

    def compile_note_files(self):
        """작업공간 최상위에 지금 있는 컴파일 참고 파일."""
        if not self:
            return
        for name in self.COMPILE_NOTE_NAMES:
            path = self.root / name
            if path.is_file():
                yield path

    def reference_files(self):
        """서랍 `컴파일 참고` 구역에 보일 파일: 컴파일 참고 파일, 모든 `.sty`·`.cls`,
        그리고 "컴파일되지 않은 .tex"(같은 이름의 원고(.md 등)도 .pdf 도 없는 .tex —
        손으로 쓴 조각이나 남의 tex). 원고에서 변환된 .tex 는 같은 이름의 원고가
        있으니 여기 안 나온다. 작업공간 최상위만 훑는다."""
        if not self:
            return
        yield from self.compile_note_files()
        for path in self._files_with((".sty", ".cls")):
            yield path
        for path in self._files_with((".tex",)):
            stem_files = [path.with_suffix(sfx) for sfx in (*self.SUFFIXES, ".pdf")]
            if not any(f.exists() for f in stem_files):
                yield path

    def aux_files(self):
        """작업공간 최상위의 부속 파일(.yaml/.yml/.bib)을 정렬된
        순서로 훑는다. 원고가 아니므로 BookIndex 는 이걸 보지 않는다
        — 서랍의 별도 구역에서만 쓰인다."""
        yield from self._files_with(self.AUX_SUFFIXES)

    def subfolder_groups(self, exclude_dirs=frozenset()):
        """작업공간의 하위 폴더들을, 각 폴더 밑의 파일들과 함께 묶어
        [(폴더 경로, [파일...]), ...] 로 돌려준다 — 폴더 이름 순서
        대로, 폴더 안 파일은 확장자 안 가리고 재귀적으로 다 모은다
        (그 폴더가 더 깊은 하위 폴더를 가져도).

        SKIP_DIRS·숨김 폴더는 항상 빠진다. exclude_dirs(예: 지금
        보고 있는 문서의 graphicspath: 폴더들 — 그림 전용이라 그림
        들여오기가 따로 다룬다)에 있는 폴더도 뺀다. 숨김 파일도
        asset_files() 와 같은 이유로 뺀다.
        """
        if not self:
            return []
        exclude_resolved = {Path(p).resolve() for p in exclude_dirs}
        groups = []
        for entry in sorted(self.root.iterdir()):
            if not entry.is_dir():
                continue
            if entry.name in self.SKIP_DIRS or entry.name.startswith("."):
                continue
            if entry.resolve() in exclude_resolved:
                continue
            files = []
            for path in sorted(entry.rglob("*")):
                if not path.is_file():
                    continue
                if any(part.startswith(".") for part in path.relative_to(entry).parts):
                    continue
                files.append(path)
            groups.append((entry, files))
        return groups

    def asset_files(self):
        """_assets/ 안의 파일을 전부(확장자 안 가리고) 정렬된 순서로
        훑는다. 원고·부속 파일과 달리 컴파일에 전혀 관여하지 않는
        참고자료다. 숨김 폴더뿐 아니라 파일 자신이 숨김(.으로 시작,
        예: macOS 의 .DS_Store)이어도 뺀다."""
        assets_root = self.root / self.ASSETS_DIR if self else None
        if not assets_root or not assets_root.is_dir():
            return
        for path in sorted(assets_root.rglob("*")):
            if not path.is_file():
                continue
            if any(part.startswith(".") for part in path.relative_to(assets_root).parts):
                continue
            yield path


# ===========================================================================
# 8. 찾기 바
# ===========================================================================

class FindBar(QWidget):
    """편집창 아래에 붙는 찾기/바꾸기 막대.

    모달 대화상자 대신 막대를 쓴 이유는 단순하다. 대화상자는 본문을 가리고
    포커스를 빼앗는데, 찾기는 본문을 보면서 하는 일이다. 닫으면 흔적이
    남지 않으므로 "편집 영역에 글 말고는 적게" 라는 원칙도 지킨다.
    """

    SCOPE_FILE = 0
    SCOPE_SELECTION = 1
    SCOPE_WORKSPACE = 2

    def __init__(self, window: "MainWindow"):
        super().__init__(window)
        self._win = window

        self.query = QLineEdit()
        self.query.setPlaceholderText("찾을 내용")
        self.query.setClearButtonEnabled(True)
        self.replacement = QLineEdit()
        self.replacement.setPlaceholderText("바꿀 내용")

        # Esc 를 누르면 지금 찾은 위치로 커서를 옮기고 막대를 닫는다.
        # QLineEdit 은 Esc 를 자기가 먼저 삼킬 수 있어서 이벤트 필터로 잡는다.
        self.query.installEventFilter(self)
        self.replacement.installEventFilter(self)

        self.scope = QComboBox()
        self.scope.addItems(["현재 파일", "선택 범위", "작업공간"])

        self.cb_case = QCheckBox("대소문자")
        self.cb_regex = QCheckBox("정규식")

        self.btn_prev = QToolButton(); self.btn_prev.setText("◀")
        self.btn_next = QToolButton(); self.btn_next.setText("▶")
        self.btn_replace = QPushButton("바꾸기")
        self.btn_replace_all = QPushButton("모두 바꾸기")
        self.btn_close = QToolButton(); self.btn_close.setText("✕")

        #: 찾기 줄 오른쪽 끝의 "바꾸기 열기" 토글. 두 번째 줄(바꾸기
        #: 줄)을 폭 넓은 한 줄에 다 몰아넣지 않고 따로 뺀 이유 자체가
        #: 이 버튼이다 — 좁은 노트북 화면에서 찾기 줄 하나만으로도
        #: 이미 폭이 빠듯한데, 바꾸기까지 같은 줄에 다 넣으면 넘친다.
        self.btn_toggle_replace = QToolButton()
        self.btn_toggle_replace.setText("바꾸기")
        self.btn_toggle_replace.setCheckable(True)
        self.btn_toggle_replace.setToolTip("바꾸기 줄 열기/닫기")

        #: 찾기·바꾸기 이력 목록. 입력칸에서 ↑/↓ 로도 넘겨 볼 수 있다.
        self.btn_history = QToolButton()
        self.btn_history.setText("⌄")
        self.btn_history.setToolTip("찾기·바꾸기 이력 (입력칸에서 ↑/↓)")

        self.status = QLabel()

        row1 = QHBoxLayout()
        row1.setContentsMargins(0, 0, 0, 0)
        row1.setSpacing(6)
        for w in (self.scope, self.query, self.btn_history, self.btn_prev,
                  self.btn_next, self.cb_case, self.cb_regex, self.status):
            row1.addWidget(w)
        row1.addStretch(1)
        row1.addWidget(self.btn_toggle_replace)
        row1.addWidget(self.btn_close)

        #: 바꾸기 줄 전체를 위젯 하나로 묶어 둔다 — show_replace() 가
        #: 이거 하나만 보이기/숨기기 하면 된다(안의 위젯을 하나씩
        #: 따로 다루지 않는다).
        self.replace_row = QWidget()
        row2 = QHBoxLayout(self.replace_row)
        row2.setContentsMargins(0, 0, 0, 0)
        row2.setSpacing(6)
        row2.addWidget(self.replacement, 1)
        row2.addWidget(self.btn_replace)
        row2.addWidget(self.btn_replace_all)

        outer = QVBoxLayout(self)
        outer.setContentsMargins(10, 6, 10, 6)
        outer.setSpacing(4)
        outer.addLayout(row1)
        outer.addWidget(self.replace_row)

        self.query.setMinimumWidth(180)
        self.replacement.setMinimumWidth(180)

        # 배선
        self.query.textChanged.connect(self._win.on_query_changed)
        self.query.returnPressed.connect(lambda: self._step(False))
        self.replacement.returnPressed.connect(self._replace_one)
        self.btn_next.clicked.connect(lambda: self._step(False))
        self.btn_prev.clicked.connect(lambda: self._step(True))
        self.btn_replace.clicked.connect(self._replace_one)
        self.btn_replace_all.clicked.connect(self._replace_all)
        # 사용자가 손으로 고치면 ↑/↓ 이력 탐색을 처음 상태로 되돌린다.
        self.query.textEdited.connect(self._history_reset)
        self.replacement.textEdited.connect(self._history_reset)
        self.btn_history.clicked.connect(self._show_history_menu)
        self._history_reset()
        self.btn_close.clicked.connect(self._win.close_find)
        self.btn_toggle_replace.toggled.connect(self.show_replace)
        self.scope.currentIndexChanged.connect(self._win.on_scope_changed)
        self.cb_case.toggled.connect(self._win.on_query_changed)
        self.cb_regex.toggled.connect(self._win.on_query_changed)

    # -- 조회 ---------------------------------------------------------------

    def eventFilter(self, obj, event):
        if (event.type() == QEvent.KeyPress and event.key() == Qt.Key_Escape
                and obj in (self.query, self.replacement)):
            self._win.focus_active_match()
            self._win.close_find()
            return True
        if (event.type() == QEvent.KeyPress and obj in (self.query, self.replacement)
                and event.key() in (Qt.Key_Up, Qt.Key_Down)
                and not (event.modifiers() & (Qt.ControlModifier | Qt.AltModifier | Qt.MetaModifier))):
            self._history_move(-1 if event.key() == Qt.Key_Up else 1,
                               pairs_only=(obj is self.replacement))
            return True
        return super().eventFilter(obj, event)

    # -- 이력 ---------------------------------------------------------------
    #
    # 항목 = {"q": 찾기, "r": 바꾸기(없으면 ""), "case": bool, "re": bool, "scope": 0|2}
    # 같은 글자라도 옵션이 다르면 결과가 달라지므로 옵션까지 한 항목으로 저장한다.
    # 남기는 때는 타이핑 중이 아니라 "실제로 찾거나 바꿨을 때"뿐이다.
    # 전역(앱 설정) 하나에 최근 순으로 HISTORY_MAX 개까지 둔다.

    HISTORY_MAX = 50
    HISTORY_KEY = "find/history"

    def history(self) -> list:
        if not hasattr(self, "_history"):
            self._history = []
            try:
                raw = self._win._settings.value(self.HISTORY_KEY, "")
                data = json.loads(raw) if raw else []
                for e in data:
                    if isinstance(e, dict) and isinstance(e.get("q"), str) and e["q"]:
                        self._history.append({
                            "q": e["q"], "r": str(e.get("r", "")),
                            "case": bool(e.get("case")), "re": bool(e.get("re")),
                            "scope": self.SCOPE_WORKSPACE if e.get("scope") == self.SCOPE_WORKSPACE
                                     else self.SCOPE_FILE})
            except (ValueError, TypeError):
                self._history = []
            del self._history[self.HISTORY_MAX:]
        return self._history

    def _current_entry(self, with_replacement: bool) -> dict:
        return {"q": self.query.text(),
                "r": self.replacement.text() if with_replacement else "",
                "case": self.cb_case.isChecked(), "re": self.cb_regex.isChecked(),
                "scope": self.SCOPE_WORKSPACE if self.is_workspace() else self.SCOPE_FILE}

    def remember(self, with_replacement: bool):
        """지금 입력을 이력 맨 앞에 남긴다. 찾기만 한 경우, 같은 찾기·옵션의
        항목이 이미 있으면(바꾸기 쌍이어도) 그 항목을 앞으로 올리기만 한다."""
        e = self._current_entry(with_replacement)
        if not e["q"]:
            return
        hist = self.history()
        same = [h for h in hist
                if h["q"] == e["q"] and h["case"] == e["case"] and h["re"] == e["re"]
                and (with_replacement and h["r"] == e["r"] or not with_replacement)]
        if same:
            e = same[0]
            hist.remove(e)
        hist.insert(0, e)
        del hist[self.HISTORY_MAX:]
        try:
            self._win._settings.setValue(self.HISTORY_KEY, json.dumps(hist, ensure_ascii=False))
        except (OSError, TypeError):
            pass
        self._history_reset()

    def clear_history(self):
        self._history = []
        self._win._settings.setValue(self.HISTORY_KEY, "")
        self._history_reset()

    def _history_reset(self, *_):
        self._hist_pos = -1
        self._hist_draft = None

    def apply_entry(self, e: dict):
        """이력 항목을 입력칸과 옵션에 채운다(신호는 한 번만 터지게 막는다)."""
        for w in (self.cb_case, self.cb_regex):
            w.blockSignals(True)
        self.cb_case.setChecked(e["case"])
        self.cb_regex.setChecked(e["re"])
        for w in (self.cb_case, self.cb_regex):
            w.blockSignals(False)
        if e["scope"] == self.SCOPE_WORKSPACE:
            if self.scope.currentIndex() != self.SCOPE_WORKSPACE:
                self.scope.setCurrentIndex(self.SCOPE_WORKSPACE)
        elif self.scope.currentIndex() == self.SCOPE_WORKSPACE:
            self.scope.setCurrentIndex(self.SCOPE_FILE)
        self.replacement.setText(e["r"])
        if e["r"]:
            self.show_replace(True)
        self.query.setText(e["q"])            # textChanged → 다시 찾기

    def _history_move(self, step: int, pairs_only: bool):
        """↑(-1)=더 오래된 것, ↓(+1)=더 최근 것. 맨 끝에서 ↓ 하면 쓰던 말로 돌아온다."""
        hist = [h for h in self.history() if h["r"] or not pairs_only]
        if not hist:
            return
        if self._hist_pos == -1:
            if step > 0:
                return
            self._hist_draft = self._current_entry(True)
        pos = self._hist_pos
        pos = 0 if pos == -1 else pos - step     # ↑ 는 인덱스를 늘린다
        if pos < 0:                              # 가장 최근 항목에서 ↓ → 쓰던 말
            draft, self._hist_draft = self._hist_draft, None
            self._hist_pos = -1
            if draft:
                self.apply_entry(dict(draft, scope=draft["scope"]))
            return
        pos = min(pos, len(hist) - 1)
        self._hist_pos = pos
        draft = self._hist_draft
        self.apply_entry(hist[pos])
        self._hist_draft = draft                 # apply_entry 가 지우지 않게 보존

    def _show_history_menu(self):
        hist = self.history()
        menu = QMenu(self)
        if not hist:
            act = menu.addAction("(이력 없음)")
            act.setEnabled(False)
        for e in hist[:20]:
            q = e["q"].replace("\n", "⏎")
            label = q if not e["r"] else f"{q}  →  {e['r']}"
            tags = [t for t, on in (("Aa", e["case"]), (".*", e["re"]),
                                    ("작업공간", e["scope"] == self.SCOPE_WORKSPACE)) if on]
            if tags:
                label += "    [" + " ".join(tags) + "]"
            if len(label) > 70:
                label = label[:69] + "…"
            menu.addAction(label.replace("&", "&&"),
                           lambda e=e: (self.apply_entry(e), self.query.setFocus()))
        if hist:
            menu.addSeparator()
            menu.addAction("이력 지우기", self.clear_history)
        menu.exec(self.btn_history.mapToGlobal(self.btn_history.rect().bottomLeft()))

    def _step(self, backward: bool):
        self.remember(False)
        self._win.find_step(backward)

    def _replace_one(self):
        self.remember(True)
        self._win.replace_current()

    def _replace_all(self):
        self.remember(True)
        self._win.replace_all()

    def text(self) -> str:
        return self.query.text()

    def replace_text(self) -> str:
        return self.replacement.text()

    def is_workspace(self) -> bool:
        return self.scope.currentIndex() == self.SCOPE_WORKSPACE

    def is_selection(self) -> bool:
        return self.scope.currentIndex() == self.SCOPE_SELECTION

    def case_sensitive(self) -> bool:
        return self.cb_case.isChecked()

    def use_regex(self) -> bool:
        return self.cb_regex.isChecked()

    def show_replace(self, on: bool):
        self.replace_row.setVisible(on)
        # 메뉴/단축키(open_find)로 불렸을 때도 토글 버튼 표시가 맞아야
        # 한다 — 신호를 막고 상태만 맞춰서 무한 재귀를 막는다.
        if self.btn_toggle_replace.isChecked() != on:
            self.btn_toggle_replace.blockSignals(True)
            self.btn_toggle_replace.setChecked(on)
            self.btn_toggle_replace.blockSignals(False)

    def set_status(self, text: str):
        # "정규식 없음" 처럼 체크 상자 글자와 상태가 이어 읽히지 않도록 앞에 구분선을 둔다(상태가 있을 때만).
        self.status.setText(f"│ {text}" if text else "")

    def apply_theme(self, theme: Theme):
        self.setStyleSheet(f"""
            QWidget {{ background: {theme.panel_bg}; color: {theme.fg}; }}
            QLineEdit {{
                background: {theme.bg}; color: {theme.fg};
                border: 1px solid {theme.gutter_fg};
                border-radius: 4px; padding: 3px 7px;
            }}
            QLineEdit:focus {{ border-color: {theme.heading}; }}
            QComboBox {{
                background: {theme.bg}; color: {theme.fg};
                border: 1px solid {theme.gutter_fg};
                border-radius: 4px; padding: 3px 7px;
            }}
            QComboBox QAbstractItemView {{
                background: {theme.bg}; color: {theme.fg};
                selection-background-color: {theme.current_line};
            }}
            QPushButton, QToolButton {{
                background: {theme.bg}; color: {theme.fg};
                border: 1px solid {theme.gutter_fg};
                border-radius: 4px; padding: 3px 9px;
            }}
            QPushButton:hover, QToolButton:hover {{ background: {theme.current_line}; }}
            QToolButton:checked {{
                background: {theme.match_active_bg}; color: {theme.fg};
                border-color: {theme.heading};
            }}
            QCheckBox {{ color: {theme.gutter_fg_active}; }}
            QLabel {{ color: {theme.gutter_fg_active}; }}
        """)


# ===========================================================================
# 9. 작업공간 검색 결과
# ===========================================================================

class ResultsPanel(QTreeWidget):
    """작업공간 전체 검색 결과. 파일별로 묶어서 보여준다."""

    def __init__(self, window: "MainWindow"):
        super().__init__(window)
        self._win = window
        self.setHeaderHidden(True)
        self.setRootIsDecorated(True)
        self.setUniformRowHeights(True)
        self.setSizePolicy(self.sizePolicy().horizontalPolicy(),
                           QSizePolicy.Fixed)
        self.itemActivated.connect(self._on_activate)
        self.itemClicked.connect(self._on_activate)

    def populate(self, hits):
        """hits: [(Path, [(행번호, 줄내용), ...]), ...]"""
        self.clear()
        total = 0
        for path, matches in hits:
            parent = QTreeWidgetItem(self, [
                f"{self._win.workspace.relative(path)}   ({len(matches)})"])
            parent.setData(0, Qt.UserRole, None)
            parent.setExpanded(True)
            for line_no, line_text in matches:
                child = QTreeWidgetItem(parent, [f"{line_no:>5}   {line_text.strip()[:110]}"])
                child.setData(0, Qt.UserRole, (path, line_no))
                total += 1
        self._fit_height(len(hits) + total)
        return total

    #: 결과 패널이 내용보다 크게 잡히면 본문이 이유 없이 밀린다. 줄 수에
    #: 맞춰 높이를 잡되, 결과가 많을 때를 위해 상한만 둔다.
    MAX_ROWS = 9

    def _fit_height(self, rows: int):
        if rows == 0:
            self.setFixedHeight(0)
            return
        unit = self.fontMetrics().height() + 6
        self.setFixedHeight(int(min(rows, self.MAX_ROWS) * unit) + 8)

    def _on_activate(self, item, _column=0):
        payload = item.data(0, Qt.UserRole)
        if payload:
            path, line_no = payload
            self._win.open_at(Path(path), line_no)

    def apply_theme(self, theme: Theme):
        self.setStyleSheet(f"""
            QTreeWidget {{
                background: {theme.panel_bg}; color: {theme.fg};
                border: none; border-top: 1px solid {theme.gutter_fg};
                outline: none;
            }}
            QTreeWidget::item {{ padding: 2px 4px; }}
            QTreeWidget::item:selected {{ background: {theme.match_active_bg}; color: {theme.fg}; }}
            {tree_branch_css(theme.fg)}
        """)



# ===========================================================================
# 9-a. 책 구조 — 계층의 진실은 {{포함}} 줄 자체다
# ===========================================================================

INCLUDE_LINE_RE = re.compile(r"^\s*\{\{([^{}\n]+?)\}\}\s*$")


@dataclass
class Node:
    """서랍에 그릴 항목 하나."""
    path: Path
    children: list           # list[Path], {{}} 가 적힌 순서 그대로
    parent: Path | None = None
    missing: list = None     # {{}} 는 있는데 실제 파일이 없는 이름들


class BookIndex:
    """작업공간을 훑어 "책 — 장" 두 단계 구조를 만든다.

    별도의 데이터베이스를 두지 않는다. 구조는 최상위 파일에 적힌 `{{이름}}`
    줄이 곧 전부다(ndhmd4tex 는 포함 단계에 제한이 없지만, 이 앱은 책▸장▸
    하위의 2단계까지만 구조로 다룬다). 색인을 따로 두면 파일과 어긋날 여지가 생기는데, 진실이 하나뿐인
    쪽이 언제나 낫다. 사용자가 main.md 를 손으로 고쳐도 서랍이 저절로 맞다.
    """

    def __init__(self, workspace: Workspace):
        self.ws = workspace
        self.roots: list = []
        self.by_path: dict = {}

    # -- 읽기 ---------------------------------------------------------------

    @staticmethod
    def read_includes(path: Path) -> list:
        """파일에 줄 단위로 적힌 {{이름}} 들을 순서대로 돌려준다."""
        try:
            lines = read_manuscript(path).splitlines()
        except (OSError, UnicodeDecodeError):
            return []
        out = []
        for line in lines:
            m = INCLUDE_LINE_RE.match(line)
            if m:
                out.append(m.group(1).strip())
        return out

    def scan(self):
        files = list(self.ws.source_files())
        includes = {p: self.read_includes(p) for p in files}

        resolved, parent_of = {}, {}
        for parent, names in includes.items():
            kids, missing = [], []
            for name in names:
                if "/" in name or "\\" in name:
                    # {{sub/ch1.md}} 는 문법상 유효하지만(파일은 찾아지지만)
                    # 서랍이 다루는 것은 "같은 폴더 안의 한 단계"뿐이다.
                    # 여기서 자식으로 편입하지 않고 missing 취급해 두면
                    # 드래그 대상이 되지 않고 서랍에 경고로만 보인다.
                    missing.append(f"{name}  (하위 폴더 — 서랍 미지원)")
                    continue
                target = (parent.parent / name).resolve()
                if target in includes and target != parent:
                    # 이미 다른 부모에게 속했으면 첫 부모를 따른다.
                    if target not in parent_of:
                        parent_of[target] = parent
                        kids.append(target)
                else:
                    missing.append(name)
            resolved[parent] = (kids, missing)

        self.by_path = {}
        self.roots = []
        for path in files:
            kids, missing = resolved[path]
            node = Node(path=path, children=kids,
                        parent=parent_of.get(path), missing=missing)
            self.by_path[path] = node
        for path in files:
            if self.by_path[path].parent is None:
                self.roots.append(self.by_path[path])
        return self.roots

    # -- 검사 ---------------------------------------------------------------

    def can_nest(self, src: Path, parent: Path):
        """src 를 parent 아래로 넣을 수 있는가. 안 되면 이유를 돌려준다.

        2단계까지 허용한다. parent 자신이 이미 누군가의 장(1단계)
        이어도 괜찮다(그러면 src 는 2단계가 된다) — 하지만 parent 가
        이미 2단계(즉 parent 의 parent 도 parent 가 있음)라면, 그
        아래에 또 넣는 것은 3단계가 되므로 막는다.
        """
        if src == parent:
            return False, "자기 자신에는 넣을 수 없습니다."
        s, p = self.by_path.get(src), self.by_path.get(parent)
        if s is None or p is None:
            return False, "작업공간 밖의 파일입니다."
        if p.parent is not None:
            grandparent = self.by_path.get(p.parent)
            if grandparent is not None and grandparent.parent is not None:
                return False, ("포함은 2단계까지만 지원됩니다.\n"
                               f"{p.path.name} 은(는) 이미 2단계(하위 파일)입니다.")
        if s.children:
            return False, (f"{src.name} 이(가) 이미 다른 원고를 포함하고 "
                           f"있습니다.\n포함은 2단계까지만 지원됩니다.")
        if s.parent == parent:
            return False, None          # 이미 그 자리 — 조용히 무시
        if src.parent != parent.parent:
            return False, ("{{이름}} 은 최상위 파일과 같은 폴더에서 찾습니다.\n"
                           "같은 폴더 안에서만 묶을 수 있습니다.")
        return True, None

    # -- 쓰기 ---------------------------------------------------------------

    @staticmethod
    def set_includes(path: Path, names: list) -> bool:
        """파일의 {{}} 줄 전체를 names 로 교체한다.

        넣기·빼기·순서 바꾸기가 전부 이 한 연산으로 표현된다. 첫 번째
        포함 줄이 있던 자리에 새 목록을 통째로 넣고 나머지는 지운다.
        하나도 없었으면 파일 끝에 붙인다.
        """
        try:
            text = read_manuscript(path)
        except (OSError, UnicodeDecodeError):
            return False
        lines = text.splitlines()
        keep, slot = [], None
        for line in lines:
            if INCLUDE_LINE_RE.match(line):
                if slot is None:
                    slot = len(keep)
                continue
            keep.append(line)
        block = []
        for n in names:
            if block:
                block.append("")   # ndhmd4tex 는 {{}} 를 각각 별개의 문단으로
                                   # 봐야 한다 — 빈 줄 없이 붙으면 한 문단으로
                                   # 뭉쳐 의도와 다르게 해석된다.
            block.append(f"{{{{{n}}}}}")
        if slot is None:
            while keep and not keep[-1].strip():
                keep.pop()
            if keep and block:
                keep.append("")
            keep.extend(block)
        else:
            keep[slot:slot] = block
        if not block:
            # 다 빼고 나면 뒤에 남은 빈 줄까지 정리한다.
            while keep and not keep[-1].strip():
                keep.pop()

        # 기존 포함 줄 사이에 있던 빈 줄이 새 block 의 빈 줄과 겹쳐 연달아
        # 여러 줄이 되는 경우가 있다(교체 위치 바로 다음). 셋 이상이면
        # 굳이 남겨 둘 이유가 없으니 하나로 눌러 둔다 — 파싱에는 지장이
        # 없지만 파일이 지저분해 보인다.
        tidy = []
        for line in keep:
            if not line.strip() and tidy and not tidy[-1].strip():
                continue
            tidy.append(line)
        keep = tidy

        out = "\n".join(keep)
        if text.endswith("\n") or not out.endswith("\n"):
            out += "\n"
        try:
            path.write_text(out, encoding="utf-8")
        except OSError:
            return False
        return True


# ===========================================================================
# 9-b. 태그 — 앱 안에서만 쓰는 검색용 표지
# ===========================================================================

#: 파일 맨 끝에 이 형태의 주석이 있으면 그 안의 #태그를 "이 파일에 박힌
#: 태그"로 본다 — TAGS 는 대문자만 인정한다(소문자·혼합 표기는
#: 태그 주석으로 보지 않는다). 맨 끝에서만 인정한다(따라서 이 정규식은 문자열의 끝
#: 을 강제한다) — 본문 중간에 우연히 비슷한 게 있어도 무시된다.
#: 단, 주석 뒤에 **빈 줄**과 **`{{…}}` 포함 줄**은 와도 된다 — 앱이 책 구조를 고칠 때(포함 줄 추가·재배열)
#: 파일 끝에 `{{…}}` 줄을 덧붙이기 때문이다. 그 밖의 글이 뒤따르면 맨 끝이 아니므로 무시한다.
INLINE_TAGS_RE = re.compile(
    r"<!--\s*TAGS:\s*(.*?)\s*-->[ \t]*(?:\r?\n[ \t]*(?:\{\{[^{}\n]+\}\}[ \t]*)?)*$")


def extract_inline_tags(text: str) -> list:
    """파일 맨 끝의 `<!--TAGS: #a #b -->` 주석에서 태그를 뽑는다.

    이 방식을 고른 이유: 파일을 옮기거나 남에게 전달해도 이 태그는
    파일 자체에 그대로 붙어 있다 — 작업공간 사이드카(tags.json)에
    두는 보통의 태그와 정반대다. YAML front matter 에 심는 방법도
    생각해 봤지만, 그러면 ndhmd4tex 이 그걸 조판 설정으로 오인할 수
    있어 배제했다.
    """
    m = INLINE_TAGS_RE.search(text.rstrip())
    if not m:
        return []
    return [tok[1:] for tok in m.group(1).split() if tok.startswith("#") and len(tok) > 1]


#: @type{citekey, ... 형태를 찾는다. 완전한 BibTeX 파서가 아니다 —
#: citekey 는 정확히 뽑되, 그 뒤 내용은 "다음 @항목 시작 전까지"로만
#: 대충 자른다(중첩된 {} 안에 또 @이 나오는 기이한 경우까지 대비할
#: 필요는 없다).
BIB_ENTRY_RE = re.compile(r"@(\w+)\s*\{\s*([^,\s}]+)\s*,")
#: title = {...} 또는 title = "..." 둘 다 받는다. 여러 줄에 걸칠 수
#: 있어 DOTALL.
BIB_TITLE_RE = re.compile(r'title\s*=\s*[{"](.+?)[}"]\s*(?=[,}]|$)',
                          re.IGNORECASE | re.DOTALL)
#: author 도 title 과 같은 요령으로 뽑는다 — 인용 삽입 패널에서 저자명
#: 필터링에 쓴다.
BIB_AUTHOR_RE = re.compile(r'author\s*=\s*[{"](.+?)[}"]\s*(?=[,}]|$)',
                           re.IGNORECASE | re.DOTALL)


def extract_bib_entries(text: str) -> list:
    """.bib 파일에서 (citekey, 제목 또는 None, 저자 또는 None) 목록을 뽑는다.

    완전한 BibTeX/biblatex 파서를 만들지 않는다 — JabRef 같은 전용
    도구가 이미 훨씬 잘한다. 이건 "bib 인용 삽입" 패널에서 "이 citekey가
    뭐였더라"만 알아보게 해 주는 가벼운 훑기다. author 는 필터링에 쓴다
    — .bib 하나에 수십, 수백 개가 흔해서 저자명으로 좁힐 수 있어야
    쓸 만하다.
    """
    matches = list(BIB_ENTRY_RE.finditer(text))
    entries = []
    for i, m in enumerate(matches):
        key = m.group(2)
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        body = text[start:end]
        title_m = BIB_TITLE_RE.search(body)
        title = re.sub(r"\s+", " ", title_m.group(1)).strip() if title_m else None
        author_m = BIB_AUTHOR_RE.search(body)
        author = re.sub(r"\s+", " ", author_m.group(1)).strip() if author_m else None
        entries.append((key, title, author))
    return entries


def find_bibliography_range_in_lines(lines: list):
    """텍스트(줄 목록) 안 첫 :::{thebibliography ...} ~ ::: 블록의
    (여는 줄 번호, 닫는 줄 번호). Editor.bibliography_range() 와 같은
    규칙이지만 QTextDocument 가 아니라 평범한 줄 목록에 대해 쓸 수
    있다 — 지금 편집기에 안 열려 있는 책의 다른 파일도 훑어야
    하므로. 없거나 닫는 ::: 를 못 찾으면 None.
    """
    fence = 0                      # 코드 펜스 안의 예시는 건너뛴다
    for i, line in enumerate(lines):
        if fence:
            m = FENCE_CLOSE_RE.match(line)
            if m and len(m.group(1)) >= fence:
                fence = 0
            continue
        m = FENCE_OPEN_LOOSE_RE.match(line)
        if m:
            fence = len(m.group(1))
            continue
        if BIBLIOGRAPHY_OPEN_RE.match(line):
            for j in range(i + 1, len(lines)):
                if ENV_CLOSE_RE.match(lines[j]):
                    return (i, j)
            return None
    return None


def parse_bibitem_lines(lines: list, delimiter: str = ",") -> list:
    """`:::{thebibliography}` 안의 줄들에서 (option, citekey, author, others)
    목록을 뽑는다.

    빈 줄로 나뉜 문단마다 \\bibitem 하나로 본다 — 저장할 때 항목 사이에
    빈 줄을 넣어 두는 것과 짝을 맞춘 것이다(안 그러면 ndhmd4tex 이 여러
    \\bibitem 을 한 문단으로 이어붙인다). author/others 는 완벽하게
    되짚을 수 없다 — 저장할 때 쓴 구분자(delimiter — 쉼표 또는 마침표,
    설정을 따른다)를 그대로 거슬러 올라갈 뿐이다. 첫 구분자 기준으로
    나누고, 없으면 전부 author 쪽에 둔다.
    """
    paragraphs = []
    current = []
    for line in lines:
        if line.strip():
            current.append(line.strip())
        else:
            if current:
                paragraphs.append(" ".join(current))
                current = []
    if current:
        paragraphs.append(" ".join(current))

    out = []
    for para in paragraphs:
        m = BIBITEM_RE.match(para)
        if not m:
            continue
        option = m.group(1) or ""
        key = m.group(2)
        rest = m.group(3)
        if delimiter in rest:
            author, others = rest.split(delimiter, 1)
            author, others = author.strip(), others.strip()
        else:
            author, others = rest.strip(), ""
        out.append((option, key, author, others))
    return out


class TagStore:
    """원고에 손대지 않고 태그를 따로 보관한다.

    태그는 검색을 위한 것이지 출판물의 일부가 아니다. 원고에 적어 넣으면
    ndhmd4tex 가 그걸 본문으로 조판하게 되므로, 작업공간 안의 사이드카
    파일에 둔다. `.ndhmd` 는 작업공간 훑기에서 이미 제외된다.
    """

    FILENAME = "tags.json"

    def __init__(self, workspace: Workspace):
        self.ws = workspace
        self._map = {}
        self.load()

    @property
    def store_path(self):
        return self.ws.root / ".ndhmd" / self.FILENAME if self.ws else None

    def load(self):
        self._map = {}
        path = self.store_path
        if not path or not path.exists():
            return
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            return
        if isinstance(data, dict):
            self._map = {k: list(v) for k, v in data.items()
                         if isinstance(v, list)}

    def save(self):
        path = self.store_path
        if not path:
            return
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(
                json.dumps(self._map, ensure_ascii=False, indent=1, sort_keys=True),
                encoding="utf-8")
        except OSError:
            pass

    def prune(self) -> int:
        """없어진 파일의 태그를 지운다. 지운 개수를 돌려준다."""
        if not self.ws:
            return 0
        alive = ({self.ws.relative(p) for p in self.ws.source_files()}
                | {self.ws.relative(p) for p in self.ws.aux_files()})
        before = len(self._map)
        self._map = {k: v for k, v in self._map.items() if k in alive}
        removed = before - len(self._map)
        if removed:
            self.save()
        return removed

    def get(self, path: Path) -> list:
        """작업공간에 저장해 둔 태그만. 이름 바꾸기·복제에서 옮겨 줄 때는
        이걸 쓴다 — 파일에 박힌 태그(get_active 가 더해 주는 것)는 파일
        자체를 따라가므로 사이드카 키 이전과 무관하다."""
        return list(self._map.get(self.ws.relative(path), []))

    def get_active(self, path: Path, live=None) -> list:
        """지금 이 파일에 걸려 있는 태그 전부 — 서랍 표시·필터·태그
        편집줄이 쓴다.

        저장해 둔 태그 뒤에, 파일 맨 끝의 `<!--TAGS: #a #b -->` 주석에서
        뽑은 것을 그대로 이어붙인다. 그 태그는 사이드카가 아니라 파일
        자체에 있으므로, 파일을 옮기거나 남에게 전달해도 그대로
        살아있다 — 이게 존재 이유다. 휘발성 정보라 중복은 신경 쓰지
        않는다.
        """
        tags = self.get(path)
        text = live(path) if live else None
        if text is None:
            try:
                text = read_manuscript(path)
            except (OSError, UnicodeDecodeError):
                text = ""
        return tags + extract_inline_tags(text)

    def set(self, path: Path, tags: list):
        key = self.ws.relative(path)
        tags = [tg for tg in dict.fromkeys(tg.strip() for tg in tags) if tg]
        if tags:
            self._map[key] = tags
        else:
            self._map.pop(key, None)
        self.save()

    def all_tags(self) -> list:
        return sorted({tg for tags in self._map.values() for tg in tags})

    def all_active_tags(self) -> list:
        """작업공간에 실제로 쓰이고 있는 태그 전부 — 사이드카에 저장된
        것과 각 파일 끝의 `<!--TAGS: ...-->` 주석에서 뽑은 것을 합쳐
        정렬해 돌려준다. 서랍 필터 콤보를 채우는 데 쓴다."""
        tags = {tg for tags in self._map.values() for tg in tags}
        if self.ws:
            for path in list(self.ws.source_files()) + list(self.ws.aux_files()):
                try:
                    text = read_manuscript(path)
                except (OSError, UnicodeDecodeError):
                    continue
                tags.update(extract_inline_tags(text))
        return sorted(tags)

    def matches(self, path: Path, needle: str) -> bool:
        needle = needle.lstrip("#").lower()
        return any(needle in tg.lower() for tg in self.get_active(path))

    @staticmethod
    def parse(text: str) -> list:
        """'#초고 #1장 미분류' → ['초고', '1장', '미분류']"""
        return [tok.lstrip("#") for tok in text.replace(",", " ").split() if tok.strip("#")]

    @staticmethod
    def format(tags: list) -> str:
        return " ".join(f"#{tg}" for tg in tags)


class NoteStore:
    """문서에 딸린 메모를 태그와 같은 자리(.ndhmd/)에, 다른 파일로 둔다.

    inline 표기 규칙이나 "이번 주까지" 같은 걸 적어 두는 자리다. 파일
    내용에는 안 남는다 — 태그와 같은 이유다: 파일을 옮기면 이 메모는
    안 따라간다. 그게 의도다(파일 자체에 남기고 싶으면 사용자가 직접
    본문이나 주석으로 적으면 된다).
    """

    FILENAME = "notes.json"

    def __init__(self, workspace: Workspace):
        self.ws = workspace
        self._map = {}
        self.load()

    @property
    def store_path(self):
        return self.ws.root / ".ndhmd" / self.FILENAME if self.ws else None

    def load(self):
        self._map = {}
        path = self.store_path
        if not path or not path.exists():
            return
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            return
        if isinstance(data, dict):
            self._map = {k: v for k, v in data.items() if isinstance(v, str)}

    def save(self):
        path = self.store_path
        if not path:
            return
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(
                json.dumps(self._map, ensure_ascii=False, indent=1, sort_keys=True),
                encoding="utf-8")
        except OSError:
            pass

    def prune(self) -> int:
        """없어진 파일의 메모를 지운다. 지운 개수를 돌려준다."""
        if not self.ws:
            return 0
        alive = ({self.ws.relative(p) for p in self.ws.source_files()}
                | {self.ws.relative(p) for p in self.ws.aux_files()})
        before = len(self._map)
        self._map = {k: v for k, v in self._map.items() if k in alive}
        removed = before - len(self._map)
        if removed:
            self.save()
        return removed

    def get(self, path: Path) -> str:
        if not self.ws or path is None:
            return ""
        return self._map.get(self.ws.relative(path), "")

    def has(self, path: Path) -> bool:
        return bool(self.get(path))

    def set(self, path: Path, text: str):
        if not self.ws or path is None:
            return
        key = self.ws.relative(path)
        text = text.strip()
        if text:
            self._map[key] = text
        else:
            self._map.pop(key, None)
        self.save()


class SynopsisStore(NoteStore):
    """원고 파일마다 붙이는 시놉시스(.ndhmd/synopsis.json). 저장·이름 바꿈 이관·정리는 메모(NoteStore)와
    같은 규칙이고, 메모가 "이 문서에 대한 쪽지"인 데 비해 이쪽은 책을 훑어볼 때 보는 한두 줄 요약이다."""

    FILENAME = "synopsis.json"


class SlotStore:
    """약어 슬롯 10개. 1~5번은 **전역**(앱 설정), 6~9·0번은 **현재 책**(작업공간의 .ndhmd/slots.json).
    키는 "1".."9","0" 문자열이다. 자주 쓰는 문구는 전역에, 소설마다 다른 인물 이름 같은 것은 책별로 둔다."""

    FILENAME = "slots.json"
    KEYS = "1234567890"
    GLOBAL_KEYS = "12345"

    def __init__(self, workspace, settings):
        self.ws = workspace
        self.settings = settings
        self._book = {}
        self.load()

    @classmethod
    def is_global(cls, key: str) -> bool:
        return key in cls.GLOBAL_KEYS

    @property
    def store_path(self):
        return self.ws.root / ".ndhmd" / self.FILENAME if self.ws else None

    def load(self):
        self._book = {}
        path = self.store_path
        if not path or not path.exists():
            return
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            return
        if isinstance(data, dict):
            self._book = {k: v for k, v in data.items() if k in self.KEYS and isinstance(v, str)}

    def book_available(self) -> bool:
        return self.ws is not None

    def get(self, key: str) -> str:
        if self.is_global(key):
            return self.settings.value(f"slots/{key}", "", type=str)
        return self._book.get(key, "")

    def set(self, key: str, text: str) -> bool:
        """저장한다. 책별 슬롯인데 책(작업공간)이 없으면 False."""
        if self.is_global(key):
            if text:
                self.settings.setValue(f"slots/{key}", text)
            else:
                self.settings.remove(f"slots/{key}")
            return True
        path = self.store_path
        if not path:
            return False
        if text:
            self._book[key] = text
        else:
            self._book.pop(key, None)
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(self._book, ensure_ascii=False, indent=1, sort_keys=True),
                            encoding="utf-8")
        except OSError:
            return False
        return True


# ===========================================================================
# 9-c. 서랍
# ===========================================================================

#: 카드 보기 ↔ 서랍 사이 끌어놓기에 쓰는 마임 형식. 줄바꿈으로 구분한 파일 경로 목록을 싣는다.
CARD_MIME = "application/x-ndhmd-card"
DRAWER_MIME = "application/x-ndhmd-drawer-paths"


class DrawerTree(QTreeWidget):
    """책 — 장 두 단계를 보여주는 나무. 그 아래 접히는 "부속 파일" 구역이
    하나 더 붙는다(원고가 아닌 .yaml/.bib 등 — 평평하고, 끌어놓기 대상이
    아니다).

    끌어놓기는 Qt 에 맡기지 않고 직접 처리한다. Qt 가 항목을 옮기게 두면
    화면과 파일이 잠깐 어긋나는데, 여기서는 파일이 진실이므로 화면을
    먼저 바꾸는 순서 자체가 틀렸다. 떨어뜨린 위치만 읽어서 포함 줄을
    고치고, 다시 훑어 그린다.
    """

    #: 부속 파일 구역 헤더 항목임을 표시하는 표식. 실제 파일 경로와
    #: 절대 겹치지 않도록 널 바이트를 섞어 둔다.
    AUX_HEADER_MARKER = "\x00aux\x00"
    #: 자료 창고 구역 헤더 표식.
    ASSETS_HEADER_MARKER = "\x00assets\x00"
    #: 하위 폴더 구역 헤더 표식 — 폴더마다 하나씩 생긴다.
    SUBFOLDER_HEADER_MARKER = "\x00subfolder\x00"
    #: 컴파일 참고 구역 헤더 표식.
    NOTES_HEADER_MARKER = "\x00notes\x00"

    def __init__(self, window: "MainWindow"):
        super().__init__(window)
        self._win = window
        self.setHeaderHidden(True)
        self.setRootIsDecorated(True)
        self.setUniformRowHeights(True)
        self.setDragDropMode(QTreeWidget.InternalMove)
        self.setSelectionMode(QTreeWidget.ExtendedSelection)
        self.setExpandsOnDoubleClick(False)
        self.itemClicked.connect(self._on_click)
        self.setMouseTracking(True)          # 📝 위에서 손가락 커서를 보이려면 필요하다
        self._press_pos = None
        self.itemExpanded.connect(self._on_expand_toggle)
        self.itemCollapsed.connect(self._on_expand_toggle)
        self.setContextMenuPolicy(Qt.CustomContextMenu)
        self.customContextMenuRequested.connect(self._menu)

    def _on_expand_toggle(self, item):
        if item.data(0, Qt.UserRole) == self.AUX_HEADER_MARKER:
            self._win._aux_expanded = item.isExpanded()
        elif item.data(0, Qt.UserRole) == self.ASSETS_HEADER_MARKER:
            self._win._assets_expanded = item.isExpanded()
        elif item.data(0, Qt.UserRole) == self.NOTES_HEADER_MARKER:
            self._win._notes_expanded = item.isExpanded()
        elif item.data(0, Qt.UserRole) == self.SUBFOLDER_HEADER_MARKER:
            folder_str = item.data(0, Qt.UserRole + 2)
            if folder_str:
                self._win._subfolder_expanded[folder_str] = item.isExpanded()
        elif item.childCount() and item.data(0, Qt.UserRole + 1) is None:
            key = item.data(0, Qt.UserRole)
            if key:                                  # 책·장 항목(경로 문자열)
                if item.isExpanded():
                    self._win._collapsed_books.discard(key)
                else:
                    self._win._collapsed_books.add(key)

    NOTE_MARK = "📝"

    def _note_mark_rect(self, item):
        """항목 글자 중 `📝 메모` 가 차지하는 사각형(뷰포트 좌표). 없으면 None.
        글자 영역은 스타일이 정한 대로 구하고, 앞 글자들의 폭만큼 오른쪽으로 민다."""
        text = item.text(0)
        if not text.startswith(self.NOTE_MARK):
            return None
        k = 0
        idx = self.indexFromItem(item)
        opt = QStyleOptionViewItem()
        opt.initFrom(self.viewport())
        opt.rect = self.visualRect(idx)
        opt.font = item.font(0) if item.font(0) != QFont() else self.font()
        opt.text = text
        opt.features |= QStyleOptionViewItem.HasDisplay
        opt.decorationSize = self.iconSize()
        if not item.icon(0).isNull():
            opt.features |= QStyleOptionViewItem.HasDecoration
        r = self.style().subElementRect(QStyle.SE_ItemViewItemText, opt, self)
        fm = QFontMetrics(opt.font)
        margin = self.style().pixelMetric(QStyle.PM_FocusFrameHMargin, opt, self) + 1
        x0 = r.left() + margin + fm.horizontalAdvance(text[:k])
        w = fm.horizontalAdvance(self.NOTE_MARK)
        return QRect(x0, r.top(), w, r.height())

    def _note_mark_at(self, pos):
        item = self.itemAt(pos)
        if item is None:
            return None
        r = self._note_mark_rect(item)
        return item if (r is not None and r.contains(pos)) else None

    def mousePressEvent(self, e):
        self._press_pos = e.position().toPoint()
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        over = self._note_mark_at(e.position().toPoint()) is not None
        self.viewport().setCursor(Qt.PointingHandCursor if over else Qt.ArrowCursor)
        super().mouseMoveEvent(e)

    def _on_click(self, item, _col=0):
        if len(self.selectedItems()) > 1:
            return                      # 여러 개를 고르는 중 — 매번 열지 않는다
        if self._press_pos is not None and self._note_mark_at(self._press_pos) is item:
            p = item.data(0, Qt.UserRole)
            if p and p not in (self.AUX_HEADER_MARKER, self.ASSETS_HEADER_MARKER,
                               self.SUBFOLDER_HEADER_MARKER, self.NOTES_HEADER_MARKER):
                self._win.focus_note_of(Path(p))
                return
        path = item.data(0, Qt.UserRole)
        if not path or path in (self.AUX_HEADER_MARKER, self.ASSETS_HEADER_MARKER,
                                self.SUBFOLDER_HEADER_MARKER, self.NOTES_HEADER_MARKER):
            return
        tag = item.data(0, Qt.UserRole + 1)
        if tag == "note":
            self._win.peek_file(Path(path))   # 한 번 클릭 = 내용 훑어보기(편집창에 안 띄운다)
            return
        if tag in ("asset", "subfolder"):
            return   # 자료 창고·하위 폴더 항목은 클릭으로 아무 것도 안 한다 — 우클릭으로만
        self._win.open_from_drawer(Path(path))

    def _menu(self, pos):
        item = self.itemAt(pos)
        if item is None:
            return
        raw = item.data(0, Qt.UserRole)
        if not raw or raw in (self.AUX_HEADER_MARKER, self.ASSETS_HEADER_MARKER,
                              self.SUBFOLDER_HEADER_MARKER, self.NOTES_HEADER_MARKER):
            return                      # 구역 헤더 — 우클릭 메뉴가 없다
        tag = item.data(0, Qt.UserRole + 1)
        if tag == "note":
            self._note_menu(pos, Path(raw))
            return
        if tag == "asset":
            self._asset_menu(pos, Path(raw))
            return
        if tag == "subfolder":
            self._subfolder_menu(pos, Path(raw))
            return
        if item not in self.selectedItems():
            self.setCurrentItem(item)   # 다중 선택 중이면 그 선택을 지우지 않는다
        path = Path(raw)
        menu = QMenu(self)
        menu.addAction("파일명 복사(&C)").triggered.connect(
            lambda: QApplication.clipboard().setText(path.name))
        menu.addSeparator()
        menu.addAction("이름 변경(&R)…").triggered.connect(
            lambda: self._win.rename_item(path))
        node = self._win.index.by_path.get(path)
        if node is not None:
            sub = menu.addMenu("구조")
            sub.addAction("장별로 자르기…").triggered.connect(
                lambda: (self._win.open_from_drawer(path), self._win.split_into_chapters()))
            merge_act = sub.addAction("하위 파일 합치기…")
            merge_act.setEnabled(bool(node.children))
            merge_act.triggered.connect(
                lambda: (self._win.open_from_drawer(path), self._win.merge_subfiles()))
        menu.addAction("복제(&D)").triggered.connect(
            lambda: self._win.duplicate_item(path))
        menu.addSeparator()
        reveal_label = "파인더에서 보기" if sys.platform == "darwin" else "탐색기에서 보기"
        menu.addAction(reveal_label).triggered.connect(
            lambda: self._win.reveal_in_file_manager(path))
        menu.addAction("자료 창고로 이동(&A)").triggered.connect(
            lambda: self._win.move_to_assets(path))
        menu.addSeparator()
        act = menu.addAction("삭제(&X)")
        act.triggered.connect(lambda: self._win.delete_item(path))
        menu.exec(self.viewport().mapToGlobal(pos))

    def _note_menu(self, pos, path: Path):
        """컴파일 참고 항목의 우클릭 메뉴 — 보고 열고 지우기만 한다(원고가 아니다)."""
        menu = QMenu(self)
        peek_act = menu.addAction("훑어보기(&P)…")
        open_act = menu.addAction("시스템 편집기로 열기(&E)")
        copy_act = menu.addAction("파일명 복사(&C)")
        reveal_act = menu.addAction(
            "파인더에서 보기" if sys.platform == "darwin" else "탐색기에서 보기")
        del_act = None
        if path.name in Workspace.COMPILE_NOTE_NAMES:
            # 컴파일러가 다시 만들어 주는 참고 파일만 앱에서 지운다. .sty/.cls/.tex 는 사용자의
            # 파일이므로 지우기를 주지 않는다(탐색기에서 직접).
            menu.addSeparator()
            del_act = menu.addAction("삭제(&X)…")
        action = menu.exec(self.viewport().mapToGlobal(pos))
        if action == peek_act:
            self._win.peek_file(path)
        elif action == open_act:
            QDesktopServices.openUrl(QUrl.fromLocalFile(str(path)))
        elif action == copy_act:
            QApplication.clipboard().setText(path.name)
        elif action == reveal_act:
            self._win.reveal_in_file_manager(path)
        elif del_act is not None and action == del_act:
            self._win.delete_compile_note(path)

    def _asset_menu(self, pos, path: Path):
        """자료 창고 항목의 우클릭 메뉴. 저장·편집은 전부 시스템에
        맡긴다 — 여기서는 훑어보기·열기·작업공간으로 옮기기만
        한다."""
        menu = QMenu(self)
        copy_act = menu.addAction("파일명 복사(&C)")
        peek_act = menu.addAction("훑어보기(&P)…")
        menu.addSeparator()
        open_act = menu.addAction("열기")
        move_act = menu.addAction("작업공간으로 이동(&W)")
        reveal_act = menu.addAction(
            "파인더에서 보기" if sys.platform == "darwin" else "탐색기에서 보기")
        action = menu.exec(self.viewport().mapToGlobal(pos))
        if action == copy_act:
            QApplication.clipboard().setText(path.name)
        elif action == peek_act:
            self._win.peek_file(path)
        elif action == open_act:
            QDesktopServices.openUrl(QUrl.fromLocalFile(str(path)))
        elif action == move_act:
            self._win.move_to_workspace_root(path)
        elif action == reveal_act:
            self._win.reveal_in_file_manager(path)

    def _subfolder_menu(self, pos, path: Path):
        """하위 폴더 항목의 우클릭 메뉴. 자료 창고 항목과 거의
        같다 — 다만 "자료 창고로 이동"이 있고("자료 창고" 항목
        자신에는 그게 필요 없다), 임의의 다른 폴더로 옮기는 기능은
        없다(그럴 일이 있으면 파인더/탐색기로 직접 하면 된다)."""
        menu = QMenu(self)
        copy_act = menu.addAction("파일명 복사(&C)")
        peek_act = menu.addAction("훑어보기(&P)…")
        menu.addSeparator()
        open_act = menu.addAction("열기")
        to_root_act = menu.addAction("작업공간으로 이동(&W)")
        to_assets_act = menu.addAction("자료 창고로 이동(&A)")
        reveal_act = menu.addAction(
            "파인더에서 보기" if sys.platform == "darwin" else "탐색기에서 보기")
        action = menu.exec(self.viewport().mapToGlobal(pos))
        if action == copy_act:
            QApplication.clipboard().setText(path.name)
        elif action == peek_act:
            self._win.peek_file(path)
        elif action == open_act:
            QDesktopServices.openUrl(QUrl.fromLocalFile(str(path)))
        elif action == to_root_act:
            self._win.move_to_workspace_root(path)
        elif action == to_assets_act:
            self._win.move_to_assets(path)
        elif action == reveal_act:
            self._win.reveal_in_file_manager(path)

    def mimeData(self, items):
        md = super().mimeData(items)
        paths = []
        for it in items:
            raw = it.data(0, Qt.UserRole)
            if raw and Path(raw) in self._win.index.by_path:
                paths.append(str(raw))
        if paths:
            md.setData(DRAWER_MIME, "\n".join(paths).encode("utf-8"))
        return md

    def dragEnterEvent(self, event):
        if event.mimeData().hasFormat(CARD_MIME):
            event.acceptProposedAction()
            return
        super().dragEnterEvent(event)

    def dragMoveEvent(self, event):
        if event.mimeData().hasFormat(CARD_MIME):
            event.acceptProposedAction()
            return
        super().dragMoveEvent(event)

    def dropEvent(self, event):
        if event.mimeData().hasFormat(CARD_MIME):
            # 카드 보기에서 끌어온 카드 — 항목 위면 그 아래로, 빈 곳이면 책에서 뺀다.
            raw = bytes(event.mimeData().data(CARD_MIME)).decode("utf-8")
            paths = [Path(x) for x in raw.split("\n") if x]
            item = self.itemAt(event.position().toPoint())
            event.setDropAction(Qt.IgnoreAction)
            event.accept()
            target = None
            if item is not None:
                tp = item.data(0, Qt.UserRole)
                if not tp or Path(tp) not in self._win.index.by_path:
                    return              # 구역 헤더·부속 파일 위 — 아무 일도 하지 않는다
                target = Path(tp)
            self._win.handle_card_drop_on_drawer(paths, target)
            return
        selected = set(self.selectedItems())
        pos = event.position().toPoint()
        target_item = self.itemAt(pos)
        where = self.dropIndicatorPosition()
        # Qt 가 항목을 움직이지 못하게 막고 우리가 처리한다.
        event.setDropAction(Qt.IgnoreAction)
        event.accept()
        if not selected:
            return

        # selectedItems() 의 순서는 고른 순서라 화면 순서와 다를 수 있다.
        # 트리에 보이는 순서대로 처리해야 여러 개를 한꺼번에 옮겨도
        # 서로의 상대 순서가 유지된다.
        ordered = []
        it = QTreeWidgetItemIterator(self)
        while it.value():
            if it.value() in selected:
                ordered.append(it.value())
            it += 1

        srcs = [Path(p) for w in ordered
               for p in [w.data(0, Qt.UserRole)] if p]
        target = target_item.data(0, Qt.UserRole) if target_item else None
        self._win.handle_drawer_drop_multi(
            srcs,
            Path(target) if target else None,
            where == QTreeWidget.OnItem,
            where == QTreeWidget.OnViewport)

    def apply_theme(self, theme: Theme):
        self.setStyleSheet(f"""
            QTreeWidget {{
                background: {theme.panel_bg}; color: {theme.fg};
                border: none; outline: none; padding: 4px 0;
            }}
            QTreeWidget::item {{ padding: 3px 4px; border-radius: 3px; }}
            QTreeWidget::item:hover {{ background: {theme.current_line}; }}
            QTreeWidget::item:selected {{ background: {theme.match_active_bg}; color: {theme.fg}; }}
            {tree_branch_css(theme.fg)}
        """)


class Drawer(QWidget):
    """왼쪽 서랍 — 거르개 한 줄과 나무.

    거르개는 평범한 QLineEdit다 — 직접 타이핑해도 되고(이름 검색,
    공백으로 구분한 여러 #태그), 그 옆 "#" 버튼을 누르면 작업공간에
    쓰이고 있는 태그 메뉴가 펼쳐져 거기서 골라도 된다. 메뉴에서
    고르면 입력창 뒤에 이어 붙는다 — 그래서 메뉴로 여러 태그를
    계속 고르면 그것들을 OR 로 묶어 거른다(refresh_drawer 의
    keep() 이 이 모양을 해석한다).

    편집 가능한 QComboBox 로 이걸 만들어 본 적이 세 번 있었는데
    매번 "항목을 고르면 입력창에 있던 내용이 사라지고 방금 고른
    항목 하나만 남는" 증상이 재현됐다 — pressed/showPopup 등 어떤
    신호로 "고르기 직전 상태"를 포착하려 해도 마찬가지였다.
    편집 가능한 QComboBox 는 펼침 목록에서 항목을 고르면 입력창을
    그 항목 하나로 동기화하는 게 핵심 동작이라 이걸 신호 타이밍으로
    피해 가기가 어려웠던 것으로 보인다. 그래서 QComboBox 자체를
    버리고, 서로 전혀 안 엮이는 QLineEdit(입력창)과 QMenu(태그
    목록)로 분리했다 — QAction 을 눌러도 다른 위젯의 내용을 자기
    마음대로 바꾸는 동작이 없으므로, 입력창 내용은 오직 이 코드가
    쓴 대로만 바뀐다.
    """

    def __init__(self, window: "MainWindow"):
        super().__init__(window)
        self._win = window

        self.filter = QLineEdit()
        self.filter.setPlaceholderText("이름 또는 #태그로 거르기")
        self.filter.setClearButtonEnabled(True)
        self.filter.textChanged.connect(window.refresh_drawer)

        self.tag_btn = QToolButton()
        self.tag_btn.setText("#")
        self.tag_btn.setToolTip("태그로 거르기 — 고르면 입력창에 이어 붙는다")
        self.tag_btn.setPopupMode(QToolButton.InstantPopup)
        self.tag_menu = QMenu(self.tag_btn)
        self.tag_btn.setMenu(self.tag_menu)

        filter_row = QHBoxLayout()
        filter_row.setSpacing(4)
        filter_row.addWidget(self.filter, 1)
        filter_row.addWidget(self.tag_btn)

        self.tree = DrawerTree(window)

        box = QVBoxLayout(self)
        box.setContentsMargins(8, 8, 4, 4)
        box.setSpacing(6)
        box.addLayout(filter_row)
        box.addWidget(self.tree, 1)
        self.setMinimumWidth(180)

    def refresh_tags(self):
        """작업공간에 쓰이고 있는 태그 전부로 "#" 버튼의 메뉴를 다시
        채운다. refresh_drawer() 가 매번 부른다."""
        self.tag_menu.clear()
        for tg in self._win.tags.all_active_tags():
            tag_text = f"#{tg}"
            act = self.tag_menu.addAction(tag_text)
            act.triggered.connect(lambda checked=False, t=tag_text: self._add_tag(t))

    def _add_tag(self, tag: str):
        """메뉴에서 태그 하나를 고르면 입력창 뒤에 이어 붙인다 —
        이미 들어 있으면 조용히 무시한다."""
        current_tags = self.filter.text().split()
        if tag not in current_tags:
            current_tags.append(tag)
        self.filter.setText(" ".join(current_tags))

    def apply_theme(self, theme: Theme):
        self.tree.apply_theme(theme)
        self.setStyleSheet(f"""
            QWidget {{ background: {theme.panel_bg}; }}
            QLineEdit {{
                background: {theme.bg}; color: {theme.fg};
                border: 1px solid {theme.gutter_fg};
                border-radius: 4px; padding: 3px 7px;
            }}
            QLineEdit:focus {{ border-color: {theme.heading}; }}
            QToolButton {{
                background: {theme.bg}; color: {theme.fg};
                border: 1px solid {theme.gutter_fg};
                border-radius: 4px; padding: 3px 8px;
            }}
            QToolButton::menu-indicator {{ image: none; width: 0px; }}
        """)




# ===========================================================================
# 9-d. 태그 막대
# ===========================================================================

class TagBar(QWidget):
    """편집창 아래 한 줄. 현재 원고의 태그만 다룬다."""

    def __init__(self, window: "MainWindow"):
        super().__init__(window)
        self._win = window
        self.label = QLabel("태그")
        self.edit = QLineEdit()
        self.edit.setPlaceholderText("#초고  #1장  — 원고에는 들어가지 않습니다")
        self.edit.editingFinished.connect(window.commit_tags)

        row = QHBoxLayout(self)
        row.setContentsMargins(10, 4, 10, 4)
        row.setSpacing(8)
        row.addWidget(self.label)
        row.addWidget(self.edit, 1)

    def set_tags(self, tags: list):
        self.edit.setText(TagStore.format(tags))

    def tags(self) -> list:
        return TagStore.parse(self.edit.text())

    def apply_theme(self, theme: Theme):
        self.setStyleSheet(f"""
            QWidget {{ background: {theme.bg}; }}
            QLabel {{ color: {theme.gutter_fg_active}; }}
            QLineEdit {{
                background: {theme.bg}; color: {theme.env_name};
                border: none; border-top: 1px solid {theme.current_line};
                padding: 3px 2px;
            }}
        """)


# ===========================================================================
# 9-e. 라벨 색인 — 참조점 모으기
# ===========================================================================

#: 라벨이 만들어지는 경로는 여섯 갈래다. 어느 하나만 봐서는 목록이 비어
#: 보이므로 전부 훑는다.
RAW_LABEL_RE = re.compile(r"\\label\{([^}\n]+)\}")
ATTR_LABEL_RE = re.compile(r"""label\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s,}]+))""")
ATTR_HASH_RE = re.compile(r"(?:^|[\s,])#([A-Za-z0-9:_.\-]+)")
ATTR_CAPTION_RE = re.compile(
    r"""(?:caption|title)\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s,}]+))""")

#: 참조 프리픽스. ndhmd4tex 의 cfg["refcite"] 에서 라벨을 가리키는 것만
#: 추렸다(@ 계열은 서지 항목 인용이라 \label 과 무관해서 여기 해당하지
#: 않는다). title:/name: 은 둘 다 "제목으로 참조"를 뜻하지만 매크로가
#: 다르다 — title: 은 프로젝트가 직접 정의하는 \titleref, name: 은
#: hyperref 가 기본 제공하는 표준 \nameref 다.
REF_PREFIXES = (
    ("#", "번호", r"\ref"),
    ("C:", "이름+번호", r"\Cref"),
    ("E:", "수식 (1)", r"\eqref"),
    ("F:", "그림 N", r"\figurename~\ref"),
    ("T:", "표 N", r"\tablename~\ref"),
    ("title:", "제목(직접 정의 매크로)", r"\titleref"),
    ("name:", "제목(hyperref 표준)", r"\nameref"),
    ("page:", "쪽수", r"\pageref"),
)
#: 참조 사용 문법: [프리픽스라벨] — 예: [#mylabel], [page:mylabel].
#: 위 REF_PREFIXES 에 있는 프리픽스로 시작할 때만 참조로 본다 — 그래야
#: 각주([^note]), 위키 인덱스([[...]]), 일반 링크([글자](url)) 와
#: 안 헷갈린다.
REF_USE_RE = re.compile(
    r"\[(" + "|".join(re.escape(p) for p, _, _ in REF_PREFIXES) + r")"
    r"([A-Za-z0-9:_.-]+)\]")


#: ndhmd4tex 의 REF_DEF_RE 와 같다(각주 정의 [^x]: 는 제외).
REF_DEF_LINE_RE = re.compile(r"^\[(?!\^)([^\[\]]+)\]:\s?(.*)$")


@dataclass
class LabelHit:
    label: str
    kind: str
    line: int
    context: str
    path: Path


class LabelIndex:
    r"""원고에서 참조점(라벨)을 긁어모은다.

    변환기를 부르지 않고 원문만 훑는다. 편집 중에도 즉시 갱신되어야 하는데
    컴파일을 기다릴 수는 없기 때문이다. 대신 규칙은 ndhmd4tex 의 것을 그대로
    쓴다 — 헤딩 속성은 parse_heading_attrs 와 같은 규칙(`#id` 토큰 또는
    `label=`), 환경·그림·프레임은 속성 자리의 `label=`, 그리고 어디서든
    인라인 `{#id}` 와 생 `\label{}`.
    """

    @staticmethod
    def _attr_label(attr: str):
        if not attr:
            return None
        m = ATTR_LABEL_RE.search(attr)
        if m:
            return next(g for g in m.groups() if g is not None).strip()
        m = ATTR_HASH_RE.search(" " + attr)
        return m.group(1) if m else None

    @staticmethod
    def _attr_caption(attr: str) -> str:
        if not attr:
            return ""
        m = ATTR_CAPTION_RE.search(attr)
        return next((g for g in m.groups() if g is not None), "").strip() if m else ""

    @staticmethod
    def _mask_code(line: str) -> str:
        """인라인 코드 안의 {#id} 는 예시일 뿐 라벨이 아니다."""
        return INLINE_CODE_RE.sub(lambda m: " " * len(m.group(0)), line)

    @classmethod
    def scan_file(cls, path: Path) -> list:
        try:
            lines = read_manuscript(path).splitlines()
        except (OSError, UnicodeDecodeError):
            return []
        return cls.scan_lines(lines, path)

    @classmethod
    def scan_lines(cls, lines: list, path: Path) -> list:
        hits, seen = [], set()
        fence = 0
        # 참조 스타일 그림의 캡션: [표지] → ![캡션][표지] 의 캡션(목록 설명용)
        ref_caps = {}
        for raw in lines:
            for fm in FIGURE_REF_RE.finditer(raw):
                ref_caps.setdefault(fm.group(2), fm.group(1))

        def add(label, kind, no, context):
            label = (label or "").strip()
            if not label or (label, no) in seen:
                return
            seen.add((label, no))
            hits.append(LabelHit(label, kind, no, context.strip()[:80], path))

        for i, raw in enumerate(lines):
            no = i + 1

            # 코드펜스 안은 통째로 건너뛴다.
            m = FENCE_CLOSE_RE.match(raw)
            if fence and m and len(m.group(1)) >= fence:
                fence = 0
                continue
            if fence:
                continue
            m = FENCE_OPEN_LOOSE_RE.match(raw)
            if m:
                fence = len(m.group(1))
                continue

            line = cls._mask_code(raw)

            # 파이프 표 바로 아래의 옵션 줄 `{label=…, caption="…"}` — 표의 라벨이다.
            mo = TABLE_OPT_RE.match(line)
            if mo and i > 0 and (_is_table_row_text(lines[i - 1])
                                 or GRID_BORDER_RE.match(lines[i - 1])):
                add(cls._attr_label(mo.group(1)), "표", no,
                    cls._attr_caption(mo.group(1)) or "표")
                continue

            m = HEADING_RE.match(line)
            if m:
                add(cls._attr_label(m.group(3)), "제목", no,
                    "#" * len(m.group(1)) + " " + m.group(2))
                continue

            m = ENV_OPEN_RE.match(line)
            if m:
                cap = cls._attr_caption(m.group(2))
                add(cls._attr_label(m.group(2)), m.group(1), no,
                    cap or f":::{{{m.group(1)}}}")
                continue

            m = FRAME_OPEN_RE.match(line)
            if m:
                add(cls._attr_label(m.group(1)), "프레임", no,
                    cls._attr_caption(m.group(1)) or "====")
                continue

            # 참조 스타일 그림의 정의 줄 — `[표지]: 경로 속성,...`. 속성에 든
            # label= 도 라벨이다(ndhmd4tex 는 이 한 줄 전체를 parse_figure_attrs
            # 로 넘긴다). 링크 정의처럼 속성이 없는 줄은 해당 없다.
            m = REF_DEF_LINE_RE.match(line)
            if m:
                parts = m.group(2).strip().split(None, 1)
                if len(parts) == 2:
                    add(cls._attr_label(parts[1]), "그림", no,
                        cls._attr_caption(parts[1]) or ref_caps.get(m.group(1))
                        or f"[{m.group(1)}]: {parts[0]}")
                continue

            for m in FIGURE_RE.finditer(line):
                add(cls._attr_label(m.group(3)), "그림", no,
                    m.group(1) or m.group(2))

            for m in INLINE_LABEL_RE.finditer(line):
                add(m.group(1), "인라인", no, line)

            for m in RAW_LABEL_RE.finditer(line):
                add(m.group(1), "raw", no, line)

        return hits

    @staticmethod
    def book_files(index: BookIndex, current: Path) -> list:
        """current 가 속한 책의 파일들을 포함 순서대로(책 루트부터
        시작해 {{}} 로 닿는 모든 파일을 재귀적으로 -- 몇 단계든).
        책이 아니면 자기만.

        current 자신이 2단계(또는 그 이상)의 하위 파일이어도 문제
        없다 -- 먼저 부모 사슬을 끝까지 올라가 진짜 책 루트를 찾은
        다음, 거기서부터 다시 아래로 전부 편다. "지금 보고 있는
        파일이 책 어디에 있든 책 전체를 기준으로 삼는다"는 설계를
        따른다(TOC, 그림 점검, 상호참조 점검, 라벨 날개, 컴파일
        대상 선택이 전부 이걸 쓴다).
        """
        node = index.by_path.get(current)
        if node is None:
            return [current]

        root_node = node
        seen_up = {root_node.path}
        while root_node.parent is not None:
            nxt = index.by_path.get(root_node.parent)
            if nxt is None or nxt.path in seen_up:
                break
            root_node = nxt
            seen_up.add(root_node.path)

        result = []
        seen_down = set()

        def walk(n):
            if n.path in seen_down:
                return
            seen_down.add(n.path)
            result.append(n.path)
            for child_path in n.children:
                child_node = index.by_path.get(child_path)
                if child_node is not None:
                    walk(child_node)

        walk(root_node)
        return result



# ===========================================================================
# 9-f. 라벨 날개
# ===========================================================================

class LabelWing(QWidget):
    """오른쪽에 여닫는 날개. 문서의 참조점을 모아 보여준다.

    쓰는 동안 가장 아쉬운 것이 "그 라벨 이름이 뭐였더라" 인데, 그걸 확인하러
    다른 파일로 건너갔다 오면 쓰던 자리를 잃는다. 그래서 이 날개의 기본
    동작은 "가기" 가 아니라 **참조 삽입** 이다. 커서는 제자리에 둔 채
    `[#라벨]` 만 꽂아 넣는다.
    """

    def __init__(self, window: "MainWindow"):
        super().__init__(window)
        self._win = window

        self.scope = QComboBox()
        self.scope.addItems(["현재 파일", "책 전체"])
        self.scope.setCurrentIndex(1)
        self.scope.currentIndexChanged.connect(window.refresh_labels)

        self.float_btn = QToolButton()
        self.float_btn.setText("⧉")
        self.float_btn.setToolTip("떼어내기 — 따로 떠다니는 창으로")
        self.float_btn.setAutoRaise(True)
        self.float_btn.setFixedSize(18, 18)
        self.float_btn.clicked.connect(lambda: self._win.toggle_float_panel("wing"))

        close_btn = QToolButton()
        close_btn.setText("✕")
        close_btn.setToolTip("닫기")
        close_btn.setAutoRaise(True)
        close_btn.setFixedSize(18, 18)
        close_btn.clicked.connect(self._close)

        header_row = QHBoxLayout()
        header_row.setContentsMargins(0, 0, 0, 0)
        header_row.addWidget(self.scope, 1)
        header_row.addWidget(self.float_btn)
        header_row.addWidget(close_btn)

        self.filter = QLineEdit()
        self.filter.setPlaceholderText("라벨 거르기")
        self.filter.setClearButtonEnabled(True)
        self.filter.textChanged.connect(window.refresh_labels)
        self.filter.returnPressed.connect(self._insert_first)

        self.tree = QTreeWidget()
        self.tree.setHeaderHidden(True)
        self.tree.setRootIsDecorated(True)
        self.tree.setUniformRowHeights(True)
        self.tree.itemActivated.connect(self._on_activate)
        self.tree.setContextMenuPolicy(Qt.CustomContextMenu)
        self.tree.customContextMenuRequested.connect(self._menu)

        self.hint = QLabel("더블클릭 → 참조 삽입 · 우클릭 → 형식 선택")
        self.hint.setWordWrap(True)

        box = QVBoxLayout(self)
        box.setContentsMargins(4, 8, 8, 4)
        box.setSpacing(6)
        box.addLayout(header_row)
        box.addWidget(self.filter)
        box.addWidget(self.tree, 1)
        box.addWidget(self.hint)
        self.setMinimumWidth(200)

    def _close(self):
        """우측 상단 [x] — 메뉴의 체크 상태도 같이 꺼야 한다(toggle_wing
        은 그 체크 상태가 바뀔 때만 자동으로 불리므로, 버튼으로 닫을
        땐 둘 다 직접 해 줘야 한다)."""
        self._win._act_wing.setChecked(False)
        self._win.toggle_wing(False)

    # -- 조회 ---------------------------------------------------------------

    def is_book(self) -> bool:
        return self.scope.currentIndex() == 1

    def needle(self) -> str:
        return self.filter.text().strip().lower()

    def _selected_hit(self):
        item = self.tree.currentItem()
        return item.data(0, Qt.UserRole) if item else None

    # -- 동작 ---------------------------------------------------------------

    def _insert_first(self):
        """거르개에서 Enter — 첫 결과를 바로 꽂는다."""
        it = self.tree.topLevelItem(0)
        while it is not None and it.data(0, Qt.UserRole) is None:
            it = it.child(0) if it.childCount() else None
        if it is not None:
            self._win.insert_reference(it.data(0, Qt.UserRole), "#")

    def _on_activate(self, item, _col=0):
        hit = item.data(0, Qt.UserRole)
        if hit:
            self._win.insert_reference(hit, "#")

    def _menu(self, pos):
        hit = self._selected_hit()
        item = self.tree.itemAt(pos)
        if item is not None:
            self.tree.setCurrentItem(item)
            hit = item.data(0, Qt.UserRole)
        if not hit:
            return
        menu = QMenu(self)
        for prefix, desc, macro in REF_PREFIXES:
            a = menu.addAction(f"[{prefix}{hit[0]}]     {desc}  →  {macro}")
            a.triggered.connect(
                lambda _=False, p=prefix, h=hit: self._win.insert_reference(h, p))
        menu.addSeparator()
        a = menu.addAction("정의 위치로 가기")
        a.triggered.connect(lambda _=False, h=hit: self._win.goto_label(h))
        a = menu.addAction("라벨 이름 복사")
        a.triggered.connect(
            lambda _=False, h=hit: QApplication.clipboard().setText(h[0]))
        menu.exec(self.tree.viewport().mapToGlobal(pos))

    def apply_theme(self, theme: Theme):
        self.setStyleSheet(f"""
            QWidget {{ background: {theme.panel_bg}; color: {theme.fg}; }}
            QLineEdit, QComboBox {{
                background: {theme.bg}; color: {theme.fg};
                border: 1px solid {theme.gutter_fg};
                border-radius: 4px; padding: 3px 7px;
            }}
            QLineEdit:focus {{ border-color: {theme.heading}; }}
            QComboBox QAbstractItemView {{
                background: {theme.bg}; color: {theme.fg};
                selection-background-color: {theme.current_line};
            }}
            QTreeWidget {{
                background: {theme.bg}; color: {theme.fg};
                border: 1px solid {theme.gutter_fg}; border-radius: 4px;
                outline: none;
            }}
            QTreeWidget::item {{ padding: 2px 3px; }}
            QTreeWidget::item:selected {{ background: {theme.match_active_bg}; color: {theme.fg}; }}
            {tree_branch_css(theme.fg)}
            QLabel {{ color: {theme.gutter_fg_active}; font-size: 11px; }}
        """)


class TocPanel(QWidget):
    """[보기] ▸ TOC 보기. 라벨 날개 바로 아래에 자리한다.

    "책 전체"에 대해서만 동작한다 — 라벨 날개처럼 현재 파일/책을
    고르는 선택지는 없다. #으로 시작하는 모든 줄을 수준별로 묶어
    트리로 보여준다. 클릭하면 그 표지로 간다.

    라벨 날개와 같은 빈도로 갱신한다(파일 전환·삭제·이동 등, 그리고
    저장할 때 — 매 입력마다는 아니다) — 두 날개의 새로고침 리듬이
    다르면 오히려 헷갈린다.
    """

    def __init__(self, window: "MainWindow"):
        super().__init__(window)
        self._win = window

        title = QLabel("TOC")

        self.tree = QTreeWidget()
        self.tree.setHeaderHidden(True)
        self.tree.itemClicked.connect(self._on_activate)
        self.tree.itemActivated.connect(self._on_activate)

        collapse_btn = QToolButton()
        collapse_btn.setText("⊟")
        collapse_btn.setToolTip("모두 접기")
        collapse_btn.setAutoRaise(True)
        collapse_btn.clicked.connect(self.tree.collapseAll)

        refresh_btn = QToolButton()
        refresh_btn.setText("⟳")
        refresh_btn.setToolTip("다시 읽기 — 타이핑만으로는 자동 갱신되지 않는다"
                               "(파일 전환·저장 때 새로 짠다)")
        refresh_btn.setAutoRaise(True)
        refresh_btn.clicked.connect(self.refresh)

        self.float_btn = QToolButton()
        self.float_btn.setText("⧉")
        self.float_btn.setToolTip("떼어내기 — 따로 떠다니는 창으로")
        self.float_btn.setAutoRaise(True)
        self.float_btn.setFixedSize(18, 18)
        self.float_btn.clicked.connect(lambda: self._win.toggle_float_panel("toc"))

        close_btn = QToolButton()
        close_btn.setText("✕")
        close_btn.setToolTip("닫기")
        close_btn.setAutoRaise(True)
        close_btn.setFixedSize(18, 18)
        close_btn.clicked.connect(self._close)

        header_row = QHBoxLayout()
        header_row.setContentsMargins(0, 0, 0, 0)
        header_row.addWidget(title)
        header_row.addStretch(1)
        header_row.addWidget(collapse_btn)
        header_row.addWidget(refresh_btn)
        header_row.addWidget(self.float_btn)
        header_row.addWidget(close_btn)

        v = QVBoxLayout(self)
        v.setContentsMargins(0, 0, 0, 0)
        v.setSpacing(2)
        v.addLayout(header_row)
        v.addWidget(self.tree, 1)

    def _close(self):
        """우측 상단 [x] — 메뉴의 체크 상태도 같이 꺼야 한다(toggle_toc
        는 그 체크 상태가 바뀔 때만 자동으로 불리므로, 버튼으로 닫을
        땐 둘 다 직접 해 줘야 한다)."""
        self._win._act_toc.setChecked(False)
        self._win.toggle_toc(False)

    def refresh(self):
        """책 전체(현재 파일이 책의 일부가 아니면 자기 파일만)의
        모든 # 줄을 수준별로 트리로 다시 짠다. 코드펜스 안은
        LabelIndex 와 같은 방식으로 건너뛴다.

        다시 짜기 전에 접어 둔 항목과 스크롤 위치를 기억했다가 되살린다
        — 안 그러면 저장할 때마다(또는 다시 읽기를 누를 때마다) 트리가
        통째로 펼쳐져 버려서, 긴 TOC 의 일부를 접어 두고 쓸 수가
        없다. 새로 생긴 표제는 기본대로 펼쳐진 채로 나온다.
        """
        collapsed = self._collapsed_keys()
        scroll_pos = self.tree.verticalScrollBar().value()
        self.tree.clear()
        win = self._win
        if win._path is None:
            return

        files = LabelIndex.book_files(win.index, win._path)
        stack = []   # [(level, QTreeWidgetItem)]
        for path in files:
            if path == win._path:
                lines = win.editor.toPlainText().splitlines()
            else:
                try:
                    lines = read_manuscript(path).splitlines()
                except (OSError, UnicodeDecodeError):
                    continue
            fence = 0
            for i, raw in enumerate(lines):
                m = FENCE_CLOSE_RE.match(raw)
                if fence and m and len(m.group(1)) >= fence:
                    fence = 0
                    continue
                if fence:
                    continue
                m = FENCE_OPEN_LOOSE_RE.match(raw)
                if m:
                    fence = len(m.group(1))
                    continue
                hm = HEADING_RE.match(raw)
                if not hm:
                    continue
                level = len(hm.group(1))
                text = hm.group(2).strip()
                while stack and stack[-1][0] >= level:
                    stack.pop()
                parent = stack[-1][1] if stack else self.tree
                item = QTreeWidgetItem(parent, [text])
                item.setData(0, Qt.UserRole, (str(path), i + 1))
                stack.append((level, item))
        self.tree.expandAll()
        self._apply_collapsed(collapsed)
        self.tree.verticalScrollBar().setValue(scroll_pos)

    def _walk_keyed(self):
        """트리를 위에서 아래로 훑으며 (항목, 키)를 낸다. 키는 (파일,
        표제 글자, 같은 파일 안에서 같은 글자가 몇 번째로 나왔는지)
        — 줄 번호는 편집하면 밀리므로 쓰지 않고, 같은 제목이 여러 번
        나오는 경우(예: "개요")는 순번으로 구분한다."""
        counts = {}

        def walk(item):
            data = item.data(0, Qt.UserRole)
            base = (data[0] if data else "", item.text(0))
            n = counts.get(base, 0)
            counts[base] = n + 1
            yield item, base + (n,)
            for i in range(item.childCount()):
                yield from walk(item.child(i))

        for i in range(self.tree.topLevelItemCount()):
            yield from walk(self.tree.topLevelItem(i))

    def _collapsed_keys(self) -> set:
        return {key for item, key in self._walk_keyed()
                if item.childCount() and not item.isExpanded()}

    def _apply_collapsed(self, keys: set):
        if not keys:
            return
        for item, key in self._walk_keyed():
            if key in keys and item.childCount():
                item.setExpanded(False)

    def _on_activate(self, item, _col=0):
        data = item.data(0, Qt.UserRole)
        if data:
            path_str, line = data
            self._win.open_at(Path(path_str), line)

    def apply_theme(self, theme: Theme):
        self.setStyleSheet(f"""
            QWidget {{ background: {theme.panel_bg}; color: {theme.fg}; }}
            QTreeWidget {{
                background: {theme.bg}; color: {theme.fg};
                border: 1px solid {theme.gutter_fg}; border-radius: 4px;
                outline: none;
            }}
            QTreeWidget::item {{ padding: 2px 3px; }}
            QTreeWidget::item:hover {{ background: {theme.current_line}; }}
            QTreeWidget::item:selected {{ background: {theme.match_active_bg}; color: {theme.fg}; }}
            {tree_branch_css(theme.fg)}
            QLabel {{ color: {theme.gutter_fg_active}; font-size: 11px; font-weight: bold; padding: 2px 4px; }}
            QToolButton {{
                background: transparent; color: {theme.gutter_fg_active};
                border: none; padding: 2px 4px; border-radius: 3px;
            }}
            QToolButton:hover {{ background: {theme.current_line}; }}
        """)


# ===========================================================================
# 9-g. 미리보기 — 수식과 그림
# ===========================================================================
#
# 왜 MathJax 가 아니라 LaTeX 인가.
#
# 이 방언의 원고는 front matter 의 `preamble:` 에 자기 매크로를 정의한다.
# MathJax 는 그것을 모르고, kotex 도 실제 폰트도 적용되지 않는다. 즉 최종
# 조판과 다르게 보이는데, 미리보기의 존재 이유가 바로 그 일치다. 게다가
# QWebEngine 은 별도의 큰 휠이고 TeX 는 이미 깔려 있다.
#
# 대신 백엔드는 갈아끼울 수 있게 두었다. MathRenderer.BACKENDS 에 한 줄
# 더하면 다른 경로가 붙는다.

@dataclass
class PreviewTarget:
    kind: str        # 'math' | 'image' | 'table'
    source: str      # 수식 원문(구분자 포함) 또는 그림 경로
    start: int
    end: int
    caption: str = ""


def trim_url(u: str) -> str:
    """맨 주소 끝에 딸린 문장부호(마침표·쉼표·닫는 괄호 …)를 뗀다. 닫는 괄호는
    여는 괄호와 짝이 맞을 때(위키 주소 따위)만 남긴다."""
    while u:
        c = u[-1]
        if c in ".,;:!?'\"*_~":
            u = u[:-1]
        elif c == ")" and u.count(")") > u.count("("):
            u = u[:-1]
        else:
            break
    return u


def _mask_code_math(line: str) -> str:
    masked = list(line)
    for rx in (INLINE_CODE_RE, INLINE_MATH_RE):
        for m in rx.finditer(line):
            for i in range(m.start(), m.end()):
                masked[i] = " "
    return "".join(masked)


def refs_in_line(line: str) -> list:
    """한 줄 안의 참조 표지를 모두 모은다 → [(종류, 키, 시작, 끝, 바깥시작, 바깥끝)].
    종류: "fn" 각주 `[^키]`, "label" 상호참조 `[#라벨]` `[page:라벨]` `[글자](#라벨)`,
    "cite" 문헌 인용 `[@키]`(쉼표로 여럿이면 키마다 하나), "figref" 이름 붙인 그림·참조 링크의
    `![캡션][키]` `[글자][키]`. 코드·수식 안은 건너뛴다. figref 키는 소문자로 돌려준다."""
    line = _mask_code_math(line)
    out = []
    dm = FOOTNOTE_DEF_RE.match(line)
    for m in FOOTNOTE_REF_RE.finditer(line):
        if dm and m.start() == 0:
            continue                       # 줄머리의 `[^키]:` 는 정의 표지다
        out.append(("fn", m.group(1), m.start(), m.end(), m.start(), m.end()))
    for m in REF_USE_RE.finditer(line):
        out.append(("label", m.group(2), m.start(), m.end(), m.start(), m.end()))
    for m in LINK_RE.finditer(line):
        if m.start() > 0 and line[m.start() - 1] == "!":
            continue
        if m.group(2).startswith("#") and len(m.group(2)) > 1:
            out.append(("label", m.group(2)[1:], m.start(), m.end(), m.start(), m.end()))
    for m in CITE_USE_RE.finditer(line):
        off = m.start(2)
        for part in m.group(2).split(","):
            key = part.strip()
            if key:
                a = off + (len(part) - len(part.lstrip()))
                out.append(("cite", key, a, a + len(key), m.start(), m.end()))
            off += len(part) + 1
    for rx in (FIGURE_REF_RE, REFLINK_RE):
        for m in rx.finditer(line):
            out.append(("figref", m.group(2).strip().lower(), m.start(), m.end(), m.start(), m.end()))
    out.sort(key=lambda t: (t[2], t[0]))
    return out


def ref_token_at(line: str, pos: int):
    """줄 안의 pos 가 참조 표지 또는 줄머리 정의 표지(`[^키]:` `[키]:`) 위이면 (종류, 키, 정의인가), 아니면 None."""
    items = refs_in_line(line)
    for t in items:                      # 키 자리에 정확히 놓였으면 그 키
        if t[2] <= pos <= t[3]:
            return t[0], t[1], False
    for t in items:                      # [@a,b] 의 괄호·쉼표 위면 첫 키
        if t[4] <= pos <= t[5]:
            return t[0], t[1], False
    dm = FOOTNOTE_DEF_RE.match(line)
    if dm and pos <= dm.start(2):
        return "fn", dm.group(0)[2:dm.group(0).index("]")], True
    rm = REF_DEF_LINE_RE.match(line)
    if rm and pos <= line.index("]:") + 2:
        return "figref", rm.group(1).strip().lower(), True
    return None


def _nonfence_lines(lines):
    """코드펜스 밖의 (0 부터 센 줄 번호, 줄)."""
    fence = 0
    for i, raw in enumerate(lines):
        m = FENCE_CLOSE_RE.match(raw)
        if fence and m and len(m.group(1)) >= fence:
            fence = 0
            continue
        if fence:
            continue
        m = FENCE_OPEN_LOOSE_RE.match(raw)
        if m:
            fence = len(m.group(1))
            continue
        yield i, raw


def xref_in_line(line: str, pos: int):
    r"""줄 안의 pos 위치가 `[글자](#라벨)`(\hyperref) 위이면 그 라벨을, 아니면 None.
    그림 `![..](#..)` 과 코드·수식 안은 아니다. line 은 펜스 안이 비워진 줄."""
    masked = list(line)
    for rx in (INLINE_CODE_RE, INLINE_MATH_RE):
        for m in rx.finditer(line):
            for i in range(m.start(), m.end()):
                masked[i] = " "
    line = "".join(masked)
    for m in LINK_RE.finditer(line):
        if m.start() > 0 and line[m.start() - 1] == "!":
            continue
        if m.start() <= pos <= m.end() and m.group(2).startswith("#"):
            return m.group(2)[1:] or None
    return None


def url_in_line(line: str, pos: int, resolve_ref, is_figure_label):
    """줄 안의 pos 위치가 '인터넷 주소'이면 그 주소를, 아니면 None 을 준다.

    인터넷 주소로 치는 것: [글자](주소) · [](주소) · [글자][표지] · 정의 줄
    [표지]: 주소 · 맨 주소. **그림은 아니다** — ![..](주소), ![..][표지], 그리고
    그림으로 쓰이는 표지의 정의 줄은 미리보기가 맡으므로 건드리지 않는다. 같은
    주소라도 그림 문법 안에 있으면 그림이고(.png 로 끝나도), 문법 없이 글 속에
    놓였으면 주소다. 코드(`…`)와 수식($…$) 안은 주소가 아니다.
    line 은 이미 코드펜스 안이 비워진 줄이어야 한다.
    resolve_ref(표지) → 주소|None, is_figure_label(표지) → bool.
    """
    # 코드·수식 안은 비운다(길이를 지켜 위치가 어긋나지 않게).
    masked = list(line)
    for rx in (INLINE_CODE_RE, INLINE_MATH_RE):
        for m in rx.finditer(line):
            for i in range(m.start(), m.end()):
                masked[i] = " "
    line = "".join(masked)
    if pos < len(line) and line[pos] == " " and not line.strip():
        return None

    spans = []                                    # 그림 문법 — 주소가 아니다
    for rx in (FIGURE_RE, FIGURE_REF_RE):
        for m in rx.finditer(line):
            spans.append((m.start(), m.end()))
            if m.start() <= pos <= m.end():
                # ![..](http://…) 처럼 경로가 인터넷 주소이면 그림이어도 그 주소를 연다(0.4.157).
                # 로컬 경로와 ![..][표지] 는 여전히 주소가 아니다.
                if rx is FIGURE_RE and re.match(r"(?i)(?:https?|ftp)://", m.group(2)):
                    return m.group(2)
                return None

    taken = list(spans)
    for m in LINK_RE.finditer(line):
        if m.start() > 0 and line[m.start() - 1] == "!":
            continue
        taken.append((m.start(), m.end()))
        if m.start() <= pos <= m.end():
            if m.group(2).startswith("#"):
                return None            # [글자](#라벨) — \hyperref, 주소가 아니다
            return m.group(2)
    for m in REFLINK_RE.finditer(line):
        if m.start() > 0 and line[m.start() - 1] == "!":
            continue
        taken.append((m.start(), m.end()))
        if m.start() <= pos <= m.end():
            return resolve_ref(m.group(2))

    d = FIGURE_DEF_RE.match(line)
    if d:
        if not is_figure_label(d.group(1)) and URL_RE.match(d.group(2)):
            return d.group(2)
        return None

    for m in BARE_URL_RE.finditer(line):
        u = trim_url(m.group(0))
        a, b = m.start(), m.start() + len(u)
        if any(x <= a < y for x, y in taken):
            continue
        if a <= pos <= b:
            return u
    return None


class PreviewScanner:
    """커서가 놓인 자리에서 미리볼 것을 찾는다.

    호버가 아니라 커서를 쓴다. 글을 쓰다가 눈을 아래로 내리면 거기 있는
    방식이라, 마우스를 움직일 일도 없고 읽는 중에 튀어나오지도 않는다.
    """

    @staticmethod
    def _fence_mask(text: str):
        """코드펜스 구간을 공백으로 지운 사본. 그 안의 $ 는 수식이 아니다.

        하이라이터와 같은 규칙으로 줄 단위로 읽는다: 여는 줄은 백틱 셋 이상 +
        (공백이 낀 것까지 포함한) 정보 문자열, 닫는 줄은 같거나 더 긴 백틱만
        있는 줄이다. 예전에는 ```이름\\n … \\n``` 꼴 정규식 하나로 찾았는데,
        showexam 처럼 정보 문자열에 공백·속성이 붙거나 백틱이 넷 이상이거나
        들여쓴 펜스는 여는 줄을 못 알아봐서 닫는 줄이 여는 줄로 둔갑했고,
        그 뒤로는 펜스 안팎이 뒤집혀 본문의 수식이 통째로 가려졌다.
        닫히지 않은 펜스는 끝까지다(하이라이터와 같다).
        """
        out = list(text)

        def blank(a, b):
            for i in range(a, b):
                if out[i] != "\n":
                    out[i] = " "

        offset, start, need = 0, None, 0
        for raw in text.split("\n"):
            line = raw.rstrip("\r")
            end = offset + len(raw)
            if start is None:
                m = FENCE_OPEN_LOOSE_RE.match(line)
                if m:
                    start, need = offset, len(m.group(1))
            else:
                m = FENCE_CLOSE_RE.match(line)
                if m and len(m.group(1)) >= need:
                    blank(start, end)
                    start = None
            offset = end + 1
        if start is not None:
            blank(start, len(text))
        return "".join(out)

    @staticmethod
    def _find_definition(text: str, key: str):
        """문서 전체에서 [key]: 경로 형태의 정의를 찾는다(ndhmd4tex
        0.12 의 참조 스타일 그림 문법). 못 찾으면 None."""
        pattern = re.compile(r"^\[" + re.escape(key) + r"\]:\s*(\S+)",
                             re.MULTILINE)
        m = pattern.search(text)
        return m.group(1) if m else None

    @staticmethod
    def _is_figure_label(text: str, key: str) -> bool:
        """[key]: 대상 형태의 독립행 정의는 그림(![캡션][key])과 일반
        링크([글자][key]) 둘 다에 쓰인다 — 정의 줄 자체는 똑같이
        생겨서 구분이 안 되므로, 실제로 어느 쪽으로 "쓰이는지"를
        문서에서 찾아 가른다. 그림으로 쓰인 적이 있을 때만 True다."""
        pattern = re.compile(
            r"!\[(?:[^\[\]]|\[[^\[\]]*\])*\]\[" + re.escape(key) + r"\]")
        return pattern.search(text) is not None

    @classmethod
    def find(cls, text: str, pos: int):
        masked = cls._fence_mask(text)

        # 우선순위: 디스플레이 수식 > 수식 환경 > 그림 > 인라인 수식.
        # 좁은 것이 넓은 것 안에 들어 있을 수 있으므로 넓은 쪽을 먼저 본다.
        for rx, kind in ((DISPLAY_MATH_RE, "math"),
                         (MATH_ENV_RE, "math"),
                         (TABLE_ENV_RE, None)):
            if rx is None:
                continue
            for m in rx.finditer(masked):
                if m.start() <= pos <= m.end() and kind:
                    return PreviewTarget(kind, text[m.start():m.end()],
                                         m.start(), m.end())

        line_start = text.rfind("\n", 0, pos) + 1
        line_end = text.find("\n", pos)
        line_end = len(text) if line_end < 0 else line_end
        line = masked[line_start:line_end]
        rel = pos - line_start

        for m in FIGURE_RE.finditer(line):
            if m.start() <= rel <= m.end():
                return PreviewTarget("image", m.group(2),
                                     line_start + m.start(),
                                     line_start + m.end(),
                                     caption=m.group(1) or "")

        # 참조 스타일: 커서가 ![캡션][표지] 위에 있으면, 문서 전체에서
        # 그 표지의 정의(다른 줄의 [표지]: 경로)를 찾아 경로를 얻는다.
        for m in FIGURE_REF_RE.finditer(line):
            if m.start() <= rel <= m.end():
                target_path = cls._find_definition(text, m.group(2))
                if target_path:
                    return PreviewTarget("image", target_path,
                                         line_start + m.start(),
                                         line_start + m.end(),
                                         caption=m.group(1) or "")

        # 커서가 정의 줄([표지]: 경로 속성...) 자체에 있어도 미리본다 —
        # 단, 이 정의가 실제로 그림(![캡션][표지])으로 쓰였을 때만이다.
        # 같은 정의 문법을 일반 링크([글자][표지])도 쓰므로, 정의 줄
        # 모양만으로는 그림인지 링크인지 가를 수 없다.
        def_m = FIGURE_DEF_RE.match(line)
        if def_m and cls._is_figure_label(text, def_m.group(1)):
            return PreviewTarget("image", def_m.group(2),
                                 line_start, line_end, caption="")

        for m in INLINE_MATH_RE.finditer(line):
            if m.start() <= rel <= m.end():
                return PreviewTarget("math", m.group(0),
                                     line_start + m.start(),
                                     line_start + m.end())

        # 커서가 딱 위에 없어도, 줄에 그림이 하나뿐이면 그것을 보여준다
        # (인라인·참조 스타일 합쳐서 하나일 때만 — 둘 다 있으면 어느
        # 쪽인지 애매해지니 시도하지 않는다).
        figs = list(FIGURE_RE.finditer(line))
        ref_figs = list(FIGURE_REF_RE.finditer(line))
        if len(figs) == 1 and not ref_figs:
            m = figs[0]
            return PreviewTarget("image", m.group(2),
                                 line_start + m.start(), line_start + m.end(),
                                 caption=m.group(1) or "")
        if len(ref_figs) == 1 and not figs:
            m = ref_figs[0]
            target_path = cls._find_definition(text, m.group(2))
            if target_path:
                return PreviewTarget("image", target_path,
                                     line_start + m.start(), line_start + m.end(),
                                     caption=m.group(1) or "")
        return cls._find_pipe_table(text, masked, pos)

    @staticmethod
    def _find_pipe_table(text: str, masked: str, pos: int):
        """커서가 파이프 표 안에 있으면 그 표 전체를 준다. 없으면 None.

        표 = 이어진(빈 줄 없는) 줄들 중 `|` 가 있는 줄의 덩어리이고, 그 안에
        구분선(|---|---|)이 있어야 한다. 구분선 없는 `|` 는 표가 아니다.
        """
        starts = [0]
        for i, ch in enumerate(masked):
            if ch == "\n":
                starts.append(i + 1)
        import bisect
        cur = bisect.bisect_right(starts, pos) - 1

        def line_at(k):
            a = starts[k]
            b = starts[k + 1] - 1 if k + 1 < len(starts) else len(masked)
            return masked[a:b]

        def is_row(k):
            l = line_at(k).strip()
            return bool(l) and "|" in l and not l.startswith("//")

        # grid 표: `+` 또는 `|` 로 시작하는 이어진 줄들이고 첫 줄이 가로 테두리.
        def is_grid_row(k):
            l = line_at(k).strip()
            return bool(l) and l[0] in "+|"

        if is_grid_row(cur):
            glo = ghi = cur
            while glo > 0 and is_grid_row(glo - 1):
                glo -= 1
            while ghi + 1 < len(starts) and is_grid_row(ghi + 1):
                ghi += 1
            if GRID_BORDER_RE.match(line_at(glo)) and ghi - glo >= 2:
                a = starts[glo]
                b = starts[ghi] + len(line_at(ghi))
                return PreviewTarget("table", text[a:b], a, b)

        if not is_row(cur):
            return None
        lo = hi = cur
        while lo > 0 and is_row(lo - 1):
            lo -= 1
        while hi + 1 < len(starts) and is_row(hi + 1):
            hi += 1
        if not any(TABLE_SEP_RE.match(line_at(k)) and "-" in line_at(k)
                   for k in range(lo, hi + 1)):
            return None
        a = starts[lo]
        b = starts[hi] + len(line_at(hi))
        return PreviewTarget("table", text[a:b], a, b)


class Preamble:
    """미리보기에 쓸 프리앰블을 원고에서 뽑아낸다.

    책의 최상위 파일에서 읽고 `setup:` 을 한 단계 따라간다(ndhmd4tex 의
    상속 규칙과 같다). 장 파일에는 프리앰블이 없는 것이 보통이므로 자기
    파일만 보면 매크로가 전부 빠진다.
    """

    CACHE = {}
    #: 마지막 YAML 파싱 실패 메시지. graphicspath 가 빈 목록으로 나올 때
    #: "선언 안 함"과 "파싱 실패로 다 날아감"을 구분하는 데 쓴다.
    LAST_ERROR: str = ""

    @staticmethod
    def _read(path: Path, live) -> str:
        """live(path) 가 텍스트를 주면 그걸 쓰고, 아니면 디스크를 읽는다.

        지금 편집 중인 파일에 방금 타이핑만 하고 아직 저장하지 않은
        front matter 는 디스크에 없다. 여기서 디스크만 보면 graphicspath
        나 preamble 매크로를 추가해도 저장 전까지 미리보기에 반영되지
        않는데, 그건 "미리보기"의 존재 이유와 어긋난다.
        """
        if live is not None:
            text = live(path)
            if text is not None:
                return text
        try:
            return read_manuscript(path)
        except (OSError, UnicodeDecodeError):
            return ""

    @classmethod
    def _front_matter(cls, path: Path, live=None) -> dict:
        text = cls._read(path, live)
        m = FRONTMATTER_RE.match(text)
        if not m:
            return {}
        try:
            import yaml
        except ImportError:
            # 구문 오류와 원인이 전혀 다르므로 따로 잡는다 — 문법은 멀쩡한데
            # "오류"라고만 나오면 원고를 계속 고쳐보게 만드는 헛수고가 된다.
            # ndhmd4tex 도 프론트매터를 읽을 때 PyYAML 을 쓰므로, 이건 이
            # 앱만의 추가 의존성이 아니라 컴파일에도 어차피 필요한 것이다.
            cls.LAST_ERROR = "PyYAML이 설치되어 있지 않습니다 — pip install pyyaml"
            return {}
        try:
            data = yaml.safe_load(m.group(1))
        except Exception as e:
            # 여기서 조용히 {} 로 돌아가면, graphicspath 하나가 아니라
            # front matter 전체가 못 읽힌 것과 "선언 안 함"이 구분되지
            # 않는다. 마지막 실패를 남겨서 진단 메시지가 집어낼 수 있게 한다.
            cls.LAST_ERROR = f"{path.name}: {e}"
            return {}
        if not isinstance(data, dict):
            cls.LAST_ERROR = f"{path.name}: 프론트매터가 목록/사전 형태가 아닙니다."
            return {}
        return data

    @classmethod
    def _root_meta(cls, index: "BookIndex", path: Path, live=None):
        """책 최상위 파일과, `setup:` 까지 합친 front matter."""
        root = LabelIndex.book_files(index, path)[0]
        meta = cls._front_matter(root, live)
        setup = meta.get("setup")
        merged = {}
        if isinstance(setup, str):
            # setup 파일은 지금 열려 있는 파일이 아닌 게 보통이라 live 를
            # 넘겨도 대개 디스크로 떨어지지만, 혹시 그것도 열려 있다면
            # 마찬가지로 최신 내용을 본다.
            merged.update(cls._front_matter(root.parent / setup, live))
        merged.update(meta)
        return root, merged

    @classmethod
    def meta(cls, index: "BookIndex", path: Path, live=None) -> dict:
        """setup: 까지 합친 front matter 전체. compileoption: 등을 꺼낼 때 쓴다."""
        _, merged = cls._root_meta(index, path, live)
        return merged

    @classmethod
    def graphicspath(cls, index: "BookIndex", path: Path, live=None) -> list:
        r"""front matter 의 graphicspath: 를 문자열 목록으로 정규화한다.

        \graphicspath{{a/}{b/}} 처럼 여러 폴더를 받을 수 있으므로 YAML
        리스트(`- images/` 형태)도, 단일 문자열도 둘 다 받아들인다.
        """
        _, merged = cls._root_meta(index, path, live)
        raw = merged.get("graphicspath")
        if raw is None:
            return []
        if isinstance(raw, str):
            raw = [raw]
        if not isinstance(raw, list):
            return []
        return [str(p).strip().strip("{}") for p in raw if str(p).strip()]

    @classmethod
    def collect(cls, index: "BookIndex", path: Path, live=None) -> str:
        root = LabelIndex.book_files(index, path)[0]
        # live 가 그 파일의 내용을 실제로 쥐고 있으면(=지금 편집 중이면)
        # 저장 여부와 무관하게 매번 새로 읽는다 — mtime 캐시는 디스크
        # 기준이라 저장 전 변경을 보지 못한다.
        if live is not None and live(root) is not None:
            _, merged = cls._root_meta(index, path, live)
            return cls._join_preamble(merged)

        try:
            stamp = root.stat().st_mtime_ns
        except OSError:
            stamp = 0
        key = (str(root), stamp)
        if key in cls.CACHE:
            return cls.CACHE[key]

        _, merged = cls._root_meta(index, path)
        out = cls._join_preamble(merged)
        cls.CACHE[key] = out
        return out

    @staticmethod
    def _join_preamble(merged: dict) -> str:
        parts = []
        for k in ("preamble", "preamble+"):
            v = merged.get(k)
            if isinstance(v, str) and v.strip():
                parts.append(v.rstrip())
        return "\n".join(parts)


class RenderSignals(QObject):
    done = Signal(int, str, str, str)   # 요청 번호, 'ok'|'error', 경로/메시지, 단계


class RenderTask(QRunnable):
    """한 번의 렌더. GUI 스레드를 막지 않도록 풀에서 돌린다."""

    def __init__(self, req_id, snippet, preamble, outdir, signals):
        super().__init__()
        self.req_id, self.snippet = req_id, snippet
        self.preamble, self.outdir, self.signals = preamble, outdir, signals

    def run(self):
        try:
            ok, payload, stage = MathRenderer.render_sync(
                self.snippet, self.preamble, self.outdir)
        except subprocess.TimeoutExpired:
            ok, payload, stage = False, "렌더가 너무 오래 걸려 중단했습니다.", ""
        except Exception as e:                      # 렌더가 앱을 죽이면 안 된다
            ok, payload, stage = False, str(e), ""
        self.signals.done.emit(self.req_id, "ok" if ok else "error", payload, stage)


class MathRenderer:
    r"""standalone 문서를 만들어 이미지로 굽는다.

    경로는 셋을 차례로 시도한다. dvisvgm 은 TeX Live 에 함께 오고 벡터라
    확대해도 깨지지 않아 첫째로 둔다. 나머지는 poppler 가 있을 때의 대비다.
    """

    #: (이름, xelatex 인자, 변환 명령 생성기, 결과 확장자)
    BACKENDS = (
        ("dvisvgm", ["-no-pdf"],
         lambda src, dst: ["dvisvgm", "--no-fonts", "--exact-bbox",
                           str(src.with_suffix(".xdv")), "-o", str(dst)], ".svg"),
        ("pdftocairo", [],
         lambda src, dst: ["pdftocairo", "-svg",
                           str(src.with_suffix(".pdf")), str(dst)], ".svg"),
        ("pdftoppm", [],
         lambda src, dst: ["pdftoppm", "-r", "200", "-png", "-singlefile",
                           str(src.with_suffix(".pdf")),
                           str(dst.with_suffix(""))], ".png"),
    )

    TIMEOUT = 25

    @staticmethod
    def documents(snippet: str, preamble: str, width_cm: float = 15.0):
        r"""시도할 문서들을 "욕심 많은 것부터" 순서대로 만든다.

        원고의 preamble 은 문서 클래스를 전제로 쓰인 것이라(geometry,
        fancyhdr 등) standalone 에서 깨질 수 있고, kotex 이 없는 환경도 있다.
        한 번에 실패시키는 대신 한 겹씩 벗겨 가며 다시 시도한다. 어느 단계로
        그려졌는지는 패널에 알려서, 매크로가 빠진 그림을 진짜라고 믿지
        않게 한다.
        """
        head = r"\documentclass[preview,border=5pt,varwidth=%.1fcm]{standalone}" % width_cm
        base = r"\usepackage{amsmath,amssymb}"
        body = "\n".join((r"\begin{document}", snippet, r"\end{document}"))

        out = []
        if preamble.strip():
            out.append(("원고 프리앰블",
                        "\n".join((head, base, r"\usepackage{kotex}", preamble, body))))
            out.append(("원고 프리앰블 (kotex 없이)",
                        "\n".join((head, base, preamble, body))))
        out.append(("기본 + kotex",
                    "\n".join((head, base, r"\usepackage{kotex}", body))))
        out.append(("기본만", "\n".join((head, base, body))))
        return out

    @classmethod
    def available_backends(cls):
        return [b for b in cls.BACKENDS if shutil.which(b[0]) is not None]

    @classmethod
    def render_sync(cls, snippet: str, preamble: str, outdir: Path):
        """(성공?, 경로 또는 메시지, 쓰인 단계) 를 돌려준다."""
        backends = cls.available_backends()
        if not backends:
            return False, ("렌더 도구를 찾지 못했습니다 — "
                           "dvisvgm, pdftocairo, pdftoppm 중 하나가 필요합니다."), ""

        outdir.mkdir(parents=True, exist_ok=True)
        src = outdir / "preview.tex"
        last = "컴파일 실패"

        for stage, tex in cls.documents(snippet, preamble):
            src.write_text(tex, encoding="utf-8")
            tex_failed = False
            for name, tex_args, make_cmd, suffix in backends:
                dst = outdir / ("preview" + suffix)
                for f in (dst, src.with_suffix(".pdf"), src.with_suffix(".xdv")):
                    f.unlink(missing_ok=True)
                run = subprocess.run(
                    ["xelatex", "-interaction=nonstopmode", "-halt-on-error",
                     *tex_args, src.name],
                    cwd=outdir, capture_output=True, timeout=cls.TIMEOUT,
                    creationflags=_NO_WINDOW)
                if run.returncode != 0:
                    last = cls._first_error(outdir / "preview.log")
                    tex_failed = True
                    break                      # TeX 쪽 문제 — 다음 후보 문서로
                conv = subprocess.run(make_cmd(src, dst), cwd=outdir,
                                      capture_output=True, timeout=cls.TIMEOUT,
                                      creationflags=_NO_WINDOW)
                if conv.returncode == 0 and dst.exists() and dst.stat().st_size:
                    return True, str(dst), stage
                last = f"{name} 변환에 실패했습니다."
            if not tex_failed:
                break                          # 변환 도구 문제 — 후보를 바꿔도 같다
        return False, last, ""

    @staticmethod
    def _first_error(log: Path) -> str:
        """.log 에서 첫 오류 줄만 뽑는다. 전체를 보여줄 자리가 없다."""
        try:
            lines = log.read_text(encoding="utf-8", errors="replace").splitlines()
        except OSError:
            return "컴파일 실패"
        for i, line in enumerate(lines):
            if line.startswith("!"):
                tail = next((l for l in lines[i + 1:i + 6] if l.startswith("l.")), "")
                return f"{line.strip()}  {tail.strip()}".strip()
        return "컴파일 실패"


# ===========================================================================
# 9-h. 미리보기 패널
# ===========================================================================

class PreviewPanel(QWidget):
    """편집창 아래의 미리보기.

    호버가 아니라 커서를 따라간다. 글을 쓰다 눈을 아래로 내리면 거기 있고,
    읽는 중에 튀어나오지 않는다.
    """

    IMAGE_DIRECT = {".png", ".jpg", ".jpeg", ".gif", ".bmp", ".webp", ".svg"}
    IMAGE_CONVERT = {".pdf", ".eps", ".ps"}

    def __init__(self, window: "MainWindow"):
        super().__init__(window)
        self._win = window
        self._source = None      # 현재 보여주는 파일 경로
        self._raster = None      # SVG 가 아닐 때의 원본 픽스맵
        self._head_raw = None    # 제목 줄의 생략 전 원본(창 크기 바뀌면 다시 생략한다)

        self.head = QLabel("미리보기")
        self.body = QLabel()
        self.body.setAlignment(Qt.AlignCenter)
        self.body.setWordWrap(True)

        #: 원격 그림을 아직 안 받았을 때만 보인다.
        self.fetch_btn = QPushButton("지금 가져오기")
        self.fetch_btn.setVisible(False)
        self.fetch_btn.setMaximumWidth(140)

        scroll = QScrollArea()
        scroll.setWidget(self.body)
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QScrollArea.NoFrame)
        #: 세로로 긴 그림을 보여줄 때, 안의 QLabel 이 그 그림 원래
        #: 크기를 "이 정도는 돼야 한다"는 요구(sizeHint)로 들고 올리는
        #: 바람에 스플리터를 거쳐 앱 전체 창까지 커지는 문제가 있었다.
        #: 세로 방향 크기 요구를 무시하게 해서, 이 패널이 실제로
        #: 차지하는 세로 공간은 오직 스플리터가 정해 준 만큼으로만
        #: 묶인다 — 다 못 보여주는 부분은 스크롤로 본다.
        scroll.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Ignored)
        self.scroll = scroll

        box = QVBoxLayout(self)
        box.setContentsMargins(10, 4, 10, 6)
        box.setSpacing(3)
        box.addWidget(self.head)
        box.addWidget(scroll, 1)
        box.addWidget(self.fetch_btn, 0, Qt.AlignHCenter)
        self.setMinimumHeight(90)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Ignored)

    # -- 표시 ---------------------------------------------------------------

    def _set_head(self, text: str):
        """제목 줄에 글자를 건다 — 그림 URL처럼 아주 길어질 수 있어서
        패널 너비에 맞춰 가운데를 생략한다("...") — 길이 전체가
        가로로 펼쳐져 창 전체를 넓히는 일이 없도록. 창 크기가 바뀌면
        다시 계산해야 하므로 원본 글자를 따로 들고 있는다."""
        self._head_raw = text
        self._apply_head_elision()

    def _apply_head_elision(self):
        if self._head_raw is None:
            return
        metrics = self.head.fontMetrics()
        avail = max(20, self.width() - 20)
        self.head.setText(metrics.elidedText(self._head_raw, Qt.ElideMiddle, avail))

    def set_message(self, head: str, body: str = ""):
        self._set_head(head)
        self._source = self._raster = None
        self.body.setPixmap(QPixmap())
        self.body.setText(body)
        self.fetch_btn.setVisible(False)

    def set_fetch_prompt(self, head: str, body: str, on_click):
        """원격 그림을 아직 안 받았을 때 — 버튼을 눌러야 나간다."""
        self.set_message(head, body)
        try:
            self.fetch_btn.clicked.disconnect()
        except (TypeError, RuntimeError):
            pass  # 아직 아무 것도 연결된 적 없으면 여기로 온다 — 정상이다
        self.fetch_btn.clicked.connect(on_click)
        self.fetch_btn.setVisible(True)

    def set_fetching(self, head: str):
        self.set_message(head, "받는 중…")

    #: 수식은 원래 크기가 아주 작다. 패널을 채우도록 키우되 한계를 둔다.
    MAX_SCALE = 3.2
    FILL = 0.88

    def set_image(self, path: str, head: str):
        self._set_head(head)
        self.body.setText("")
        self._source = path
        self._raster = None if path.lower().endswith(".svg") else QPixmap(path)
        if self._raster is not None and self._raster.isNull():
            self.set_message(head, "그릴 수 없는 파일입니다.")
            return
        self._redraw()

    def set_pixmap(self, pm: QPixmap, head: str):
        """이미 그려진 픽스맵을 그대로 보인다(파이프 표 미리보기). 파일이 아니므로
        _redraw 의 다시 그리기 대상이 아니다 — 큰 표는 스크롤로 본다."""
        self._set_head(head)
        self._source = self._raster = None
        self.body.setText("")
        self.body.setPixmap(pm)
        self.fetch_btn.setVisible(False)

    def _redraw(self):
        """SVG 는 벡터이므로 매번 패널 크기에 맞춰 다시 그린다.

        한 번 구운 픽스맵을 확대·축소하면 수식처럼 원래 크기가 작은 것이
        흐려진다. 다시 그리면 어떤 크기에서도 선명하다.
        """
        if self._source is None:
            return
        avail = self.scroll.viewport().size()
        if avail.width() < 8 or avail.height() < 8:
            return
        box = QSize(int(avail.width() * self.FILL), int(avail.height() * self.FILL))

        if self._raster is not None:
            pm = self._raster
            if pm.width() > box.width() or pm.height() > box.height():
                pm = pm.scaled(box, Qt.KeepAspectRatio, Qt.SmoothTransformation)
            self.body.setPixmap(pm)
            return

        renderer = QSvgRenderer(self._source)
        if not renderer.isValid():
            self.set_message(self.head.text(), "그릴 수 없는 파일입니다.")
            return
        native = renderer.defaultSize()
        if native.width() <= 0 or native.height() <= 0:
            return
        scale = min(box.width() / native.width(), box.height() / native.height())
        scale = min(scale, self.MAX_SCALE)
        dpr = self.devicePixelRatioF()
        lw, lh = native.width() * scale, native.height() * scale   # 논리 크기
        pm = QPixmap(max(1, int(round(lw * dpr))), max(1, int(round(lh * dpr))))
        pm.setDevicePixelRatio(dpr)
        pm.fill(Qt.transparent)
        painter = QPainter(pm)
        # 그릴 영역을 명시해야 한다. render(painter) 만 부르면 dpr 이 1 이 아닐 때
        # (HiDPI·분수 배율 화면) SVG 가 dpr 배로 크게 그려져 오른쪽·아래가 잘린다.
        renderer.render(painter, QRectF(0, 0, lw, lh))
        painter.end()
        self.body.setPixmap(pm)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._redraw()
        self._apply_head_elision()

    #: LaTeX 이 굽는 글자는 항상 검은 잉크다. 앱이 다크 테마여도 미리보기
    #: 바탕은 밝게 고정해야 글자가 보인다 — 조판 결과가 실제로 검은 잉크
    #: 위에 놓이는 것과도 더 가깝다.
    CANVAS_BG = "#EFEBDD"
    CANVAS_ERROR_FG = "#A8432A"

    def apply_theme(self, theme: Theme):
        self.setStyleSheet(f"""
            QWidget {{ background: {theme.panel_bg}; }}
            QScrollArea {{ background: {self.CANVAS_BG};
                           border: 1px solid {theme.gutter_fg}; border-radius: 4px; }}
            QLabel {{ background: transparent; color: {theme.gutter_fg_active};
                      font-size: 11px; }}
        """)
        self.body.setStyleSheet(
            f"QLabel {{ background: {self.CANVAS_BG}; color: {self.CANVAS_ERROR_FG}; "
            f"padding: 8px; }}")
        self._redraw()


# ===========================================================================
# 9-i. 마크업 점검
# ===========================================================================

#: ndhmd4tex 는 자기 출력을 _PrefixedStream 으로 감싸 모든 줄 앞에
#: `[ndhmd] ` 를 붙인다(grep 으로 컴파일러 로그와 갈라내기 위해서다).
#: 이걸 먼저 떼지 않으면 접두어가 경로의 일부로 읽혀, 절대경로가
#: 상대경로로 오인되고 대상 폴더에 이어 붙는다.
TOOL_PREFIX_RE = re.compile(r"^\[[A-Za-z0-9_.\-]{1,20}\]\s+")

#: ndhmd4tex --lint 의 한 줄. `경로:줄: 등급: 메시지`
LINT_LINE_RE = re.compile(r"^(.*?):(\d+):\s*(오류|경고):\s*(.*)$")


def strip_tool_prefix(line: str) -> str:
    return TOOL_PREFIX_RE.sub("", line, count=1)


class IssuePanel(QTreeWidget):
    """마크업 점검 결과.

    대화창이 아니라 패널인 이유는 단순하다. 모달이면 42행 오류를 읽고,
    닫고, 42행으로 가고, 그 사이 87행을 잊는다. 고치는 동안 떠 있으면서
    누르면 그 줄로 가는 쪽이 맞다.
    """

    MAX_ROWS = 10

    def __init__(self, window: "MainWindow"):
        super().__init__(window)
        self._win = window
        self.setHeaderHidden(True)
        self.setRootIsDecorated(True)
        self.setUniformRowHeights(True)
        self.setSizePolicy(self.sizePolicy().horizontalPolicy(), QSizePolicy.Fixed)
        self.itemClicked.connect(self._on_activate)
        self.itemActivated.connect(self._on_activate)

    def populate(self, issues, header: str):
        """issues: [(Path, 줄, 등급, 메시지), ...]"""
        self.clear()
        by_file = {}
        for path, line, level, msg in issues:
            by_file.setdefault(path, []).append((line, level, msg))

        rows = 0
        top = QTreeWidgetItem(self, [f"{header}        ✕ 닫기"])
        top.setData(0, Qt.UserRole, "close")
        top.setExpanded(True)
        rows += 1
        for path, items in by_file.items():
            parent = QTreeWidgetItem(self, [
                f"{path.name}   (오류 {sum(1 for _, lv, _ in items if lv == '오류')}"
                f" · 경고 {sum(1 for _, lv, _ in items if lv != '오류')})"])
            parent.setData(0, Qt.UserRole, None)
            parent.setExpanded(True)
            rows += 1
            for line, level, msg in items:
                mark = "●" if level == "오류" else "○"
                child = QTreeWidgetItem(parent, [f"{mark} {line:>5}   {msg}"])
                child.setData(0, Qt.UserRole, (str(path), line))
                child.setToolTip(0, msg)
                rows += 1
        self._fit(rows)
        self.setVisible(True)

    def _fit(self, rows: int):
        unit = self.fontMetrics().height() + 6
        self.setFixedHeight(int(min(max(rows, 1), self.MAX_ROWS) * unit) + 8)

    def _on_activate(self, item, _col=0):
        payload = item.data(0, Qt.UserRole)
        if payload == "close":
            self.setVisible(False)
            self._win.editor.setFocus()
        elif payload:
            path, line = payload
            self._win.open_at(Path(path), line)

    def apply_theme(self, theme: Theme):
        self.setStyleSheet(f"""
            QTreeWidget {{
                background: {theme.panel_bg}; color: {theme.fg};
                border: none; border-top: 1px solid {theme.gutter_fg};
                outline: none;
            }}
            QTreeWidget::item {{ padding: 2px 4px; }}
            QTreeWidget::item:selected {{ background: {theme.match_active_bg}; color: {theme.fg}; }}
            {tree_branch_css(theme.fg)}
        """)


class Ndhmd4tex:
    """ndhmd4tex 를 어디서 찾을지 아는 객체.

    실행 파일로 깔려 있을 수도, .py 스크립트로 있을 수도 있다. 후자는
    지금 돌고 있는 파이썬으로 실행한다 — 사용자가 venv 를 쓰는 경우가
    흔하고, 그때 시스템 python3 로 부르면 yaml 이 없다는 소리를 듣는다.
    """

    SETTING = "tool/ndhmd4tex"

    def __init__(self, settings: QSettings):
        self._settings = settings

    def path(self):
        saved = self._settings.value(self.SETTING, "")
        if saved and Path(saved).exists():
            return Path(saved)
        found = shutil.which("ndhmd4tex") or shutil.which("ndhmd4tex.py")
        return Path(found) if found else None

    def set_path(self, path: Path):
        self._settings.setValue(self.SETTING, str(path))

    def command(self, args: list):
        tool = self.path()
        if tool is None:
            return None
        if tool.suffix.lower() == ".py":
            return [sys.executable, str(tool), *args]
        return [str(tool), *args]


class NdhmdSyncTool:
    """ndhmdsync 를 어디서 찾을지 아는 객체. Ndhmd4tex 와 완전히 같은
    패턴이다 — 실행 파일일 수도 .py 스크립트일 수도 있고, 후자는
    지금 돌고 있는 파이썬으로 돌린다."""

    SETTING = "tool/ndhmdsync"

    def __init__(self, settings: QSettings):
        self._settings = settings

    def path(self):
        saved = self._settings.value(self.SETTING, "")
        if saved and Path(saved).exists():
            return Path(saved)
        found = shutil.which("ndhmdsync") or shutil.which("ndhmdsync.py")
        return Path(found) if found else None

    def set_path(self, path: Path):
        self._settings.setValue(self.SETTING, str(path))

    def command(self, args: list):
        tool = self.path()
        if tool is None:
            return None
        if tool.suffix.lower() == ".py":
            return [sys.executable, str(tool), *args]
        return [str(tool), *args]


# ===========================================================================
# 9-j. 설정
# ===========================================================================

class Prefs:
    """설정값을 한곳에서 읽고 쓴다. 키 이름을 여기 한 번만 적는다."""

    THEMES = ("system", "light", "dark")
    BACKENDS = ("ksruncltex", "latexmk")
    ENGINES = ("xelatex", "lualatex", "pdflatex")
    #: 컴파일이 성공한 뒤 PDF 를 어떻게 여는가. forward 는 정방향 검색(ndhmdsync 가
    #: 등록된 PDF 뷰어를 그 자리에 연다)이라, 시스템 뷰어가 따로 또 뜨지 않는다.
    AFTER_COMPILE = (("forward", "정방향 검색으로 열기 (커서 위치)"),
                     ("system", "시스템 PDF 뷰어로 열기"),
                     ("none", "열지 않음"))

    def __init__(self, settings: QSettings):
        self.s = settings

    def font_family(self) -> str:
        return self.s.value("prefs/font_family", "", type=str)

    def font_size(self) -> float:
        return self.s.value("prefs/font_size", 12.5, type=float)

    def font_mono_only(self) -> bool:
        """환경설정의 글꼴 목록을 고정폭 글꼴로 한정할지. 기본 켜짐."""
        return self.s.value("prefs/font_mono_only", True, type=bool)

    def tab_spaces(self) -> int:
        return self.s.value("prefs/tab_spaces", 4, type=int)

    def tab_to_spaces(self) -> bool:
        return self.s.value("prefs/tab_to_spaces", True, type=bool)

    def smart_quotes_style(self) -> str:
        """"off"(기본, 안 건드림) / "curly"(영어식 곡선) /
        "cjk"(낫표) / "french"(기메)."""
        return self.s.value("prefs/smart_quotes", "off", type=str)

    def smart_punctuation(self) -> bool:
        """마침표·쉼표를 고리점(。)·모점(、)으로 바꿀지."""
        return self.s.value("prefs/smart_punctuation", False, type=bool)

    def jigsaw_preamble(self) -> str:
        """조각 그림 도구에서 마지막으로 쓴 프리앰블(새 그림의 시작값)."""
        return self.s.value("prefs/jigsaw_preamble", JigsawFigure.DEFAULT_PREAMBLE, type=str)

    def jigsaw_engine(self) -> str:
        """조각 그림 도구에서 마지막으로 고른 엔진."""
        v = self.s.value("prefs/jigsaw_engine", "xelatex", type=str)
        return v if v in JigsawFigure.ENGINES else "xelatex"

    def jigsaw_class(self) -> str:
        """조각 그림 도구에서 마지막으로 고른 문서 클래스."""
        v = self.s.value("prefs/jigsaw_class", "standalone", type=str)
        return v if v in JigsawFigure.CLASSES else "standalone"

    def auto_preview(self) -> bool:
        """커서가 수식·그림·표 위에 일정 시간 머물면 미리보기 패널을
        자동으로 열고, 벗어나면(수동으로 켜 둔 게 아니라면) 자동으로
        닫을지. 기본은 꺼짐 — 미리보기 패널의 원래 설계 철학("읽는
        중에 튀어나오지 않는다")과 반대 방향이라 옵트인으로 둔다."""
        return self.s.value("prefs/auto_preview", False, type=bool)

    def animation(self) -> bool:
        """ndhmd4tex 에 --animation 을 넘길지. 애니메이션 gif/webp 를 프레임으로 쪼개
        \\animategraphics 로 넣는다. 기본 꺼짐(꺼져 있으면 첫 프레임만 쓴다)."""
        return self.s.value("prefs/animation", False, type=bool)

    def animation_frames(self) -> int:
        """애니메이션에서 쓸 프레임 상한. 0 = 전부(--animation=all)."""
        return self.s.value("prefs/animation_frames", 40, type=int)

    def auto_preview_delay(self) -> float:
        """자동 미리보기가 뜨기까지 머물러야 하는 시간(초). 0.5~3.0."""
        return self.s.value("prefs/auto_preview_delay", 1.5, type=float)

    def word_wrap(self) -> bool:
        return self.s.value("prefs/word_wrap", True, type=bool)

    def set_word_wrap(self, on: bool):
        self.s.setValue("prefs/word_wrap", on)

    def remember_geometry(self) -> bool:
        return self.s.value("prefs/remember_geometry", True, type=bool)

    def item_gap(self) -> bool:
        """설명 목록(`항목 :: 설명`) 항목 사이를 화면에서만 벌린다. 기본 꺼짐."""
        return self.s.value("prefs/item_gap", False, type=bool)

    def item_gap_scale(self) -> float:
        return self.s.value("prefs/item_gap_scale", 2.0, type=float)

    def item_gap_bullets(self) -> bool:
        return self.s.value("prefs/item_gap_bullets", False, type=bool)

    def hanja_recent_first(self) -> bool:
        """한자 후보에서 최근에 고른 한자를 같은 읽기 안에서 앞세운다. 기본 꺼짐."""
        return self.s.value("prefs/hanja_recent_first", False, type=bool)

    def hanja_hangul_first(self) -> bool:
        """한자 병기: 원래 한글을 두고 한자를 괄호로 덧붙인다(국가(國家)). 기본 꺼짐."""
        return self.s.value("prefs/hanja_hangul_first", False, type=bool)

    def hanja_parenthesize(self) -> bool:
        """한자를 넣을 때 읽기를 괄호로 병기한다(國家(국가)). 기본 꺼짐."""
        return self.s.value("prefs/hanja_parenthesize", False, type=bool)

    def auto_close_drawer(self) -> bool:
        """글을 고치기 시작하면(저장된 상태에서 처음 고칠 때) 서랍을 자동으로 닫는다. 기본 꺼짐."""
        return self.s.value("prefs/auto_close_drawer", False, type=bool)

    def clean_sub_products(self) -> bool:
        """책 전체 컴파일이 성공하면 그 책 하위 파일의 단독 산출물
        (.tex/.nmdsync/.synctex)을 지운다. 기본 켜짐."""
        return self.s.value("prefs/clean_sub_products", True, type=bool)

    def reopen_last(self) -> bool:
        """시작할 때 마지막에 열어 둔 원고를 다시 연다. 기본 꺼짐."""
        return self.s.value("prefs/reopen_last", False, type=bool)

    def last_shell_command(self) -> str:
        return self.s.value("prefs/last_shell_command", "", type=str)

    def tblrdoumi_path(self) -> str:
        """직접 지정해 둔 tblrDoumi 실행 파일(.app/.exe) 경로 — 정해진
        자리에서 못 찾았을 때 물어봐서 저장해 둔 것."""
        return self.s.value("prefs/tblrdoumi_path", "", type=str)

    def drawer_sort(self) -> str:
        """서랍 최상위 파일 정렬 — "name"(이름순, 기본) 또는
        "mtime"(최신 수정순). 장/절(자식) 순서는 안 건드린다 — 그건
        {{}} 로 정한 책의 구조라 알파벳/수정 시각과 무관해야 맞다."""
        return self.s.value("prefs/drawer_sort", "name", type=str)

    def bib_delimiter(self) -> str:
        """참고문헌 그리드에서 author 뒤에 쉼표를 찍을지 마침표를 찍을지.
        스타일 가이드마다 다르다 — 흔한 두 관례 중 고르게만 해 둔다."""
        return self.s.value("prefs/bib_delimiter", ",", type=str)

    def custom_symbols(self) -> list:
        """보조 입력 ▸ 사용자 탭에 직접 추가해 둔 기호들."""
        raw = self.s.value("prefs/custom_symbols", "", type=str)
        if not raw:
            return []
        try:
            data = json.loads(raw)
        except (json.JSONDecodeError, TypeError):
            return []
        return data if isinstance(data, list) else []

    def set_custom_symbols(self, symbols: list):
        self.s.setValue("prefs/custom_symbols", json.dumps(symbols, ensure_ascii=False))

    def fullscreen_column(self) -> int:
        return self.s.value("prefs/fullscreen_column", 120, type=int)

    def reflow_width(self) -> int:
        return self.s.value("prefs/reflow_width", 80, type=int)

    def reflow_single_line(self) -> bool:
        return self.s.value("prefs/reflow_single_line", False, type=bool)

    def auto_fetch_images(self) -> bool:
        #: 기본 꺼짐 — ndhmd4tex 의 --fetch-images 기본값과 같은 이유다.
        #: 미리보기는 컴파일보다 훨씬 자주 열리므로, 자동으로 켜 두면
        #: 남의 원고를 열어보기만 해도 그쪽 서버에 요청이 나간다.
        return self.s.value("prefs/auto_fetch_images", False, type=bool)

    def theme(self) -> str:
        return self.s.value("prefs/theme", "system", type=str)

    def compiler_backend(self) -> str:
        return self.s.value("prefs/compiler_backend", self.BACKENDS[0], type=str)

    def tex_engine(self) -> str:
        return self.s.value("prefs/tex_engine", self.ENGINES[0], type=str)

    def after_compile(self) -> str:
        v = self.s.value("prefs/after_compile", "forward", type=str)
        return v if v in dict(self.AFTER_COMPILE) else "forward"

    def resolved_theme(self) -> Theme:
        """'system' 은 여기서 실제 Theme 객체로 풀린다."""
        choice = self.theme()
        if choice in THEMES:
            return THEMES[choice]
        try:
            scheme = QGuiApplication.styleHints().colorScheme()
            return DARK if scheme == Qt.ColorScheme.Dark else LIGHT
        except AttributeError:
            return LIGHT          # Qt 6.5 미만 — 밝은 테마로 물러난다

    def write(self, **kwargs):
        for k, v in kwargs.items():
            self.s.setValue(f"prefs/{k}", v)


class FontFamilyCombo(QComboBox):
    """글꼴 가족 콤보. QFontComboBox 의 `고정폭` 필터는 글꼴의 fixedPitch 표시를 보는데,
    Noto Sans Mono CJK 처럼 라틴 반각·한글 전각으로 폭이 둘인 "CJK 모노" 글꼴은 그 표시가
    꺼져 있어(Qt 가 not-fixed 로 본다) 필터에 걸려 사라진다. 그래서 고정폭 한정 모드에서는
    fixedPitch 이거나 이름에 Mono/Code/Courier 같은 표지가 있는 글꼴도 함께 나열한다."""

    MONO_NAME_RE = re.compile(r"mono|code|courier|consol|menlo|typewriter|terminal|term\b|"
                              r"d2coding|sarasa|nanumgothiccoding|나눔고딕코딩", re.I)

    def __init__(self, parent=None):
        super().__init__(parent)
        self._mono_only = True
        self._rebuild()

    @classmethod
    def is_mono_like(cls, family: str) -> bool:
        return QFontDatabase.isFixedPitch(family) or bool(cls.MONO_NAME_RE.search(family))

    def _rebuild(self, keep: str = ""):
        keep = keep or self.currentText()
        self.blockSignals(True)
        self.clear()
        for fam in sorted(set(QFontDatabase.families()), key=str.casefold):
            if self._mono_only and not self.is_mono_like(fam):
                continue
            self.addItem(fam)
            self.setItemData(self.count() - 1, QFont(fam), Qt.FontRole)   # 목록에서 글꼴 미리보기
        self.blockSignals(False)
        if keep:
            self.setCurrentFont(QFont(keep))

    def set_mono_only(self, on: bool):
        if on != self._mono_only:
            self._mono_only = on
            self._rebuild()

    def setCurrentFont(self, font: QFont):
        i = self.findText(font.family())
        if i >= 0:
            self.setCurrentIndex(i)

    def currentFont(self) -> QFont:
        return QFont(self.currentText())


class PreferencesDialog(QDialog):
    """설정 창. 폰트·탭·테마·컴파일러 백엔드는 저장하면 바로 반영된다."""

    def __init__(self, window: "MainWindow"):
        super().__init__(window)
        self._win = window
        self.prefs = window.prefs
        self.setWindowTitle("설정")
        self.setMinimumWidth(420)

        form = QFormLayout()
        form.setLabelAlignment(Qt.AlignRight)

        # -- 글꼴 --
        self.font_combo = FontFamilyCombo()
        current = self.prefs.font_family()
        mono_only = self.prefs.font_mono_only()
        if current and not FontFamilyCombo.is_mono_like(current):
            mono_only = False       # 이미 고정폭이 아닌 글꼴을 쓰고 있으면 목록에서 사라지지 않게
        self.font_mono_only = QCheckBox("고정폭 글꼴만")
        self.font_mono_only.setChecked(mono_only)
        self.font_mono_only.setToolTip(
            "끄면 모든 글꼴을 고르는 목록에 나열합니다. 옛한글처럼 고정폭 글꼴에 없는 글자를\n"
            "쓸 때 필요합니다. 고정폭이 아니면 표·코드의 열이 어긋나 보일 수 있고, 본문 폭 계산\n"
            "(\"0\" 글자 폭 기준)도 글꼴에 따라 달라집니다.")
        self._apply_font_filter()
        if current:
            self.font_combo.setCurrentFont(QFont(current))
        self.font_mono_only.toggled.connect(self._apply_font_filter)
        self.font_size = QDoubleSpinBox()
        self.font_size.setRange(7.0, 32.0)
        self.font_size.setSingleStep(0.5)
        self.font_size.setValue(self.prefs.font_size())
        font_row = QHBoxLayout()
        font_row.addWidget(self.font_combo, 1)
        font_row.addWidget(self.font_size)
        form.addRow("편집창 글꼴", font_row)
        form.addRow("", self.font_mono_only)

        # -- 탭 --
        self.tab_spaces = QSpinBox()
        self.tab_spaces.setRange(1, 8)
        self.tab_spaces.setValue(self.prefs.tab_spaces())
        form.addRow("탭 너비(칸)", self.tab_spaces)

        self.tab_to_spaces = QCheckBox("탭 문자(\\t)를 스페이스로")
        self.tab_to_spaces.setChecked(self.prefs.tab_to_spaces())
        self.tab_to_spaces.setToolTip(
            "YAML 프론트매터에 탭 문자가 섞이면 파서가 바로 오류를 냅니다. "
            "끄면 Tab 키가 탭 문자를 그대로 넣습니다 — 탭 문자를 선호하는 "
            "분들을 위해 꺼 둘 수 있게 했습니다.")
        form.addRow("", self.tab_to_spaces)

        # -- 목록 항목 간격(표시 전용) --
        self.item_gap = QCheckBox("설명 목록 항목 사이 간격 (화면 표시만)")
        self.item_gap.setChecked(self.prefs.item_gap())
        self.item_gap.setToolTip(
            "ndhmd4tex 는 목록 항목 사이의 빈 줄을 허용하지 않습니다. 대신 `항목 :: 설명` 줄의\n"
            "`::` 앞 공백 한 글자를 크게 그려 그 줄을 높입니다. 원고 내용·줄 번호·실행 취소에는\n"
            "영향이 없고 화면에서만 항목이 벌어져 보입니다. 기본은 꺼져 있습니다.")
        self.item_gap_scale = QDoubleSpinBox()
        self.item_gap_scale.setRange(1.2, 4.0)
        self.item_gap_scale.setSingleStep(0.2)
        self.item_gap_scale.setDecimals(1)
        self.item_gap_scale.setSuffix(" 배")
        self.item_gap_scale.setValue(self.prefs.item_gap_scale())
        self.item_gap_scale.setEnabled(self.item_gap.isChecked())
        self.item_gap.toggled.connect(self.item_gap_scale.setEnabled)
        gap_row = QHBoxLayout()
        gap_row.addWidget(self.item_gap)
        gap_row.addWidget(self.item_gap_scale)
        gap_row.addStretch(1)
        form.addRow("", gap_row)
        self.item_gap_bullets = QCheckBox("글머리표·번호 목록에도 적용")
        self.item_gap_bullets.setChecked(self.prefs.item_gap_bullets())
        self.item_gap_bullets.setToolTip("`- `, `1. ` 뒤의 공백을 키웁니다. 위 항목이 꺼져 있으면 무시됩니다.")
        self.item_gap_bullets.setEnabled(self.item_gap.isChecked())
        self.item_gap.toggled.connect(self.item_gap_bullets.setEnabled)
        form.addRow("", self.item_gap_bullets)

        # -- 한자 변환 --
        self.hanja_recent = QCheckBox("한자 변환: 최근 입력한 한자 우선")
        self.hanja_recent.setChecked(self.prefs.hanja_recent_first())
        self.hanja_recent.setToolTip(
            "F9 후보 창에서 한 번 고른 한자를 같은 읽기의 후보 맨 앞으로 올립니다.\n"
            "예: `가` 에서 歌 를 골랐으면 다음부터 歌 가 먼저 나옵니다.")
        form.addRow("", self.hanja_recent)
        self.hanja_paren = QCheckBox("한자 변환: 한글 병기 — 國家(국가)")
        self.hanja_paren.setChecked(self.prefs.hanja_parenthesize())
        self.hanja_paren.setToolTip("한자를 넣을 때 읽기를 괄호로 덧붙입니다.")
        form.addRow("", self.hanja_paren)
        self.hanja_hg = QCheckBox("한자 변환: 한자 병기 — 국가(國家)")
        self.hanja_hg.setChecked(self.prefs.hanja_hangul_first())
        self.hanja_hg.setToolTip("원래 한글을 그대로 두고 한자를 괄호로 덧붙입니다. 한글 병기와는 둘 중 하나만 켜집니다.")
        form.addRow("", self.hanja_hg)
        # 두 병기는 함께 쓸 수 없다 — 하나를 켜면 다른 하나는 꺼진다.
        self.hanja_paren.toggled.connect(lambda on: on and self.hanja_hg.setChecked(False))
        self.hanja_hg.toggled.connect(lambda on: on and self.hanja_paren.setChecked(False))

        # -- 창 크기·위치 --
        self.remember_geometry = QCheckBox("창 크기·위치 기억")
        self.remember_geometry.setChecked(self.prefs.remember_geometry())
        self.remember_geometry.setToolTip(
            "켜 두면 다음에 실행할 때 지난번 창 크기와 위치를 그대로 "
            "되살립니다.")
        form.addRow("", self.remember_geometry)

        self.reopen_last = QCheckBox("마지막 원고 다시 열기")
        self.reopen_last.setChecked(self.prefs.reopen_last())
        self.reopen_last.setToolTip(
            "켜면 앱을 시작할 때 직전에 열어 두었던 원고를 그 줄 위치까지 다시 엽니다.\n"
            "작업공간은 원래 저장되어 있으므로, 그 작업공간 안의 파일일 때만 열립니다.\n"
            "PDF 뷰어의 역방향 검색이나 파일 인자로 시작할 때는 그쪽이 우선합니다.\n"
            "기본은 꺼져 있습니다.")
        form.addRow("", self.reopen_last)
        self.auto_close_drawer = QCheckBox("글쓰기가 시작되면 서랍을 자동으로 닫기")
        self.auto_close_drawer.setChecked(self.prefs.auto_close_drawer())
        self.auto_close_drawer.setToolTip(
            "저장된 상태의 원고를 처음 고치는 순간 서랍을 닫아 글쓰기에 집중하게 합니다.\n"
            "서랍은 Ctrl+B 로 다시 열 수 있고, 다시 열어 두면 계속 고치는 동안에는 닫히지 않습니다\n"
            "(저장한 뒤 다시 고치기 시작할 때 또 닫힙니다).")
        form.addRow("", self.auto_close_drawer)
        self.clean_sub_products = QCheckBox("책을 컴파일하면 하위 파일의 단독 산출물 지우기")
        self.clean_sub_products.setChecked(self.prefs.clean_sub_products())
        self.clean_sub_products.setToolTip(
            "책 전체 컴파일이 성공하면, 그 책에 포함된 하위 파일의 .tex·.nmdsync·.synctex 를\n"
            "지웁니다(이전에 '이 파일만' 컴파일해서 생긴 낡은 것). PDF 는 지우지 않습니다.\n"
            "정방향 검색은 하위 파일 자신의 .nmdsync 와 PDF 가 있으면 그쪽으로,\n"
            "없으면 책의 PDF 로 갑니다.")
        form.addRow("", self.clean_sub_products)

        # -- 전체화면 폭 제한 --
        self.fs_column = QSpinBox()
        self.fs_column.setRange(40, 300)
        self.fs_column.setValue(self.prefs.fullscreen_column())
        self.fs_column.setSuffix(" 자")
        form.addRow("전체화면 편집 폭", self.fs_column)
        hint = QLabel("전체화면일 때만 적용됩니다. 창 모드에서는 창 크기를 따릅니다.")
        hint.setStyleSheet("color: palette(mid); font-size: 11px;")
        hint.setWordWrap(True)
        form.addRow("", hint)

        # -- 문단 재배열 --
        self.reflow_width = QSpinBox()
        self.reflow_width.setRange(20, 200)
        self.reflow_width.setValue(self.prefs.reflow_width())
        self.reflow_width.setSuffix(" 자")
        form.addRow("문단 재배열 너비", self.reflow_width)
        self.reflow_single = QCheckBox("한 줄로 합치기(끄면 위 너비에서 줄바꿈)")
        self.reflow_single.setChecked(self.prefs.reflow_single_line())
        self.reflow_single.toggled.connect(
            lambda on: self.reflow_width.setEnabled(not on))
        self.reflow_width.setEnabled(not self.reflow_single.isChecked())
        form.addRow("", self.reflow_single)

        # -- 원격 그림 --
        self.auto_fetch = QCheckBox("미리보기에서 원격 그림 자동으로 가져오기")
        self.auto_fetch.setChecked(self.prefs.auto_fetch_images())
        self.auto_fetch.setToolTip(
            "꺼두면 URL 그림은 '지금 가져오기'를 눌러야 내려받습니다.\n"
            "남이 준 원고를 열 때 의도치 않게 외부로 요청이 나가지 않도록 "
            "기본은 꺼져 있습니다.")
        form.addRow("", self.auto_fetch)

        # -- 자동 미리보기 --
        self.auto_preview = QCheckBox("커서가 수식·그림·표 위에 머물면 미리보기 자동으로 열기")
        self.auto_preview.setChecked(self.prefs.auto_preview())
        self.auto_preview.setToolTip(
            "기본은 꺼져 있습니다 — 미리보기 패널은 원래 \"읽는 중에 튀어나오지\n"
            "않는다\"는 게 설계 의도라, 이건 그 반대로 쓰고 싶을 때만 켜는 것입니다.\n"
            "켜 두면, 벗어났을 때도 자동으로 연 경우에만 스스로 닫힙니다 —\n"
            "Ctrl+Shift+P 로 직접 열어 둔 것은 그대로 둡니다.")
        self.auto_preview_delay = QDoubleSpinBox()
        self.auto_preview_delay.setRange(0.5, 3.0)
        self.auto_preview_delay.setSingleStep(0.1)
        self.auto_preview_delay.setDecimals(1)
        self.auto_preview_delay.setSuffix(" 초")
        self.auto_preview_delay.setValue(self.prefs.auto_preview_delay())
        self.auto_preview_delay.setEnabled(self.auto_preview.isChecked())
        self.auto_preview.toggled.connect(self.auto_preview_delay.setEnabled)
        auto_preview_row = QHBoxLayout()
        auto_preview_row.addWidget(self.auto_preview)
        auto_preview_row.addWidget(QLabel("머무는 시간"))
        auto_preview_row.addWidget(self.auto_preview_delay)
        form.addRow("", auto_preview_row)

        # -- 테마 --
        self.theme_combo = QComboBox()
        self.theme_combo.addItem("시스템을 따름", "system")
        self.theme_combo.addItem("밝게", "light")
        self.theme_combo.addItem("어둡게", "dark")
        self.theme_combo.addItem("고대비(순백)", "high_contrast")
        self.theme_combo.addItem("빨강", "red")
        self.theme_combo.addItem("노랑", "yellow")
        self.theme_combo.addItem("초록", "green")
        self.theme_combo.addItem("파랑", "blue")
        idx = self.theme_combo.findData(self.prefs.theme())
        self.theme_combo.setCurrentIndex(max(0, idx))
        form.addRow("테마", self.theme_combo)

        form.addRow(self._divider())

        # -- 인버스 서치 --
        #
        # 예전엔 체크박스였다. 그런데 이건 우리 QSettings 에만 있는
        # "그래야 한다는 바람"일 뿐, ndhmdsync.ini 의 실제 상태와는
        # 무관하다 — 누군가 밖에서 그 파일을 고쳐서 등록이 없어져도
        # 체크박스는 계속 체크된 채로 남는다. 그래서 실제 파일을 읽어
        # 지금 상태를 보여주고, "등록"은 그 자리에서 바로 실행하는
        # 버튼으로 바꿨다 — 이건 지속되는 설정이 아니라 한 번 하는
        # 동작이다.
        self.inverse_status = QLabel()
        self.inverse_status.setWordWrap(True)
        self._refresh_inverse_status()
        inverse_btn = QPushButton("지금 등록")
        inverse_btn.setToolTip(
            "SumatraPDF(Windows)·Skim(macOS)에서 Ctrl+클릭으로 이 앱을 열 수 "
            "있게 합니다. 누르면 ndhmdsync.ini 에 지금 바로 등록합니다.")
        inverse_btn.clicked.connect(self._register_inverse_now)
        inverse_row = QHBoxLayout()
        inverse_row.addWidget(self.inverse_status, 1)
        inverse_row.addWidget(inverse_btn)
        form.addRow("PDF 뷰어 역방향 검색", inverse_row)

        # -- PDF 뷰어 기본 앱 --
        #
        # ndhmdsync.ini 의 [PDFVIEW] command 를 우리가 대신 채워 준다.
        # OS 별로 정해진 설치 위치에서 찾아서 등록하는 것뿐이라, 위와
        # 같은 "상태 표시 + 버튼" 모양을 그대로 따른다.
        self.pdfview_status = QLabel()
        self.pdfview_status.setWordWrap(True)
        self._refresh_pdfview_status()
        pdfview_btn = QPushButton("감지된 뷰어로 등록")
        pdfview_btn.setToolTip(
            "Windows 는 SumatraPDF, macOS 는 Skim, Linux 는 Okular 을 "
            "정해진 설치 위치에서 찾아 ndhmdsync.ini 의 [PDFVIEW] 에 "
            "등록합니다.")
        pdfview_btn.clicked.connect(self._register_pdfview_now)
        pdfview_row = QHBoxLayout()
        pdfview_row.addWidget(self.pdfview_status, 1)
        pdfview_row.addWidget(pdfview_btn)
        form.addRow("PDF 뷰어 기본 앱", pdfview_row)

        # -- 컴파일러 백엔드 --
        self.backend_combo = QComboBox()
        self.backend_combo.addItems(Prefs.BACKENDS)
        self.backend_combo.setCurrentText(self.prefs.compiler_backend())
        self.backend_combo.setToolTip(
            "latexmk: 여러 번 컴파일이 필요한 참고문헌·색인을 알아서 반복합니다.\n"
            "ksruncltex: 실패 시 콘솔 출력을 그대로 보여줍니다(줄별 되짚기 없음).")
        self.engine_combo = QComboBox()
        self.engine_combo.addItems(Prefs.ENGINES)
        self.engine_combo.setCurrentText(self.prefs.tex_engine())
        backend_row = QHBoxLayout()
        backend_row.addWidget(self.backend_combo)
        backend_row.addWidget(self.engine_combo)
        form.addRow("컴파일러", backend_row)

        self.after_compile_combo = QComboBox()
        for key, label in Prefs.AFTER_COMPILE:
            self.after_compile_combo.addItem(label, key)
        self.after_compile_combo.setCurrentIndex(
            max(self.after_compile_combo.findData(self.prefs.after_compile()), 0))
        self.after_compile_combo.setToolTip(
            "정방향 검색: 컴파일이 끝나면 지금 커서 줄에 해당하는 PDF 자리를, 등록된 PDF 뷰어로\n"
            "엽니다. 시스템 뷰어와 등록한 뷰어가 다를 때 둘이 함께 뜨는 일이 없습니다.\n"
            "정방향 검색이 안 되는 경우(예: 하위 원고만 컴파일)에는 PDF만 연다.")
        form.addRow("컴파일 뒤", self.after_compile_combo)

        self.animation = QCheckBox("애니메이션 gif/webp 를 움직이게 넣기 (--animation)")
        self.animation.setChecked(self.prefs.animation())
        self.animation.setToolTip(
            "꺼져 있으면 애니메이션 그림도 첫 프레임만 쓴다.\n"
            "켜면 프레임을 PNG 로 쪼개 \\animategraphics 로 넣는다 — 움직임은 PDF 뷰어가\n"
            "지원할 때(Acrobat 계열)만 보이고, 그 밖의 뷰어는 첫 장만 보인다.\n"
            "프레임별 지연은 살지 않고 단일 속도로 재생한다. 프레임이 많으면\n"
            "컴파일이 느려지고 PDF 가 커진다. 적용은 다음 컴파일부터.\n"
            "※ ndhmd4tex 은 animate 패키지를 불러 주지 않는다 — 원고의 preamble 에\n"
            "\\usepackage{animate} 가 있어야 컴파일된다.")
        self.animation_frames = QSpinBox()
        self.animation_frames.setRange(0, 1000)
        self.animation_frames.setSpecialValueText("전부")
        self.animation_frames.setSuffix(" 장까지")
        self.animation_frames.setValue(self.prefs.animation_frames())
        self.animation_frames.setEnabled(self.animation.isChecked())
        self.animation.toggled.connect(self.animation_frames.setEnabled)
        anim_row = QHBoxLayout()
        anim_row.addWidget(self.animation)
        anim_row.addWidget(self.animation_frames)
        form.addRow("", anim_row)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)

        box = QVBoxLayout(self)
        box.addLayout(form)
        box.addStretch(1)
        box.addWidget(buttons)

    def _divider(self):
        line = QLabel()
        line.setFixedHeight(1)
        line.setStyleSheet("background: palette(mid);")
        return line

    def _inverse_search_status_text(self) -> str:
        """등록 여부뿐 아니라, 등록된 게 이 앱 자신인지도 구별해서
        보여준다. 다른 도구가 이미 등록해 둔 걸 이 앱 것으로 착각하면
        "지금 등록"을 눌러도 왜 안 되나 헷갈리게 된다."""
        ini_path = ndhmdsync_config_path()
        if ini_path is None or not ini_path.is_file():
            return "등록되어 있지 않습니다."
        config = configparser.ConfigParser(interpolation=None)
        try:
            config.read(ini_path, encoding="utf-8")
        except configparser.Error:
            return "설정 파일을 읽는 중 오류가 있습니다."
        cmd = config.get("EDITOR", "command", fallback="").strip()
        if not cmd:
            return "등록되어 있지 않습니다."
        if cmd == self_invoke_template():
            return "이 앱이 등록되어 있습니다."
        return f"다른 프로그램이 등록되어 있습니다:\n{cmd}"

    def _refresh_inverse_status(self):
        self.inverse_status.setText(self._inverse_search_status_text())

    def _register_inverse_now(self):
        self._win.register_as_inverse_search_target()
        self._refresh_inverse_status()

    def _pdfview_status_text(self) -> str:
        ini_path = ndhmdsync_config_path()
        if ini_path is None or not ini_path.is_file():
            return "설정 안 됨(ndhmdsync 자체 기본값 사용)"
        config = configparser.ConfigParser(interpolation=None)
        try:
            config.read(ini_path, encoding="utf-8")
        except configparser.Error:
            return "설정 파일을 읽는 중 오류가 있습니다."
        cmd = config.get("PDFVIEW", "command", fallback="").strip()
        return f"설정됨: {cmd}" if cmd else "설정 안 됨(ndhmdsync 자체 기본값 사용)"

    def _refresh_pdfview_status(self):
        self.pdfview_status.setText(self._pdfview_status_text())

    def _register_pdfview_now(self):
        self._win.register_pdf_viewer()
        self._refresh_pdfview_status()

    def _apply_font_filter(self, *_):
        """고정폭만/전체 글꼴 목록을 바꾼다. 필터를 바꾸면 목록이 다시 만들어지므로 고른 글꼴을 되돌린다."""
        family = self.font_combo.currentFont().family()
        self.font_combo.set_mono_only(self.font_mono_only.isChecked())
        if family:
            self.font_combo.setCurrentFont(QFont(family))

    def accept(self):
        # 스핀박스에 숫자를 타이핑하고 바로 Enter 를 치면, 그 Enter 가
        # 대화상자의 기본 버튼(OK)을 먼저 눌러 accept() 가 실행되고,
        # 정작 스핀박스 자신의 "입력 확정" 처리는 그 뒤에 오는 경우가
        # 있다 — 그러면 .value() 가 방금 타이핑한 값이 아니라 그 이전
        # 값을 돌려준다. 콤보박스(클릭 선택)는 이 문제가 없어서 폰트
        # 패밀리는 멀쩡한데 크기만 항상 이전 값으로 되돌아가는 것처럼
        # 보이는 증상과 정확히 맞아떨어진다. 읽기 전에 전부 강제로
        # 확정시켜 둔다.
        self.font_size.interpretText()
        self.tab_spaces.interpretText()
        self.fs_column.interpretText()
        self.reflow_width.interpretText()
        self.auto_preview_delay.interpretText()
        self.item_gap_scale.interpretText()
        self.prefs.write(
            font_family=self.font_combo.currentFont().family(),
            font_size=self.font_size.value(),
            font_mono_only=self.font_mono_only.isChecked(),
            tab_spaces=self.tab_spaces.value(),
            tab_to_spaces=self.tab_to_spaces.isChecked(),
            remember_geometry=self.remember_geometry.isChecked(),
            reopen_last=self.reopen_last.isChecked(),
            auto_close_drawer=self.auto_close_drawer.isChecked(),
            clean_sub_products=self.clean_sub_products.isChecked(),
            fullscreen_column=self.fs_column.value(),
            reflow_width=self.reflow_width.value(),
            reflow_single_line=self.reflow_single.isChecked(),
            auto_fetch_images=self.auto_fetch.isChecked(),
            auto_preview=self.auto_preview.isChecked(),
            auto_preview_delay=self.auto_preview_delay.value(),
            theme=self.theme_combo.currentData(),
            compiler_backend=self.backend_combo.currentText(),
            tex_engine=self.engine_combo.currentText(),
            after_compile=self.after_compile_combo.currentData(),
            animation=self.animation.isChecked(),
            animation_frames=self.animation_frames.value(),
            item_gap=self.item_gap.isChecked(),
            item_gap_scale=self.item_gap_scale.value(),
            item_gap_bullets=self.item_gap_bullets.isChecked(),
            hanja_recent_first=self.hanja_recent.isChecked(),
            hanja_parenthesize=self.hanja_paren.isChecked(),
            hanja_hangul_first=self.hanja_hg.isChecked(),
        )
        self._win.apply_preferences()
        super().accept()


# ===========================================================================
# 9-l2. 한자 변환 (F9) — libhangul 사전
# ===========================================================================

_HANJA_MODULE = None          # 모듈 또는 False(없음)
HANJA_PAGE = 10


def _bundle_dirs() -> list:
    here = Path(__file__).resolve().parent
    return [here, Path(sys.executable).resolve().parent,
            Path(getattr(sys, "_MEIPASS", here)), Path.home() / ".config" / "ndhmd4tex",
            Path.home() / "Library" / "ndhmd4tex", Path.home() / ".config" / "ndhmdWriter"]


def load_hanja_core():
    """한자 변환 코어(hanja_core.py)를 찾아 불러온다. 없으면 None — 선택 기능이다."""
    global _HANJA_MODULE
    if _HANJA_MODULE is not None:
        return _HANJA_MODULE or None
    import importlib.util
    try:
        import hanja_core as mod
        _HANJA_MODULE = mod
        return mod
    except Exception:
        pass
    for d in _bundle_dirs():
        f = d / "hanja_core.py"
        if f.is_file():
            try:
                spec = importlib.util.spec_from_file_location("hanja_core", f)
                mod = importlib.util.module_from_spec(spec)
                sys.modules["hanja_core"] = mod
                spec.loader.exec_module(mod)
                _HANJA_MODULE = mod
                return mod
            except Exception as e:
                print(f"hanja_core 를 불러오지 못했습니다: {e}", file=sys.stderr)
    _HANJA_MODULE = False
    return None


def find_hanja_txt(name: str = "hanja.txt"):
    for d in _bundle_dirs():
        f = d / name
        if f.is_file():
            return f
    return None


def find_mssymbol_txt():
    """기호 사전(ㄱ+한자 기호표). 없어도 한자 변환은 된다."""
    return find_hanja_txt("mssymbol.txt")


def hanja_data_dir() -> Path:
    """사전 DB(hanja_dict.db)와 최근 기록(hanja_user.db)을 두는 폴더.
    Windows: 실행 파일(.exe, 소스 실행이면 이 .py)이 있는 폴더. 쓸 수 없는 곳(Program Files 등)이면
    사용자 데이터 폴더(%APPDATA%/ndhmdWriter/hanja)로 물러난다.
    macOS: ~/Library/ndhmd4tex/ , Linux: ~/.config/ndhmd4tex/ (ndhmd4tex 가 설정을 두는 폴더와 같다)."""
    if sys.platform.startswith("win"):
        here = Path(sys.executable).resolve().parent if getattr(sys, "frozen", False) \
            else Path(__file__).resolve().parent
        try:
            probe = here / ".hanja_write_test"
            probe.write_text("x")
            probe.unlink()
            return here
        except OSError:
            base = Path(QStandardPaths.writableLocation(QStandardPaths.AppDataLocation)
                        or (Path.home() / ".ndhmdWriter"))
            return base / "hanja"
    if sys.platform == "darwin":
        return Path.home() / "Library" / "ndhmd4tex"
    return Path.home() / ".config" / "ndhmd4tex"


class _HanjaBuildSignals(QObject):
    done = Signal(object)            # 오류 문자열 또는 None


class _HanjaBuild(QRunnable):
    """사전 DB 를 백그라운드에서 만든다(처음 쓸 때 한 번)."""

    def __init__(self, core, txt: Path, db: Path, sym=None):
        super().__init__()
        self.core, self.txt, self.db, self.sym = core, txt, db, sym
        self.signals = _HanjaBuildSignals()

    def run(self):
        try:
            self.core.build_dict(str(self.txt), str(self.db), str(self.sym) if self.sym else None)
            self.signals.done.emit(None)
        except Exception as e:
            self.signals.done.emit(str(e))


class HanjaPopup(QFrame):
    """한자 후보 창. 10개씩 쪽을 나눠 보여 준다. 1~9,0 = 고르기 · ↑↓ 이동 · Enter 고르기 ·
    Space/→/PageDown/F9/+ 다음 쪽 · ←/PageUp/- 이전 쪽 · Esc 닫기."""

    chosen = Signal(int, str, str, int, int)  # (바꿀 글자 수, 한자, 읽기, 뒤에 남는 글자 수, 기호 여부)

    def __init__(self, window: "MainWindow", candidates: list):
        super().__init__(window, Qt.Popup)
        self.cands = candidates
        self.page = 0
        self.row = 0
        self.pages = max(1, (len(candidates) + HANJA_PAGE - 1) // HANJA_PAGE)
        t = window._theme
        self._t = t
        self.setStyleSheet(
            f"HanjaPopup {{ background: {t.panel_bg}; border: 1px solid {t.gutter_fg}; }}"
            f"QLabel {{ color: {t.fg}; }}")
        self.head = QLabel()
        self.body = QLabel()
        self.body.setTextFormat(Qt.RichText)
        self.foot = QLabel("1~0 선택 · Space/→ 다음 쪽 · ← 이전 쪽 · Esc 닫기")
        self.foot.setStyleSheet(f"color: {t.gutter_fg_active}; font-size: 11px;")
        box = QVBoxLayout(self)
        box.setContentsMargins(8, 6, 8, 6)
        box.addWidget(self.head)
        box.addWidget(self.body)
        box.addWidget(self.foot)
        self.setFocusPolicy(Qt.StrongFocus)
        self._render()

    def _items(self):
        return self.cands[self.page * HANJA_PAGE:(self.page + 1) * HANJA_PAGE]

    def _render(self):
        t = self._t
        items = self._items()
        self.row = max(0, min(self.row, len(items) - 1))
        lines = []
        for i, (n, hanja, reading, meaning, _t, _k) in enumerate(items):
            sel = i == self.row
            # 공백 글자(전각 공백 등)는 눈에 안 보이니 코드 포인트로 알려 준다.
            shown = hanja if hanja.strip() else f"[U+{ord(hanja[0]):04X}]" if hanja else ""
            style = (f"background:{t.match_active_bg};" if sel else "")
            lines.append(
                f"<div style='{style}padding:1px 4px;white-space:pre'>"
                f"<span style='color:{t.gutter_fg_active}'>{(i + 1) % 10}</span>&nbsp; "
                f"<span style='font-size:16px;color:{t.fg}'>{shown}</span>&nbsp; "
                f"<span style='color:{t.fg}'>{meaning or reading}</span></div>")
        self.body.setText("".join(lines))
        what = "훈음(음을 고르세요)" if self.cands and self.cands[0][5] == 2 else "한자 후보"
        self.head.setText(f"{what} {len(self.cands)}개 — {self.page + 1}/{self.pages} 쪽")

    def _go_page(self, delta):
        np_ = self.page + delta
        if 0 <= np_ < self.pages:
            self.page, self.row = np_, 0
            self._render()

    def _choose(self, idx):
        items = self._items()
        if 0 <= idx < len(items):
            n, hanja, reading, _m, tail, kind = items[idx]
            self.close()
            self.chosen.emit(n, hanja, reading, tail, kind)

    def keyPressEvent(self, e):
        k = e.key()
        if k == Qt.Key_Escape:
            self.close()
        elif Qt.Key_1 <= k <= Qt.Key_9:
            self._choose(k - Qt.Key_1)
        elif k == Qt.Key_0:
            self._choose(9)
        elif k in (Qt.Key_Return, Qt.Key_Enter):
            self._choose(self.row)
        elif k == Qt.Key_Down:
            if self.row + 1 < len(self._items()):
                self.row += 1
                self._render()
            else:
                self._go_page(1)
        elif k == Qt.Key_Up:
            if self.row > 0:
                self.row -= 1
                self._render()
            elif self.page > 0:
                self._go_page(-1)
                self.row = len(self._items()) - 1
                self._render()
        elif k in (Qt.Key_Space, Qt.Key_Right, Qt.Key_PageDown, Qt.Key_F9, Qt.Key_Plus,
                   Qt.Key_Equal, Qt.Key_Tab):
            self._go_page(1)
        elif k in (Qt.Key_Left, Qt.Key_PageUp, Qt.Key_Minus, Qt.Key_Backtab):
            self._go_page(-1)
        else:
            e.ignore()

    def wheelEvent(self, e):
        self._go_page(1 if e.angleDelta().y() < 0 else -1)


# ===========================================================================
# 9-m. 한중일 입력기 (pmIME 코어)
# ===========================================================================

_PMIME_MODULE = None          # 한 번 찾아 둔다: 모듈 또는 False(없음)


def load_pmime_core():
    """pmIME 변환 코어(pmime_core.py)를 찾아 불러온다. 이 파일 곁, 실행 파일 곁,
    ~/.config/pmimegui 순으로 찾는다. 없으면 None — 이 기능은 선택 사항이다."""
    global _PMIME_MODULE
    if _PMIME_MODULE is not None:
        return _PMIME_MODULE or None
    import importlib.util
    try:                       # PyInstaller 로 묶었거나 sys.path 에 있으면 그냥 불러온다
        import pmime_core as mod
        _PMIME_MODULE = mod
        return mod
    except Exception:
        pass
    here = Path(__file__).resolve().parent
    dirs = [here, Path(sys.executable).resolve().parent,
            Path(getattr(sys, "_MEIPASS", here)), Path.home() / ".config" / "pmimegui"]
    for d in dirs:
        f = d / "pmime_core.py"
        if f.is_file():
            try:
                spec = importlib.util.spec_from_file_location("pmime_core", f)
                mod = importlib.util.module_from_spec(spec)
                sys.modules["pmime_core"] = mod
                spec.loader.exec_module(mod)
                _PMIME_MODULE = mod
                return mod
            except Exception as e:                      # 깨진 파일 — 기능만 끈다
                print(f"pmime_core 를 불러오지 못했습니다: {e}", file=sys.stderr)
    _PMIME_MODULE = False
    return None


class PmImePanel(QDialog):
    """한·중·일 문자 입력기. 로마자로 쓰면 아래 칸에 바로 변환되고, 삽입하면 편집창의
    커서 위치에 들어간다(선택이 있으면 그것을 대체). 변환은 pmIME 코어(pmime_core.py)가
    한다. 줄 첫머리에 `%pm` `%frk` `%mix` `%rrk` `%du` `%ed` `%jp` `%clean`(+`[shin]` 등 한자 필터)을
    쓰면 그 줄만 다른 엔진으로 변환된다. `%uc` `%lc` `%tc`는 변환 없이 대문자/소문자/낱말마다 첫 글자 대문자로 바꾼다.

    Enter = 삽입(비우기가 켜져 있으면 편집창으로 포커스 복귀), Shift+Enter = 줄바꿈, Esc = 창 닫기, Alt+Z = 방금 삽입한 입력 되살리기.
    기본 정규화는 NFC(완성형 음절)이다. 옛한글처럼 조합되지 않는 자모는 NFC에서도 자모로 남는다."""

    ENGINES = [("pm", "pm (%pm)"), ("frkim", "frkim (%frk)"), ("pmfrk", "mix (%mix)"),
               ("rrk", "rrk-ex (%rrk)"), ("dubeol", "두벌식 (%du)"), ("dubeol_rev", "한글자판→영문 (%ed)"), ("kana", "かな (%jp)"), ("transparent", "변환 없음 (%clean)")]
    HANJA = [("none", "한자 필터 없음"), ("shinjitai", "新字体 (shin)"), ("kyujitai", "舊字體 (kyu)"),
             ("simplified", "简体 (sim)"), ("hanja", "한자 (han)")]

    def __init__(self, window: "MainWindow"):
        super().__init__(window, Qt.Tool)
        self._win = window
        self._core = load_pmime_core()
        self._last_input = ""
        self.setWindowTitle("한중일 pm 입력기")

        s = window._settings
        self.engine = QComboBox()
        for key, label in self.ENGINES:
            self.engine.addItem(label, key)
        self.engine.setCurrentIndex(max(0, self.engine.findData(
            s.value("pmime/engine", "pm", type=str))))
        self.hanja = QComboBox()
        for key, label in self.HANJA:
            self.hanja.addItem(label, key)
        self.hanja.setCurrentIndex(max(0, self.hanja.findData(
            s.value("pmime/hanja", "none", type=str))))

        self.nfc = QCheckBox("NFC")
        self.nfc.setChecked(s.value("pmime/nfc", True, type=bool))
        self.nfc.setToolTip("끄면 NFD(첫가끝 자모)로 내보냅니다. 옛한글을 조합해 쓸 때만 끄세요.\n"
                            "NFD 글자는 문단 재배열 너비·글자 수 계산에서 3글자로 셉니다.")
        self.latex = QCheckBox("LaTeX 확장")
        self.latex.setChecked(s.value("pmime/latex", True, type=bool))
        self.latex.setToolTip("\\'e → é, \\x{AC00} → 가 같은 LaTeX 표기를 실제 문자로 바꿉니다.")
        self.clear_after = QCheckBox("삽입 후 비우기")
        self.clear_after.setChecked(s.value("pmime/clear_after", True, type=bool))

        self.input = QPlainTextEdit()
        self.input.setPlaceholderText("로마자로 입력 — Enter 삽입 · Shift+Enter 줄바꿈 · Esc 닫기 · Alt+Z 되살리기")
        self.output = QPlainTextEdit()
        self.output.setReadOnly(True)
        self.output.setPlaceholderText("변환 결과")
        self.input.installEventFilter(self)

        kanji_btn = QPushButton("일어사용자한자")
        kanji_btn.setToolTip("일본어 사용자 한자 사전(customkanji.json)을 찾아 입력하고, 등록·수정·삭제합니다.")
        kanji_btn.clicked.connect(self.open_kanji)
        kanji_btn.setEnabled(self._core is not None)
        insert_btn = QPushButton("삽입")
        insert_btn.clicked.connect(self.insert)
        copy_btn = QPushButton("복사")
        copy_btn.clicked.connect(self.copy)
        clear_btn = QPushButton("비우기")
        clear_btn.clicked.connect(self.clear)

        row1 = QHBoxLayout()
        row1.addWidget(self.engine, 1)
        row1.addWidget(self.hanja, 1)
        row2 = QHBoxLayout()
        row2.addWidget(self.nfc)
        row2.addWidget(self.latex)
        row2.addWidget(self.clear_after)
        row2.addStretch(1)
        btns = QHBoxLayout()
        btns.addWidget(kanji_btn)
        btns.addStretch(1)
        btns.addWidget(clear_btn)
        btns.addWidget(copy_btn)
        btns.addWidget(insert_btn)
        self.status = QLabel("")

        box = QVBoxLayout(self)
        box.addLayout(row1)
        box.addLayout(row2)
        box.addWidget(self.input, 1)
        box.addWidget(self.output, 1)
        box.addLayout(btns)
        box.addWidget(self.status)
        self.resize(380, 420)
        if self._core is None:
            self.input.setEnabled(False)
            self.status.setText("pmime_core.py 를 찾지 못했습니다 — ndhmdWriter.py 와 같은 폴더에 두세요.")

        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.setInterval(80)
        self._timer.timeout.connect(self.update_output)
        self.input.textChanged.connect(self._timer.start)
        for w in (self.engine, self.hanja):
            w.currentIndexChanged.connect(self._changed)
        for w in (self.nfc, self.latex, self.clear_after):
            w.toggled.connect(self._changed)
        QShortcut(QKeySequence("Alt+Z"), self, activated=self.undo_insert)
        self.apply_theme(window._theme)

    def open_kanji(self):
        if getattr(self, "_kanji_dialog", None) is None:
            self._kanji_dialog = PmKanjiDialog(self)
        else:
            self._kanji_dialog.reload()
        self._kanji_dialog.show()
        self._kanji_dialog.raise_()
        self._kanji_dialog.activateWindow()
        self._kanji_dialog.search.setFocus()
        self._kanji_dialog.search.selectAll()

    def apply_theme(self, theme: Theme):
        if getattr(self, "_kanji_dialog", None) is not None:
            self._kanji_dialog.apply_theme(theme)
        # 앱 테마는 OS 의 밝기와 따로 가므로(맥이 라이트인데 앱이 다크일 수 있다) 라벨·체크박스
        # 글자색과 안내문(placeholder) 색을 테마로 직접 정해야 한다. 안 그러면 어두운 바탕에
        # 시스템의 검은 글씨가 얹혀 안 보인다.
        self.setStyleSheet(f"""
            QDialog {{ background: {theme.panel_bg}; }}
            QLabel, QCheckBox {{ color: {theme.fg}; }}
            QPlainTextEdit {{ background: {theme.panel_bg}; color: {theme.fg};
                border: 1px solid {theme.gutter_fg}; }}
        """)
        for edit in (self.input, self.output):
            pal = edit.palette()
            pal.setColor(QPalette.PlaceholderText, QColor(theme.gutter_fg_active))
            edit.setPalette(pal)

    def _changed(self, *_):
        s = self._win._settings
        s.setValue("pmime/engine", self.engine.currentData())
        s.setValue("pmime/hanja", self.hanja.currentData())
        s.setValue("pmime/nfc", self.nfc.isChecked())
        s.setValue("pmime/latex", self.latex.isChecked())
        s.setValue("pmime/clear_after", self.clear_after.isChecked())
        self.update_output()

    def converted(self, text=None) -> str:
        """입력창(또는 넘겨 준 text)을 지금 설정으로 변환한다."""
        if self._core is None:
            return ""
        self._core.set_latex_expand(self.latex.isChecked())
        return self._core.convert_input(
            self.input.toPlainText() if text is None else text,
            engine_mode=self.engine.currentData(),
            hanja_mode=self.hanja.currentData(),
            norm_mode="NFC" if self.nfc.isChecked() else "NFD")

    def update_output(self):
        try:
            self.output.setPlainText(self.converted())
        except Exception as e:                      # 엔진 오류가 앱을 죽이지 않게
            self.output.setPlainText("")
            self.status.setText(f"변환 오류: {e}")

    def insert(self):
        """결과를 편집창 커서 위치에 넣는다(선택이 있으면 대체). 편집창으로 포커스를 옮기지 않는다 —
        이어서 계속 입력할 수 있다."""
        self.update_output()
        text = self.output.toPlainText()
        if not text:
            return
        self._win.editor.textCursor().insertText(text)   # 한 번의 실행 취소 단위
        self._last_input = self.input.toPlainText()
        if self.clear_after.isChecked():
            self.input.clear()
            self.output.clear()
            # 비우고 났으면 한 번의 입력이 끝난 것이다 — 글을 이어 쓰러 편집창으로 돌아간다.
            win = self._win
            win.raise_()
            win.activateWindow()
            win.editor.setFocus(Qt.OtherFocusReason)
        self.status.setText("삽입했습니다")

    def copy(self):
        self.update_output()
        QApplication.clipboard().setText(self.output.toPlainText())
        self.status.setText("클립보드로 복사했습니다")

    def clear(self):
        if self.input.toPlainText():
            self._last_input = self.input.toPlainText()
        self.input.clear()
        self.output.clear()

    def undo_insert(self):
        if self._last_input:
            self.input.setPlainText(self._last_input)
            self._last_input = ""
            self.status.setText("입력을 되살렸습니다")

    def eventFilter(self, obj, event):
        if obj is self.input and event.type() == QEvent.KeyPress:
            if event.key() in (Qt.Key_Return, Qt.Key_Enter) and not (event.modifiers() & Qt.ShiftModifier):
                self.insert()
                return True
            if event.key() == Qt.Key_Escape:
                self.close()            # 다른 도구 창들과 같이 Esc = 창 닫기 (비우기는 버튼)
                return True
        return super().eventFilter(obj, event)


class PmKanjiDialog(QDialog):
    """일본어 사용자 한자 사전(customkanji.json) — 찾아서 입력기에 넣고, 등록·수정·삭제한다.
    사전의 키는 `{h:ai}` 꼴이고, 한중일 pm 입력기의 `かな`(%jp) 엔진에서 한자로 바뀐다
    (예: `%jp {h:ai} no kimochi` → 愛のきもち). 항목을 고르면 그 **키**가 입력기 입력칸에 들어간다.
    저장 위치·반영은 pmime_core 가 맡는다(저장 즉시 변환기에도 반영)."""

    def __init__(self, panel: "PmImePanel"):
        super().__init__(panel, Qt.Tool)
        self._panel = panel
        self._core = panel._core
        self.setWindowTitle("일본어 사용자 한자")
        self.resize(360, 420)

        self.search = QLineEdit()
        self.search.setPlaceholderText("검색 (키·한자·신자체로도)")
        self.search.textChanged.connect(self.refresh)
        self.search.installEventFilter(self)
        self.list = QListWidget()
        self.list.itemDoubleClicked.connect(lambda *_: self.pick())
        self.list.installEventFilter(self)
        f = self.list.font()
        f.setPointSizeF(f.pointSizeF() * 1.15)
        self.list.setFont(f)

        add_btn = QPushButton("새 단어")
        add_btn.clicked.connect(self.add_word)
        edit_btn = QPushButton("수정")
        edit_btn.clicked.connect(self.edit_word)
        del_btn = QPushButton("삭제")
        del_btn.clicked.connect(self.delete_word)
        reload_btn = QPushButton("다시 읽기")
        reload_btn.setToolTip("파일을 다시 읽습니다(다른 곳에서 고쳤을 때)")
        reload_btn.clicked.connect(self.reload)
        btns = QHBoxLayout()
        for b in (add_btn, edit_btn, del_btn):
            btns.addWidget(b)
        btns.addStretch(1)
        btns.addWidget(reload_btn)

        self.info = QLabel("")
        self.info.setStyleSheet("color: gray;")
        self.info.setWordWrap(True)

        box = QVBoxLayout(self)
        box.addWidget(self.search)
        box.addWidget(self.list, 1)
        box.addLayout(btns)
        box.addWidget(self.info)
        self.apply_theme(panel._win._theme)
        self.refresh()

    def apply_theme(self, theme: Theme):
        self.setStyleSheet(f"""
            QDialog {{ background: {theme.panel_bg}; }}
            QLabel {{ color: {theme.gutter_fg_active}; }}
            QLineEdit, QListWidget {{ background: {theme.bg}; color: {theme.fg};
                border: 1px solid {theme.gutter_fg}; }}
            QListWidget::item:selected {{ background: {theme.match_active_bg}; color: {theme.fg}; }}
        """)
        pal = self.search.palette()
        pal.setColor(QPalette.PlaceholderText, QColor(theme.gutter_fg_active))
        self.search.setPalette(pal)

    # -- 목록 -----------------------------------------------------------------

    def _data(self):
        return self._core.load_custom_kanji()

    def refresh(self, *_):
        data = self._data()
        text = self.search.text()
        if text:
            shin = self._core.kanji_tables.get("shinjitai", {})
            conv = "".join(shin.get(ch, ch) for ch in text).lower()
            low = text.lower()
            data = {k: v for k, v in data.items()
                    if low in k.lower() or low in v.lower() or conv in k.lower() or conv in v.lower()}
        self.list.clear()
        # 짧은 키 먼저 (숫자 0~9 로 바로 고르기 쉽게)
        for i, (key, val) in enumerate(sorted(data.items(), key=lambda kv: (len(kv[0]), kv[0]))):
            tag = f"[{i}]" if i <= 9 else "    "
            item = QListWidgetItem(f"{tag} {val}   {key}")
            item.setData(Qt.UserRole, key)
            item.setData(Qt.UserRole + 1, val)
            self.list.addItem(item)
        if self.list.count():
            self.list.setCurrentRow(0)
        self.info.setText(f"{self.list.count()} / {len(self._data())} 단어 — "
                          f"{self._core.custom_kanji_write_path()}")

    def reload(self):
        self._core.load_kanji_tables()
        self.refresh()

    def _current(self):
        item = self.list.currentItem()
        return (item.data(Qt.UserRole), item.data(Qt.UserRole + 1)) if item else (None, None)

    # -- 입력기로 보내기 ----------------------------------------------------------

    def pick(self, row: int | None = None):
        item = self.list.item(row) if row is not None else self.list.currentItem()
        if item is None:
            return
        self._panel.input.insertPlainText(item.data(Qt.UserRole))
        self._panel.input.setFocus()
        self._panel.activateWindow()

    def eventFilter(self, obj, event):
        if event.type() == QEvent.ShortcutOverride and event.key() == Qt.Key_Escape:
            event.accept()
            return True
        if event.type() == QEvent.KeyPress:
            key = event.key()
            if key == Qt.Key_Escape:
                if obj is self.search and self.search.text():
                    self.search.clear()
                else:
                    self.close()
                return True
            if obj is self.search and key == Qt.Key_Down:
                self.list.setFocus()
                return True
            if obj is self.list and key in (Qt.Key_Return, Qt.Key_Enter):
                self.pick()
                return True
            if obj is self.search and key in (Qt.Key_Return, Qt.Key_Enter):
                self.pick()
                return True
            if obj is self.list and Qt.Key_0 <= key <= Qt.Key_9 and not event.modifiers():
                row = key - Qt.Key_0
                if row < self.list.count():
                    self.pick(row)
                return True
        return super().eventFilter(obj, event)

    # -- 등록·수정·삭제 --------------------------------------------------------------

    def _form(self, title, key="", val=""):
        d = QDialog(self)
        d.setWindowTitle(title)
        form = QFormLayout(d)
        k = QLineEdit(key[3:-1] if key.startswith("{h:") else key)
        k.setPlaceholderText("로마자 키 — 예: ai, ai2 (소문자)")
        v = QLineEdit(val)
        v.setPlaceholderText("예: 愛")
        form.addRow("키 ({h:…}):", k)
        form.addRow("한자:", v)
        bb = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        bb.accepted.connect(d.accept)
        bb.rejected.connect(d.reject)
        form.addRow(bb)
        if d.exec() != QDialog.Accepted:
            return None
        return k.text().strip(), v.text().strip()

    def _select_key(self, key):
        self.search.clear()
        for i in range(self.list.count()):
            if self.list.item(i).data(Qt.UserRole) == key:
                self.list.setCurrentRow(i)
                break

    def add_word(self):
        r = self._form("새 단어 등록")
        if not r or not (r[0] and r[1]):
            return
        try:
            key = self._core.add_custom_word(*r)
        except (OSError, ValueError) as e:
            QMessageBox.warning(self, "새 단어 등록", f"저장하지 못했습니다: {e}")
            return
        self.refresh()
        self._select_key(key)

    def edit_word(self):
        key, val = self._current()
        if key is None:
            return
        r = self._form("단어 수정", key, val)
        if not r or not (r[0] and r[1]):
            return
        try:
            new_key = self._core.update_custom_word(key, *r)
        except (OSError, ValueError) as e:
            QMessageBox.warning(self, "단어 수정", f"저장하지 못했습니다: {e}")
            return
        self.refresh()
        self._select_key(new_key)

    def delete_word(self):
        key, val = self._current()
        if key is None:
            return
        if QMessageBox.question(self, "단어 삭제", f"{val}   {key}\n\n이 단어를 사전에서 지울까요?",
                                QMessageBox.Yes | QMessageBox.No, QMessageBox.No) != QMessageBox.Yes:
            return
        row = self.list.currentRow()
        try:
            self._core.delete_custom_word(key)
        except OSError as e:
            QMessageBox.warning(self, "단어 삭제", f"저장하지 못했습니다: {e}")
            return
        self.refresh()
        if self.list.count():
            self.list.setCurrentRow(min(row, self.list.count() - 1))


# ===========================================================================
# 9-k. 선택 영역 변형
# ===========================================================================

#: Enter 이어쓰기와 변형 풀기가 함께 쓰는 목록 표지 정규식.
#: 앞쪽 캡처(들여쓰기)가 탭이든 공백이든 그대로 보존된다.
LIST_PREFIX_RE = re.compile(r"^(\s*)([-*+]|\d+[.)])(\s+)")


class SelectionTransform:
    """선택 영역을 통째로 다른 문법으로 감싸거나 벗긴다.

    전부 "완전한 줄" 단위로 동작한다 — 커서가 줄 중간에 있어도 그 줄
    전체를 포함하도록 먼저 넓힌다. 그래야 코드펜스나 환경이 줄 경계를
    벗어나 깨지는 일이 없다.
    """

    @staticmethod
    def expand_to_lines(cursor: QTextCursor) -> QTextCursor:
        doc = cursor.document()
        start = doc.findBlock(cursor.selectionStart()).position()
        end_block = doc.findBlock(max(cursor.selectionStart(), cursor.selectionEnd() - 1)
                                  if cursor.hasSelection() else cursor.position())
        end = end_block.position() + end_block.length() - 1
        out = QTextCursor(doc)
        out.setPosition(start)
        out.setPosition(max(start, end), QTextCursor.KeepAnchor)
        return out

    @classmethod
    def lines_of(cls, cursor: QTextCursor):
        c = cls.expand_to_lines(cursor)
        return c, c.selectedText().split("\u2029")   # Qt 는 단락 구분자로 U+2029 를 쓴다

    @classmethod
    def to_bullet_list(cls, cursor: QTextCursor):
        c, lines = cls.lines_of(cursor)
        out = []
        for line in lines:
            if not line.strip():
                out.append(line)
                continue
            m = LIST_PREFIX_RE.match(line)
            indent = m.group(1) if m else re.match(r"^(\s*)", line).group(1)
            rest = line[m.end():] if m else line[len(indent):]
            out.append(f"{indent}- {rest}")
        c.insertText("\n".join(out))

    @classmethod
    def to_numbered_list(cls, cursor: QTextCursor):
        c, lines = cls.lines_of(cursor)
        out, n = [], 1
        for line in lines:
            if not line.strip():
                out.append(line)
                continue
            m = LIST_PREFIX_RE.match(line)
            indent = m.group(1) if m else re.match(r"^(\s*)", line).group(1)
            rest = line[m.end():] if m else line[len(indent):]
            out.append(f"{indent}{n}. {rest}")
            n += 1
        c.insertText("\n".join(out))

    @classmethod
    def to_code_fence(cls, cursor: QTextCursor):
        c, lines = cls.lines_of(cursor)
        body = "\n".join(lines)
        # 안쪽에 이미 백틱이 있으면 그보다 긴 펜스를 골라야 안전하다.
        longest = max((len(m.group(0)) for m in re.finditer(r"`+", body)), default=0)
        fence = "`" * max(3, longest + 1)
        c.insertText(f"{fence}\n{body}\n{fence}")

    @classmethod
    def to_environment(cls, cursor: QTextCursor, name: str):
        c, lines = cls.lines_of(cursor)
        body = "\n".join(lines)
        c.insertText(f":::{{{name}}}\n{body}\n:::")

    @classmethod
    def to_blockquote(cls, cursor: QTextCursor):
        """빈 줄도 `>` 만 남겨서 이어 준다 — 그냥 비워 두면 거기서 인용문이
        끊겨 여러 문단이 하나의 인용문으로 묶이지 않는다."""
        c, lines = cls.lines_of(cursor)
        out = [f"> {line}" if line.strip() else ">" for line in lines]
        c.insertText("\n".join(out))

    @classmethod
    def unwrap(cls, cursor: QTextCursor) -> bool:
        """감싸고 있는 펜스·환경·인용문·목록 중 하나를 벗긴다. 벗긴 것이
        있으면 True."""
        c, lines = cls.lines_of(cursor)
        if len(lines) >= 2:
            first, last = lines[0], lines[-1]
            fm = FENCE_OPEN_LOOSE_RE.match(first)
            if fm and FENCE_CLOSE_RE.match(last) and len(fm.group(1)) <= len(
                    re.match(r"`+", last).group(0)):
                c.insertText("\n".join(lines[1:-1]))
                return True
            if ENV_OPEN_RE.match(first) and ENV_CLOSE_RE.match(last):
                c.insertText("\n".join(lines[1:-1]))
                return True
        # 모든 줄이 '>' 로 시작하면 인용문으로 보고 그 표지를 벗긴다.
        quote_lines = [l for l in lines if l.strip()]
        if quote_lines and all(QUOTE_RE.match(l) for l in quote_lines):
            out = [QUOTE_RE.sub(r"\1", line) for line in lines]
            c.insertText("\n".join(out))
            return True
        # 그게 아니면 목록 표지를 벗긴다.
        if any(LIST_PREFIX_RE.match(line) for line in lines if line.strip()):
            out = [LIST_PREFIX_RE.sub(r"\1", line) for line in lines]
            c.insertText("\n".join(out))
            return True
        return False

    @classmethod
    def reflow_paragraphs(cls, cursor: QTextCursor, width: int, single_line: bool):
        """선택 영역을 문단 단위로 재배열한다.

        빈 줄로 나뉜 각 덩어리를 문단 하나로 보고, 그 안의 여러 줄을
        공백 하나로 이어붙인 다음 다시 접어 나간다 — single_line 이면
        그대로 한 줄로, 아니면 width 자에서 자연스러운 낱말 경계로
        접는다(textwrap 이 하는 일 그대로).

        인용문(그 문단의 모든 줄이 '>' 로 시작하는 경우)은 표지를 뗀
        채로 합치고 접은 뒤, 나온 줄마다 다시 '> ' 를 붙인다 — 그냥
        접기만 하면 인용문 표지가 문장 한가운데 섞여 들어간다.
        """
        c, lines = cls.lines_of(cursor)

        groups = []          # [[줄, ...], ...] — 빈 리스트는 빈 줄 하나를 뜻한다
        current = []
        for line in lines:
            if line.strip():
                current.append(line)
            else:
                if current:
                    groups.append(current)
                    current = []
                groups.append([])
        if current:
            groups.append(current)

        # 건드리지 않을 줄: 코드펜스(펜스 줄 포함) 안, 그리고 아래 문단.
        fenced = set()       # lines 의 인덱스
        fence_len = 0
        for i, line in enumerate(lines):
            if fence_len:
                fenced.add(i)
                m = FENCE_CLOSE_RE.match(line)
                if m and len(m.group(1)) >= fence_len:
                    fence_len = 0
            else:
                m = FENCE_OPEN_LOOSE_RE.match(line)
                if m:
                    fenced.add(i)
                    fence_len = len(m.group(1))

        def keep_as_is(group_lines):
            # 목록 항목·표 줄이 있는 문단, 링크 [글](주소)·[글][표지] 가 든 문단,
            # 코드펜스 줄은 접지 않고 그대로 둔다 — 합치면 구조가 깨진다.
            for l in group_lines:
                if (LIST_PREFIX_RE.match(l) or l.lstrip().startswith("|")
                        or LINK_RE.search(l) or REFLINK_RE.search(l)):
                    return True
            return False

        # groups 와 lines 의 대응을 위해 줄 인덱스를 함께 센다.
        out_lines = []
        idx = 0
        for group in groups:
            if not group:
                out_lines.append("")
                idx += 1
                continue
            first = idx
            idx += len(group)
            if any(k in fenced for k in range(first, idx)) or keep_as_is(group):
                out_lines.extend(group)
                continue
            is_quote = all(QUOTE_RE.match(l) for l in group)
            if is_quote:
                text = " ".join(QUOTE_RE.sub(r"\1", l).strip() for l in group)
            else:
                text = " ".join(l.strip() for l in group)
            text = re.sub(r"\s+", " ", text).strip()
            wrapped = [text] if single_line else (textwrap.wrap(text, width=width) or [""])
            if is_quote:
                wrapped = [f"> {w}" for w in wrapped]
            out_lines.extend(wrapped)

        c.insertText("\n".join(out_lines))


# ===========================================================================
# 9-l. LaTeX 악센트 입력
# ===========================================================================

class AccentPanel(QDialog):
    r"""보조 입력. 탭마다 성격이 다른 두 문제를 각각 다룬다.

    "라틴 확장" 탭은 표준 LaTeX 확장 악센트를 유니코드 문자로 바로 꽂아 넣는다.
    ndhmd4tex 에게 `\"o` 같은 표기를 해석시키는 방법도 있었지만, xelatex 과
    lualatex 은 애초에 UTF-8 을 그대로 받아들인다. 그러니 `ö` 를 원고에
    직접 써넣는 쪽이 훨씬 간단하고, ndhmd4tex 는 손댈 필요가 없다.

    "문장부호·괄호" 탭은 지금까지 IME 로만 넣을 수 있던 CJK 문장부호와
    괄호, 자주 쓰는 특수기호를 모았다. 자모 조합이 필요 없는 낱글자들이라
    악센트 탭과 같은 (자모×표지) 표 대신 그냥 평평한 버튼 목록이다.

    두 탭 다 비모달로 띄운다. 계속 고르면서 원고를 보는 것이 목적이라,
    창이 떠 있는 동안에도 편집을 막아서는 안 된다.
    """

    #: (표시 이름, 결합 문자) — 각 행이 되고, 기본 자모 한 벌에 적용된다.
    #: 조합이 아니라 그 자체로 완결된 라틴 확장 글자. 자모×표지 표
    #: 밖에 별도 줄로 둔다.
    SPECIAL_LATIN = list("øǿæǽǣœß")
    #: 대문자가 실제로 있는 것만 적는다. ß 는 전통적으로 한 글자짜리
    #: 대문자가 없다(SS 로 풀어 쓰는 관례라 짝이 안 맞는다) — 그래서
    #: "대문자" 를 켜도 ß 만 그대로 남는다.
    SPECIAL_LATIN_UPPER = {
        "ø": "Ø", "ǿ": "Ǿ", "æ": "Æ", "ǽ": "Ǽ", "ǣ": "Ǣ", "œ": "Œ",
    }

    DIACRITICS = (
        ("악상 시르콩플렉스 ^", "\u0302"),
        ("악상 그라브 `", "\u0300"),
        ("악상 테귀 ´", "\u0301"),
        ("트레마 ¨", "\u0308"),
        ("틸드 ~", "\u0303"),
        ("카론 ˇ", "\u030C"),
        ("마크롱 ¯", "\u0304"),
        ("브레베 ˘", "\u0306"),
        ("세디유 ¸", "\u0327"),
        ("링 ˚", "\u030A"),
        ("점(위) ˙", "\u0307"),
        ("오고넥 ˛", "\u0328"),
    )
    BASES = "aeiouyncszgltdrw"

    #: (분류, [낱글자, ...]) — 지금까지 IME 로만 넣던 것들 우선.
    SYMBOL_GROUPS = (
        ("괄호", list("「」『』〈〉《》【】〔〕（）｛｝")),
        ("문장부호", list("、。・·…⋯〜※々〆！？：；～ː‘’“”")),
        ("기호", list("§¶©®™°′″×÷±≒≠≤≥≈∞–—¡¿❡†‡‼⁇⁈⁉‰№〶")),
        ("화살표", list("→⇒⟹⇨➯←⇐⟸⇦")),
        ("번호", list("⓪①②③④⑤⑥⑦⑧⑨⑩➊➋➌➍➎➏➐➑➒➓")),
        ("통화", list("$€¥¢£₩")),
        ("그림문자", list("○●◎☆★◇◆□■△▲▽▼◁◀▷▶♤♠♡♥♧♣☏☎☜☞♭♪♬㉿㈜")),
        ("표정", list("☺☻☹")),
        #: kotex 의 enumerate 패키지에서 순서를 매길 때 쓰는 것들 —
        #: 중복(예: ①)이 있어도 상관없다고 하셔서 그대로 모아 둔다.
        ("글머리", list("가㈎㉮ㄱ㈀㉠⑴①⒜ⓐⅰⅠ")),
    )

    #: IPA 확장 블록. 유니코드 표에서 쓰는 순서(16개씩) 그대로 — IPA 를
    #: 다루는 사람에게는 이 순서 자체가 익숙한 지도 구실을 한다.
    IPA_LETTERS = list(
        "ɐɑɒɓɔɕɖɗɘəɚɛɜɝɞɟ"
        "ɠɡɢɣɤɥɦɧɨɩɪɫɬɭɮɯ"
        "ɰɱɲɳɴɵɶɷɸɹɺɻɼɽɾɿ"
        "ʀʁʂʃʄʅʆʇʈʉʊʋʌʍʎʏ"
        "ʐʑʒʓʔʕʖʗʘʙʚʛʜʝʞʟ"
        "ʠʡʢʣʤʥʦʧʨʩʪʫʬʭʮʯ"
        "ŋł"
    )

    def __init__(self, window: "MainWindow"):
        super().__init__(window, Qt.Tool)
        self._win = window
        self.setWindowTitle("보조 입력")
        self.setModal(False)

        self.tabs = QTabWidget()
        self.tabs.addTab(self._build_accent_tab(), "라틴 확장")
        self.tabs.addTab(self._build_symbol_tab(), "문장부호·괄호")
        self.tabs.addTab(self._build_wrapped_grid([("", self.IPA_LETTERS)], 16),
                         "IPA 확장")
        self.tabs.addTab(self._build_user_tab(), "사용자")

        hint = QLabel("눌러서 커서 위치에 삽입 · 창은 열어 둔 채로 계속 쓸 수 있습니다")
        hint.setWordWrap(True)

        #: 16진수 코드포인트를 직접 쳐서 넣는다 — 표에 없는 글자를
        #: 매번 새로 만들지 않아도 된다.
        hex_row = QHBoxLayout()
        hex_row.addWidget(QLabel("코드포인트:"))
        self.hex_edit = QLineEdit()
        self.hex_edit.setPlaceholderText("예: AC00, U+1F600, 0x2603")
        self.hex_edit.returnPressed.connect(self._insert_from_hex)
        hex_insert_btn = QPushButton("삽입")
        hex_insert_btn.clicked.connect(self._insert_from_hex)
        hex_row.addWidget(self.hex_edit, 1)
        hex_row.addWidget(hex_insert_btn)

        box = QVBoxLayout(self)
        box.addWidget(self.tabs, 1)
        box.addLayout(hex_row)
        box.addWidget(hint)
        self.resize(380, 460)

    def _insert_from_hex(self):
        """코드포인트 입력칸의 16진수를 글자로 바꿔 커서 위치에 꽂는다.

        U+, 0x 접두어는 있어도 없어도 받는다. 잘못된 값이면(16진수가
        아니거나, 유효한 코드포인트 범위를 벗어나거나, 서로게이트
        영역이면) 조용히 무시하지 않고 입력칸을 붉게 표시해 알려준다.
        """
        raw = self.hex_edit.text().strip()
        if not raw:
            return
        cleaned = re.sub(r"^(U\+|0[xX])", "", raw, flags=re.IGNORECASE)
        try:
            code = int(cleaned, 16)
            if not (0 <= code <= 0x10FFFF) or 0xD800 <= code <= 0xDFFF:
                raise ValueError
        except ValueError:
            self.hex_edit.setStyleSheet("background: #F7CFCF;")
            return
        self.hex_edit.setStyleSheet("")
        self._insert(chr(code))
        self.hex_edit.clear()

    # -- 악센트 탭 ----------------------------------------------------------

    def _build_accent_tab(self) -> QWidget:
        host = QWidget()
        v = QVBoxLayout(host)

        self.upper = QCheckBox("대문자")
        self.upper.toggled.connect(self._rebuild_accent)

        self.accent_grid_host = QWidget()
        self.accent_grid = QGridLayout(self.accent_grid_host)
        self.accent_grid.setSpacing(3)
        scroll = QScrollArea()
        scroll.setWidget(self.accent_grid_host)
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QScrollArea.NoFrame)

        v.addWidget(self.upper)
        v.addWidget(scroll, 1)
        self._rebuild_accent()
        return host

    @staticmethod
    def _compose(base: str, mark: str) -> str:
        import unicodedata
        return unicodedata.normalize("NFC", base + mark)

    def _rebuild_accent(self):
        grid = self.accent_grid
        while grid.count():
            item = grid.takeAt(0)
            if item.widget():
                item.widget().deleteLater()

        # 특수 라틴 문자 — 조합이 아니라 그 자체로 완결된 글자라 표
        # 맨 위에 별도 줄로 둔다. 대문자 토글에 실제 대문자가 있는
        # 것만 반응한다(ß 는 짝이 없어 그대로 남는다).
        is_upper = self.upper.isChecked()
        grid.addWidget(QLabel("특수"), 0, 0)
        for col, ch in enumerate(self.SPECIAL_LATIN, start=1):
            shown = self.SPECIAL_LATIN_UPPER.get(ch, ch) if is_upper else ch
            btn = QToolButton()
            btn.setText(shown)
            btn.setToolTip(f"{shown}  (U+{ord(shown):04X})")
            btn.clicked.connect(lambda _=False, c=shown: self._insert(c))
            grid.addWidget(btn, 0, col)

        bases = self.BASES.upper() if self.upper.isChecked() else self.BASES
        grid.addWidget(QLabel(""), 1, 0)
        for col, base in enumerate(bases, start=1):
            lbl = QLabel(base)
            lbl.setAlignment(Qt.AlignCenter)
            grid.addWidget(lbl, 1, col)

        for row, (name, mark) in enumerate(self.DIACRITICS, start=2):
            grid.addWidget(QLabel(name), row, 0)
            for col, base in enumerate(bases, start=1):
                ch = self._compose(base, mark)
                btn = QToolButton()
                btn.setText(ch)
                btn.setToolTip(f"{ch}  (U+{ord(ch[0]):04X})" if len(ch) == 1
                               else f"{ch}  (조합 문자)")
                btn.clicked.connect(lambda _=False, c=ch: self._insert(c))
                grid.addWidget(btn, row, col)

    # -- 문장부호·괄호 탭 / IPA 탭 공용 ---------------------------------------

    #: 한 묶음 안에서 한 줄에 놓을 글자 수. 묶음이 길어지면 줄이 옆으로
    #: 한없이 늘어나는 대신 여기서 접어 내려간다.
    SYMBOLS_PER_ROW = 9

    def _build_symbol_tab(self) -> QWidget:
        return self._build_wrapped_grid(self.SYMBOL_GROUPS, self.SYMBOLS_PER_ROW)

    def _build_wrapped_grid(self, groups, per_row: int) -> QWidget:
        """(이름표, [문자, ...]) 목록을 묶음별로 per_row 개씩 접어 내려가는
        평면 그리드로 만든다. 문장부호 탭과 IPA 탭이 같이 쓴다."""
        host = QWidget()
        grid = QGridLayout(host)
        grid.setSpacing(3)
        row = 0
        for label, chars in groups:
            for i, ch in enumerate(chars):
                sub_row, col = divmod(i, per_row)
                if col == 0 and label:
                    # 묶음의 첫 줄에만 이름표를 붙이고, 접혀 내려간 줄은
                    # 빈 칸으로 맞춰 표 전체의 세로줄이 어긋나지 않게 한다.
                    grid.addWidget(QLabel(label if sub_row == 0 else ""), row + sub_row, 0)
                btn = QToolButton()
                btn.setText(ch)
                btn.setToolTip(f"{ch}  (U+{ord(ch):04X})")
                btn.clicked.connect(lambda _=False, c=ch: self._insert(c))
                grid.addWidget(btn, row + sub_row, col + 1)
            row += -(-len(chars) // per_row)  # ceil
        grid.setColumnStretch(per_row + 1, 1)

        scroll = QScrollArea()
        scroll.setWidget(host)
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QScrollArea.NoFrame)
        wrapper = QWidget()
        wv = QVBoxLayout(wrapper)
        wv.setContentsMargins(0, 0, 0, 0)
        wv.addWidget(scroll)
        return wrapper

    # -- 사용자 탭 -------------------------------------------------------------
    #
    # 직접 추가/삭제한다. 16개씩 접어 내려간다(IPA 탭과 같은 폭) —
    # 이것도 결국 _build_wrapped_grid() 가 쓰는 것과 같은 그리기
    # 방식이지만, 목록이 설정에 따라 바뀌므로 매번 다시 그려야 해서
    # 별도로 둔다.

    USER_SYMBOLS_PER_ROW = 16

    def _build_user_tab(self) -> QWidget:
        host = QWidget()
        v = QVBoxLayout(host)

        add_row = QHBoxLayout()
        self.user_add_edit = QLineEdit()
        self.user_add_edit.setPlaceholderText("추가할 문자(코드포인트 입력칸도 같이 쓸 수 있습니다)")
        self.user_add_edit.returnPressed.connect(self._add_user_symbol)
        add_btn = QPushButton("추가")
        add_btn.clicked.connect(self._add_user_symbol)
        add_row.addWidget(self.user_add_edit, 1)
        add_row.addWidget(add_btn)

        hint = QLabel("우클릭 — 목록에서 삭제")
        hint.setStyleSheet("color: palette(mid); font-size: 11px;")

        self.user_grid_host = QWidget()
        self.user_grid = QGridLayout(self.user_grid_host)
        self.user_grid.setSpacing(3)
        scroll = QScrollArea()
        scroll.setWidget(self.user_grid_host)
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QScrollArea.NoFrame)

        v.addLayout(add_row)
        v.addWidget(hint)
        v.addWidget(scroll, 1)

        self._rebuild_user_grid()
        return host

    def _rebuild_user_grid(self):
        grid = self.user_grid
        while grid.count():
            item = grid.takeAt(0)
            if item.widget():
                item.widget().deleteLater()

        symbols = self._win.prefs.custom_symbols()
        per_row = self.USER_SYMBOLS_PER_ROW
        for i, ch in enumerate(symbols):
            row, col = divmod(i, per_row)
            btn = QToolButton()
            btn.setText(ch)
            btn.setToolTip(f"{ch}  (우클릭: 삭제)")
            btn.clicked.connect(lambda _=False, c=ch: self._insert(c))
            btn.setContextMenuPolicy(Qt.CustomContextMenu)
            btn.customContextMenuRequested.connect(
                lambda _pos, c=ch: self._remove_user_symbol(c))
            grid.addWidget(btn, row, col)
        grid.setColumnStretch(per_row, 1)

    def _add_user_symbol(self):
        text = self.user_add_edit.text().strip()
        if not text:
            return
        symbols = self._win.prefs.custom_symbols()
        if text not in symbols:
            symbols.append(text)
            self._win.prefs.set_custom_symbols(symbols)
            self._rebuild_user_grid()
        self.user_add_edit.clear()

    def _remove_user_symbol(self, ch: str):
        symbols = self._win.prefs.custom_symbols()
        if ch in symbols:
            symbols.remove(ch)
            self._win.prefs.set_custom_symbols(symbols)
            self._rebuild_user_grid()

    # -- 공통 -----------------------------------------------------------------

    def _insert(self, ch: str):
        self._win.editor.insertPlainText(ch)
        # 이 패널은 별도의 최상위 창(Qt.Tool)이라, 편집창의 포커스
        # 위젯만 지정해서는 OS 차원의 활성 창이 여전히 이 패널로 남는다
        # — activateWindow() 로 메인 창 자체를 먼저 앞으로 가져와야
        # 실제로 다시 타이핑할 수 있는 상태가 된다.
        self._win.activateWindow()
        self._win.editor.setFocus()

    def apply_theme(self, theme: Theme):
        self.setStyleSheet(f"""
            QDialog {{ background: {theme.panel_bg}; color: {theme.fg}; }}
            QLabel {{ color: {theme.gutter_fg_active}; }}
            QTabWidget::pane {{ border: 1px solid {theme.gutter_fg}; }}
            QTabBar::tab {{
                background: {theme.bg}; color: {theme.gutter_fg_active};
                padding: 5px 12px; border: 1px solid {theme.gutter_fg};
                border-bottom: none; border-top-left-radius: 4px;
                border-top-right-radius: 4px;
            }}
            QTabBar::tab:selected {{ background: {theme.panel_bg}; color: {theme.fg}; }}
            QToolButton {{
                background: {theme.bg}; color: {theme.fg};
                border: 1px solid {theme.gutter_fg}; border-radius: 3px;
                min-width: 26px; min-height: 24px; font-size: 13px;
            }}
            QToolButton:hover {{ background: {theme.current_line}; }}
        """)


# ===========================================================================
# 9-m. 원격 그림 — ndhmd4tex 과 같은 캐시를 공유한다
# ===========================================================================
#
# ndhmd4tex 은 URL 그림을 책 폴더의 _images/ 에 URL 의 SHA1 해시 이름으로
# 캐싱하고, 다운로드 자체는 --fetch-images 없이는 하지 않는다(주석 그대로:
# "재현성이 아니라 보안" — 남의 .md 를 열기만 해도 요청이 나가면 안 된다).
#
# 미리보기는 이 위험이 컴파일보다 크다. 컴파일은 사용자가 명령을 내릴 때
# 한 번 일어나지만, 미리보기는 커서를 움직일 때마다 일어난다. 자동으로
# 매번 요청을 내보내면 남의 원고를 열어보기만 해도 추적 픽셀과 똑같은 일이
# 생긴다. 그래서 캐시 조회(네트워크 없음)는 항상 허용하고, 실제 다운로드는
# 설정에서 켜지 않는 한 사용자가 그때그때 눌러야 나가게 한다.
#
# 캐시 이름 규칙과 폴더는 ndhmd4tex 과 정확히 같게 맞췄다 — 그래야 앱에서
# 미리 보느라 받아둔 그림을 컴파일이 다시 받지 않고, 반대의 경우도 같다.

IMAGE_CACHE_DIR = "_images"
URL_RE = re.compile(r"^[a-zA-Z][a-zA-Z0-9+.\-]*://")

_TEX_READY_EXT = {".pdf", ".png", ".jpg", ".jpeg", ".eps", ".ps", ".bmp", ".mps"}
_CONVERTIBLE_EXT = {".tif", ".tiff", ".webp", ".gif"}
_HANDOFF_EXT = {".svg", ".svgz", ".ai", ".psd"}
_CTYPE_EXT = {
    "image/png": ".png", "image/jpeg": ".jpg", "image/gif": ".gif",
    "image/webp": ".webp", "image/tiff": ".tiff", "image/bmp": ".bmp",
    "image/svg+xml": ".svg", "application/pdf": ".pdf",
}


class ImageFetchError(Exception):
    pass


def is_image_url(text: str) -> bool:
    return bool(URL_RE.match(text.strip()))


def _cache_name(url: str, ext: str) -> str:
    return hashlib.sha1(url.encode("utf-8")).hexdigest()[:16] + ext


def cached_image(url: str, base_dir: Path):
    """이미 받아둔 그림이 있으면 그 경로를, 없으면 None. 네트워크를 안 쓴다."""
    cache = Path(base_dir) / IMAGE_CACHE_DIR
    guess = Path(urllib.parse.urlparse(url).path).suffix.lower()
    if guess:
        cand = cache / _cache_name(url, guess)
        if cand.is_file():
            return cand
    for ext in sorted(_TEX_READY_EXT | _CONVERTIBLE_EXT | _HANDOFF_EXT):
        cand = cache / _cache_name(url, ext)
        if cand.is_file():
            return cand
    return None


def fetch_image_sync(url: str, base_dir: Path) -> Path:
    """실제로 내려받는다. 반드시 사용자 동의(설정 또는 버튼)를 거친 뒤에만
    불러야 한다 — 이 함수 자체는 그 동의를 확인하지 않는다."""
    hit = cached_image(url, base_dir)
    if hit is not None:
        return hit

    guess = Path(urllib.parse.urlparse(url).path).suffix.lower()
    req = urllib.request.Request(url, headers={
        "User-Agent": "ndhmdWriter/0.1 (+https://ktug.org)",
    })
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            ctype = (resp.headers.get("Content-Type") or "").split(";")[0].strip().lower()
            data = resp.read()
    except Exception as e:
        raise ImageFetchError(f"그림을 내려받지 못했습니다: {url}\n{type(e).__name__}: {e}")

    ext = _CTYPE_EXT.get(ctype) or guess
    if not ext:
        raise ImageFetchError(
            f"그림의 형식을 알 수 없습니다: {url}\n"
            f"Content-Type: {ctype or '(없음)'} — URL에도 확장자가 없습니다.")
    if ctype and ctype.startswith("text/"):
        raise ImageFetchError(
            f"그림이 아니라 문서가 돌아왔습니다: {url}\nContent-Type: {ctype}")

    cache = Path(base_dir) / IMAGE_CACHE_DIR
    cache.mkdir(parents=True, exist_ok=True)
    dst = cache / _cache_name(url, ext)
    try:
        dst.write_bytes(data)
    except OSError as e:
        raise ImageFetchError(f"캐시에 쓰지 못했습니다: {dst}\n{e}")
    return dst


class FetchSignals(QObject):
    done = Signal(int, str, str, str)   # 요청 번호, url, 'ok'|'error', 경로 또는 메시지


class FetchTask(QRunnable):
    def __init__(self, req_id: int, url: str, base_dir: Path, signals: FetchSignals):
        super().__init__()
        self.req_id, self.url, self.base_dir, self.signals = req_id, url, base_dir, signals

    def run(self):
        try:
            path = fetch_image_sync(self.url, self.base_dir)
            self.signals.done.emit(self.req_id, self.url, "ok", str(path))
        except ImageFetchError as e:
            self.signals.done.emit(self.req_id, self.url, "error", str(e))
        except Exception as e:
            self.signals.done.emit(self.req_id, self.url, "error", str(e))


# ===========================================================================
# 9-n. 컴파일 전 그림 점검
# ===========================================================================
#
# ndhmd4tex 의 prepare_image() 가 컴파일 시점에 하는 판단은 셋으로 갈린다.
#
#   URL              → --fetch-images 없이는 캐시에 없으면 ImageError
#   변환 필요한 형식   → (.webp/.tiff/.gif) Pillow로 옆에 -ext.png 를 만들어야 함
#   못 받는 형식       → (.svg 등) 자동으로 고칠 수 없음, 사용자가 손봐야 함
#
# 이 판단은 전부 네트워크 없이 미리 계산된다. 그러니 컴파일을 걸기 전에
# GUI 가 먼저 훑어서 부족한 것만 동의 하에 채워 두면, 컴파일러 자체에는
# --fetch-images 를 아예 안 넘겨도 된다 — "네트워크는 항상 명시적 동의를
# 거친다"는 원칙이 미리보기와 컴파일 양쪽에서 똑같이 유지된다.

def classify_local_image(path: Path) -> str:
    """'ready' | 'needs_convert' | 'handoff' | 'unknown'."""
    ext = path.suffix.lower()
    if ext in _HANDOFF_EXT:
        return "handoff"
    if ext in _CONVERTIBLE_EXT:
        target = path.with_name(path.stem + path.suffix.replace(".", "-") + ".png")
        return "ready" if target.is_file() else "needs_convert"
    if ext in _TEX_READY_EXT:
        return "ready"
    return "unknown"


def pillow_available() -> bool:
    """Pillow 는 ndhmd4tex 과 똑같이 선택적 의존성이다.

    webp/tiff/gif 를 안 쓰는 원고는 이 앱도 컴파일러도 Pillow 없이 완전히
    잘 돌아간다. 그래서 요구사항에 강제로 넣지 않고, 필요한 시점에만 있는지
    확인해 한 번에 깔끔한 안내를 준다 — 그림마다 raw ImportError 가 반복해서
    뜨는 것보다 낫다.
    """
    try:
        import PIL  # noqa: F401
        return True
    except ImportError:
        return False


def have_qtpdf() -> bool:
    """QtPdf 모듈(PDF 페이지를 실제로 그려서 보여주는 것)이 설치돼
    있는지. Pillow와 같은 이유로 선택 의존성이다 — 없어도 그림
    들여오기는 PDF를 계속 후보로 보여준다, 다만 실제 페이지 미리보기
    대신 시스템의 일반 PDF 파일 아이콘을 쓴다.
    """
    try:
        from PySide6.QtPdf import QPdfDocument  # noqa: F401
        return True
    except ImportError:
        return False


class FilePeekDialog(QDialog):
    """서랍의 자료 창고·하위 폴더 항목 우클릭 ▸ 훑어보기.

    편집창에는 띄우지 않고(그 항목은 애초에 편집 대상으로 보지
    않는다) 내용만 파악한다 — 텍스트는 읽기 전용으로, 그림은 그대로,
    PDF는(QtPdf가 있으면) 첫 페이지만 보여준다. 그 외 형식은 미리볼
    수 없다는 안내와 "시스템 프로그램으로 열기" 버튼만 준다. 한 번에
    파일 하나만 본다 — 여러 개를 한꺼번에 훑어보는 기능은 없다.
    """

    TEXT_SUFFIXES = {".md", ".txt", ".nmd", ".mmd", ".yaml", ".yml",
                     ".bib", ".tex", ".sty", ".cls", ".json", ".csv", ".log"}
    IMAGE_SUFFIXES = {".png", ".jpg", ".jpeg", ".gif", ".bmp", ".webp"}

    def __init__(self, window: "MainWindow", path: Path):
        super().__init__(window, Qt.Tool)
        self._win = window
        self.path = path
        rel = window.workspace.relative(path) if window.workspace else str(path)
        self.setWindowTitle(f"훑어보기 — {rel}")
        self.resize(640, 560)

        box = QVBoxLayout(self)
        suffix = path.suffix.lower()
        if suffix in self.IMAGE_SUFFIXES:
            self._show_image(box)
        elif suffix == ".pdf":
            self._show_pdf(box)
        elif self._looks_like_text():
            self._show_text(box)
        else:
            self._show_unsupported(box)

        open_btn = QPushButton("시스템 프로그램으로 열기")
        open_btn.clicked.connect(
            lambda: QDesktopServices.openUrl(QUrl.fromLocalFile(str(self.path))))
        close_btn = QPushButton("닫기")
        close_btn.clicked.connect(self.close)
        btn_row = QHBoxLayout()
        btn_row.addStretch(1)
        btn_row.addWidget(open_btn)
        btn_row.addWidget(close_btn)
        box.addLayout(btn_row)

    def _looks_like_text(self) -> bool:
        """확장자로 바로 알 수 없으면, 앞부분을 utf-8 로 읽어 본다 —
        디코딩되고 널 바이트가 없으면 텍스트로 본다."""
        if self.path.suffix.lower() in self.TEXT_SUFFIXES:
            return True
        try:
            with open(self.path, "rb") as f:
                chunk = f.read(4096)
            chunk.decode("utf-8")
            return b"\x00" not in chunk
        except (OSError, UnicodeDecodeError):
            return False

    def _show_text(self, box):
        try:
            text = read_manuscript(self.path)
        except (OSError, UnicodeDecodeError) as e:
            self._show_unsupported(box, f"읽지 못했습니다: {e}")
            return
        edit = QTextEdit()
        edit.setReadOnly(True)
        edit.setStyleSheet("font-family: monospace;")
        edit.setPlainText(text)
        box.addWidget(edit, 1)

    def _show_image(self, box):
        pix = QPixmap(str(self.path))
        if pix.isNull():
            self._show_unsupported(box)
            return
        label = QLabel()
        label.setAlignment(Qt.AlignCenter)
        label.setPixmap(pix.scaled(600, 500, Qt.KeepAspectRatio, Qt.SmoothTransformation))
        scroll = QScrollArea()
        scroll.setWidget(label)
        scroll.setWidgetResizable(True)
        box.addWidget(scroll, 1)

    def _show_pdf(self, box):
        if have_qtpdf():
            try:
                from PySide6.QtPdf import QPdfDocument
                doc = QPdfDocument()
                if (doc.load(str(self.path)) == QPdfDocument.Error.None_
                        and doc.pageCount() > 0):
                    page_size = doc.pagePointSize(0).toSize()
                    if not page_size.isEmpty():
                        scale = min(600 / page_size.width(),
                                   780 / page_size.height(), 2.0)
                        render_size = QSize(int(page_size.width() * scale),
                                           int(page_size.height() * scale))
                        image = doc.render(0, render_size)
                        if not image.isNull():
                            label = QLabel()
                            label.setAlignment(Qt.AlignCenter)
                            label.setPixmap(QPixmap.fromImage(image))
                            scroll = QScrollArea()
                            scroll.setWidget(label)
                            scroll.setWidgetResizable(True)
                            box.addWidget(scroll, 1)
                            if doc.pageCount() > 1:
                                note = QLabel(f"(전체 {doc.pageCount()}쪽 중 1쪽만 미리봅니다)")
                                note.setStyleSheet("color: palette(mid); font-size: 11px;")
                                box.addWidget(note)
                            return
            except Exception:
                pass   # 렌더링 실패는 조용히 "미리볼 수 없음" 안내로 물러난다
        self._show_unsupported(box, "PDF 미리보기를 쓰려면 QtPdf 가 있어야 합니다.")

    def _show_unsupported(self, box, msg="미리볼 수 없는 파일 형식입니다."):
        label = QLabel(msg + "\n아래 \"시스템 프로그램으로 열기\"를 눌러 보세요.")
        label.setAlignment(Qt.AlignCenter)
        label.setWordWrap(True)
        box.addWidget(label, 1)


def convert_local_image(path: Path) -> Path:
    """ndhmd4tex 과 같은 규칙으로 PNG 사본을 만든다. 실패하면 예외를 낸다."""
    from PIL import Image
    target = path.with_name(path.stem + path.suffix.replace(".", "-") + ".png")
    Image.open(path).convert("RGB").save(target)
    return target


def scan_image_sources(win: "MainWindow"):
    """책 전체에서 ![](경로) 와 ![][표지] 를 훑어 URL 과 로컬 경로를
    나눠 돌려준다.

    지금 편집 중인 파일은 디스크가 아니라 편집창에서 읽는다 — 저장 전
    변경도 점검에 반영되어야 한다(그림 미리보기에서 같은 이유로 이미
    쓰고 있는 것과 같은 원칙이다).

    참조 스타일(![캡션][표지] + 별도 줄의 [표지]: 경로)은 정의를 그
    파일 안에서만 찾는다(파일을 건너 정의를 공유하지 않는다). [표지]:
    줄은 일반 링크 참조도 똑같은 모양으로 쓰므로, 실제로 ![][표지]
    로 쓰인 표지만 그림으로 센다 — 정의만 있고 그림 참조가 없으면
    조용히 무시한다(PreviewScanner 와 같은 원칙).
    """
    remote, local = {}, {}
    for path in LabelIndex.book_files(win.index, win._path):
        if path == win._path:
            text = win.editor.toPlainText()
        else:
            try:
                text = read_manuscript(path)
            except (OSError, UnicodeDecodeError):
                continue
        lines = text.splitlines()

        definitions = {}
        for line in lines:
            def_m = FIGURE_DEF_RE.match(line)
            if def_m:
                definitions[def_m.group(1)] = def_m.group(2)

        for i, line in enumerate(lines):
            for m in FIGURE_RE.finditer(line):
                src = m.group(2)
                bucket = remote if is_image_url(src) else local
                bucket.setdefault(src, []).append((path, i + 1))
            for m in FIGURE_REF_RE.finditer(line):
                src = definitions.get(m.group(2))
                if src is None:
                    continue
                bucket = remote if is_image_url(src) else local
                bucket.setdefault(src, []).append((path, i + 1))
    return remote, local


def flatten_all_includes(text: str, base_dir: Path, _depth: int = 0, _seen=None):
    """{{파일}} 을 몇 겹이든 전부 그 파일의 내용으로 재귀적으로 바꿔
    넣는다 -- [파일] > 내보내기 > 한 개 파일로 내보내기 전용이다.
    ndhmd4tex 은 이제 {{}} 를 몇 단계든 직접 풀지만, 여기서는
    ndhmd4tex 을 아예 거치지 않고(단순 텍스트 파일로 내보내는 것이므로)
    이 앱이 직접 끝까지 편다.

    끼워 넣는 파일의 frontmatter 는 잘라낸다 -- 맨 처음 호출한
    최상위 파일(책 루트)의 frontmatter 만 결과에 남는다.

    (병합된 텍스트, 못 찾았거나 순환이라 그대로 남겨 둔 이름 목록) 을
    돌려준다. 순환 포함은 지금까지 펼친 파일 경로(_seen)에 있으면
    막고, 너무 깊으면(드문 실수 방지) 8단계에서 멈춘다.
    """
    if _seen is None:
        _seen = set()
    missing = []
    if _depth > 8:
        return text, missing

    def repl(m):
        name = m.group(1).strip()
        target = (base_dir / name).resolve()
        if target in _seen or not target.is_file():
            missing.append(name)
            return m.group(0)
        try:
            sub_text = read_manuscript(target)
        except (OSError, UnicodeDecodeError):
            missing.append(name)
            return m.group(0)
        sub_text = FRONTMATTER_RE.sub("", sub_text, count=1)
        expanded, sub_missing = flatten_all_includes(
            sub_text, target.parent, _depth + 1, _seen | {target})
        missing.extend(sub_missing)
        return expanded

    new_text = INCLUDE_RE.sub(repl, text)
    return new_text, missing

def find_all_references(win: "MainWindow"):
    """책 전체에서 [프리픽스라벨](예: [#mylabel], [page:mylabel]) 을
    전부 훑는다 — 죽었든(그 라벨이 어디에도 선언 안 됨) 살았든 상관
    없이. (path, line, prefix, label, is_dead) 목록을 돌려준다.

    "참조"는 언제나 책 전체를 기본 감시 단위로 삼는다 — 지금 편집
    중인 파일이 책의 일부면 책 전체를, 책이 아니면 자기 파일만 본다
    (LabelIndex.book_files() 의 원칙 그대로다).

    라벨 선언 수집은 LabelIndex.scan_file/scan_lines 를 그대로
    재사용한다. 지금 편집 중인 파일은 디스크가 아니라 편집창에서
    읽는다 — 다른 점검들과 같은 원칙이다.
    """
    files = LabelIndex.book_files(win.index, win._path)

    declared = set()
    for path in files:
        if path == win._path:
            hits = LabelIndex.scan_lines(win.editor.toPlainText().splitlines(), path)
        else:
            hits = LabelIndex.scan_file(path)
        declared.update(h.label for h in hits)

    refs = []
    for path in files:
        if path == win._path:
            lines = win.editor.toPlainText().splitlines()
        else:
            try:
                lines = read_manuscript(path).splitlines()
            except (OSError, UnicodeDecodeError):
                continue
        fence = 0
        for i, raw in enumerate(lines):
            m = FENCE_CLOSE_RE.match(raw)
            if fence and m and len(m.group(1)) >= fence:
                fence = 0
                continue
            if fence:
                continue
            m = FENCE_OPEN_LOOSE_RE.match(raw)
            if m:
                fence = len(m.group(1))
                continue
            line = LabelIndex._mask_code(raw)
            for m in REF_USE_RE.finditer(line):
                prefix, label = m.group(1), m.group(2)
                refs.append((path, i + 1, prefix, label, label not in declared))
            for m in LINK_RE.finditer(line):
                if m.start() > 0 and line[m.start() - 1] == "!":
                    continue
                if m.group(2).startswith("#") and len(m.group(2)) > 1:
                    label = m.group(2)[1:]
                    refs.append((path, i + 1, XREF_PREFIX, label,
                                 label not in declared))
    return refs


#: 인용 사용 문법: [@키] [@t:키] [@p:키] [@a:키] [@y:키] (쉼표로 여러 키). 링크 `[@x](url)`·`[@x][ref]` 는 제외.
CITE_USE_RE = re.compile(r"\[(@[tpay]:|@)([^\]\n]+)\](?![(\[])")
BIB_SKIP_TYPES = {"comment", "string", "preamble"}
BIBITEM_ANY_RE = re.compile(r"\\bibitem(?:\[[^\]]*\])?\s*\{([^}\s]+)\}")
BIB_RESOURCE_RE = re.compile(
    r"\\(?:addbibresource(?:\[[^\]]*\])?|bibliography)\s*\{([^}]+)\}")


def _book_text_lines(win: "MainWindow"):
    """책 전체의 (path, 줄 목록). 지금 편집 중인 파일은 편집창에서 읽는다."""
    out = []
    for path in LabelIndex.book_files(win.index, win._path):
        if path == win._path:
            lines = win.editor.toPlainText().splitlines()
        else:
            try:
                lines = read_manuscript(path).splitlines()
            except (OSError, UnicodeDecodeError):
                continue
        out.append((path, lines))
    return out


def collect_citation_keys(win: "MainWindow", book_lines=None):
    """문헌 키가 어디에 선언돼 있는지 모은다 → ({키: (경로, 줄)}, 원본 설명 목록,
    {bib 경로: (선언한 원고, 줄)}). 마지막은 `\\addbibresource`·`\\bibliography` 가 그 .bib 를 가리킨
    줄이다(작업공간 최상위 .bib 가 어디서도 선언되지 않았으면 없다).

    원본: ① 책 안의 `\\bibitem{키}`(:::{thebibliography} 블록 포함) ② 작업공간 최상위의
    .bib 파일들 ③ 원고의 `\\addbibresource{…}`·`\\bibliography{…}` 가 가리키는 .bib
    (책 폴더·작업공간 기준). 완전한 BibTeX 파서가 아니다(BIB_ENTRY_RE 와 같은 훑기).
    같은 키가 여럿이면 먼저 찾은 것을 정의 위치로 삼는다.
    """
    book_lines = book_lines if book_lines is not None else _book_text_lines(win)
    keys, sources, decls = {}, [], {}
    n_item = 0
    for path, lines in book_lines:
        fence = 0
        for i, raw in enumerate(lines):
            m = FENCE_CLOSE_RE.match(raw)
            if fence and m and len(m.group(1)) >= fence:
                fence = 0
                continue
            if fence:
                continue
            m = FENCE_OPEN_LOOSE_RE.match(raw)
            if m:
                fence = len(m.group(1))
                continue
            for bm in BIBITEM_ANY_RE.finditer(raw):
                n_item += 1
                keys.setdefault(bm.group(1), (path, i + 1))
    if n_item:
        sources.append(f"\\bibitem {n_item}개")

    bibs = []
    if win.workspace:
        bibs += [p for p in win.workspace.aux_files() if p.suffix.lower() == ".bib"]
    base_dirs = []
    try:
        base_dirs.append(LabelIndex.book_files(win.index, win._path)[0].parent)
    except Exception:
        pass
    if win.workspace and getattr(win.workspace, "root", None):
        base_dirs.append(Path(win.workspace.root))
    for _path, lines in book_lines:
        for ln, raw in enumerate(lines, 1):
            for rm in BIB_RESOURCE_RE.finditer(raw):
                for name in rm.group(1).split(","):
                    name = name.strip()
                    if not name:
                        continue
                    if not name.lower().endswith(".bib"):
                        name += ".bib"
                    for d in base_dirs:
                        cand = d / name
                        if cand.is_file():
                            bibs.append(cand)
                            try:
                                decls.setdefault(cand.resolve(), (_path, ln))
                            except OSError:
                                pass
                            break
    seen, n_bib = set(), 0
    for bp in bibs:
        try:
            rp = bp.resolve()
        except OSError:
            rp = bp
        if rp in seen:
            continue
        seen.add(rp)
        try:
            text = read_manuscript(bp)
        except (OSError, UnicodeDecodeError):
            continue
        n_bib += 1
        for bm in BIB_ENTRY_RE.finditer(text):
            if bm.group(1).lower() in BIB_SKIP_TYPES:
                continue
            keys.setdefault(bm.group(2), (bp, text.count("\n", 0, bm.start()) + 1))
    if n_bib:
        sources.append(f".bib {n_bib}개 파일")
    return keys, sources, decls


def find_all_citations(win: "MainWindow"):
    """책 전체의 [@키] 류 인용을 훑는다 → (목록, 키 사전, 원본 설명, bib 선언 줄 사전).
    목록 원소는 (path, line, prefix, key, state), state 는 "ok" / "dead" / "unknown".
    문헌 원본(\\bibitem·.bib)을 하나도 못 찾으면 존재 여부를 알 수 없으므로 전부 "unknown"
    (죽었다고 단정하지 않는다)."""
    book_lines = _book_text_lines(win)
    keys, sources, decls = collect_citation_keys(win, book_lines)
    cites = []
    for path, lines in book_lines:
        fence = 0
        for i, raw in enumerate(lines):
            m = FENCE_CLOSE_RE.match(raw)
            if fence and m and len(m.group(1)) >= fence:
                fence = 0
                continue
            if fence:
                continue
            m = FENCE_OPEN_LOOSE_RE.match(raw)
            if m:
                fence = len(m.group(1))
                continue
            line = LabelIndex._mask_code(raw)
            for m in CITE_USE_RE.finditer(line):
                for key in m.group(2).split(","):
                    key = key.strip()
                    if not key:
                        continue
                    state = "unknown" if not sources else ("ok" if key in keys else "dead")
                    cites.append((path, i + 1, m.group(1), key, state))
    return cites, keys, sources, decls


#: find_all_references 의 prefix 자리에 [글자](#라벨)(\hyperref) 을 나타내는 표지.
XREF_PREFIX = "(#"


def ref_display(prefix: str, label: str) -> str:
    """참조를 원문에 쓰는 모양으로: [#라벨] / [page:라벨] / [글자](#라벨)."""
    return f"[…](#{label})" if prefix == XREF_PREFIX else f"[{prefix}{label}]"


def ref_at_position(line: str, pos: int):
    """줄 안의 pos 가 참조형 마크업([프리픽스라벨] 또는 [글자](#라벨)) 위이면
    (prefix, label), 아니면 None. 코드·수식 안은 아니다."""
    line = LabelIndex._mask_code(line)
    for m in INLINE_MATH_RE.finditer(line):
        line = line[:m.start()] + " " * (m.end() - m.start()) + line[m.end():]
    for m in REF_USE_RE.finditer(line):
        if m.start() <= pos <= m.end():
            return m.group(1), m.group(2)
    for m in CITE_USE_RE.finditer(line):
        if m.start() <= pos <= m.end():
            # [@a,b] 에서는 커서가 놓인 키를 돌려준다(끝 괄호 위면 첫 키).
            off, picked = m.start(2), None
            for part in m.group(2).split(","):
                a, b = off, off + len(part)
                if picked is None:
                    picked = part.strip()
                if a <= pos <= b:
                    picked = part.strip()
                    break
                off = b + 1
            if picked:
                return m.group(1), picked
    for m in LINK_RE.finditer(line):
        if m.start() > 0 and line[m.start() - 1] == "!":
            continue
        if m.start() <= pos <= m.end() and m.group(2).startswith("#") \
                and len(m.group(2)) > 1:
            return XREF_PREFIX, m.group(2)[1:]
    return None


def find_dead_references(win: "MainWindow"):
    """find_all_references() 중 죽은(\\ref는 있지만 \\label은 없는)
    것만 — (path, line, prefix, label) 4튜플로, 기존에 이 이름을
    쓰던 곳(상호참조 점검 도입 초기)과의 호환을 위해 그대로 둔다."""
    return [(p, ln, pre, lab) for p, ln, pre, lab, dead in find_all_references(win) if dead]


class ImageImportPanel(QDialog):
    """그림 들여오기. 비모달 — 목록을 열어 둔 채 계속 커서를 옮겨 가며
    여러 장을 골라 넣을 수 있다.

    그림 미리보기와는 다르다. 미리보기는 원고에 이미 적힌 그림을
    보여주는 것이고, 이건 아직 안 적힌 그림 중 뭘 쓸지 고르게 하는
    것이다 — 그래서 훑는 대상도 "원고가 참조하는 그림"이 아니라
    "폴더 안에 있는 그림 파일 전부"다.

    어느 폴더를 훑을지는 지금 파일의 graphicspath: 를 따른다(없으면
    작업공간 전체). 클릭하면 폴더 이름 없이 파일 이름만 커서 위치에
    꽂는다 — graphicspath: 가 있는 이유 자체가 "그 폴더들 안에서 이름만
    으로 찾게 하려는 것"이니, 폴더 이름을 같이 넣으면 그 존재 이유를
    무색하게 만든다.

    PDF 그림도 후보에 넣는다. 다만 작업공간 루트에 있는 pdf는 원고를
    조판해서 나온 결과물(같은 이름의 .md 가 있는 것)일 수 있어서,
    그런 건 뺀다. 같은 이름의 .tex 만 있는 것은 조각 그림이므로 그림이다 — graphicspath: 로 지정한 폴더(루트 제외) 안의 pdf는
    이런 걱정이 없으니 그냥 다 보여준다.
    """

    THUMB_SIZE = 72
    EXTENSIONS = (".png", ".jpg", ".jpeg", ".gif", ".webp")
    PDF_EXTENSION = ".pdf"
    #: ndhmd4tex 이 .gif/.webp 에서 만들어 내는 부산물 — 원본이 옆에 있으면 목록에서 뺀다.
    _FRAMES_DIR_RE = re.compile(r"(.+)-(gif|webp)-frames", re.I)
    _FIRST_FRAME_RE = re.compile(r"(.+)-(gif|webp)", re.I)

    def __init__(self, window: "MainWindow"):
        super().__init__(window, Qt.Tool)
        self._win = window
        self.setWindowTitle("그림 들여오기")
        self.resize(340, 460)

        self.hint = QLabel()
        self.hint.setWordWrap(True)
        self.hint.setStyleSheet("color: palette(mid); font-size: 11px;")

        interaction_hint = QLabel("클릭 — 선택 · 더블클릭 — 삽입 · 우클릭 — 정보/열기/이름만 삽입")
        interaction_hint.setWordWrap(True)
        interaction_hint.setStyleSheet("color: palette(mid); font-size: 11px;")

        self.list = QListWidget()
        self.list.setViewMode(QListView.IconMode)
        self.list.setIconSize(QSize(self.THUMB_SIZE, self.THUMB_SIZE))
        self.list.setResizeMode(QListView.Adjust)
        self.list.setMovement(QListView.Static)
        self.list.setSpacing(6)
        self.list.setWordWrap(True)
        self.list.setUniformItemSizes(True)
        self.list.itemDoubleClicked.connect(self._on_double_click)
        self.list.setContextMenuPolicy(Qt.CustomContextMenu)
        self.list.customContextMenuRequested.connect(self._show_context_menu)

        #: figure로 넣을지(체크되면 ![""](...)), 아니면 그냥 인라인
        #: 그림(![](...))으로 넣을지. width 는 그 뒤 {width=...} 속성 —
        #: 더 복잡한 설정(placement 등)은 지금은 다루지 않는다.
        self.figure_check = QCheckBox("figure로 삽입")
        self.width_edit = QLineEdit(".6\\linewidth")
        self.width_edit.setPlaceholderText("예: .6\\linewidth, 5cm")
        opt_row = QHBoxLayout()
        opt_row.addWidget(self.figure_check)
        opt_row.addWidget(QLabel("width="))
        opt_row.addWidget(self.width_edit, 1)

        refresh_btn = QPushButton("새로고침")
        refresh_btn.clicked.connect(self.refresh)
        import_btn = QPushButton("가져오기…")
        import_btn.clicked.connect(self._import_external_image)
        btn_row = QHBoxLayout()
        btn_row.addWidget(refresh_btn)
        btn_row.addWidget(import_btn)

        box = QVBoxLayout(self)
        box.addWidget(self.hint)
        box.addWidget(interaction_hint)
        box.addWidget(self.list, 1)
        box.addLayout(opt_row)
        box.addLayout(btn_row)

        self.refresh()

    def _import_external_image(self):
        """작업공간 밖에 있는 그림(또는 PDF) 파일을 골라, 지금 훑고
        있는 폴더 목록의 맨 앞 폴더로 복사해 온다. graphicspath: 가
        여러 개여도 문제를 단순하게 하려고 첫 번째 폴더 하나로 정한다
        — graphicspath: 가 없으면 그 목록은 작업공간 최상위 하나뿐이다.
        """
        dirs, _ = self._search_dirs()
        if not dirs:
            QMessageBox.information(self, "그림 들여오기", "작업공간에서 파일을 먼저 열어 주세요.")
            return
        dest_dir = dirs[0]
        pattern = " ".join(f"*{s}" for s in (*self.EXTENSIONS, self.PDF_EXTENSION))
        start_dir = str(self._win.workspace.root.parent) \
            if self._win.workspace.root.parent.is_dir() else str(Path.home())
        name, _ = QFileDialog.getOpenFileName(
            self, "그림 들여오기", start_dir, f"그림 ({pattern})")
        if not name:
            return
        src = Path(name)
        if self._win.workspace.contains(src):
            QMessageBox.information(self, "그림 들여오기", "이미 작업공간 안에 있는 파일입니다.")
            return
        dest = dest_dir / src.name
        if dest.exists():
            new_name, ok = QInputDialog.getText(
                self, "그림 들여오기",
                f"'{dest_dir.name}' 폴더에 이미 '{src.name}' 이(가) 있습니다.\n"
                f"다른 이름으로 들여올 이름:", text=src.name)
            if not ok or not new_name.strip():
                return
            dest = dest_dir / new_name.strip()
            if not dest.suffix:
                dest = dest.with_suffix(src.suffix)
            if dest.exists():
                QMessageBox.warning(self, "그림 들여오기", f"{dest.name} 이(가) 이미 있습니다.")
                return
        try:
            dest_dir.mkdir(parents=True, exist_ok=True)
            shutil.copy2(str(src), str(dest))
        except OSError as e:
            QMessageBox.warning(self, "그림 들여오기", f"복사하지 못했습니다: {e}")
            return
        self.refresh()
        self._win.statusBar().showMessage(
            f"{src.name} 을(를) {self._win.workspace.relative(dest_dir)} 로 들여왔습니다.", 4000)

    # -- 조회 -----------------------------------------------------------------

    def _search_dirs(self):
        """훑을 폴더 목록과, graphicspath: 를 실제로 썼는지 여부."""
        win = self._win
        if win._path is None or not win.workspace:
            return [], False
        book_dir = LabelIndex.book_files(win.index, win._path)[0].parent
        gps = Preamble.graphicspath(win.index, win._path, win._live_reader)
        if gps:
            dirs = []
            for gp in gps:
                d = (book_dir / gp).resolve()
                if d.is_dir() and d not in dirs:
                    dirs.append(d)
            if dirs:
                return dirs, True
        return [win.workspace.root], False

    def refresh(self):
        """지금 파일 기준으로 폴더를 다시 훑는다. 파일을 옮겨 다니며
        graphicspath: 가 바뀌면 MainWindow 가 이걸 불러 준다."""
        self.list.clear()
        dirs, used_gp = self._search_dirs()
        if not dirs:
            self.hint.setText("작업공간에서 파일을 먼저 열어 주세요.")
            return
        self.hint.setText(
            "graphicspath: 에 지정된 폴더를 훑습니다." if used_gp else
            "graphicspath: 가 없어 작업공간 전체를 훑습니다.")

        seen = set()
        root = self._win.workspace.root.resolve()
        for d in dirs:
            d_is_root = d.resolve() == root
            for p in sorted(d.rglob("*")):
                if not p.is_file():
                    continue
                suffix = p.suffix.lower()
                is_pdf = suffix == self.PDF_EXTENSION
                if suffix not in self.EXTENSIONS and not is_pdf:
                    continue
                if any(part in Workspace.SKIP_DIRS or part.startswith(".")
                       for part in p.relative_to(d).parts[:-1]):
                    continue
                if p in seen:
                    continue
                if self._is_animation_byproduct(p, d):
                    continue
                if is_pdf and d_is_root and not self._pdf_is_orphaned(p):
                    continue   # 같은 이름의 .md 가 있으면 조판 결과물로 보고 뺀다(.tex 만 있으면 조각 그림)
                seen.add(p)

                if is_pdf:
                    icon = self._pdf_icon(p)
                else:
                    pix = QPixmap(str(p))
                    if pix.isNull() and suffix in (".gif", ".webp"):
                        pix = self._pillow_first_frame(p)
                    if pix.isNull():
                        if suffix in (".gif", ".webp"):
                            # Qt 가 못 읽어도 목록에서 빼지는 않는다(ndhmd4tex 이 쓸 수 있다).
                            icon = QFileIconProvider().icon(QFileInfo(str(p)))
                            it = QListWidgetItem(icon, p.name)
                            it.setData(Qt.UserRole, p.name)
                            it.setData(Qt.UserRole + 1, str(p))
                            it.setToolTip(self._win.workspace.relative(p))
                            self.list.addItem(it)
                        continue
                    thumb = pix.scaled(self.THUMB_SIZE, self.THUMB_SIZE,
                                       Qt.KeepAspectRatio, Qt.SmoothTransformation)
                    icon = QIcon(thumb)

                it = QListWidgetItem(icon, p.name)
                it.setData(Qt.UserRole, p.name)
                it.setData(Qt.UserRole + 1, str(p))
                it.setToolTip(self._win.workspace.relative(p) if self._win.workspace else str(p))
                self.list.addItem(it)

        if self.list.count() == 0:
            self.hint.setText(self.hint.text() + " (그림 없음)")

    @classmethod
    def _is_animation_byproduct(cls, p: Path, base: Path) -> bool:
        """ndhmd4tex 이 .gif/.webp 에서 만들어 내는 파일인가 — 원본이 옆에 있을 때만.

        ① `이름-webp-frames/`(또는 `-gif-frames/`) 폴더 안의 프레임 0.png, 1.png …
           (`--animation` 일 때). 폴더 이름 앞부분과 같은 이름의 `이름.webp` 가 그 폴더 옆에 있어야 한다.
        ② `이름-webp.png`(또는 `-gif.png`) — 변환으로 만든 첫 프레임. 옆에 `이름.webp` 가 있어야 한다.
        원본이 없으면(사용자가 직접 둔 폴더·파일이면) 그대로 보여 준다."""
        try:
            parents = p.relative_to(base).parts[:-1]
        except ValueError:
            parents = ()
        cur = base
        for part in parents:
            cur = cur / part
            m = cls._FRAMES_DIR_RE.fullmatch(part)
            if m and (cur.parent / f"{m.group(1)}.{m.group(2)}").is_file():
                return True
        if p.suffix.lower() == ".png":
            m = cls._FIRST_FRAME_RE.fullmatch(p.stem)
            if m and (p.parent / f"{m.group(1)}.{m.group(2)}").is_file():
                return True
        return False

    @staticmethod
    def _pillow_first_frame(path: Path) -> QPixmap:
        """Qt 에 webp/gif 플러그인이 없을 때 Pillow 로 첫 프레임을 읽는다. 못 읽으면 빈 픽스맵."""
        try:
            from PIL import Image
            with Image.open(path) as im:
                im = im.convert("RGBA")
                data = im.tobytes("raw", "RGBA")
                qimg = QImage(data, im.width, im.height, 4 * im.width,
                              QImage.Format_RGBA8888).copy()
            return QPixmap.fromImage(qimg)
        except Exception:
            return QPixmap()

    @staticmethod
    def _pdf_is_orphaned(path: Path) -> bool:
        """이 pdf와 같은 폴더에 같은 이름의 .md 가 있으면 그 원고를 조판해서
        나온 결과물로 본다 — 그림 후보가 아니다. .tex 만 있는 pdf 는 그림이다:
        조각 그림 도구가 만든 그림은 foo.pdf 옆에 foo.tex(소스)를 두기 때문에,
        .tex 의 유무로는 원고 결과물과 가를 수 없다. 원고는 반드시 .md 에서
        시작하므로 .md 가 있느냐가 기준이다."""
        return not path.with_suffix(".md").exists()

    def _pdf_icon(self, path: Path) -> QIcon:
        """QtPdf 가 있으면 첫 페이지를 실제로 그려서 섬네일로 쓴다.
        없거나 렌더링이 실패하면 시스템의 일반 PDF 파일 아이콘으로
        조용히 물러난다 — 어느 쪽이든 PDF 자체를 후보에서 빼지는
        않는다."""
        if have_qtpdf():
            try:
                from PySide6.QtPdf import QPdfDocument
                doc = QPdfDocument()
                if doc.load(str(path)) == QPdfDocument.Error.None_ \
                        and doc.pageCount() > 0:
                    page_size = doc.pagePointSize(0).toSize()
                    if not page_size.isEmpty():
                        image = doc.render(0, page_size)
                        if not image.isNull():
                            pix = QPixmap.fromImage(image).scaled(
                                self.THUMB_SIZE, self.THUMB_SIZE,
                                Qt.KeepAspectRatio, Qt.SmoothTransformation)
                            return QIcon(pix)
            except Exception:
                pass   # 렌더링 실패는 조용히 파일 아이콘으로 물러난다
        return QFileIconProvider().icon(QFileInfo(str(path)))

    # -- 동작 -----------------------------------------------------------------

    def _on_double_click(self, item: QListWidgetItem):
        name = item.data(Qt.UserRole)
        alt = '""' if self.figure_check.isChecked() else ""
        width = self.width_edit.text().strip()
        attr = f"{{width={width}}}" if width else ""
        self._win.editor.insertPlainText(f"![{alt}]({name}){attr}")
        # 이 패널도 AccentPanel 처럼 별도의 최상위 창이라, 편집창의
        # setFocus() 만으로는 OS 차원의 활성 창이 안 바뀐다.
        self._win.activateWindow()
        self._win.editor.setFocus()

    def _insert_name_only(self, item: QListWidgetItem):
        name = item.data(Qt.UserRole)
        self._win.editor.insertPlainText(name)
        self._win.activateWindow()
        self._win.editor.setFocus()

    def _show_context_menu(self, pos):
        item = self.list.itemAt(pos)
        if item is None:
            return
        full_path = item.data(Qt.UserRole + 1)
        menu = QMenu(self)
        info_act = menu.addAction("그림 정보")
        open_act = menu.addAction("열기")
        menu.addSeparator()
        name_act = menu.addAction("그림 이름만 삽입")
        action = menu.exec(self.list.viewport().mapToGlobal(pos))
        if action == info_act:
            self._show_image_info(full_path)
        elif action == open_act:
            QDesktopServices.openUrl(QUrl.fromLocalFile(full_path))
        elif action == name_act:
            self._insert_name_only(item)

    def _show_image_info(self, full_path: str):
        path = Path(full_path)
        rel = self._win.workspace.relative(path) if self._win.workspace else str(path)
        lines = [rel]
        try:
            size_bytes = path.stat().st_size
            lines.append(f"크기: {size_bytes / 1024:.1f} KB")
        except OSError:
            pass
        if path.suffix.lower() != self.PDF_EXTENSION:
            pix = QPixmap(full_path)
            if not pix.isNull():
                lines.append(f"해상도: {pix.width()} × {pix.height()} px")
        else:
            lines.append("PDF 그림 — 해상도 정보 없음")
        QMessageBox.information(self, "그림 정보", "\n".join(lines))


# ===========================================================================
# 조각 그림 — LaTeX 조각을 PDF 그림으로 구워 그림 폴더에 넣는 도구
# ===========================================================================

class JigsawFigure:
    r"""조각 그림의 파일 형식과 컴파일.

    그림 하나는 짝을 이루는 파일들이다 — 컴파일러가 쓰는 ``foo.pdf``(쪽이
    여럿이면 ``foo-1.pdf``, ``foo-2.pdf`` …)와, 그것을 만든 완결된 문서
    ``foo.tex``. 원고에는 그냥 ``![""](foo.pdf)`` 가 들어가므로
    ndhmd4tex 는 이 도구를 전혀 모른다. 옆에 이 도구가 만든 ``.tex`` 가
    있는 PDF 만 "조각 그림"으로 보고 다시 열어 고칠 수 있다.

    문서 클래스는 standalone(기본, 한 덩어리 그림), article, oblivoir 중
    고른다. 뒤의 둘은 문단·여러 줄 수식처럼 폭이 정해져야 하는 것을 위한
    것이고, 여러 쪽이 나오면 쪽마다 따로 잘라 낱장 그림으로 만든다.
    """

    MARK = "% ndhmdWriter jigsaw"
    PRE_BEGIN = "% --- preamble ---"
    PRE_END = "% --- end preamble ---"
    DEFAULT_PREAMBLE = "\\usepackage{tikz}"
    TIMEOUT = 60
    NAME_RE = re.compile(r"^[\w.\-]+$")
    #: 고를 수 있는 엔진. 첫째가 기본이다. luamplib(MetaPost 그림)처럼
    #: LuaTeX 에서만 되는 것이 있어 lualatex 도 둔다.
    ENGINES = ("xelatex", "lualatex")
    ENGINE_RE = re.compile(r"^% engine: (\w+)\s*$", re.M)
    #: 문서 클래스. 첫째가 기본이다.
    CLASSES = ("standalone", "article", "oblivoir")
    CLASS_RE = re.compile(r"^% class: (\w+)\s*$", re.M)
    #: 쪽 자르기용 래스터 배율(72dpi 의 몇 배) — 잉크 상자를 이 해상도로
    #: 잰다. 오차(1/배율 pt)보다 큰 여유를 CROP_MARGIN 으로 둔다.
    CROP_SCALE = 3
    CROP_MARGIN = 2.0                   # bp
    PAGES_RE = re.compile(r"Output written on .*?\((\d+) pages?")

    @classmethod
    def compose(cls, preamble: str, body: str, engine: str = "xelatex",
                klass: str = "standalone") -> str:
        head = ("\\documentclass[border=2pt]{standalone}" if klass == "standalone"
                else f"\\documentclass{{{klass}}}")
        lines = [
            cls.MARK + " — 조각 그림 도구가 만든 파일. 도구에서 편집·재생성한다.",
            f"% engine: {engine}",
            f"% class: {klass}",
            head,
            cls.PRE_BEGIN, preamble.strip("\n"), cls.PRE_END]
        if klass != "standalone":
            # 쪽 번호·머리글이 잉크로 남아 자르는 상자에 섞이지 않게 한다.
            # 사용자의 프리앰블 뒤에 두어 fancyhdr 등을 이긴다.
            lines.append("\\pagestyle{empty}")
        lines += ["\\begin{document}", body.strip("\n"), "\\end{document}", ""]
        return "\n".join(lines)

    @classmethod
    def parse(cls, text: str):
        """(프리앰블, 본문, 엔진, 클래스) 또는 이 도구의 형식이 아니면 None.
        엔진·클래스 줄이 없는 옛 파일은 xelatex, standalone 으로 본다."""
        if not text.startswith(cls.MARK):
            return None
        a, b = text.find(cls.PRE_BEGIN), text.find(cls.PRE_END)
        d, e = text.find("\\begin{document}"), text.rfind("\\end{document}")
        if min(a, b, d, e) < 0 or not (a < b < d < e):
            return None
        pre = text[a + len(cls.PRE_BEGIN):b].strip("\n")
        body = text[d + len("\\begin{document}"):e].strip("\n")
        m = cls.ENGINE_RE.search(text[:a])
        engine = m.group(1) if m and m.group(1) in cls.ENGINES else "xelatex"
        m = cls.CLASS_RE.search(text[:a])
        klass = m.group(1) if m and m.group(1) in cls.CLASSES else "standalone"
        return pre, body, engine, klass

    @classmethod
    def sidecar(cls, pdf: Path):
        """pdf 옆에 이 도구가 만든 .tex 가 있으면 그 경로, 아니면 None."""
        tex = pdf.with_suffix(".tex")
        try:
            if pdf.suffix.lower() == ".pdf" and tex.is_file():
                with open(tex, encoding="utf-8") as f:
                    if f.read(len(cls.MARK)) == cls.MARK:
                        return tex
        except (OSError, UnicodeDecodeError):
            pass
        return None

    @classmethod
    def locate(cls, pdf: Path):
        """pdf 가 조각 그림이면 그것을 만든 .tex, 아니면 None. 여러 쪽
        그림의 낱장(foo-2.pdf)은 foo.tex 로 이어진다."""
        tex = cls.sidecar(pdf)
        if tex:
            return tex
        m = re.match(r"^(.*)-(\d+)$", pdf.stem)
        if m and pdf.suffix.lower() == ".pdf":
            return cls.sidecar(pdf.with_name(m.group(1) + ".pdf"))
        return None

    @classmethod
    def figure_files(cls, directory: Path, name: str) -> list:
        """name 이라는 조각 그림의 PDF 들(foo.pdf 또는 foo-1.pdf, foo-2.pdf …)."""
        out = []
        single = directory / f"{name}.pdf"
        if single.is_file():
            out.append(single)
        numbered = re.compile(r"^%s-(\d+)\.pdf$" % re.escape(name))
        try:
            found = [(int(m.group(1)), p) for p in directory.iterdir()
                     if (m := numbered.match(p.name))]
        except OSError:
            found = []
        out += [p for _, p in sorted(found)]
        return out

    # -- 컴파일 ---------------------------------------------------------------

    @classmethod
    def _run(cls, engine: str, tex: Path, cwd: Path, env):
        """TeX 를 한 번 돌린다. (성공?, 오류 요약) — 로그는 tex 옆에 남는다."""
        try:
            run = subprocess.run(
                [engine, "-interaction=nonstopmode", "-halt-on-error",
                 "-no-shell-escape", tex.name],
                cwd=cwd, env=env, capture_output=True, timeout=cls.TIMEOUT,
                creationflags=_NO_WINDOW)
        except subprocess.TimeoutExpired:
            return False, f"{cls.TIMEOUT}초 안에 끝나지 않아 중단했습니다."
        except OSError as e:
            return False, f"{engine} 을(를) 실행하지 못했습니다: {e}"
        pdf = tex.with_suffix(".pdf")
        if run.returncode != 0 or not pdf.is_file() or not pdf.stat().st_size:
            return False, MathRenderer._first_error(tex.with_suffix(".log"))
        return True, ""

    @classmethod
    def compile(cls, preamble: str, body: str, outdir: Path, search_dirs=(),
                engine: str = "xelatex", klass: str = "standalone"):
        """(성공?, 낱장 PDF 경로 목록 또는 오류 요약, 로그 발췌).

        standalone 은 PDF 한 개. article/oblivoir 는 먼저 보통 문서로 굽고,
        쪽마다 잉크 상자를 재어(QtPdf, 없으면 pdftoppm) 낱장 PDF 로 잘라
        낸다. 자르기는 외부 도구(pdfcrop·Ghostscript) 없이 TeX 의
        \\includegraphics[page=,trim=,clip] 로 한다 — 그림 내용은 벡터 그대로다.
        search_dirs 는 \\includegraphics·\\input 이 작업공간 파일을 찾도록
        TEXINPUTS 에 얹는다. 셸 이스케이프는 끈다 — 남의 원고를 열어
        컴파일해도 명령이 돌지 않게."""
        if engine not in cls.ENGINES:
            return False, f"알 수 없는 엔진: {engine}", ""
        if klass not in cls.CLASSES:
            return False, f"알 수 없는 문서 클래스: {klass}", ""
        if shutil.which(engine) is None:
            return False, f"{engine} 을(를) 찾지 못했습니다.", ""
        outdir.mkdir(parents=True, exist_ok=True)
        for old in outdir.glob("*.pdf"):
            old.unlink(missing_ok=True)
        src = outdir / "jigsaw.tex"
        src.write_text(cls.compose(preamble, body, engine, klass), encoding="utf-8")
        env = dict(os.environ)
        env["TEXINPUTS"] = os.pathsep.join(
            [*(str(d) for d in search_dirs), env.get("TEXINPUTS", "")])

        ok, why = cls._run(engine, src, outdir, env)
        log = cls._log_excerpt(outdir / "jigsaw.log")
        if not ok:
            return False, why, log
        if klass == "standalone":
            return True, [outdir / "jigsaw.pdf"], log

        try:
            log_text = (outdir / "jigsaw.log").read_text(encoding="utf-8", errors="replace")
        except OSError:
            log_text = ""
        m = cls.PAGES_RE.search(log_text)
        pages = int(m.group(1)) if m else 1
        try:
            boxes = cls._page_boxes(outdir / "jigsaw.pdf", pages, outdir)
        except Exception as e:             # 래스터 도구가 없거나 PDF 를 못 읽는 경우
            return False, f"쪽을 자르지 못했습니다: {e}", ""
        crop_engine = "pdflatex" if shutil.which("pdflatex") else engine
        out = []
        for i, box in enumerate(boxes, start=1):
            if box is None:
                continue                   # 빈 쪽(끝에 딸려 나온 것 등)은 버린다
            l, b, r, t = box
            crop = outdir / f"crop-{i}.tex"
            crop.write_text(
                "\\documentclass[border=0pt]{standalone}\n\\usepackage{graphicx}\n"
                "\\begin{document}"
                f"\\includegraphics[page={i},trim={l:.2f}bp {b:.2f}bp {r:.2f}bp {t:.2f}bp,clip]"
                "{jigsaw.pdf}\\end{document}\n", encoding="utf-8")
            ok, why = cls._run(crop_engine, crop, outdir, env)
            if not ok:
                return False, f"{i}쪽을 자르지 못했습니다: {why}", cls._log_excerpt(outdir / f"crop-{i}.log")
            out.append(outdir / f"crop-{i}.pdf")
        if not out:
            return False, "그림이 비어 있습니다(찍힌 것이 없는 쪽뿐입니다).", ""
        return True, out, log

    @classmethod
    def _page_boxes(cls, pdf: Path, pages: int, workdir: Path) -> list:
        """쪽마다 잉크가 있는 영역을 \\includegraphics 의 trim 값(bp)
        (왼쪽, 아래, 오른쪽, 위)으로 돌려준다. 잉크가 없으면 None.
        래스터로 그려 흰 바탕이 아닌 가장자리를 찾는다 — 순수 바이트
        연산이라 numpy 가 필요 없다."""
        S = cls.CROP_SCALE
        use_qtpdf = have_qtpdf()
        doc = None
        if use_qtpdf:
            from PySide6.QtPdf import QPdfDocument
            doc = QPdfDocument()
            if doc.load(str(pdf)) != QPdfDocument.Error.None_:
                raise RuntimeError("PDF 를 읽지 못했습니다")
        elif shutil.which("pdftoppm") is None:
            raise RuntimeError("QtPdf 또는 pdftoppm 이 필요합니다")
        # 거의 흰색(>=250)은 흰색으로 본다 — 반투명 가장자리의 잡티를 무시.
        table = bytes(255 if v >= 250 else v for v in range(256))
        result = []
        try:
            for i in range(pages):
                if doc is not None:
                    size = doc.pagePointSize(i)
                    w_pt, h_pt = size.width(), size.height()
                    img = doc.render(i, QSize(max(1, int(w_pt * S + 0.999)),
                                              max(1, int(h_pt * S + 0.999))))
                    flat = QImage(img.size(), QImage.Format_RGB32)
                    flat.fill(Qt.white)           # 투명 바탕이면 검게 읽히므로 흰 종이에 얹는다
                    p = QPainter(flat)
                    p.drawImage(0, 0, img)
                    p.end()
                    gray = flat.convertToFormat(QImage.Format_Grayscale8)
                else:
                    stem = workdir / f"raster-{i + 1}"
                    subprocess.run(
                        ["pdftoppm", "-gray", "-r", str(72 * S), "-f", str(i + 1),
                         "-l", str(i + 1), "-singlefile", str(pdf), str(stem)],
                        capture_output=True, timeout=cls.TIMEOUT, creationflags=_NO_WINDOW)
                    gray = QImage(str(stem) + ".pgm").convertToFormat(QImage.Format_Grayscale8)
                    if gray.isNull():
                        raise RuntimeError("pdftoppm 이 쪽을 그리지 못했습니다")
                    w_pt, h_pt = gray.width() / S, gray.height() / S
                W, H = gray.width(), gray.height()
                stride = gray.bytesPerLine()
                buf = bytes(gray.constBits()).translate(table)
                top = bottom = None
                left, right = W, -1
                for y in range(H):
                    row = buf[y * stride:y * stride + W]
                    inked = row.strip(b"\xff")
                    if not inked:
                        continue
                    if top is None:
                        top = y
                    bottom = y
                    lead = W - len(row.lstrip(b"\xff"))
                    trail = len(row.rstrip(b"\xff"))
                    if lead < left:
                        left = lead
                    if trail - 1 > right:
                        right = trail - 1
                if top is None:
                    result.append(None)
                    continue
                fx, fy = W / w_pt, H / h_pt
                m = cls.CROP_MARGIN
                x0, x1 = left / fx - m, (right + 1) / fx + m
                y0, y1 = top / fy - m, (bottom + 1) / fy + m
                result.append((max(0.0, x0), max(0.0, h_pt - y1),
                               max(0.0, w_pt - x1), max(0.0, y0)))
        finally:
            if doc is not None:
                doc.close()
        return result

    @staticmethod
    def _log_excerpt(log: Path, tail: int = 40) -> str:
        """첫 오류부터 이어지는 몇 줄(없으면 로그 끝)."""
        try:
            lines = log.read_text(encoding="utf-8", errors="replace").splitlines()
        except OSError:
            return ""
        for i, line in enumerate(lines):
            if line.startswith("!"):
                return "\n".join(lines[i:i + 14])
        return "\n".join(lines[-tail:])


class _JigsawWorker(QThread):
    """TeX 컴파일은 몇 초 걸릴 수 있어서 화면을 막지 않으려고 따로 돌린다."""

    done = Signal(bool, object, str)   # 성공?, PDF 경로 목록 또는 오류 요약, 로그 발췌

    def __init__(self, preamble, body, outdir, search_dirs, engine, klass, parent=None):
        super().__init__(parent)
        self._args = (preamble, body, outdir, tuple(search_dirs), engine, klass)

    def run(self):
        try:
            ok, res, log = JigsawFigure.compile(*self._args)
        except Exception as e:             # 스레드에서 예외가 새면 앱이 죽는다
            ok, res, log = False, f"예기치 못한 오류: {e}", ""
        self.done.emit(ok, res, log)


class JigsawDialog(QDialog):
    """조각 그림 만들기·편집. 비모달.

    새로 만들 때는 [저장하고 삽입] — 그림 폴더에 PDF 와 .tex 를 쓰고
    커서 자리에 ``![""](이름.pdf)`` 를 넣는다(쪽이 여럿이면 이름-1.pdf,
    이름-2.pdf … 를 한 줄씩). 편집할 때는 [재생성] — 같은 이름으로
    덮어쓴다(원고는 건드리지 않는다).
    그림 크기·정렬 같은 것은 이 도구가 정하지 않는다 — 원고에서 평소의
    마크다운 속성(``{width=...}`` 등)으로 직접 준다.
    """

    def __init__(self, window: "MainWindow", tex: Path = None):
        super().__init__(window, Qt.Tool)
        self._win = window
        self._edit_tex = tex
        self._worker = None
        self._tmp = Path(tempfile.mkdtemp(prefix="ndhmd_jigsaw_"))
        self._built_key = None             # 마지막으로 성공한 컴파일의 (프리앰블, 본문, 엔진, 클래스)
        self._built_pages = []             # 그때 나온 낱장 PDF 들(임시 폴더 안)
        self._after = None                 # 컴파일이 끝나면 이어서 할 일
        self.setAttribute(Qt.WA_DeleteOnClose)
        self.resize(640, 760)

        mono = QFont(window.editor.font())
        dirs = window.graphics_dirs()
        self._dest_dir = tex.parent if tex else (dirs[0] if dirs else None)

        self.name_edit = QLineEdit()
        self.name_edit.setPlaceholderText("파일 이름 (확장자 없이)")
        self.dest_label = QLabel()
        self.dest_label.setStyleSheet("color: gray;")

        self.class_combo = QComboBox()
        self.class_combo.addItems(JigsawFigure.CLASSES)
        self.class_combo.setToolTip(
            "standalone: 한 덩어리 그림(TikZ 등).\n"
            "article / oblivoir: 문단·여러 줄 수식처럼 폭이 정해져야 하는 것.\n"
            "여러 쪽이 나오면 쪽마다 따로 잘라 낱장 그림으로 만든다.")
        self.engine_combo = QComboBox()
        self.engine_combo.addItems(JigsawFigure.ENGINES)
        self.engine_combo.setToolTip(
            "xelatex 가 기본. luamplib(MetaPost 그림) 등 LuaTeX 에서만 되는 것은 lualatex.")

        self.pre_edit = QPlainTextEdit()
        self.pre_edit.setFont(mono)
        self.pre_edit.setMaximumHeight(110)
        self.pre_edit.setTabChangesFocus(True)
        self.pre_edit.setPlaceholderText("예) \\usepackage{tikz}\n\\usepackage{xcolor}")
        self.body_edit = QPlainTextEdit()
        self.body_edit.setFont(mono)
        #: 색상 팔레트 같은 보조 창이 "어느 입력칸에 꽂을지" 알 수 있도록,
        #: 마지막으로 커서가 있었던 프리앰블/그림 코드 칸을 기억한다.
        self._last_edit = self.body_edit
        self.pre_edit.installEventFilter(self)
        self.body_edit.installEventFilter(self)
        self.body_edit.setPlaceholderText(
            "\\begin{tikzpicture}\n  \\draw[blue, thick] (0,0) circle (1cm);\n\\end{tikzpicture}")

        self.preview = QLabel("미리보기를 누르면 여기에 그림이 나옵니다.")
        self.preview.setAlignment(Qt.AlignCenter)
        self.preview.setStyleSheet("background: white; color: gray;")
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setWidget(self.preview)
        scroll.setMinimumHeight(140)

        self.status = QLabel("")
        self.status.setWordWrap(True)
        self.log = QPlainTextEdit()
        self.log.setReadOnly(True)
        self.log.setFont(mono)
        self.log.setMaximumHeight(130)
        self.log.hide()

        self.preview_btn = QPushButton("미리보기")
        self.preview_btn.setToolTip("임시 폴더에 컴파일해 보기만 합니다 (Ctrl+Enter)")
        self.preview_btn.setShortcut(QKeySequence("Ctrl+Return"))
        self.preview_btn.clicked.connect(lambda: self._compile(None))
        self.save_btn = QPushButton("재생성" if tex else "저장하고 삽입")
        self.save_btn.setDefault(True)
        self.save_btn.clicked.connect(self._save)
        close_btn = QPushButton("닫기")
        close_btn.clicked.connect(self.close)

        btns = QHBoxLayout()
        btns.addWidget(self.preview_btn)
        btns.addStretch(1)
        btns.addWidget(self.save_btn)
        btns.addWidget(close_btn)

        lay = QVBoxLayout(self)
        name_row = QHBoxLayout()
        name_row.addWidget(QLabel("이름:"))
        name_row.addWidget(self.name_edit, 1)
        name_row.addWidget(QLabel(".pdf"))
        lay.addLayout(name_row)
        opt_row = QHBoxLayout()
        opt_row.addWidget(QLabel("클래스:"))
        opt_row.addWidget(self.class_combo)
        opt_row.addSpacing(12)
        opt_row.addWidget(QLabel("엔진:"))
        opt_row.addWidget(self.engine_combo)
        opt_row.addStretch(1)
        lay.addLayout(opt_row)
        lay.addWidget(self.dest_label)
        lay.addWidget(QLabel("프리앰블 (패키지·색 정의 등)"))
        lay.addWidget(self.pre_edit)
        lay.addWidget(QLabel("그림 코드"))
        lay.addWidget(self.body_edit, 2)
        lay.addWidget(scroll, 2)
        lay.addWidget(self.status)
        lay.addWidget(self.log)
        lay.addLayout(btns)

        if tex:
            self._load_existing(tex)
        else:
            self.setWindowTitle("조각 그림 만들기")
            self.name_edit.setText(self._free_name())
            self.pre_edit.setPlainText(window.prefs.jigsaw_preamble())
            self.engine_combo.setCurrentText(window.prefs.jigsaw_engine())
            self.class_combo.setCurrentText(window.prefs.jigsaw_class())
        self._update_dest_label()

    # -- 준비 -----------------------------------------------------------------

    def _load_existing(self, tex: Path):
        self.setWindowTitle(f"조각 그림 편집 — {tex.stem}")
        self.name_edit.setText(tex.stem)
        self.name_edit.setReadOnly(True)
        try:
            parsed = JigsawFigure.parse(tex.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError):
            parsed = None
        if parsed is None:
            self.status.setText(f"{tex.name} 을(를) 읽지 못했습니다.")
            self.save_btn.setEnabled(False)
            return
        self.pre_edit.setPlainText(parsed[0])
        self.body_edit.setPlainText(parsed[1])
        self.engine_combo.setCurrentText(parsed[2])
        self.class_combo.setCurrentText(parsed[3])
        files = JigsawFigure.figure_files(tex.parent, tex.stem)
        if files:
            self._show_pdfs(files)         # 지금 그림 그대로 먼저 보여 준다

    def _free_name(self) -> str:
        d = self._dest_dir
        n = 1
        while d is not None and ((d / f"jigsaw-{n}.tex").exists()
                                 or JigsawFigure.figure_files(d, f"jigsaw-{n}")):
            n += 1
        return f"jigsaw-{n}"

    def _update_dest_label(self):
        if self._dest_dir is None:
            self.dest_label.setText("작업공간에서 파일을 먼저 열어 주세요.")
            return
        self.dest_label.setText(f"저장 폴더: {self._win.workspace.relative(self._dest_dir)}"
                                if self._win.workspace else str(self._dest_dir))

    # -- 컴파일 ---------------------------------------------------------------

    def _key(self):
        return (self.pre_edit.toPlainText(), self.body_edit.toPlainText(),
                self.engine_combo.currentText(), self.class_combo.currentText())

    def _compile(self, then):
        if self._worker is not None:
            return
        if not self.body_edit.toPlainText().strip():
            self.status.setText("그림 코드를 적어 주세요.")
            return
        self._after = then
        self.status.setText("컴파일 중…")
        self.log.hide()
        self.preview_btn.setEnabled(False)
        self.save_btn.setEnabled(False)
        key = self._key()
        self._pending_key = key
        self._worker = _JigsawWorker(key[0], key[1], self._tmp,
                                     self._win.jigsaw_search_dirs(), key[2], key[3], self)
        self._worker.done.connect(self._on_compiled)
        self._worker.start()

    def _on_compiled(self, ok: bool, res, log: str):
        worker, self._worker = self._worker, None
        if worker is not None:
            worker.wait()
            worker.deleteLater()
        self.preview_btn.setEnabled(True)
        self.save_btn.setEnabled(True)
        after, self._after = self._after, None
        if not ok:
            self.status.setText(f"컴파일 실패: {res}")
            if log:
                self.log.setPlainText(log)
                self.log.show()
            return
        self._built_key, self._built_pages = self._pending_key, [Path(p) for p in res]
        n = len(self._built_pages)
        self.status.setText("컴파일했습니다." if n == 1 else
                            f"컴파일했습니다 — {n}쪽, 쪽마다 따로 저장됩니다.")
        self._show_pdfs(self._built_pages)
        if after:
            after()

    def _render_pdf(self, pdf: Path, scale: float = 2.0):
        """PDF 첫 쪽을 픽스맵으로. QtPdf 가 없으면 poppler 로."""
        if have_qtpdf():
            try:
                from PySide6.QtPdf import QPdfDocument
                doc = QPdfDocument(self)
                pix = None
                if doc.load(str(pdf)) == QPdfDocument.Error.None_ and doc.pageCount() > 0:
                    size = doc.pagePointSize(0)
                    img = doc.render(0, QSize(max(1, int(size.width() * scale)),
                                              max(1, int(size.height() * scale))))
                    if not img.isNull():
                        pix = QPixmap.fromImage(img)
                doc.close()
                if pix is not None:
                    return pix
            except Exception:
                pass
        for tool in ("pdftocairo", "pdftoppm"):
            if shutil.which(tool):
                out = self._tmp / "view"
                try:
                    subprocess.run([tool, "-png", "-r", str(int(72 * scale)), "-singlefile",
                                    str(pdf), str(out)], capture_output=True,
                                   timeout=20, creationflags=_NO_WINDOW)
                except (subprocess.TimeoutExpired, OSError):
                    continue
                cand = QPixmap(str(out) + ".png")
                if not cand.isNull():
                    return cand
        return None

    def _show_pdfs(self, pdfs: list):
        """낱장 PDF 들을 위에서 아래로 이어 미리보기 자리에 그린다."""
        scale = 2.0
        pixes = [p for p in (self._render_pdf(f, scale) for f in pdfs) if p is not None]
        if not pixes:
            self.preview.setPixmap(QPixmap())
            self.preview.setText("미리보기를 그릴 수 없습니다(PDF 는 만들어졌습니다).")
            return
        gap = int(10 * scale)
        width = max(p.width() for p in pixes)
        height = sum(p.height() for p in pixes) + gap * (len(pixes) - 1)
        sheet = QPixmap(width, height)
        sheet.fill(Qt.white)
        painter = QPainter(sheet)
        y = 0
        for i, p in enumerate(pixes):
            if i:
                painter.setPen(QColor("#c8c8c8"))
                painter.drawLine(0, y + gap // 2, width, y + gap // 2)
            painter.drawPixmap(0, y, p)
            y += p.height() + gap
        painter.end()
        sheet.setDevicePixelRatio(scale)
        self.preview.setText("")
        self.preview.setPixmap(sheet)

    # -- 저장 -----------------------------------------------------------------

    def _save(self):
        if self._dest_dir is None:
            QMessageBox.information(self, "조각 그림", "작업공간에서 파일을 먼저 열어 주세요.")
            return
        name = self.name_edit.text().strip()
        if name.lower().endswith(".pdf"):
            name = name[:-4]
        if not JigsawFigure.NAME_RE.match(name):
            QMessageBox.warning(self, "조각 그림",
                                "파일 이름에는 글자·숫자·점·밑줄·붙임표만 쓸 수 있습니다.")
            return
        if self._edit_tex is None and (
                (self._dest_dir / f"{name}.tex").exists()
                or JigsawFigure.figure_files(self._dest_dir, name)):
            if QMessageBox.question(
                    self, "조각 그림",
                    f"'{name}' 이(가) 이미 있습니다. 덮어쓸까요?") != QMessageBox.Yes:
                return
        if self._built_key != self._key() or not self._built_pages:
            self._compile(lambda: self._write_out(name))
        else:
            self._write_out(name)

    def _write_out(self, name: str):
        pre, body, engine, klass = self._key()
        pages = self._built_pages
        names = ([f"{name}.pdf"] if len(pages) == 1
                 else [f"{name}-{i}.pdf" for i in range(1, len(pages) + 1)])
        tex_dest = self._dest_dir / f"{name}.tex"
        ours = JigsawFigure.sidecar(self._dest_dir / f"{name}.pdf") is not None
        before = [p.name for p in JigsawFigure.figure_files(self._dest_dir, name)]
        try:
            self._dest_dir.mkdir(parents=True, exist_ok=True)
            for src, dst in zip(pages, names):
                shutil.copyfile(str(src), str(self._dest_dir / dst))
            tex_dest.write_text(JigsawFigure.compose(pre, body, engine, klass),
                                encoding="utf-8")
            # 쪽 수가 바뀌어 더는 안 쓰는 낱장은 지운다 — 이 도구가 만든
            # 그림(옆에 .tex 가 있었던 것)일 때만.
            stale = [n for n in before if n not in names] if ours else []
            for n in stale:
                (self._dest_dir / n).unlink(missing_ok=True)
        except OSError as e:
            QMessageBox.warning(self, "조각 그림", f"저장하지 못했습니다: {e}")
            return
        win = self._win
        win.prefs.write(jigsaw_preamble=pre, jigsaw_engine=engine, jigsaw_class=klass)
        panel = getattr(win, "_image_import_panel", None)
        if panel is not None:
            panel.refresh()
        if self._edit_tex is None:
            win.editor.insertPlainText("\n\n".join(f'![""]({n})' for n in names))
            win.statusBar().showMessage(
                f"조각 그림 {names[0]} 을(를) 만들어 넣었습니다."
                if len(names) == 1 else
                f"조각 그림 {name} 을(를) {len(names)}쪽으로 만들어 넣었습니다.", 4000)
            self.close()
            win.activateWindow()
            win.editor.setFocus()
        else:
            msg = f"{name} 을(를) 다시 만들었습니다."
            if stale or (before and sorted(before) != sorted(names)):
                msg += (f" 쪽 수가 바뀌어 파일이 {', '.join(names)} 이(가) 되었습니다"
                        f"(지운 것: {', '.join(stale) if stale else '없음'}) — "
                        "원고의 그림 줄을 확인하세요.")
            else:
                msg += " 원고 쪽 미리보기는 파일을 다시 열거나 F5 로 새로 고치세요."
            self.status.setText(msg)
            win.statusBar().showMessage(f"조각 그림 {name} 을(를) 재생성했습니다.", 4000)

    def eventFilter(self, obj, ev):
        if ev.type() == QEvent.FocusIn and obj in (self.pre_edit, self.body_edit):
            self._last_edit = obj
        return super().eventFilter(obj, ev)

    def event(self, ev):
        if ev.type() == QEvent.WindowActivate:
            self._win._active_jigsaw = self
        return super().event(ev)

    def insert_target(self) -> QPlainTextEdit:
        """보조 창(색상 팔레트 등)이 글자를 꽂을 입력칸."""
        return self._last_edit

    def target_label(self) -> str:
        which = "프리앰블" if self._last_edit is self.pre_edit else "그림 코드"
        return f"조각 그림 ‘{self.name_edit.text() or '이름 없음'}’ — {which}"

    def closeEvent(self, event):
        if getattr(self._win, "_active_jigsaw", None) is self:
            self._win._active_jigsaw = None
        if self._worker is not None:
            self._worker.wait()
        shutil.rmtree(self._tmp, ignore_errors=True)
        dialogs = getattr(self._win, "_jigsaw_dialogs", None)
        if dialogs is not None and self in dialogs:
            dialogs.remove(self)
        super().closeEvent(event)


def rgb_to_cmyk(r: float, g: float, b: float):
    """0~1 실수 RGB를 0~1 실수 CMYK로. svgnam.def 는 CMYK를 안 주므로
    이걸로 채운다."""
    if r == 0 and g == 0 and b == 0:
        return (0.0, 0.0, 0.0, 1.0)
    k = 1 - max(r, g, b)
    c = (1 - r - k) / (1 - k)
    m = (1 - g - k) / (1 - k)
    y = (1 - b - k) / (1 - k)
    return (c, m, y, k)


class ColorSwatchButton(QPushButton):
    """색상 팔레트 한 칸. rgb 는 0~1 실수 3개, cmyk 는 0~1 실수 4개
    (없으면 None), hsb 는 ninecolors 데이터 형식 그대로(없으면 None).
    왼쪽 클릭은 on_click(color_name) 을 부른다(보통 편집창에 색 이름을
    꽂는 데 쓴다). 우클릭은 이름/RGB/CMYK/HSB 를 클립보드로
    복사하는 메뉴를 띄운다 — ninecolorspalette2.py 원본의 동작을
    그대로 가져왔다.
    """

    def __init__(self, name: str, rgb01, cmyk01=None, hsb=None,
                on_click=None, parent=None):
        super().__init__(name, parent)
        self.color_name = name
        self.rgb01 = rgb01
        self.cmyk01 = cmyk01
        self.hsb = hsb
        self._on_click = on_click

        r, g, b = (int(round(c * 255)) for c in rgb01)
        luma = 0.299 * rgb01[0] + 0.587 * rgb01[1] + 0.114 * rgb01[2]
        text_color = "black" if luma > 0.5 else "white"
        self.setStyleSheet(
            f"QPushButton {{ background-color: rgb({r},{g},{b}); "
            f"color: {text_color}; border-radius: 4px; text-align: left; "
            f"padding-left: 6px; font-weight: bold; height: 26px; }} "
            f"QPushButton:hover {{ border: 1px solid palette(highlight); }}")
        self.clicked.connect(self._handle_click)

    def _handle_click(self):
        if self._on_click:
            self._on_click(self.color_name)

    def contextMenuEvent(self, event):
        menu = QMenu(self)
        name_act = menu.addAction("색상 이름 복사")
        rgb_act = menu.addAction("RGB 값 복사")
        cmyk_act = menu.addAction("CMYK 값 복사") if self.cmyk01 else None
        hsb_act = menu.addAction("HSB 값 복사") if self.hsb else None

        action = menu.exec(event.globalPos())
        clip = QApplication.clipboard()
        win = self.window()
        status = win.statusBar() if hasattr(win, "statusBar") else None

        if action == name_act:
            clip.setText(self.color_name)
            if status:
                status.showMessage(f"복사됨: {self.color_name}", 2000)
        elif action == rgb_act:
            r, g, b = (int(round(c * 255)) for c in self.rgb01)
            val = f"({r}, {g}, {b})"
            clip.setText(val)
            if status:
                status.showMessage(f"RGB 복사됨: {val}", 2000)
        elif cmyk_act and action == cmyk_act:
            val = "(" + ", ".join(f"{v:.3f}" for v in self.cmyk01) + ")"
            clip.setText(val)
            if status:
                status.showMessage(f"CMYK 복사됨: {val}", 2000)
        elif hsb_act and action == hsb_act:
            val = f"{self.hsb}"
            clip.setText(val)
            if status:
                status.showMessage(f"HSB 복사됨: {val}", 2000)


class ColorPalettePanel(QDialog):
    """[도구] ▸ 색상 팔레트. xcolor 기본 색(19개)과 SVG 색(151개, 사용자가
    첨부한 svgnam.def 에서 그대로 뽑았다) 조견표 — 클릭하면 그 색 이름을
    편집창 커서 위치에 꽂는다(조각 그림 창이 열려 있으면 그 창의 입력칸으로).
    우클릭하면 이름/RGB/CMYK 값을 클립보드로 복사할 수 있다.

    "Nine Colors" 탭은 사용자가 따로 만든 ninecolorspalette2.py 의
    데이터를 그대로 들여왔다 — 13개 색 계열 × 9단계 명도 + 흑백.
    원본의 색상칸 클릭 처리에 정의되지 않은 메서드(select_and_close)를
    부르는 버그가 있었다 — 흰색/검정 줄만 정상 동작했다. 여기서는 모든
    칸이 똑같이 on_click 을 부르도록 고쳤다.
    """

    BASE_COLORS = {
        "red": {"rgb": (1.0, 0.0, 0.0), "cmyk": (0.0, 1.0, 1.0, 0.0)},
        "green": {"rgb": (0.0, 1.0, 0.0), "cmyk": (1.0, 0.0, 1.0, 0.0)},
        "blue": {"rgb": (0.0, 0.0, 1.0), "cmyk": (1.0, 1.0, 0.0, 0.0)},
        "brown": {"rgb": (0.75, 0.5, 0.25), "cmyk": (0.0, 0.25, 0.5, 0.25)},
        "lime": {"rgb": (0.75, 1.0, 0.0), "cmyk": (0.25, 0.0, 1.0, 0.0)},
        "orange": {"rgb": (1.0, 0.5, 0.0), "cmyk": (0.0, 0.5, 1.0, 0.0)},
        "pink": {"rgb": (1.0, 0.75, 0.75), "cmyk": (0.0, 0.25, 0.25, 0.0)},
        "purple": {"rgb": (0.75, 0.0, 0.25), "cmyk": (0.0, 0.75, 0.5, 0.25)},
        "teal": {"rgb": (0.0, 0.5, 0.5), "cmyk": (0.5, 0.0, 0.0, 0.5)},
        "violet": {"rgb": (0.5, 0.0, 0.5), "cmyk": (0.0, 0.5, 0.0, 0.5)},
        "cyan": {"rgb": (0.0, 1.0, 1.0), "cmyk": (1.0, 0.0, 0.0, 0.0)},
        "magenta": {"rgb": (1.0, 0.0, 1.0), "cmyk": (0.0, 1.0, 0.0, 0.0)},
        "yellow": {"rgb": (1.0, 1.0, 0.0), "cmyk": (0.0, 0.0, 1.0, 0.0)},
        "olive": {"rgb": (0.5, 0.5, 0.0), "cmyk": (0.0, 0.0, 1.0, 0.5)},
        "black": {"rgb": (0.0, 0.0, 0.0), "cmyk": (0.0, 0.0, 0.0, 1.0)},
        "darkgray": {"rgb": (0.25, 0.25, 0.25), "cmyk": (0.0, 0.0, 0.0, 0.75)},
        "gray": {"rgb": (0.5, 0.5, 0.5), "cmyk": (0.0, 0.0, 0.0, 0.5)},
        "lightgray": {"rgb": (0.75, 0.75, 0.75), "cmyk": (0.0, 0.0, 0.0, 0.25)},
        "white": {"rgb": (1.0, 1.0, 1.0), "cmyk": (0.0, 0.0, 0.0, 0.0)},
    }

    #: svgnam.def(xcolor svgnames 옵션)에서 그대로 뽑은 151개.
    SVG_COLORS = {
        'AliceBlue': (0.94, 0.972, 1.0),
        'AntiqueWhite': (0.98, 0.92, 0.844),
        'Aqua': (0.0, 1.0, 1.0),
        'Aquamarine': (0.498, 1.0, 0.83),
        'Azure': (0.94, 1.0, 1.0),
        'Beige': (0.96, 0.96, 0.864),
        'Bisque': (1.0, 0.894, 0.77),
        'Black': (0.0, 0.0, 0.0),
        'BlanchedAlmond': (1.0, 0.92, 0.804),
        'Blue': (0.0, 0.0, 1.0),
        'BlueViolet': (0.54, 0.17, 0.888),
        'Brown': (0.648, 0.165, 0.165),
        'BurlyWood': (0.87, 0.72, 0.53),
        'CadetBlue': (0.372, 0.62, 0.628),
        'Chartreuse': (0.498, 1.0, 0.0),
        'Chocolate': (0.824, 0.41, 0.116),
        'Coral': (1.0, 0.498, 0.312),
        'CornflowerBlue': (0.392, 0.585, 0.93),
        'Cornsilk': (1.0, 0.972, 0.864),
        'Crimson': (0.864, 0.08, 0.235),
        'Cyan': (0.0, 1.0, 1.0),
        'DarkBlue': (0.0, 0.0, 0.545),
        'DarkCyan': (0.0, 0.545, 0.545),
        'DarkGoldenrod': (0.72, 0.525, 0.044),
        'DarkGray': (0.664, 0.664, 0.664),
        'DarkGreen': (0.0, 0.392, 0.0),
        'DarkGrey': (0.664, 0.664, 0.664),
        'DarkKhaki': (0.74, 0.716, 0.42),
        'DarkMagenta': (0.545, 0.0, 0.545),
        'DarkOliveGreen': (0.332, 0.42, 0.185),
        'DarkOrange': (1.0, 0.55, 0.0),
        'DarkOrchid': (0.6, 0.196, 0.8),
        'DarkRed': (0.545, 0.0, 0.0),
        'DarkSalmon': (0.912, 0.59, 0.48),
        'DarkSeaGreen': (0.56, 0.736, 0.56),
        'DarkSlateBlue': (0.284, 0.24, 0.545),
        'DarkSlateGray': (0.185, 0.31, 0.31),
        'DarkSlateGrey': (0.185, 0.31, 0.31),
        'DarkTurquoise': (0.0, 0.808, 0.82),
        'DarkViolet': (0.58, 0.0, 0.828),
        'DeepPink': (1.0, 0.08, 0.576),
        'DeepSkyBlue': (0.0, 0.75, 1.0),
        'DimGray': (0.41, 0.41, 0.41),
        'DimGrey': (0.41, 0.41, 0.41),
        'DodgerBlue': (0.116, 0.565, 1.0),
        'FireBrick': (0.698, 0.132, 0.132),
        'FloralWhite': (1.0, 0.98, 0.94),
        'ForestGreen': (0.132, 0.545, 0.132),
        'Fuchsia': (1.0, 0.0, 1.0),
        'Gainsboro': (0.864, 0.864, 0.864),
        'GhostWhite': (0.972, 0.972, 1.0),
        'Gold': (1.0, 0.844, 0.0),
        'Goldenrod': (0.855, 0.648, 0.125),
        'Gray': (0.5, 0.5, 0.5),
        'Green': (0.0, 0.5, 0.0),
        'GreenYellow': (0.68, 1.0, 0.185),
        'Grey': (0.5, 0.5, 0.5),
        'Honeydew': (0.94, 1.0, 0.94),
        'HotPink': (1.0, 0.41, 0.705),
        'IndianRed': (0.804, 0.36, 0.36),
        'Indigo': (0.294, 0.0, 0.51),
        'Ivory': (1.0, 1.0, 0.94),
        'Khaki': (0.94, 0.9, 0.55),
        'Lavender': (0.9, 0.9, 0.98),
        'LavenderBlush': (1.0, 0.94, 0.96),
        'LawnGreen': (0.488, 0.99, 0.0),
        'LemonChiffon': (1.0, 0.98, 0.804),
        'LightBlue': (0.68, 0.848, 0.9),
        'LightCoral': (0.94, 0.5, 0.5),
        'LightCyan': (0.88, 1.0, 1.0),
        'LightGoldenrod': (0.933, 0.867, 0.51),
        'LightGoldenrodYellow': (0.98, 0.98, 0.824),
        'LightGray': (0.828, 0.828, 0.828),
        'LightGreen': (0.565, 0.932, 0.565),
        'LightGrey': (0.828, 0.828, 0.828),
        'LightPink': (1.0, 0.712, 0.756),
        'LightSalmon': (1.0, 0.628, 0.48),
        'LightSeaGreen': (0.125, 0.698, 0.668),
        'LightSkyBlue': (0.53, 0.808, 0.98),
        'LightSlateBlue': (0.518, 0.44, 1.0),
        'LightSlateGray': (0.468, 0.532, 0.6),
        'LightSlateGrey': (0.468, 0.532, 0.6),
        'LightSteelBlue': (0.69, 0.77, 0.87),
        'LightYellow': (1.0, 1.0, 0.88),
        'Lime': (0.0, 1.0, 0.0),
        'LimeGreen': (0.196, 0.804, 0.196),
        'Linen': (0.98, 0.94, 0.9),
        'Magenta': (1.0, 0.0, 1.0),
        'Maroon': (0.5, 0.0, 0.0),
        'MediumAquamarine': (0.4, 0.804, 0.668),
        'MediumBlue': (0.0, 0.0, 0.804),
        'MediumOrchid': (0.73, 0.332, 0.828),
        'MediumPurple': (0.576, 0.44, 0.86),
        'MediumSeaGreen': (0.235, 0.7, 0.444),
        'MediumSlateBlue': (0.484, 0.408, 0.932),
        'MediumSpringGreen': (0.0, 0.98, 0.604),
        'MediumTurquoise': (0.284, 0.82, 0.8),
        'MediumVioletRed': (0.78, 0.084, 0.52),
        'MidnightBlue': (0.098, 0.098, 0.44),
        'MintCream': (0.96, 1.0, 0.98),
        'MistyRose': (1.0, 0.894, 0.884),
        'Moccasin': (1.0, 0.894, 0.71),
        'NavajoWhite': (1.0, 0.87, 0.68),
        'Navy': (0.0, 0.0, 0.5),
        'NavyBlue': (0.0, 0.0, 0.5),
        'OldLace': (0.992, 0.96, 0.9),
        'Olive': (0.5, 0.5, 0.0),
        'OliveDrab': (0.42, 0.556, 0.136),
        'Orange': (1.0, 0.648, 0.0),
        'OrangeRed': (1.0, 0.27, 0.0),
        'Orchid': (0.855, 0.44, 0.84),
        'PaleGoldenrod': (0.932, 0.91, 0.668),
        'PaleGreen': (0.596, 0.985, 0.596),
        'PaleTurquoise': (0.688, 0.932, 0.932),
        'PaleVioletRed': (0.86, 0.44, 0.576),
        'PapayaWhip': (1.0, 0.936, 0.835),
        'PeachPuff': (1.0, 0.855, 0.725),
        'Peru': (0.804, 0.52, 0.248),
        'Pink': (1.0, 0.752, 0.796),
        'Plum': (0.868, 0.628, 0.868),
        'PowderBlue': (0.69, 0.88, 0.9),
        'Purple': (0.5, 0.0, 0.5),
        'Red': (1.0, 0.0, 0.0),
        'RosyBrown': (0.736, 0.56, 0.56),
        'RoyalBlue': (0.255, 0.41, 0.884),
        'SaddleBrown': (0.545, 0.27, 0.075),
        'Salmon': (0.98, 0.5, 0.448),
        'SandyBrown': (0.956, 0.644, 0.376),
        'SeaGreen': (0.18, 0.545, 0.34),
        'Seashell': (1.0, 0.96, 0.932),
        'Sienna': (0.628, 0.32, 0.176),
        'Silver': (0.752, 0.752, 0.752),
        'SkyBlue': (0.53, 0.808, 0.92),
        'SlateBlue': (0.415, 0.352, 0.804),
        'SlateGray': (0.44, 0.5, 0.565),
        'SlateGrey': (0.44, 0.5, 0.565),
        'Snow': (1.0, 0.98, 0.98),
        'SpringGreen': (0.0, 1.0, 0.498),
        'SteelBlue': (0.275, 0.51, 0.705),
        'Tan': (0.824, 0.705, 0.55),
        'Teal': (0.0, 0.5, 0.5),
        'Thistle': (0.848, 0.75, 0.848),
        'Tomato': (1.0, 0.39, 0.28),
        'Turquoise': (0.25, 0.88, 0.815),
        'Violet': (0.932, 0.51, 0.932),
        'VioletRed': (0.816, 0.125, 0.565),
        'Wheat': (0.96, 0.87, 0.7),
        'White': (1.0, 1.0, 1.0),
        'WhiteSmoke': (0.96, 0.96, 0.96),
        'Yellow': (1.0, 1.0, 0.0),
        'YellowGreen': (0.604, 0.804, 0.196),
    }

    NINE_HUES = [
        "gray", "red", "brown", "yellow", "olive",
        "green", "teal", "cyan", "azure", "blue",
        "violet", "magenta", "purple",
    ]

    #: ninecolorspalette2.py 원본 그대로(Gemini 생성, Copilot 교정이라고
    #: 원저자가 남긴 주석도 유지했다).
    NINE_COLORS = {

        "gray1": {"rgb": (36, 36, 36), "cmyk": (0.0, 0.0, 0.0, 0.86), "gray": 0.14},
        "gray2": {"rgb": (59, 59, 59), "cmyk": (0.0, 0.0, 0.0, 0.77), "gray": 0.23},
        "gray3": {"rgb": (77, 77, 77), "cmyk": (0.0, 0.0, 0.0, 0.70), "gray": 0.30},
        "gray4": {"rgb": (97, 97, 97), "cmyk": (0.0, 0.0, 0.0, 0.62), "gray": 0.38},
        "gray5": {"rgb": (117, 117, 117), "cmyk": (0.0, 0.0, 0.0, 0.54), "gray": 0.46},
        "gray6": {"rgb": (140, 140, 140), "cmyk": (0.0, 0.0, 0.0, 0.45), "gray": 0.55},
        "gray7": {"rgb": (163, 163, 163), "cmyk": (0.0, 0.0, 0.0, 0.36), "gray": 0.64},
        "gray8": {"rgb": (191, 191, 191), "cmyk": (0.0, 0.0, 0.0, 0.25), "gray": 0.75},
        "gray9": {"rgb": (222, 222, 222), "cmyk": (0.0, 0.0, 0.0, 0.13), "gray": 0.87},
        "red1": {"rgb": (76, 8, 8), "cmyk": (0.0, 0.89, 0.89, 0.7), "hsb": (0.0, 0.89, 0.3)},
        "red2": {"rgb": (117, 13, 13), "cmyk": (0.0, 0.89, 0.89, 0.54), "hsb": (0.0, 0.89, 0.46)},
        "red3": {"rgb": (156, 17, 17), "cmyk": (0.0, 0.89, 0.89, 0.39), "hsb": (0.0, 0.89, 0.61)},
        "red4": {"rgb": (194, 21, 21), "cmyk": (0.0, 0.89, 0.89, 0.24), "hsb": (0.0, 0.89, 0.76)},
        "red5": {"rgb": (230, 30, 30), "cmyk": (0.0, 0.87, 0.87, 0.1), "hsb": (0.0, 0.87, 0.9)},
        "red6": {"rgb": (237, 90, 90), "cmyk": (0.0, 0.62, 0.62, 0.07), "hsb": (0.0, 0.62, 0.93)},
        "red7": {"rgb": (242, 133, 133), "cmyk": (0.0, 0.45, 0.45, 0.05), "hsb": (0.0, 0.45, 0.95)},
        "red8": {"rgb": (245, 171, 171), "cmyk": (0.0, 0.3, 0.3, 0.04), "hsb": (0.0, 0.3, 0.96)},
        "red9": {"rgb": (250, 212, 212), "cmyk": (0.0, 0.15, 0.15, 0.02), "hsb": (0.0, 0.15, 0.98)},
        "brown1": {"rgb": (56, 31, 6), "cmyk": (0.0, 0.45, 0.89, 0.78), "hsb": (30.0, 0.89, 0.22)},
        "brown2": {"rgb": (87, 48, 10), "cmyk": (0.0, 0.45, 0.89, 0.66), "hsb": (30.0, 0.89, 0.34)},
        "brown3": {"rgb": (117, 65, 13), "cmyk": (0.0, 0.45, 0.89, 0.54), "hsb": (30.0, 0.89, 0.46)},
        "brown4": {"rgb": (145, 81, 16), "cmyk": (0.0, 0.45, 0.89, 0.43), "hsb": (30.0, 0.89, 0.57)},
        "brown5": {"rgb": (176, 98, 19), "cmyk": (0.0, 0.45, 0.89, 0.31), "hsb": (30.0, 0.89, 0.69)},
        "brown6": {"rgb": (209, 116, 23), "cmyk": (0.0, 0.45, 0.89, 0.18), "hsb": (30.0, 0.89, 0.82)},
        "brown7": {"rgb": (232, 143, 53), "cmyk": (0.0, 0.39, 0.77, 0.09), "hsb": (30.0, 0.77, 0.91)},
        "brown8": {"rgb": (240, 179, 117), "cmyk": (0.0, 0.26, 0.51, 0.06), "hsb": (30.0, 0.51, 0.94)},
        "brown9": {"rgb": (247, 216, 186), "cmyk": (0.0, 0.12, 0.25, 0.03), "hsb": (30.0, 0.25, 0.97)},
        "yellow1": {"rgb": (38, 38, 4), "cmyk": (0.0, 0.0, 0.89, 0.85), "hsb": (60.0, 0.89, 0.15)},
        "yellow2": {"rgb": (59, 59, 6), "cmyk": (0.0, 0.0, 0.89, 0.77), "hsb": (60.0, 0.89, 0.23)},
        "yellow3": {"rgb": (79, 79, 9), "cmyk": (0.0, 0.0, 0.89, 0.69), "hsb": (60.0, 0.89, 0.31)},
        "yellow4": {"rgb": (99, 99, 11), "cmyk": (0.0, 0.0, 0.89, 0.61), "hsb": (60.0, 0.89, 0.39)},
        "yellow5": {"rgb": (122, 122, 13), "cmyk": (0.0, 0.0, 0.89, 0.52), "hsb": (60.0, 0.89, 0.48)},
        "yellow6": {"rgb": (145, 145, 16), "cmyk": (0.0, 0.0, 0.89, 0.43), "hsb": (60.0, 0.89, 0.57)},
        "yellow7": {"rgb": (168, 168, 19), "cmyk": (0.0, 0.0, 0.89, 0.34), "hsb": (60.0, 0.89, 0.66)},
        "yellow8": {"rgb": (196, 196, 22), "cmyk": (0.0, 0.0, 0.89, 0.23), "hsb": (60.0, 0.89, 0.77)},
        "yellow9": {"rgb": (230, 230, 25), "cmyk": (0.0, 0.0, 0.89, 0.1), "hsb": (60.0, 0.89, 0.9)},
        "olive1": {"rgb": (23, 41, 4), "cmyk": (0.45, 0.0, 0.89, 0.84), "hsb": (90.0, 0.89, 0.16)},
        "olive2": {"rgb": (37, 66, 7), "cmyk": (0.45, 0.0, 0.89, 0.74), "hsb": (90.0, 0.89, 0.26)},
        "olive3": {"rgb": (48, 87, 10), "cmyk": (0.45, 0.0, 0.89, 0.66), "hsb": (90.0, 0.89, 0.34)},
        "olive4": {"rgb": (61, 110, 12), "cmyk": (0.44, 0.0, 0.89, 0.57), "hsb": (90.0, 0.89, 0.43)},
        "olive5": {"rgb": (74, 133, 15), "cmyk": (0.45, 0.0, 0.89, 0.48), "hsb": (90.0, 0.89, 0.52)},
        "olive6": {"rgb": (86, 156, 17), "cmyk": (0.45, 0.0, 0.89, 0.39), "hsb": (90.0, 0.89, 0.61)},
        "olive7": {"rgb": (102, 184, 20), "cmyk": (0.45, 0.0, 0.89, 0.28), "hsb": (90.0, 0.89, 0.72)},
        "olive8": {"rgb": (119, 214, 24), "cmyk": (0.45, 0.0, 0.89, 0.16), "hsb": (90.0, 0.89, 0.84)},
        "olive9": {"rgb": (177, 240, 115), "cmyk": (0.26, 0.0, 0.52, 0.06), "hsb": (90.0, 0.52, 0.94)},
        "green1": {"rgb": (5, 43, 5), "cmyk": (0.89, 0.0, 0.89, 0.83), "hsb": (120.0, 0.89, 0.17)},
        "green2": {"rgb": (8, 69, 8), "cmyk": (0.89, 0.0, 0.89, 0.73), "hsb": (120.0, 0.89, 0.27)},
        "green3": {"rgb": (10, 89, 10), "cmyk": (0.89, 0.0, 0.89, 0.65), "hsb": (120.0, 0.89, 0.35)},
        "green4": {"rgb": (12, 112, 12), "cmyk": (0.89, 0.0, 0.89, 0.56), "hsb": (120.0, 0.89, 0.44)},
        "green5": {"rgb": (15, 138, 15), "cmyk": (0.89, 0.0, 0.89, 0.46), "hsb": (120.0, 0.89, 0.54)},
        "green6": {"rgb": (18, 163, 18), "cmyk": (0.89, 0.0, 0.89, 0.36), "hsb": (120.0, 0.89, 0.64)},
        "green7": {"rgb": (21, 191, 21), "cmyk": (0.89, 0.0, 0.89, 0.25), "hsb": (120.0, 0.89, 0.75)},
        "green8": {"rgb": (24, 222, 24), "cmyk": (0.89, 0.0, 0.89, 0.13), "hsb": (120.0, 0.89, 0.87)},
        "green9": {"rgb": (148, 242, 148), "cmyk": (0.39, 0.0, 0.39, 0.05), "hsb": (120.0, 0.39, 0.95)},
        "teal1": {"rgb": (5, 43, 24), "cmyk": (0.89, 0.0, 0.45, 0.83), "hsb": (150.0, 0.89, 0.17)},
        "teal2": {"rgb": (7, 66, 37), "cmyk": (0.89, 0.0, 0.45, 0.74), "hsb": (150.0, 0.89, 0.26)},
        "teal3": {"rgb": (10, 89, 50), "cmyk": (0.89, 0.0, 0.44, 0.65), "hsb": (150.0, 0.89, 0.35)},
        "teal4": {"rgb": (12, 112, 62), "cmyk": (0.89, 0.0, 0.45, 0.56), "hsb": (150.0, 0.89, 0.44)},
        "teal5": {"rgb": (15, 135, 75), "cmyk": (0.89, 0.0, 0.45, 0.47), "hsb": (150.0, 0.89, 0.53)},
        "teal6": {"rgb": (18, 161, 89), "cmyk": (0.89, 0.0, 0.44, 0.37), "hsb": (150.0, 0.89, 0.63)},
        "teal7": {"rgb": (21, 189, 105), "cmyk": (0.89, 0.0, 0.45, 0.26), "hsb": (150.0, 0.89, 0.74)},
        "teal8": {"rgb": (24, 219, 122), "cmyk": (0.89, 0.0, 0.45, 0.14), "hsb": (150.0, 0.89, 0.86)},
        "teal9": {"rgb": (138, 242, 190), "cmyk": (0.43, 0.0, 0.21, 0.05), "hsb": (150.0, 0.43, 0.95)},
        "cyan1": {"rgb": (4, 41, 41), "cmyk": (0.89, 0.0, 0.0, 0.84), "hsb": (180.0, 0.89, 0.16)},
        "cyan2": {"rgb": (7, 64, 64), "cmyk": (0.89, 0.0, 0.0, 0.75), "hsb": (180.0, 0.89, 0.25)},
        "cyan3": {"rgb": (10, 87, 87), "cmyk": (0.89, 0.0, 0.0, 0.66), "hsb": (180.0, 0.89, 0.34)},
        "cyan4": {"rgb": (12, 107, 107), "cmyk": (0.89, 0.0, 0.0, 0.58), "hsb": (180.0, 0.89, 0.42)},
        "cyan5": {"rgb": (14, 130, 130), "cmyk": (0.89, 0.0, 0.0, 0.49), "hsb": (180.0, 0.89, 0.51)},
        "cyan6": {"rgb": (17, 156, 156), "cmyk": (0.89, 0.0, 0.0, 0.39), "hsb": (180.0, 0.89, 0.61)},
        "cyan7": {"rgb": (20, 181, 181), "cmyk": (0.89, 0.0, 0.0, 0.29), "hsb": (180.0, 0.89, 0.71)},
        "cyan8": {"rgb": (23, 212, 212), "cmyk": (0.89, 0.0, 0.0, 0.17), "hsb": (180.0, 0.89, 0.83)},
        "cyan9": {"rgb": (120, 240, 240), "cmyk": (0.5, 0.0, 0.0, 0.06), "hsb": (180.0, 0.5, 0.94)},
        "azure1": {"rgb": (7, 37, 66), "cmyk": (0.89, 0.45, 0.0, 0.74), "hsb": (210.0, 0.89, 0.26)},
        "azure2": {"rgb": (12, 58, 105), "cmyk": (0.89, 0.45, 0.0, 0.59), "hsb": (210.0, 0.89, 0.41)},
        "azure3": {"rgb": (15, 78, 140), "cmyk": (0.89, 0.45, 0.0, 0.45), "hsb": (210.0, 0.89, 0.55)},
        "azure4": {"rgb": (19, 98, 176), "cmyk": (0.89, 0.45, 0.0, 0.31), "hsb": (210.0, 0.89, 0.69)},
        "azure5": {"rgb": (23, 117, 212), "cmyk": (0.89, 0.44, 0.0, 0.17), "hsb": (210.0, 0.89, 0.83)},
        "azure6": {"rgb": (53, 143, 232), "cmyk": (0.77, 0.39, 0.0, 0.09), "hsb": (210.0, 0.77, 0.91)},
        "azure7": {"rgb": (100, 168, 237), "cmyk": (0.58, 0.29, 0.0, 0.07), "hsb": (210.0, 0.58, 0.93)},
        "azure8": {"rgb": (148, 195, 242), "cmyk": (0.39, 0.2, 0.0, 0.05), "hsb": (210.0, 0.39, 0.95)},
        "azure9": {"rgb": (200, 225, 250), "cmyk": (0.2, 0.1, 0.0, 0.02), "hsb": (210.0, 0.2, 0.98)},
        "blue1": {"rgb": (13, 13, 122), "cmyk": (0.89, 0.89, 0.0, 0.52), "hsb": (240.0, 0.89, 0.48)},
        "blue2": {"rgb": (20, 20, 186), "cmyk": (0.89, 0.89, 0.0, 0.27), "hsb": (240.0, 0.89, 0.73)},
        "blue3": {"rgb": (37, 37, 230), "cmyk": (0.84, 0.84, 0.0, 0.1), "hsb": (240.0, 0.84, 0.9)},
        "blue4": {"rgb": (70, 70, 235), "cmyk": (0.7, 0.7, 0.0, 0.08), "hsb": (240.0, 0.7, 0.92)},
        "blue5": {"rgb": (100, 100, 237), "cmyk": (0.58, 0.58, 0.0, 0.07), "hsb": (240.0, 0.58, 0.93)},
        "blue6": {"rgb": (127, 127, 240), "cmyk": (0.47, 0.47, 0.0, 0.06), "hsb": (240.0, 0.47, 0.94)},
        "blue7": {"rgb": (157, 157, 245), "cmyk": (0.36, 0.36, 0.0, 0.04), "hsb": (240.0, 0.36, 0.96)},
        "blue8": {"rgb": (186, 186, 247), "cmyk": (0.25, 0.25, 0.0, 0.03), "hsb": (240.0, 0.25, 0.97)},
        "blue9": {"rgb": (217, 217, 250), "cmyk": (0.13, 0.13, 0.0, 0.02), "hsb": (240.0, 0.13, 0.98)},
        "violet1": {"rgb": (52, 10, 94), "cmyk": (0.45, 0.89, 0.0, 0.63), "hsb": (270.0, 0.89, 0.37)},
        "violet2": {"rgb": (81, 16, 145), "cmyk": (0.45, 0.89, 0.0, 0.43), "hsb": (270.0, 0.89, 0.57)},
        "violet3": {"rgb": (106, 21, 191), "cmyk": (0.45, 0.89, 0.0, 0.25), "hsb": (270.0, 0.89, 0.75)},
        "violet4": {"rgb": (132, 34, 230), "cmyk": (0.43, 0.85, 0.0, 0.1), "hsb": (270.0, 0.85, 0.9)},
        "violet5": {"rgb": (155, 75, 235), "cmyk": (0.34, 0.68, 0.0, 0.08), "hsb": (270.0, 0.68, 0.92)},
        "violet6": {"rgb": (175, 110, 240), "cmyk": (0.27, 0.54, 0.0, 0.06), "hsb": (270.0, 0.54, 0.94)},
        "violet7": {"rgb": (193, 143, 242), "cmyk": (0.2, 0.41, 0.0, 0.05), "hsb": (270.0, 0.41, 0.95)},
        "violet8": {"rgb": (213, 178, 247), "cmyk": (0.14, 0.28, 0.0, 0.03), "hsb": (270.0, 0.28, 0.97)},
        "violet9": {"rgb": (232, 215, 250), "cmyk": (0.07, 0.14, 0.0, 0.02), "hsb": (270.0, 0.14, 0.98)},
        "magenta1": {"rgb": (66, 7, 66), "cmyk": (0.0, 0.89, 0.0, 0.74), "hsb": (300.0, 0.89, 0.26)},
        "magenta2": {"rgb": (105, 12, 105), "cmyk": (0.0, 0.89, 0.0, 0.59), "hsb": (300.0, 0.89, 0.41)},
        "magenta3": {"rgb": (138, 15, 138), "cmyk": (0.0, 0.89, 0.0, 0.46), "hsb": (300.0, 0.89, 0.54)},
        "magenta4": {"rgb": (171, 19, 171), "cmyk": (0.0, 0.89, 0.0, 0.33), "hsb": (300.0, 0.89, 0.67)},
        "magenta5": {"rgb": (204, 22, 204), "cmyk": (0.0, 0.89, 0.0, 0.2), "hsb": (300.0, 0.89, 0.8)},
        "magenta6": {"rgb": (232, 56, 232), "cmyk": (0.0, 0.76, 0.0, 0.09), "hsb": (300.0, 0.76, 0.91)},
        "magenta7": {"rgb": (240, 115, 240), "cmyk": (0.0, 0.52, 0.0, 0.06), "hsb": (300.0, 0.52, 0.94)},
        "magenta8": {"rgb": (245, 164, 245), "cmyk": (0.0, 0.33, 0.0, 0.04), "hsb": (300.0, 0.33, 0.96)},
        "magenta9": {"rgb": (250, 207, 250), "cmyk": (0.0, 0.17, 0.0, 0.02), "hsb": (300.0, 0.17, 0.98)},
        "purple1": {"rgb": (74, 8, 41), "cmyk": (0.0, 0.89, 0.45, 0.71), "hsb": (330.0, 0.89, 0.29)},
        "purple2": {"rgb": (115, 13, 64), "cmyk": (0.0, 0.89, 0.45, 0.55), "hsb": (330.0, 0.89, 0.45)},
        "purple3": {"rgb": (150, 17, 83), "cmyk": (0.0, 0.89, 0.44, 0.41), "hsb": (330.0, 0.89, 0.59)},
        "purple4": {"rgb": (186, 20, 103), "cmyk": (0.0, 0.89, 0.45, 0.27), "hsb": (330.0, 0.89, 0.73)},
        "purple5": {"rgb": (224, 25, 125), "cmyk": (0.0, 0.89, 0.45, 0.12), "hsb": (330.0, 0.89, 0.88)},
        "purple6": {"rgb": (235, 80, 157), "cmyk": (0.0, 0.66, 0.33, 0.08), "hsb": (330.0, 0.66, 0.92)},
        "purple7": {"rgb": (240, 127, 183), "cmyk": (0.0, 0.47, 0.23, 0.06), "hsb": (330.0, 0.47, 0.94)},
        "purple8": {"rgb": (245, 169, 207), "cmyk": (0.0, 0.31, 0.16, 0.04), "hsb": (330.0, 0.31, 0.96)},
        "purple9": {"rgb": (250, 210, 230), "cmyk": (0.0, 0.16, 0.08, 0.02), "hsb": (330.0, 0.16, 0.98)},
        "black": {"rgb": (0,0,0), "cmyk": (0.0,0.0,0.0,1.0), "hsb": (0,0,0)},
        "white": {"rgb": (255,255,255), "cmyk": (0,0,0,0), "hsb": (0,1,1)},    }

    def __init__(self, window: "MainWindow"):
        super().__init__(window, Qt.Tool)
        self._win = window
        self.setWindowTitle("색상 팔레트")
        self.resize(680, 520)

        tabs = QTabWidget()
        tabs.addTab(self._build_swatch_tab(self.BASE_COLORS, per_row=4),
                    "xcolor 기본")
        tabs.addTab(self._build_svg_tab(), "SVG 색상")
        tabs.addTab(self._build_nine_tab(), "Nine Colors")

        hint = QLabel("클릭 — 색 이름 삽입 · 우클릭 — 이름/RGB/CMYK 복사")
        hint.setStyleSheet("color: palette(mid); font-size: 11px;")

        #: 조각 그림 창이 열려 있으면 색 이름은 편집창이 아니라 그 창의
        #: 입력칸으로 간다(팔레트를 가장 자주 쓰는 곳이 조각 그림의 TikZ
        #: 코드이기 때문). 편집창에 넣고 싶으면 아래 체크를 켠다.
        self.target_label = QLabel()
        self.target_label.setStyleSheet("font-size: 11px;")
        self.chk_editor = QCheckBox("항상 편집창에 삽입")
        self.chk_editor.setToolTip(
            "조각 그림 창이 열려 있어도 색 이름을 본문 편집창에 넣습니다.")
        self.chk_editor.toggled.connect(lambda _=None: self._refresh_target())
        foot = QHBoxLayout()
        foot.addWidget(self.target_label, 1)
        foot.addWidget(self.chk_editor)

        box = QVBoxLayout(self)
        box.addWidget(tabs, 1)
        box.addWidget(hint)
        box.addLayout(foot)
        self._refresh_target()

    def _jigsaw_target(self):
        if self.chk_editor.isChecked():
            return None
        return self._win.jigsaw_insert_target()

    def _refresh_target(self):
        dlg = self._jigsaw_target()
        self.target_label.setText(
            "삽입 대상: " + (dlg.target_label() if dlg is not None else "편집창"))

    def event(self, ev):
        # 팔레트를 누를 때(활성화)마다 지금 어디로 들어가는지 새로 보여 준다.
        if ev.type() in (QEvent.WindowActivate, QEvent.Show):
            self._refresh_target()
        return super().event(ev)

    def _insert(self, name: str):
        dlg = self._jigsaw_target()
        if dlg is not None:
            edit = dlg.insert_target()
            edit.insertPlainText(name)
            dlg.activateWindow()
            edit.setFocus()
            self._refresh_target()
            return
        self._win.editor.insertPlainText(name)
        # 이 패널도 별도의 최상위 창(Qt.Tool)이라, 편집창 setFocus() 만
        # 으로는 OS 차원의 활성 창이 안 바뀐다.
        self._win.activateWindow()
        self._win.editor.setFocus()

    def _build_swatch_tab(self, data: dict, per_row: int) -> QWidget:
        host = QWidget()
        grid = QGridLayout(host)
        grid.setSpacing(3)
        for i, (name, entry) in enumerate(data.items()):
            row, col = divmod(i, per_row)
            btn = ColorSwatchButton(name, entry["rgb"], entry.get("cmyk"),
                                    entry.get("hsb"), on_click=self._insert)
            grid.addWidget(btn, row, col)
        grid.setColumnStretch(per_row, 1)
        return self._scrollable(host)

    def _build_svg_tab(self) -> QWidget:
        host = QWidget()
        v = QVBoxLayout(host)

        self.svg_search = QLineEdit()
        self.svg_search.setPlaceholderText("색 이름 검색(예: Aqua, DarkGreen)…")
        self.svg_search.setClearButtonEnabled(True)
        self.svg_search.textChanged.connect(self._filter_svg)
        v.addWidget(self.svg_search)

        grid_host = QWidget()
        self.svg_grid = QGridLayout(grid_host)
        self.svg_grid.setSpacing(3)
        per_row = 5
        self._svg_buttons = []
        for i, (name, rgb) in enumerate(self.SVG_COLORS.items()):
            row, col = divmod(i, per_row)
            cmyk = rgb_to_cmyk(*rgb)
            btn = ColorSwatchButton(name, rgb, cmyk, on_click=self._insert)
            self.svg_grid.addWidget(btn, row, col)
            self._svg_buttons.append(btn)
        self.svg_grid.setColumnStretch(per_row, 1)

        v.addWidget(self._scrollable(grid_host), 1)
        return host

    def _filter_svg(self, text: str):
        needle = text.strip().lower()
        for btn in self._svg_buttons:
            btn.setVisible(not needle or needle in btn.color_name.lower())

    def _build_nine_tab(self) -> QWidget:
        host = QWidget()
        grid = QGridLayout(host)
        grid.setSpacing(2)
        for row, hue in enumerate(self.NINE_HUES):
            for col in range(9):
                name = f"{hue}{col + 1}"
                data = self.NINE_COLORS.get(name)
                if not data:
                    continue
                rgb01 = tuple(c / 255 for c in data["rgb"])
                btn = ColorSwatchButton(name, rgb01, data.get("cmyk"),
                                        data.get("hsb"), on_click=self._insert)
                grid.addWidget(btn, row, col)
        row = len(self.NINE_HUES)
        for col, name in enumerate(["white", "black"]):
            data = self.NINE_COLORS.get(name)
            if not data:
                continue
            rgb01 = tuple(c / 255 for c in data["rgb"])
            btn = ColorSwatchButton(name, rgb01, data.get("cmyk"),
                                    on_click=self._insert)
            grid.addWidget(btn, row, col)
        return self._scrollable(host)

    @staticmethod
    def _scrollable(host: QWidget) -> QWidget:
        scroll = QScrollArea()
        scroll.setWidget(host)
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QScrollArea.NoFrame)
        return scroll


# ---------------------------------------------------------------------------
# 수식 편집기 (ndhmdMath 에서 합침) — 1. 순수 함수: 화면 없이 시험할 수 있는 부분
# ---------------------------------------------------------------------------

_BEGIN_END_RE = re.compile(r"\\(begin|end)\s*\{([A-Za-z]+\*?)\}")


def _comment_spans(text: str):
    """이스케이프되지 않은 % 에서 줄 끝까지."""
    spans = []
    for m in re.finditer(r"(?<!\\)%[^\n]*", text):
        spans.append((m.start(), m.end()))
    return spans


def _in_spans(pos: int, spans) -> bool:
    return any(a <= pos < b for a, b in spans)


def scan_brackets(text: str):
    r"""괄호 짝을 찾는다. (짝 사전, 틀린 위치 목록) 을 돌려준다.

    짝 사전은 {위치: 짝의 위치}(양방향). 틀린 것으로 치는 것은 `{}`,
    `\left`/`\right`, `\begin`/`\end` 뿐이다 — `[0,1)` 처럼 (, [ 는 반쯤 열린
    구간을 쓰는 것이 정상이라 짝이 안 맞아도 나무라지 않는다(짝이 맞으면
    강조는 해 준다).
    """
    comments = _comment_spans(text)
    pairs: dict[int, int] = {}
    bad: list[int] = []
    stack_brace: list[int] = []
    stack_soft: list[tuple[str, int]] = []
    stack_lr: list[int] = []
    stack_env: list[tuple[str, int]] = []
    i, n = 0, len(text)
    while i < n:
        if _in_spans(i, comments):
            i += 1
            continue
        c = text[i]
        if c == "\\":
            m = re.match(r"\\(left|right)(?![A-Za-z])", text[i:])
            if m:
                if m.group(1) == "left":
                    stack_lr.append(i)
                else:
                    if stack_lr:
                        j = stack_lr.pop()
                        pairs[i] = j
                        pairs[j] = i
                    else:
                        bad.append(i)
                i += m.end()
                continue
            m = _BEGIN_END_RE.match(text, i)
            if m:
                if m.group(1) == "begin":
                    stack_env.append((m.group(2), i))
                else:
                    if stack_env and stack_env[-1][0] == m.group(2):
                        _, j = stack_env.pop()
                        pairs[i] = j
                        pairs[j] = i
                    else:
                        bad.append(i)
                i = m.end()
                continue
            i += 2                      # \{ \} \\ \& 같은 이스케이프는 건너뛴다
            continue
        if c == "{":
            stack_brace.append(i)
        elif c == "}":
            if stack_brace:
                j = stack_brace.pop()
                pairs[i] = j
                pairs[j] = i
            else:
                bad.append(i)
        elif c in "([":
            stack_soft.append((c, i))
        elif c in ")]":
            want = "(" if c == ")" else "["
            for k in range(len(stack_soft) - 1, -1, -1):
                if stack_soft[k][0] == want:
                    j = stack_soft[k][1]
                    del stack_soft[k:]
                    pairs[i] = j
                    pairs[j] = i
                    break
        i += 1
    bad += stack_brace + stack_lr + [p for _, p in stack_env]
    return pairs, sorted(set(bad))


#: 격자로 편집할 수 있는 환경. 값은 begin 바로 뒤에 붙는 인자의 종류:
#:   None = 없음, "opt" = 선택 인자 [..] 가 올 수 있음, "req" = 필수 인자 {..}
GRID_ENVS = {
    "matrix": None, "pmatrix": None, "bmatrix": None, "Bmatrix": None,
    "vmatrix": None, "Vmatrix": None, "smallmatrix": None,
    "cases": None, "dcases": None, "rcases": None,
    "align": None, "align*": None, "aligned": "opt",
    "alignat": "req", "alignat*": "req", "alignedat": "req",
    "flalign": None, "flalign*": None,
    "gather": None, "gather*": None, "gathered": "opt",
    "eqnarray": None, "eqnarray*": None, "split": None, "multline": None,
    "multline*": None, "array": "req",
}


@dataclass
class EnvSpan:
    name: str
    start: int          # \begin 의 시작
    body_start: int     # 인자까지 지난 본문의 시작
    body_end: int       # \end 의 시작
    end: int            # \end{..} 의 끝
    arg: str            # begin 뒤의 인자 원문("" 또는 "[t]", "{cc}")


def _read_group(text: str, i: int, open_c: str, close_c: str):
    """text[i] 가 open_c 일 때 짝이 되는 close_c 바로 다음 위치. 없으면 None."""
    if i >= len(text) or text[i] != open_c:
        return None
    depth = 0
    j = i
    while j < len(text):
        c = text[j]
        if c == "\\":
            j += 2
            continue
        if c == open_c:
            depth += 1
        elif c == close_c:
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    return None


def find_envs(text: str):
    """본문에 있는 모든 (\\begin..\\end) 짝을 EnvSpan 목록으로."""
    comments = _comment_spans(text)
    stack: list[tuple[str, int, int]] = []     # (이름, begin 시작, begin 끝)
    out: list[EnvSpan] = []
    for m in _BEGIN_END_RE.finditer(text):
        if _in_spans(m.start(), comments):
            continue
        name = m.group(2)
        if m.group(1) == "begin":
            stack.append((name, m.start(), m.end()))
        else:
            for k in range(len(stack) - 1, -1, -1):
                if stack[k][0] == name:
                    nm, s, be = stack[k]
                    del stack[k:]
                    kind = GRID_ENVS.get(nm)
                    body_start, arg = be, ""
                    if kind == "req":
                        e = _read_group(text, be, "{", "}")
                        if e:
                            arg = text[be:e]
                            body_start = e
                    elif kind == "opt":
                        e = _read_group(text, be, "[", "]")
                        if e:
                            arg = text[be:e]
                            body_start = e
                    out.append(EnvSpan(nm, s, body_start, m.start(), m.end(), arg))
                    break
    return out


def env_at(text: str, pos: int, names=None):
    """pos 를 감싸는 가장 안쪽 환경(names 에 있는 것만). 없으면 None."""
    names = GRID_ENVS if names is None else names
    best = None
    for e in find_envs(text):
        if e.name in names and e.start <= pos <= e.end:
            if best is None or (e.end - e.start) < (best.end - best.start):
                best = e
    return best


def split_rows(body: str):
    r"""환경 본문을 (칸 목록, 줄 끝 표시) 의 목록으로 쪼갠다.

    줄 끝 표시는 `\\` 또는 `\\[2pt]` 처럼 원문 그대로(마지막 줄은 "").
    중괄호·중첩 환경·`\&`·주석 안의 `&` 와 `\\` 는 구분자로 보지 않는다.
    주석(% ...)은 칸의 끝에 붙은 채로 보존된다.
    """
    rows: list[tuple[list[str], str]] = []
    cells: list[str] = []
    cur_start = 0
    depth = 0
    env_depth = 0
    i, n = 0, len(body)
    while i < n:
        c = body[i]
        if c == "%" and (i == 0 or body[i - 1] != "\\"):
            j = body.find("\n", i)
            i = n if j < 0 else j
            continue
        if c == "\\":
            m = _BEGIN_END_RE.match(body, i)
            if m:
                env_depth += 1 if m.group(1) == "begin" else -1
                i = m.end()
                continue
            if body.startswith("\\\\", i):
                if depth == 0 and env_depth == 0:
                    cells.append(body[cur_start:i])
                    j = i + 2
                    if j < n and body[j] == "*":
                        j += 1
                    k = j
                    while k < n and body[k] in " \t":
                        k += 1
                    if k < n and body[k] == "[":
                        e = _read_group(body, k, "[", "]")
                        if e:
                            j = e
                    rows.append((cells, body[i:j]))
                    cells = []
                    cur_start = j
                    i = j
                    continue
                i += 2
                continue
            i += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        elif c == "&" and depth == 0 and env_depth == 0:
            cells.append(body[cur_start:i])
            cur_start = i + 1
        i += 1
    tail = body[cur_start:]
    if tail.strip() or cells:
        cells.append(tail)
        rows.append((cells, ""))
    return [([c.strip() for c in cs], sep) for cs, sep in rows]


def _ends_in_comment(cell: str) -> bool:
    """칸의 끝이 % 주석으로 끝나는가 — 그 뒤에 & 나 \\\\ 를 같은 줄에 이어
    붙이면 주석 속으로 들어가 의미가 바뀐다."""
    spans = _comment_spans(cell)
    return bool(spans) and spans[-1][1] == len(cell)


def join_rows(rows, pad: bool = True, indent: str = "  ", amp_style: str = " & "):
    r"""split_rows 의 역. pad=True 면 열을 맞춰 소스에서도 정렬이 보이게 한다.
    주석으로 끝나는 칸은 줄을 바꿔 뒤따르는 & 와 \\ 가 주석에 먹히지 않게 한다."""
    ncols = max((len(cs) for cs, _ in rows), default=0)
    widths = [0] * ncols
    if pad:
        for cs, _ in rows:
            for k, c in enumerate(cs):
                if (k < ncols - 1 or len(cs) < ncols) and "\n" not in c \
                        and not _ends_in_comment(c):
                    widths[k] = max(widths[k], len(c))
    lines = []
    for cs, sep in rows:
        out = indent
        for k, c in enumerate(cs):
            last = k == len(cs) - 1
            text = c.ljust(widths[k]) if (pad and not last and "\n" not in c) else c
            if _ends_in_comment(c) and not last:
                out += text + "\n" + indent + amp_style.lstrip()
            else:
                out += text + ("" if last else amp_style)
        if sep:
            out = (out.rstrip() if not _ends_in_comment(cs[-1] if cs else "") else out) \
                + ("\n" + indent if cs and _ends_in_comment(cs[-1]) else " ") + sep
        lines.append(out.rstrip())
    return "\n".join(lines)


def rebuild_env(text: str, env: EnvSpan, rows) -> str:
    """env 의 본문을 rows 로 바꾼 새 전체 텍스트."""
    head = text[env.start:env.body_start]
    tail = text[env.body_end:env.end]
    body = join_rows(rows)
    return text[:env.start] + head + "\n" + body + "\n" + tail + text[env.end:]


def matrix_skeleton(env: str, rows: int, cols: int, arg: str = "") -> str:
    r"""새 환경 템플릿(스니펫 문법: ${n} 이 탭 정지점). 칸마다 정지점이 있어
    탭으로 훑으며 채울 수 있다."""
    n = 1
    lines = []
    for r in range(rows):
        cells = []
        for _ in range(cols):
            cells.append("${%d}" % n)
            n += 1
        lines.append("  " + " & ".join(cells) + (" \\\\" if r < rows - 1 else ""))
    return "\\begin{%s}%s\n%s\n\\end{%s}" % (env, arg, "\n".join(lines), env)


# ---------------------------------------------------------------------------
# 2. 스니펫 — "${1}" 정지점이 있는 템플릿
# ---------------------------------------------------------------------------

_STOP_RE = re.compile(r"\$\{(\d+)\}")


def parse_snippet(template: str, selection: str = ""):
    r"""(삽입할 글, [정지점 위치들]) — 정지점은 번호 순서(그 뒤 $0 = 끝).
    선택 영역이 있으면 첫 정지점(${1}) 자리에 그 글을 넣고 그 정지점은 없앤다."""
    out = []
    stops: list[tuple[int, int]] = []        # (번호, 위치)
    pos = 0
    last = 0
    first_used = False
    for m in _STOP_RE.finditer(template):
        out.append(template[last:m.start()])
        pos += len(template[last:m.start()])
        num = int(m.group(1))
        if num == 1 and selection and not first_used:
            out.append(selection)
            pos += len(selection)
            first_used = True
        else:
            stops.append((num, pos))
        last = m.end()
    out.append(template[last:])
    stops.sort(key=lambda t: (t[0] == 0, t[0], t[1]))
    return "".join(out), [p for _, p in stops]


# ---------------------------------------------------------------------------
# 3. 명령 목록 — 자동 완성에 쓴다
# ---------------------------------------------------------------------------

#: (명령, 스니펫 또는 None, 설명/글리프). 스니펫이 없으면 명령 이름만 넣는다.
STRUCTURES = [
    (r"\frac", r"\frac{${1}}{${2}}", "분수"),
    (r"\dfrac", r"\dfrac{${1}}{${2}}", "분수(디스플레이 크기)"),
    (r"\tfrac", r"\tfrac{${1}}{${2}}", "분수(인라인 크기)"),
    (r"\cfrac", r"\cfrac{${1}}{${2}}", "연분수"),
    (r"\binom", r"\binom{${1}}{${2}}", "이항계수"),
    (r"\sqrt", r"\sqrt{${1}}", "제곱근"),
    (r"\sum", r"\sum_{${1}}^{${2}}", "∑"),
    (r"\prod", r"\prod_{${1}}^{${2}}", "∏"),
    (r"\int", r"\int_{${1}}^{${2}}", "∫"),
    (r"\oint", r"\oint_{${1}}", "∮"),
    (r"\iint", r"\iint_{${1}}", "∬"),
    (r"\iiint", r"\iiint_{${1}}", "∭"),
    (r"\lim", r"\lim_{${1} \to ${2}}", "극한"),
    (r"\limsup", r"\limsup_{${1} \to ${2}}", "상극한"),
    (r"\liminf", r"\liminf_{${1} \to ${2}}", "하극한"),
    (r"\max", r"\max_{${1}}", "최댓값"),
    (r"\min", r"\min_{${1}}", "최솟값"),
    (r"\sup", r"\sup_{${1}}", "상한"),
    (r"\inf", r"\inf_{${1}}", "하한"),
    (r"\bigcup", r"\bigcup_{${1}}^{${2}}", "⋃"),
    (r"\bigcap", r"\bigcap_{${1}}^{${2}}", "⋂"),
    (r"\overline", r"\overline{${1}}", "위줄"),
    (r"\underline", r"\underline{${1}}", "밑줄"),
    (r"\overbrace", r"\overbrace{${1}}^{${2}}", "위 중괄호"),
    (r"\underbrace", r"\underbrace{${1}}_{${2}}", "아래 중괄호"),
    (r"\overset", r"\overset{${1}}{${2}}", "위에 얹기"),
    (r"\underset", r"\underset{${1}}{${2}}", "아래에 달기"),
    (r"\xrightarrow", r"\xrightarrow{${1}}", "긴 화살표(위 글)"),
    (r"\xleftarrow", r"\xleftarrow{${1}}", "긴 화살표(위 글)"),
    (r"\substack", r"\substack{${1} \\ ${2}}", "여러 줄 첨자"),
    (r"\text", r"\text{${1}}", "글자(본문 글꼴)"),
    (r"\textbf", r"\textbf{${1}}", "굵은 글자"),
    (r"\mathrm", r"\mathrm{${1}}", "로만체"),
    (r"\mathbf", r"\mathbf{${1}}", "굵은체"),
    (r"\boldsymbol", r"\boldsymbol{${1}}", "굵은 기호"),
    (r"\mathbb", r"\mathbb{${1}}", "칠판체 ℝ"),
    (r"\mathcal", r"\mathcal{${1}}", "필기체 𝒜"),
    (r"\mathfrak", r"\mathfrak{${1}}", "프락투어 𝔄"),
    (r"\mathscr", r"\mathscr{${1}}", "스크립트체"),
    (r"\mathit", r"\mathit{${1}}", "이탤릭"),
    (r"\mathsf", r"\mathsf{${1}}", "산세리프"),
    (r"\mathtt", r"\mathtt{${1}}", "타자체"),
    (r"\operatorname", r"\operatorname{${1}}", "함수 이름"),
    (r"\hat", r"\hat{${1}}", "모자"),
    (r"\widehat", r"\widehat{${1}}", "긴 모자"),
    (r"\tilde", r"\tilde{${1}}", "물결"),
    (r"\widetilde", r"\widetilde{${1}}", "긴 물결"),
    (r"\bar", r"\bar{${1}}", "줄"),
    (r"\vec", r"\vec{${1}}", "벡터"),
    (r"\dot", r"\dot{${1}}", "점"),
    (r"\ddot", r"\ddot{${1}}", "두 점"),
    (r"\left(", r"\left(${1}\right)", "( … ) 크기 맞춤"),
    (r"\left[", r"\left[${1}\right]", "[ … ] 크기 맞춤"),
    (r"\left\{", r"\left\{${1}\right\}", "{ … } 크기 맞춤"),
    (r"\left|", r"\left|${1}\right|", "| … | 크기 맞춤"),
    (r"\left\|", r"\left\|${1}\right\|", "‖ … ‖ 크기 맞춤"),
    (r"\left\langle", r"\left\langle ${1}\right\rangle", "⟨ … ⟩ 크기 맞춤"),
    (r"\left\lfloor", r"\left\lfloor ${1}\right\rfloor", "⌊ … ⌋ 크기 맞춤"),
    (r"\left\lceil", r"\left\lceil ${1}\right\rceil", "⌈ … ⌉ 크기 맞춤"),
    (r"\left.", r"\left.${1}\right|_{${2}}", "한쪽만 있는 구분자"),
    (r"\tag", r"\tag{${1}}", "식 번호 직접 지정"),
    (r"\label", r"\label{${1}}", "라벨"),
    (r"\intertext", r"\intertext{${1}}", "정렬 사이 글"),
    (r"\qquad", None, "넓은 공백"),
    (r"\quad", None, "공백"),
    (r"\,", None, "얇은 공백"),
    (r"\;", None, "중간 공백"),
    (r"\!", None, "음의 공백"),
]


def _env_entries():
    out = []
    for name, rows, cols in (("pmatrix", 2, 2), ("bmatrix", 2, 2), ("Bmatrix", 2, 2),
                             ("vmatrix", 2, 2), ("Vmatrix", 2, 2), ("matrix", 2, 2),
                             ("smallmatrix", 2, 2), ("cases", 2, 2), ("array", 2, 2)):
        arg = "{" + "c" * cols + "}" if name == "array" else ""
        out.append((r"\begin{%s}" % name, matrix_skeleton(name, rows, cols, arg),
                    "행렬/환경 (탭으로 칸 이동)"))
    for name in ("align", "align*", "aligned", "gather", "gather*", "gathered",
                 "multline", "multline*", "split", "flalign"):
        n = 2 if name not in ("gather", "gather*", "gathered", "multline", "multline*") else 1
        out.append((r"\begin{%s}" % name, matrix_skeleton(name, 2, n),
                    "여러 줄 수식 환경"))
    out.append((r"\begin{equation}", "\\begin{equation}\n  ${1}\n\\end{equation}", "식"))
    out.append((r"\begin{equation*}", "\\begin{equation*}\n  ${1}\n\\end{equation*}", "번호 없는 식"))
    return out


#: 글리프를 옆에 보여 줄 기호들 — "명령 글자" 쌍을 공백으로 나열.
_SYMBOLS = r"""
\alpha α \beta β \gamma γ \delta δ \epsilon ϵ \varepsilon ε \zeta ζ \eta η \theta θ \vartheta ϑ
\iota ι \kappa κ \lambda λ \mu μ \nu ν \xi ξ \pi π \varpi ϖ \rho ρ \varrho ϱ \sigma σ \varsigma ς
\tau τ \upsilon υ \phi ϕ \varphi φ \chi χ \psi ψ \omega ω
\Gamma Γ \Delta Δ \Theta Θ \Lambda Λ \Xi Ξ \Pi Π \Sigma Σ \Upsilon Υ \Phi Φ \Psi Ψ \Omega Ω
\leq ≤ \le ≤ \geq ≥ \ge ≥ \neq ≠ \ne ≠ \equiv ≡ \approx ≈ \sim ∼ \simeq ≃ \cong ≅ \propto ∝
\ll ≪ \gg ≫ \subset ⊂ \supset ⊃ \subseteq ⊆ \supseteq ⊇ \in ∈ \notin ∉ \ni ∋ \mid ∣ \parallel ∥ \perp ⊥
\leqslant ⩽ \geqslant ⩾ \lesssim ≲ \gtrsim ≳ \nmid ∤ \subsetneq ⊊ \supsetneq ⊋
\pm ± \mp ∓ \times × \div ÷ \cdot ⋅ \ast ∗ \circ ∘ \bullet ∙ \cup ∪ \cap ∩ \setminus ∖
\oplus ⊕ \ominus ⊖ \otimes ⊗ \odot ⊙ \wedge ∧ \vee ∨ \land ∧ \lor ∨ \neg ¬ \lnot ¬
\leftarrow ← \rightarrow → \to → \gets ← \leftrightarrow ↔ \Leftarrow ⇐ \Rightarrow ⇒ \Leftrightarrow ⇔
\iff ⟺ \implies ⟹ \impliedby ⟸ \mapsto ↦ \longrightarrow ⟶ \longleftarrow ⟵ \longmapsto ⟼
\uparrow ↑ \downarrow ↓ \updownarrow ↕ \nearrow ↗ \searrow ↘ \hookrightarrow ↪ \rightleftharpoons ⇌
\infty ∞ \partial ∂ \nabla ∇ \forall ∀ \exists ∃ \nexists ∄ \emptyset ∅ \varnothing ∅ \hbar ℏ \ell ℓ
\Re ℜ \Im ℑ \aleph ℵ \angle ∠ \triangle △ \surd √ \prime ′ \top ⊤ \bot ⊥ \checkmark ✓
\dots … \cdots ⋯ \vdots ⋮ \ddots ⋱ \ldots …
\langle ⟨ \rangle ⟩ \lfloor ⌊ \rfloor ⌋ \lceil ⌈ \rceil ⌉ \lVert ‖ \rVert ‖ \vert | \Vert ‖
\sin  \cos  \tan  \cot  \sec  \csc  \arcsin  \arccos  \arctan  \sinh  \cosh  \tanh
\log  \ln  \lg  \exp  \det  \gcd  \deg  \dim  \ker  \arg  \Pr  \hom  \mod  \bmod  \pmod
\displaystyle  \textstyle  \scriptstyle  \limits  \nolimits  \not  \stackrel  \phantom  \hphantom  \vphantom
\newcommand  \DeclareMathOperator  \mathbin  \mathrel  \mathop  \mathord  \mathpunct  \mathopen  \mathclose
"""


def build_command_table():
    """[(명령, 스니펫|None, 설명)] — 구조 → 환경 → 기호 순."""
    table = list(STRUCTURES) + _env_entries()
    toks = _SYMBOLS.split()
    i = 0
    while i < len(toks):
        cmd = toks[i]
        if i + 1 < len(toks) and not toks[i + 1].startswith("\\"):
            table.append((cmd, None, toks[i + 1]))
            i += 2
        else:
            table.append((cmd, None, ""))
            i += 1
    seen, out = set(), []
    for item in table:
        if item[0] not in seen:
            seen.add(item[0])
            out.append(item)
    return out


COMMANDS = build_command_table()

#: 커서 바로 앞의 "쓰다 만 명령" — \begin{al 처럼 중괄호 안까지 포함.
PREFIX_RE = re.compile(r"\\(?:begin\{[A-Za-z*]*|left\\?[A-Za-z.|{(\[]*|[A-Za-z]+|[,;!])$")


# ---------------------------------------------------------------------------
# 4. Qt 부분
# ---------------------------------------------------------------------------

def is_dark(widget: QWidget) -> bool:
    return widget.palette().color(QPalette.Window).lightness() < 128


class LatexHighlighter(QSyntaxHighlighter):
    """명령·구분자(& \\\\)·주석·중괄호에 색을 입힌다."""

    def __init__(self, doc, dark: bool):
        super().__init__(doc)
        self.set_dark(dark)

    def set_dark(self, dark: bool):
        def fmt(color, bold=False, italic=False):
            f = QTextCharFormat()
            f.setForeground(QColor(color))
            if bold:
                f.setFontWeight(QFont.Bold)
            f.setFontItalic(italic)
            return f
        if dark:
            self.f_cmd, self.f_sep = fmt("#7fb3ff"), fmt("#ffb454", True)
            self.f_comment, self.f_env = fmt("#7d8590", italic=True), fmt("#c792ea", True)
            self.f_brace = fmt("#9ccc65")
        else:
            self.f_cmd, self.f_sep = fmt("#1a5fb4"), fmt("#c64600", True)
            self.f_comment, self.f_env = fmt("#8a8f98", italic=True), fmt("#8e44ad", True)
            self.f_brace = fmt("#2e7d32")
        self.rehighlight()

    def highlightBlock(self, text):
        for m in re.finditer(r"\\(?:begin|end)(?=\s*\{)|\\[A-Za-z]+\*?|\\.", text):
            word = m.group(0)
            if word in (r"\begin", r"\end"):
                self.setFormat(m.start(), m.end() - m.start(), self.f_env)
            elif word == "\\\\":
                self.setFormat(m.start(), 2, self.f_sep)
            else:
                self.setFormat(m.start(), m.end() - m.start(), self.f_cmd)
        for m in re.finditer(r"(?<!\\)&", text):
            self.setFormat(m.start(), 1, self.f_sep)
        for m in re.finditer(r"[{}]", text):
            self.setFormat(m.start(), 1, self.f_brace)
        m = re.search(r"(?<!\\)%.*$", text)
        if m:
            self.setFormat(m.start(), len(text) - m.start(), self.f_comment)


class SourceEdit(QPlainTextEdit):
    """LaTeX 소스 편집기 — 자동 완성, 탭 정지점 스니펫, 괄호 짝 강조."""

    changed_for_preview = Signal()
    refresh_requested = Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        font = QFontDatabase.systemFont(QFontDatabase.FixedFont)
        font.setPointSize(max(font.pointSize(), 13))
        self.setFont(font)
        self.setTabStopDistance(self.fontMetrics().horizontalAdvance(" ") * 2)
        self.setLineWrapMode(QPlainTextEdit.WidgetWidth)
        self.highlighter = LatexHighlighter(self.document(), is_dark(self))
        self._stops: list[QTextCursor] = []        # 탭으로 갈 남은 정지점
        self.auto_pair = False                      # ( [ | 를 \\left…\\right 짝으로

        self._model = QStandardItemModel(self)
        for cmd, snippet, desc in COMMANDS:
            it = QStandardItem(f"{cmd}    {desc}" if desc else cmd)
            it.setData(cmd, Qt.UserRole)
            it.setData(snippet, Qt.UserRole + 1)
            it.setData(cmd, Qt.EditRole)
            self._model.appendRow(it)
        self._completer = QCompleter(self._model, self)
        self._completer.setWidget(self)
        self._completer.setCompletionMode(QCompleter.PopupCompletion)
        self._completer.setCaseSensitivity(Qt.CaseSensitive)
        self._completer.setCompletionRole(Qt.UserRole)
        self._completer.setFilterMode(Qt.MatchStartsWith)
        self._completer.setMaxVisibleItems(12)
        self._completer.popup().clicked.connect(self._popup_clicked)

        self.cursorPositionChanged.connect(self._update_extra)
        self.textChanged.connect(self._update_extra)
        self.textChanged.connect(self.changed_for_preview)

    # -- 스니펫 ---------------------------------------------------------------

    def insert_snippet(self, template: str):
        cur = self.textCursor()
        selection = cur.selectedText().replace("\u2029", "\n") if cur.hasSelection() else ""
        text, stops = parse_snippet(template, selection)
        cur.beginEditBlock()
        start = min(cur.selectionStart(), cur.selectionEnd())
        cur.insertText(text)
        cur.endEditBlock()
        self._stops = []
        # 마지막 정지점 뒤에 "스니펫 끝" 정지점을 하나 더 둔다 — 마지막 칸을
        # 채우고 Tab 을 한 번 더 누르면 닫는 괄호·\\end 밖으로 나간다.
        for p in stops + ([len(text)] if stops and stops[-1] != len(text) else []):
            c = QTextCursor(self.document())
            c.setPosition(start + p)
            self._stops.append(c)
        if self._stops:
            self._goto_stop()
        else:
            c = self.textCursor()
            c.setPosition(start + len(text))
            self.setTextCursor(c)

    def _goto_stop(self) -> bool:
        if not self._stops:
            return False
        c = self._stops.pop(0)
        self.setTextCursor(QTextCursor(c))
        return True

    # -- 자동 완성 ------------------------------------------------------------

    def _prefix(self) -> str:
        cur = self.textCursor()
        before = cur.block().text()[:cur.positionInBlock()]
        m = PREFIX_RE.search(before)
        return m.group(0) if m else ""

    def _popup_clicked(self, index):
        self._accept_completion(index)

    def _accept_completion(self, index):
        proxy_model = index.model()
        cmd = proxy_model.data(index, Qt.UserRole)
        snippet = proxy_model.data(index, Qt.UserRole + 1)
        prefix = self._prefix()
        cur = self.textCursor()
        cur.movePosition(QTextCursor.Left, QTextCursor.KeepAnchor, len(prefix))
        cur.removeSelectedText()
        self.setTextCursor(cur)
        self._completer.popup().hide()
        if snippet:
            self.insert_snippet(snippet)
        elif self.auto_pair and cmd in (r"\vert", r"\Vert") and \
                self._pair_ok(self.toPlainText()[:self.textCursor().position()]):
            self._auto_pair(cmd, cmd)
        else:
            self.textCursor().insertText(cmd)

    def _maybe_show_completer(self):
        prefix = self._prefix()
        if len(prefix) < 3 and not prefix.startswith(r"\left"):
            self._completer.popup().hide()
            return
        self._completer.setCompletionPrefix(prefix)
        popup = self._completer.popup()
        if self._completer.completionCount() == 0 or (
                self._completer.completionCount() == 1
                and self._completer.currentCompletion() == prefix
                and not self._snippet_for(prefix)):
            popup.hide()
            return
        popup.setCurrentIndex(self._completer.completionModel().index(0, 0))
        rect = self.cursorRect()
        rect.setWidth(popup.sizeHintForColumn(0) + popup.verticalScrollBar().sizeHint().width() + 8)
        self._completer.complete(rect)

    def _snippet_for(self, cmd: str):
        for c, s, _ in COMMANDS:
            if c == cmd:
                return s
        return None

    def keyPressEvent(self, event):
        popup = self._completer.popup()
        if popup.isVisible():
            if event.key() in (Qt.Key_Return, Qt.Key_Enter, Qt.Key_Tab):
                idx = popup.currentIndex()
                if idx.isValid():
                    self._accept_completion(idx)
                    return
            if event.key() == Qt.Key_Escape:
                popup.hide()
                return
            if event.key() in (Qt.Key_Up, Qt.Key_Down, Qt.Key_PageUp, Qt.Key_PageDown):
                event.ignore()          # 팝업이 가져간다
                return
        if event.key() == Qt.Key_Tab and not event.modifiers():
            if self._goto_stop():
                return
            # 정지점이 없고 바로 앞이 쓰다 만 명령이면 완성 시도
            prefix = self._prefix()
            if prefix:
                self._completer.setCompletionPrefix(prefix)
                if self._completer.completionCount() >= 1:
                    self._accept_completion(self._completer.completionModel().index(0, 0))
                    return
            self.textCursor().insertText("  ")
            return
        if event.key() in (Qt.Key_Return, Qt.Key_Enter) and \
                event.modifiers() & Qt.ControlModifier:
            if not self.close_environment():
                self.refresh_requested.emit()
            return
        if self.auto_pair and event.text() and len(event.text()) == 1 and \
                not event.modifiers() & (Qt.ControlModifier | Qt.AltModifier | Qt.MetaModifier):
            if self._try_auto_pair(event.text()):
                popup.hide()
                return
        if event.key() == Qt.Key_Escape and self._stops:
            self._stops = []
            return
        super().keyPressEvent(event)
        if event.text() and (event.text().isalpha() or event.text() in "\\{*" or
                             event.key() == Qt.Key_Backspace):
            self._maybe_show_completer()
        else:
            popup.hide() if not event.text() else None

    # -- 자동 괄호 짝 ----------------------------------------------------------

    _PAIRS = {"(": ("(", ")"), "[": ("[", "]"), "|": ("|", "|")}
    _SKIP_BEFORE = re.compile(r"\\(?:left|right|[bB]ig{1,2}[lrm]?|middle)\s*$|\\$")

    @staticmethod
    def _pair_ok(before: str) -> bool:
        """앞이 줄머리나 공백일 때만 짝을 만든다. f( 나 x^( 처럼 다른 부호 뒤는 제외."""
        return not before or before[-1] in " \t\n"

    @staticmethod
    def _plain_open_on_top(before: str, ch: str) -> bool:
        """커서 앞에서 아직 닫히지 않은 가장 안쪽 괄호가 \\left 없는 보통 괄호이고
        ch 와 짝이면 True — 이때의 닫는 괄호는 \\right 를 건너뛰지 않고 그대로 쓴다."""
        stack = []
        for m in re.finditer(r"\\left\s*([(\[])|\\right\s*([)\]])|\\.|([()\[\]])", before):
            if m.group(1):
                stack.append(("L", m.group(1)))
            elif m.group(2):
                if stack and stack[-1][0] == "L":
                    stack.pop()
            elif m.group(3):
                b = m.group(3)
                if b in "([":
                    stack.append(("P", b))
                elif stack and stack[-1][0] == "P":
                    stack.pop()
        want = "(" if ch == ")" else "["
        return bool(stack) and stack[-1] == ("P", want)

    def _auto_pair(self, lo: str, hi: str):
        """\\left<lo> … \\right<hi> 를 쓰고 커서를 가운데에 둔다. 선택이 있으면 감싼다."""
        cur = self.textCursor()
        sel = cur.selectedText().replace("\u2029", "\n") if cur.hasSelection() else ""
        start = cur.selectionStart()
        head = "\\left" + lo + " "
        cur.beginEditBlock()
        cur.insertText(head + sel + " \\right" + hi)
        cur.endEditBlock()
        end = QTextCursor(self.document())
        end.setPosition(cur.position())
        mid = QTextCursor(self.document())
        mid.setPosition(start + len(head) + len(sel))
        self.setTextCursor(mid)
        self._stops = [end]

    def _try_auto_pair(self, ch: str) -> bool:
        """글쇠 하나를 가로채 처리했으면 True."""
        text = self.toPlainText()
        cur = self.textCursor()
        pos = cur.position()
        before, after = text[:pos], text[pos:]
        line_before = before.rsplit("\n", 1)[-1]
        if "%" in line_before.replace("\\%", ""):
            return False                              # 주석 안
        # 닫는 글쇠: 이미 써 둔 \right.. 위로 건너뛴다
        close = {")": r"\)", "]": r"\]", "|": r"\|", "}": r"\\\}"}.get(ch)
        if ch == "}" and before.endswith("\\") and not cur.hasSelection() and \
                re.match(r"[ \t]*\\right\\\}", after):
            cur.setPosition(pos - 1, QTextCursor.KeepAnchor)      # 직접 친 \\ 는 지운다
            cur.removeSelectedText()
            pos -= 1
            before, after = text[:pos], text[pos + 1:]
        if ch in ")]" and self._plain_open_on_top(before, ch):
            return False                              # f(x) 의 ) 는 그냥 입력
        if close and not cur.hasSelection():
            m = re.match(r"[ \t]*\\right" + close, after)
            if m and not (ch == "|" and re.search(r"\\left\|[ \t]*$", before)):
                cur.setPosition(pos + m.end())
                self.setTextCursor(cur)
                self._stops = []
                return True
        if ch == "}" and not before.endswith("\\"):
            return False
        if ch == "|":
            # 바로 앞에서 만든 \left| 짝 한가운데서 | 를 또 치면 ‖ 로 바꾼다
            m = re.search(r"\\left\|[ \t]*$", before)
            n = re.match(r"[ \t]*\\right\|", after)
            if m and n and not cur.hasSelection():
                cur.setPosition(pos - len(m.group(0)) + 0)
                cur.setPosition(pos + n.end(), QTextCursor.KeepAnchor)
                cur.beginEditBlock()
                cur.insertText("\\left\\| ")
                mid = cur.position()
                cur.insertText(" \\right\\|")
                cur.endEditBlock()
                end = QTextCursor(self.document())
                end.setPosition(cur.position())
                c = QTextCursor(self.document())
                c.setPosition(mid)
                self.setTextCursor(c)
                self._stops = [end]
                return True
        if ch == "{":
            if before.endswith("\\") and not before.endswith("\\\\") and \
                    self._pair_ok(before[:-1]):
                cur.setPosition(pos - 1, QTextCursor.KeepAnchor)   # 앞의 \\ 를 흡수
                cur.removeSelectedText()
                self.setTextCursor(cur)
                self._auto_pair("\\{", "\\}")
                return True
            return False                              # 보통의 { 는 그룹이라 그대로 둔다
        if ch in self._PAIRS:
            if self._SKIP_BEFORE.search(before) or not self._pair_ok(before):
                return False
            lo, hi = self._PAIRS[ch]
            self._auto_pair(lo, hi)
            return True
        return False

    def unclosed_env(self):
        """커서 앞쪽에서 열렸으나 아직 닫히지 않은 가장 안쪽 환경 이름. 없으면 None."""
        text = self.toPlainText()
        pos = self.textCursor().position()
        stack = []
        for m in re.finditer(r"(?<!\\)%[^\n]*|\\(begin|end)\s*\{([A-Za-z]+\*?)\}", text):
            if not m.group(1):
                continue                      # 주석
            if m.group(1) == "begin":
                stack.append((m.group(2), m.start()))
            elif stack and stack[-1][0] == m.group(2):
                stack.pop()
        stack = [e for e in stack if e[1] < pos]
        return stack[-1][0] if stack else None

    def close_environment(self) -> bool:
        """Ctrl+Enter: 열린 \\begin{X} 에 짝이 되는 \\end{X} 를 써 넣고
        커서를 그 사이 빈 줄에 둔다. 닫을 것이 없으면 False."""
        name = self.unclosed_env()
        if not name:
            return False
        cur = self.textCursor()
        cur.beginEditBlock()
        cur.movePosition(QTextCursor.MoveOperation.EndOfBlock)
        line = cur.block().text()
        indent = re.match(r"\s*", line).group(0)
        cur.insertText("\n" + indent + "  \n" + indent + "\\end{" + name + "}")
        cur.endEditBlock()
        cur.movePosition(QTextCursor.MoveOperation.Up)
        cur.movePosition(QTextCursor.MoveOperation.EndOfBlock)
        self.setTextCursor(cur)
        self._stops = []
        return True

    # -- 괄호 짝 강조 ---------------------------------------------------------

    def _update_extra(self):
        text = self.toPlainText()
        pairs, bad = scan_brackets(text)
        dark = is_dark(self)
        sels = []

        def mk(pos, length, bg=None, underline=False):
            s = QTextEdit.ExtraSelection()
            c = QTextCursor(self.document())
            c.setPosition(pos)
            c.setPosition(min(pos + length, len(text)), QTextCursor.KeepAnchor)
            s.cursor = c
            if bg:
                s.format.setBackground(QColor(bg))
            if underline:
                s.format.setUnderlineStyle(QTextCharFormat.WaveUnderline)
                s.format.setUnderlineColor(QColor("#e53935"))
                s.format.setForeground(QColor("#e53935"))
            return s

        def tok_len(pos):
            m = re.match(r"\\(?:left|right|begin|end)(?![A-Za-z])(?:\s*\{[A-Za-z*]+\})?", text[pos:])
            return m.end() if m else 1

        for p in bad:
            sels.append(mk(p, tok_len(p), underline=True))
        p = self.textCursor().position()
        for q in (p, p - 1):
            if q in pairs:
                hl = "#3b6e3b" if dark else "#bfe8bf"
                sels.append(mk(q, tok_len(q), hl))
                sels.append(mk(pairs[q], tok_len(pairs[q]), hl))
                break
        self.setExtraSelections(sels)
        self.bracket_problems = len(bad)



# ---------------------------------------------------------------------------
# 5. 미리보기 — 실제 TeX 로 굽는다
# ---------------------------------------------------------------------------

#: 이것으로 시작하면 수식 모드 밖에서 그대로 쓰는 환경이다(자동 감지용).
MATH_MODE_ENVS = ("align", "align*", "alignat", "alignat*", "flalign", "flalign*", "gather",
                  "gather*", "multline", "multline*", "equation", "equation*", "eqnarray",
                  "eqnarray*", "math", "displaymath")


def detect_mode(source: str) -> str:
    """'inline' | 'display' | 'env' — 소스 모양으로 어림한다."""
    m = re.match(r"\s*\\begin\s*\{([A-Za-z]+\*?)\}", source)
    if not m:
        return "inline"
    return "env" if m.group(1) in MATH_MODE_ENVS else "display"


def ink_x_range(img: QImage):
    """흰 바탕에서 잉크가 있는 가로 범위 (왼쪽 px, 오른쪽 px 끝). 없으면 None."""
    img = img.convertToFormat(QImage.Format_RGB32)
    w, h, bpl = img.width(), img.height(), img.bytesPerLine()
    data = bytes(img.constBits())
    lo, hi = w, 0
    for y in range(h):
        row = data[y * bpl:y * bpl + 4 * w]
        a = len(row) - len(row.lstrip(b"\xff"))
        if a >= 4 * w:
            continue
        b = len(row.rstrip(b"\xff"))
        lo = min(lo, a // 4)
        hi = max(hi, -(-b // 4))
    return (lo, hi) if hi > lo else None


H_MARGIN_PT = 3.0        # 미리보기 그림 좌우에 남기는 여백 (pt)


def crop_h(img: QImage, margin_px: int) -> QImage:
    r = ink_x_range(img)
    if not r:
        return img
    x0 = max(0, r[0] - margin_px)
    x1 = min(img.width(), r[1] + margin_px)
    return img.copy(x0, 0, x1 - x0, img.height())


def compose_document(source: str, mode: str, preamble: str, kotex: bool):
    """(문서 전체, 소스 첫 줄이 문서의 몇 번째 줄인지(0 기준))."""
    if mode == "auto":
        mode = detect_mode(source)
    if mode == "inline":
        body = "$" + source + "$"
    elif mode == "display":
        body = "\\[" + source + "\\]"
    else:
        body = source
    head = ["\\documentclass[preview,border=6pt]{standalone}",
            "\\usepackage{amsmath,amssymb,mathtools}"]
    if kotex:
        head.append("\\usepackage{kotex}")
    if preamble.strip():
        head += preamble.strip("\n").split("\n")
    head += ["\\begin{document}"]
    return "\n".join(head + [body, "\\end{document}", ""]), len(head)


def tex_error(log_text: str, offset: int):
    """(요약, 소스 기준 줄 번호 또는 0)."""
    lines = log_text.splitlines()
    for i, line in enumerate(lines):
        if line.startswith("!"):
            msg = line[1:].strip()
            lno = 0
            for l2 in lines[i + 1:i + 8]:
                m = re.match(r"l\.(\d+)", l2)
                if m:
                    lno = int(m.group(1)) - offset
                    break
            return msg, max(lno, 0)
    return "컴파일 실패", 0


class RenderJob(QThread):
    done = Signal(int, bool, str, int)          # 번호, 성공?, PDF 경로|오류 요약, 오류 줄

    def __init__(self, job_id, doc, offset, workdir, parent=None):
        super().__init__(parent)
        self.job_id, self.doc, self.offset, self.workdir = job_id, doc, offset, Path(workdir)

    def run(self):
        try:
            self.workdir.mkdir(parents=True, exist_ok=True)
            tex = self.workdir / f"m{self.job_id}.tex"
            tex.write_text(self.doc, encoding="utf-8")
            if shutil.which("xelatex") is None:
                self.done.emit(self.job_id, False, "xelatex 를 찾지 못했습니다.", 0)
                return
            run = subprocess.run(
                ["xelatex", "-interaction=nonstopmode", "-halt-on-error", "-no-shell-escape",
                 tex.name], cwd=self.workdir, capture_output=True, timeout=40,
                creationflags=_NO_WINDOW)
            pdf = tex.with_suffix(".pdf")
            if run.returncode != 0 or not pdf.is_file():
                try:
                    log = tex.with_suffix(".log").read_text(encoding="utf-8", errors="replace")
                except OSError:
                    log = ""
                msg, line = tex_error(log, self.offset)
                self.done.emit(self.job_id, False, msg, line)
                return
            self.done.emit(self.job_id, True, str(pdf), 0)
        except subprocess.TimeoutExpired:
            self.done.emit(self.job_id, False, "40초 안에 끝나지 않아 중단했습니다.", 0)
        except Exception as e:
            self.done.emit(self.job_id, False, f"예기치 못한 오류: {e}", 0)


class PreviewPane(QWidget):
    """디바운스된 요청으로 TeX 를 돌리고 결과 PDF 를 그려 보여 준다."""

    status = Signal(str, bool, int)            # 메시지, 오류?, 오류 줄

    def __init__(self, parent=None):
        super().__init__(parent)
        self._workdir = Path(tempfile.mkdtemp(prefix="ndhmdmath_"))
        self._job_id = 0
        self._job: RenderJob | None = None
        self._pending = None
        self._pdf: Path | None = None
        self._zoom = 2.0
        self.kotex = self._has_kotex()

        self.label = QLabel("수식을 입력하면 여기에 TeX 로 구운 그림이 나옵니다.")
        self.label.setAlignment(Qt.AlignCenter)
        self.label.setStyleSheet("background: white; color: #666; padding: 8px;")
        self.scroll = QScrollArea()
        self.scroll.setWidgetResizable(True)
        self.scroll.setWidget(self.label)
        self.err = QLabel("")
        self.err.setWordWrap(True)
        self.err.setStyleSheet("color: #e53935;")
        self.err.hide()
        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.addWidget(self.scroll, 1)
        lay.addWidget(self.err)

        # 오른쪽 위 모서리에 떠 있는 작은 단추 — 기호 패널을 여닫는다
        self.side_btn = QToolButton(self)
        self.side_btn.setAutoRaise(True)
        self.side_btn.setCursor(Qt.PointingHandCursor)
        self.side_btn.setFixedSize(24, 24)
        self.side_btn.setText("\u25b6")
        self.side_btn.raise_()

        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.timeout.connect(self._fire)
        self._req = None
        self._retried = False

    def resizeEvent(self, ev):
        super().resizeEvent(ev)
        sb = self.scroll.verticalScrollBar()
        gap = sb.width() if sb.isVisible() else 0
        self.side_btn.move(self.width() - self.side_btn.width() - gap - 4, 4)
        self.side_btn.raise_()

    @staticmethod
    def _has_kotex() -> bool:
        if shutil.which("kpsewhich") is None:
            return False
        try:
            out = subprocess.run(["kpsewhich", "kotex.sty"], capture_output=True, text=True,
                                 timeout=10, creationflags=_NO_WINDOW).stdout
        except (OSError, subprocess.TimeoutExpired):
            return False
        return bool(out.strip())

    def set_zoom(self, z: float):
        self._zoom = z
        if self._pdf is not None:
            self._draw(self._pdf)

    def request(self, source: str, mode: str, preamble: str, delay_ms: int = 600):
        self._req = (source, mode, preamble)
        self._retried = False
        self._timer.start(delay_ms)

    def refresh_now(self):
        self._timer.stop()
        self._fire()

    def _fire(self):
        if self._req is None:
            return
        source, mode, preamble = self._req
        self._retried = False
        if not source.strip():
            self.label.setPixmap(QPixmap())
            self.label.setText("수식을 입력하면 여기에 TeX 로 구운 그림이 나옵니다.")
            self.err.hide()
            self._pdf = None
            self.status.emit("", False, 0)
            return
        doc, offset = compose_document(source, mode, preamble, self.kotex)
        if self._job is not None:
            self._pending = (doc, offset)
            return
        self._start(doc, offset)

    def _start(self, doc, offset):
        self._job_id += 1
        self.status.emit("컴파일 중…", False, 0)
        self._job = RenderJob(self._job_id, doc, offset, self._workdir, self)
        self._job.done.connect(self._on_done)
        self._job.start()

    def _on_done(self, job_id, ok, res, line):
        job, self._job = self._job, None
        if job is not None:
            job.wait()
            job.deleteLater()
        if self._pending is not None:
            doc, offset = self._pending
            self._pending = None
            self._start(doc, offset)
            return
        if not ok and self._req and self._req[2].strip() and not line and not self._retried:
            self._retried = True                     # 프리앰블 탓일 수 있다 — 벗겨서 한 번 더
            src, mode, _pre = self._req
            doc, offset = compose_document(src, mode, "", self.kotex)
            self._start(doc, offset)
            return
        if not ok:
            where = f" (소스 {line}번째 줄 근처)" if line else ""
            self.err.setText(f"TeX 오류: {res}{where}")
            self.err.show()
            self.status.emit(f"오류: {res}{where}", True, line)
            return
        self.err.hide()
        self._pdf = Path(res)
        self._draw(self._pdf)
        self.status.emit("미리보기 갱신" + (" (프리앰블 오류로 프리앰블 없이 그렸습니다)"
                                         if self._retried else ""), False, 0)

    def _draw(self, pdf: Path):
        dpr = self.devicePixelRatioF()
        pix = None
        if have_qtpdf():
            try:
                from PySide6.QtPdf import QPdfDocument
                doc = QPdfDocument(self)
                if doc.load(str(pdf)) == QPdfDocument.Error.None_ and doc.pageCount() > 0:
                    size = doc.pagePointSize(0)
                    scale = self._zoom * dpr
                    img = doc.render(0, QSize(max(1, int(size.width() * scale)),
                                              max(1, int(size.height() * scale))))
                    if not img.isNull():
                        flat = QImage(img.size(), QImage.Format_RGB32)
                        flat.fill(Qt.white)
                        p = QPainter(flat)
                        p.drawImage(0, 0, img)
                        p.end()
                        pix = QPixmap.fromImage(
                            crop_h(flat, int(round(H_MARGIN_PT * scale))))
                doc.close()
            except Exception:
                pix = None
        if pix is None and shutil.which("pdftoppm"):
            out = pdf.with_suffix("")
            subprocess.run(["pdftoppm", "-png", "-r", str(int(72 * self._zoom * dpr)),
                            "-singlefile", str(pdf), str(out)], capture_output=True,
                           timeout=20, creationflags=_NO_WINDOW)
            cand = QPixmap(str(out) + ".png")
            pix = (QPixmap.fromImage(crop_h(cand.toImage(),
                                            int(round(H_MARGIN_PT * self._zoom * dpr))))
                   if not cand.isNull() else None)
        if pix is None:
            self.label.setPixmap(QPixmap())
            self.label.setText("그림을 그릴 수 없습니다(QtPdf 또는 pdftoppm 이 필요합니다).")
            return
        pix.setDevicePixelRatio(dpr)
        self.label.setText("")
        self.label.setPixmap(pix)

    def shutdown(self):
        self._timer.stop()
        if self._job is not None:
            self._job.wait()
        shutil.rmtree(self._workdir, ignore_errors=True)


# ---------------------------------------------------------------------------
# 6. 격자 편집기 · 새 환경 삽입
# ---------------------------------------------------------------------------

ALIGN_ENVS = {"align", "align*", "aligned", "alignat", "alignat*", "alignedat",
              "flalign", "flalign*", "eqnarray", "eqnarray*", "split"}


class _DividerDelegate(QStyledItemDelegate):
    """첫 열 오른쪽에 굵은 빨간 줄 — align 류에서 자동으로 들어가는 정렬용 & 자리."""

    def paint(self, painter, option, index):
        super().paint(painter, option, index)
        if index.column() == 0:
            painter.save()
            painter.setPen(QPen(QColor("#e53935"), 3))
            x = option.rect.right()
            painter.drawLine(x, option.rect.top(), x, option.rect.bottom())
            painter.restore()


class GridEditorDialog(QDialog):
    """행렬·cases·align 류를 칸 단위로 편집한다. `&` 와 `\\\\` 는 만들어 준다."""

    def __init__(self, text: str, env: EnvSpan, parent=None):
        super().__init__(parent)
        self._text, self._env = text, env
        self.setWindowTitle(f"격자 편집 — {env.name}")
        self.resize(640, 380)
        rows = split_rows(text[env.body_start:env.body_end])
        if not rows:
            rows = [([""], "")]
        self._seps = [sep for _, sep in rows]
        self._orig_len = [len(cs) for cs, _ in rows]
        self._align = env.name in ALIGN_ENVS
        ncols = max(len(cs) for cs, _ in rows)
        if self._align:
            ncols = max(ncols, 2)          # 정렬 & 의 앞/뒤 두 열은 늘 보인다
        self.table = QTableWidget(len(rows), ncols)
        mono = QFontDatabase.systemFont(QFontDatabase.FixedFont)
        self.table.setFont(mono)
        self.table.setEditTriggers(QAbstractItemView.AllEditTriggers)
        self.table.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        for r, (cs, _) in enumerate(rows):
            for c in range(ncols):
                self.table.setItem(r, c, QTableWidgetItem(cs[c] if c < len(cs) else ""))
        if self._align:
            self.table.setItemDelegateForColumn(0, _DividerDelegate(self.table))
        self._relabel()

        def btn(label, slot):
            b = QPushButton(label)
            b.clicked.connect(slot)
            return b
        bar = QHBoxLayout()
        for label, slot in (("행 추가", self._add_row), ("행 삭제", self._del_row),
                            ("열 추가", self._add_col), ("열 삭제", self._del_col)):
            bar.addWidget(btn(label, slot))
        bar.addStretch(1)
        hint = QLabel("칸에는 수식만 적으세요. & 와 \\\\ 는 저장할 때 자동으로 넣습니다"
                      + (" (빨간 줄이 정렬 &)" if self._align else "") + ". "
                      "소스의 % 주석도 그대로 보존됩니다.")
        hint.setWordWrap(True)
        box = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        box.accepted.connect(self.accept)
        box.rejected.connect(self.reject)
        lay = QVBoxLayout(self)
        lay.addLayout(bar)
        lay.addWidget(self.table, 1)
        lay.addWidget(hint)
        lay.addWidget(box)
        hint.setText(hint.text() + "\nTab/Shift+Tab 칸 이동 · Ctrl+Enter 아래에 행 추가 · "
                     "Ctrl+Tab 오른쪽에 열 추가")
        for seq, slot in (("Tab", lambda: self._step(1)), ("Shift+Tab", lambda: self._step(-1)),
                          ("Ctrl+Return", self._add_row_below), ("Ctrl+Enter", self._add_row_below),
                          ("Ctrl+Tab", self._add_col_right)):
            sc = QShortcut(QKeySequence(seq), self)
            sc.setContext(Qt.WidgetWithChildrenShortcut)
            sc.activated.connect(slot)

    def _goto(self, r: int, c: int):
        self.table.setCurrentCell(r, c)
        self.table.setFocus()
        it = self.table.item(r, c)
        if it:
            self.table.editItem(it)

    def _step(self, d: int):
        """다음/이전 칸. 줄 끝에서는 다음/이전 줄로 넘어간다."""
        R, C = self.table.rowCount(), self.table.columnCount()
        r, c = max(self.table.currentRow(), 0), max(self.table.currentColumn(), 0)
        i = r * C + c + d
        if i < 0:
            i = 0
        if i >= R * C:
            self._add_row_below(at_end=True)
            return
        self._goto(i // C, i % C)

    def _add_row_below(self, at_end=False):
        c = max(self.table.currentColumn(), 0)
        if at_end:
            self.table.setCurrentCell(self.table.rowCount() - 1, c)
        self._commit()
        self._goto(self._add_row(), 0 if at_end else c)

    def _add_col_right(self):
        r = max(self.table.currentRow(), 0)
        self._commit()
        self._goto(r, self._add_col())

    def _commit(self):
        """열려 있는 셀 편집기의 내용을 확정한다."""
        w = QApplication.focusWidget()
        if w is not None and w is not self.table:
            w.clearFocus()
            self.table.setFocus()

    def _relabel(self):
        self.table.setVerticalHeaderLabels([str(i + 1) for i in range(self.table.rowCount())])
        self.table.setHorizontalHeaderLabels([str(i + 1) for i in range(self.table.columnCount())])

    def _add_row(self):
        r = self.table.currentRow()
        r = self.table.rowCount() if r < 0 else r + 1
        self.table.insertRow(r)
        for c in range(self.table.columnCount()):
            self.table.setItem(r, c, QTableWidgetItem(""))
        self._seps.insert(r, "\\\\")
        self._orig_len.insert(r, 0)           # 새 줄은 끝의 빈 칸을 떼어 낸다
        self._relabel()
        return r

    def _del_row(self):
        r = self.table.currentRow()
        if r >= 0 and self.table.rowCount() > 1:
            self.table.removeRow(r)
            del self._seps[r]
            del self._orig_len[r]
            self._relabel()

    def _add_col(self):
        c = self.table.currentColumn()
        c = self.table.columnCount() if c < 0 else c + 1
        if self._align:
            c = max(c, 2)                  # 첫 열 뒤의 정렬 & 자리는 건드리지 않는다
        self.table.insertColumn(c)
        for r in range(self.table.rowCount()):
            self.table.setItem(r, c, QTableWidgetItem(""))
        if not self._align:
            self._orig_len = [n + 1 for n in self._orig_len]
        self._relabel()
        return c

    def _del_col(self):
        c = self.table.currentColumn()
        if c >= 0 and self.table.columnCount() > 1:
            self.table.removeColumn(c)
            self._orig_len = [min(n, self.table.columnCount()) for n in self._orig_len]
            self._relabel()

    def result_text(self) -> str:
        rows = []
        n = self.table.rowCount()
        for r in range(n):
            cells = []
            for c in range(self.table.columnCount()):
                it = self.table.item(r, c)
                cells.append(it.text().strip() if it else "")
            keep = max(self._orig_len[r], 1)
            while len(cells) > keep and not cells[-1]:
                cells.pop()
            sep = self._seps[r]
            if r < n - 1 and not sep:
                sep = "\\\\"
            rows.append((cells, sep))
        return rebuild_env(self._text, self._env, rows)


class NewEnvDialog(QDialog):
    """행렬·cases·align 등을 행×열 크기로 골라 템플릿으로 삽입."""

    ENVS = ("pmatrix", "bmatrix", "Bmatrix", "vmatrix", "Vmatrix", "matrix", "smallmatrix",
            "cases", "array", "align", "align*", "aligned", "gather", "gather*", "gathered",
            "multline", "split")

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("행렬·환경 삽입")
        self.combo = QComboBox()
        self.combo.addItems(self.ENVS)
        self.rows = QSpinBox()
        self.rows.setRange(1, 30)
        self.rows.setValue(2)
        self.cols = QSpinBox()
        self.cols.setRange(1, 20)
        self.cols.setValue(2)
        form = QFormLayout(self)
        form.addRow("환경", self.combo)
        form.addRow("행", self.rows)
        form.addRow("열 (& 로 나뉘는 칸 수)", self.cols)
        box = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        box.accepted.connect(self.accept)
        box.rejected.connect(self.reject)
        form.addRow(box)

    def snippet(self) -> str:
        name = self.combo.currentText()
        cols = self.cols.value()
        arg = "{" + "c" * cols + "}" if name == "array" else ""
        return matrix_skeleton(name, self.rows.value(), cols, arg)


# ---------------------------------------------------------------------------
# 7. 메인 창
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# 5b. 기호 일람표 패널
# ---------------------------------------------------------------------------

#: _SYMBOLS 의 줄 번호(0 기준) → 분류. 마지막 분류는 인자가 필요한 명령이라 그림은 그리지 않는다.
SYMBOL_GROUPS = (("그리스 문자", (0, 3)), ("관계", (4, 6)), ("연산·논리", (7, 8)),
                 ("화살표", (9, 11)), ("기타 기호", (12, 13)), ("점·괄호", (14, 15)),
                 ("함수 이름", (16, 17)), ("스타일·정의", (18, 19)))
_TEXT_ONLY_GROUPS = {"스타일·정의"}


def symbol_groups():
    """[(분류, [(명령, 글자|''), …])] — _SYMBOLS 에서 만든다."""
    lines = [ln for ln in _SYMBOLS.strip("\n").split("\n")]
    out = []
    for name, (a, b) in SYMBOL_GROUPS:
        items, seen = [], set()
        for ln in lines[a:b + 1]:
            toks = ln.split()
            i = 0
            while i < len(toks):
                cmd = toks[i]
                glyph = ""
                if i + 1 < len(toks) and not toks[i + 1].startswith("\\"):
                    glyph = toks[i + 1]
                    i += 2
                else:
                    i += 1
                if cmd not in seen:
                    seen.add(cmd)
                    items.append((cmd, glyph))
        out.append((name, items))
    return out


def symbol_sheet_tex(cmds):
    """명령 하나가 한 쪽(standalone multi)이 되는 문서."""
    shown = {"\\mod": "a\\mod b", "\\bmod": "a\\bmod b", "\\pmod": "a\\pmod{b}"}
    body = "\n".join("\\begin{sym}" + shown.get(c, c) + "\\end{sym}" for c in cmds)
    return ("\\documentclass[multi=sym,border=2pt]{standalone}\n"
            "\\usepackage{amsmath,amssymb,mathtools}\n"
            "\\newenvironment{sym}{$}{$}\n\\begin{document}\n" + body + "\n\\end{document}\n")


class SymbolSheetJob(QThread):
    """일람표 PDF 를 한 번 만들어 캐시한다. 실패하면 글자 표시로 대신한다."""
    done = Signal(bool, str)

    def __init__(self, cmds, pdf: Path, parent=None):
        super().__init__(parent)
        self.cmds, self.pdf = list(cmds), Path(pdf)

    def run(self):
        try:
            if shutil.which("xelatex") is None:
                self.done.emit(False, "xelatex 없음")
                return
            work = self.pdf.parent / "work"
            work.mkdir(parents=True, exist_ok=True)
            tex = work / "sheet.tex"
            tex.write_text(symbol_sheet_tex(self.cmds), encoding="utf-8")
            subprocess.run(["xelatex", "-interaction=nonstopmode", "-no-shell-escape", tex.name],
                           cwd=work, capture_output=True, timeout=120,
                           creationflags=_NO_WINDOW)
            out = work / "sheet.pdf"
            if not out.is_file():
                self.done.emit(False, "컴파일 실패")
                return
            shutil.copyfile(out, self.pdf)
            shutil.rmtree(work, ignore_errors=True)
            self.done.emit(True, str(self.pdf))
        except Exception as e:
            self.done.emit(False, str(e))


class SymbolPanel(QWidget):
    """분류 + 검색 + 기호 격자. 누르면 chosen(명령) 신호."""
    chosen = Signal(str)
    CELL = QSize(64, 46)

    def __init__(self, parent=None):
        super().__init__(parent)
        self._groups = symbol_groups()
        self._icons = {}                       # 명령 → QIcon (그림이 준비되면)
        self._job = None
        self.search = QLineEdit()
        self.search.setPlaceholderText("검색: 명령 이름 (예: arrow, le)")
        self.search.setClearButtonEnabled(True)
        self.group = QComboBox()
        self.group.addItem("전체", None)
        self.group.addItem("구조 (분수·근호 …)", "__struct__")
        for name, _ in self._groups:
            self.group.addItem(name, name)
        self.list = QListWidget()
        self.list.setViewMode(QListWidget.IconMode)
        self.list.setResizeMode(QListWidget.Adjust)
        self.list.setMovement(QListWidget.Static)
        self.list.setUniformItemSizes(True)
        self.list.setGridSize(self.CELL)
        self.list.setIconSize(QSize(self.CELL.width() - 12, self.CELL.height() - 12))
        self.list.setWordWrap(False)
        self.status = QLabel("")
        lay = QVBoxLayout(self)
        lay.setContentsMargins(4, 4, 4, 4)
        lay.addWidget(self.search)
        lay.addWidget(self.group)
        lay.addWidget(self.list, 1)
        lay.addWidget(self.status)
        self.search.textChanged.connect(self._fill)
        self.group.currentIndexChanged.connect(self._fill)
        self.list.itemClicked.connect(self._pick)
        self._fill()

    # -- 항목 채우기 ---------------------------------------------------------

    def _entries(self):
        key = self.group.currentData()
        q = self.search.text().strip().lstrip("\\").lower()
        res = []
        if key == "__struct__":
            for cmd, snip, desc in STRUCTURES:
                res.append((cmd, snip, "", desc))
        if key != "__struct__":
            for name, items in self._groups:
                if key in (None, name):
                    for cmd, glyph in items:
                        res.append((cmd, None, glyph, name))
        if q:
            res = [e for e in res if q in e[0].lower() or q in e[3].lower() or q == e[2]]
        return res

    def _fill(self, *_):
        self.list.clear()
        for cmd, snip, glyph, desc in self._entries():
            it = QListWidgetItem()
            icon = self._icons.get(cmd)
            if icon is not None:
                it.setIcon(icon)
            else:
                it.setText(cmd if snip is not None else (glyph or cmd))
            it.setToolTip(f"{cmd}   {desc}")
            it.setData(Qt.UserRole, snip if snip else cmd)
            it.setData(Qt.UserRole + 1, snip is not None)
            it.setSizeHint(self.CELL)
            it.setTextAlignment(Qt.AlignCenter)
            self.list.addItem(it)

    def _pick(self, it):
        text = it.data(Qt.UserRole)
        if not it.data(Qt.UserRole + 1) and re.fullmatch(r"\\[A-Za-z]+", text):
            text += " "                        # 뒤에 글자가 붙어도 명령이 깨지지 않게
        self.chosen.emit(text)

    # -- 그림 준비 -------------------------------------------------------------

    def ensure_images(self):
        """처음 열릴 때 한 번. 캐시가 있으면 바로 쓰고, 없으면 만든다."""
        if self._icons or self._job is not None:
            return
        cmds = [c for name, items in self._groups if name not in _TEXT_ONLY_GROUPS
                for c, _g in items]
        key = hashlib.sha1((symbol_sheet_tex(cmds) + "v1").encode()).hexdigest()[:12]
        base = Path(QStandardPaths.writableLocation(QStandardPaths.CacheLocation)
                    or tempfile.gettempdir()) / "ndhmdMath"
        base.mkdir(parents=True, exist_ok=True)
        pdf = base / f"symbols-{key}.pdf"
        self._cmds = cmds
        if pdf.is_file():
            self._load(pdf)
            return
        if not have_qtpdf() or shutil.which("xelatex") is None:
            self.status.setText("글자로 표시합니다 (xelatex 또는 QtPdf 없음)")
            return
        self.status.setText("기호 그림을 처음 한 번 만드는 중…")
        self._job = SymbolSheetJob(cmds, pdf, self)
        self._job.done.connect(lambda ok, m: self._load(Path(m)) if ok else
                               self.status.setText("글자로 표시합니다 (" + m + ")"))
        self._job.start()

    def _load(self, pdf: Path):
        try:
            from PySide6.QtPdf import QPdfDocument
        except ImportError:
            return
        doc = QPdfDocument(self)
        if doc.load(str(pdf)) != QPdfDocument.Error.None_ or doc.pageCount() != len(self._cmds):
            self.status.setText("글자로 표시합니다 (일람표 쪽 수가 맞지 않음)")
            try:
                pdf.unlink()
            except OSError:
                pass
            return
        dark = is_dark(self)
        dpr = self.devicePixelRatioF()
        box = self.list.iconSize()
        for i, cmd in enumerate(self._cmds):
            sz = doc.pagePointSize(i)
            sc = min(box.width() / max(sz.width(), 1), box.height() / max(sz.height(), 1), 2.2)
            sc *= dpr * 1.0
            img = doc.render(i, QSize(max(1, int(sz.width() * sc)), max(1, int(sz.height() * sc))))
            flat = QImage(img.size(), QImage.Format_RGB32)
            flat.fill(Qt.white)
            p = QPainter(flat)
            p.drawImage(0, 0, img)
            p.end()
            if dark:
                flat.invertPixels()
            pm = QPixmap.fromImage(flat)
            pm.setDevicePixelRatio(dpr)
            self._icons[cmd] = QIcon(pm)
        doc.close()
        self.status.setText(f"기호 {len(self._icons)}개 — 누르면 커서 위치에 들어갑니다")
        self._fill()

    def shutdown(self):
        if self._job is not None:
            self._job.wait()


INSERT_MENU = (
    ("분수·근호·첨자", (r"\frac", r"\dfrac", r"\binom", r"\sqrt", "^", "_")),
    ("큰 연산자", (r"\sum", r"\prod", r"\int", r"\oint", r"\lim", r"\bigcup", r"\bigcap")),
    ("괄호(크기 맞춤)", (r"\left(", r"\left[", r"\left\{", r"\left|", r"\left\|",
                     r"\left\langle", r"\left\lfloor", r"\left\lceil", r"\left.")),
    ("글꼴·장식", (r"\mathbb", r"\mathcal", r"\mathfrak", r"\mathbf", r"\mathrm", r"\boldsymbol",
               r"\text", r"\operatorname", r"\hat", r"\widehat", r"\tilde", r"\bar", r"\vec",
               r"\dot", r"\overline", r"\underline", r"\overbrace", r"\underbrace",
               r"\overset", r"\underset", r"\xrightarrow")),
)

_EXTRA_SNIPPETS = {"^": ("위 첨자", "^{${1}}"), "_": ("아래 첨자", "_{${1}}")}


class MathEditorWindow(QMainWindow):
    """독립 앱의 주 창. 나중에 Writer 에 합칠 때는 text()/set_text() 만 쓰면 된다."""

    #: 본문에 넣기를 눌렀을 때(수식, 모양). 모양은 inline|display|env.
    committed = Signal(str, str)
    #: 창이 닫혔다(넣었든 취소했든).
    finished = Signal()

    def __init__(self, path: Path | None = None, text: str = "", parent=None,
                 embedded: bool = False, preamble: str = ""):
        super().__init__(parent)
        self.embedded = embedded
        self._committed = False
        self.settings = QSettings("ktug.org", "ndhmdMath")
        self.path = path
        self._dirty = False
        self.setAcceptDrops(False)

        self.mode = QComboBox()
        for key, label in (("auto", "자동 판별"), ("inline", "인라인  $…$"),
                           ("display", "디스플레이  \\[…\\]"), ("env", "환경 그대로")):
            self.mode.addItem(label, key)
        idx = self.mode.findData(self.settings.value("mode", "auto", type=str))
        self.mode.setCurrentIndex(max(idx, 0))
        self.zoom = QComboBox()
        for z in (100, 150, 200, 300, 400):
            self.zoom.addItem(f"{z}%", z / 100.0)
        zi = self.zoom.findData(float(self.settings.value("zoom", 3.0)))
        self.zoom.setCurrentIndex(zi if zi >= 0 else 3)
        self.pre_toggle = QCheckBox("프리앰블")
        self.pre_edit = QPlainTextEdit()
        self.pre_edit.setPlaceholderText("\\newcommand{\\R}{\\mathbb{R}} 처럼 쓰는 정의나 \\usepackage")
        if embedded:
            self.pre_edit.setPlainText(preamble)      # 원고의 preamble: 을 그대로 쓴다
            self.pre_edit.setReadOnly(True)
            self.pre_toggle.setText("원고 프리앰블")
        else:
            self.pre_edit.setPlainText(self.settings.value("preamble", "", type=str))
        self.pre_edit.setMaximumHeight(90)
        self.pre_edit.setFont(QFontDatabase.systemFont(QFontDatabase.FixedFont))
        self.pre_edit.setVisible(bool(self.pre_edit.toPlainText().strip()) and not embedded)
        self.pre_toggle.setChecked(self.pre_edit.isVisible())

        self.source = SourceEdit()
        self.source.setPlainText(text)
        self.preview = PreviewPane()

        top = QHBoxLayout()
        top.addWidget(QLabel("모양:"))
        top.addWidget(self.mode)
        top.addStretch(1)
        top.addWidget(self.pre_toggle)
        top.addWidget(QLabel("확대:"))
        top.addWidget(self.zoom)
        left = QWidget()
        lv = QVBoxLayout(left)
        lv.setContentsMargins(6, 6, 6, 6)
        lv.addLayout(top)
        lv.addWidget(self.pre_edit)
        lv.addWidget(self.source, 1)
        self.split = QSplitter(Qt.Horizontal)
        self.split.addWidget(left)
        self.split.addWidget(self.preview)
        self.split.setStretchFactor(0, 1)
        self.split.setStretchFactor(1, 1)
        self.setCentralWidget(self.split)
        self.symbols = SymbolPanel()
        self.sym_dock = QDockWidget("기호 일람표", self)
        self.sym_dock.setObjectName("symdock")
        self.sym_dock.setWidget(self.symbols)
        self.addDockWidget(Qt.RightDockWidgetArea, self.sym_dock)
        self.sym_dock.setVisible(self.settings.value("symbols", False, type=bool))
        self.sym_dock.visibilityChanged.connect(
            lambda v: self.symbols.ensure_images() if v else None)
        self.symbols.chosen.connect(self._insert_symbol)
        self.preview.side_btn.clicked.connect(
            lambda: self.sym_dock.setVisible(not self.sym_dock.isVisible()))

        def _sync_btn(v):
            self.preview.side_btn.setText("\u25c0" if v else "\u25b6")
            self.preview.side_btn.setToolTip("기호 일람표 닫기 (F4)" if v else "기호 일람표 열기 (F4)")
        self.sym_dock.visibilityChanged.connect(_sync_btn)
        _sync_btn(self.sym_dock.isVisible())

        self.msg = QLabel("")
        self.pos = QLabel("")
        self.statusBar().addWidget(self.msg, 1)
        self.statusBar().addPermanentWidget(self.pos)
        if embedded:
            hint = QLabel("Ctrl+Enter 본문에 넣기 · Esc 취소")
            hint.setStyleSheet("color: gray; padding-right: 10px;")
            self.statusBar().addPermanentWidget(hint)

        self._build_menus()
        self.source.changed_for_preview.connect(self._on_changed)
        self.source.cursorPositionChanged.connect(self._update_pos)
        self._first_env = None
        self.source.refresh_requested.connect(
            self.commit if embedded else self.preview.refresh_now)
        self.mode.currentIndexChanged.connect(lambda _=0: self._request(0))
        self.zoom.currentIndexChanged.connect(
            lambda _=0: self.preview.set_zoom(self.zoom.currentData()))
        self.pre_toggle.toggled.connect(self.pre_edit.setVisible)
        self.pre_edit.textChanged.connect(self._on_changed)
        self.preview.status.connect(self._on_preview_status)
        self.preview.set_zoom(self.zoom.currentData())

        geo = self.settings.value("geometry")
        if geo:
            self.restoreGeometry(geo)
        else:
            self.resize(1100, 560)
        self._update_title()
        self._update_pos()
        self._request(0)

    # -- 외부에서 쓰는 창구 ------------------------------------------------------

    def text(self) -> str:
        return self.source.toPlainText()

    def set_text(self, text: str):
        self.source.setPlainText(text)
        self._dirty = False
        self._update_title()

    # -- 메뉴 ------------------------------------------------------------------

    def _act(self, menu, label, slot, shortcut=None):
        a = QAction(label, self)
        if shortcut:
            a.setShortcut(QKeySequence(shortcut))
        a.triggered.connect(lambda _=False: slot())
        menu.addAction(a)
        return a

    def _build_menus(self):
        if self.embedded:
            m = self.menuBar().addMenu("수식(&M)")
            self._act(m, "본문에 넣기 (Ctrl+Enter)", self.commit)
            self._act(m, "취소 (Esc)", self.close)
        else:
            m = self.menuBar().addMenu("파일(&F)")
            self._act(m, "열기…", self.open_file, "Ctrl+O")
            self._act(m, "저장", self.save_file, "Ctrl+S")
            self._act(m, "다른 이름으로 저장…", self.save_as, "Ctrl+Shift+S")
            m.addSeparator()
            self._act(m, "클립보드에서 불러오기", self.paste_from_clipboard)
            m.addSeparator()
            self._act(m, "종료", self.close, "Ctrl+Q")

        m = self.menuBar().addMenu("보기(&V)")
        m.addAction(self.sym_dock.toggleViewAction())
        self.sym_dock.toggleViewAction().setShortcut(QKeySequence("F4"))
        m = self.menuBar().addMenu("편집(&E)")
        self._act(m, "격자로 편집(&G)…", self.edit_grid, "Ctrl+G")
        self._act(m, "미리보기 바로 갱신", self.preview.refresh_now, "F5")
        m.addSeparator()
        self.act_pair = self._act(m, "자동 괄호 짝 (\\left…\\right)", lambda: None)
        self.act_pair.setCheckable(True)
        self.act_pair.setChecked(self.settings.value("auto_pair", False, type=bool))
        self.act_pair.setToolTip("( [ | 를 치면 \\left( \\right) 를 채우고 커서를 가운데에 둔다")
        self.source.auto_pair = self.act_pair.isChecked()
        self.act_pair.toggled.connect(lambda v: setattr(self.source, "auto_pair", v))
        if not self.embedded:
            m.addSeparator()
            cm = m.addMenu("복사")
            self._act(cm, "소스 그대로", lambda: self._copy(None), "Ctrl+Shift+C")
            self._act(cm, "$ … $ 로 감싸서", lambda: self._copy("inline"))
            self._act(cm, "\\[ … \\] 로 감싸서", lambda: self._copy("display"))

        m = self.menuBar().addMenu("삽입(&I)")
        table = {c: (s, d) for c, s, d in COMMANDS}
        for title, cmds in INSERT_MENU:
            sub = m.addMenu(title)
            for c in cmds:
                if c in _EXTRA_SNIPPETS:
                    label, snip = _EXTRA_SNIPPETS[c]
                else:
                    snip, desc = table[c]
                    label = f"{c}    {desc}"
                self._act(sub, label, lambda s=snip: self.source.insert_snippet(s))
        m.addSeparator()
        self._act(m, "행렬·환경 삽입…", self.insert_env, "Ctrl+Shift+M")

    # -- 동작 ------------------------------------------------------------------

    def _request(self, delay=600):
        self.preview.request(self.text(), self.mode.currentData(),
                             self.pre_edit.toPlainText(), delay)

    def _auto_env_mode(self):
        """첫 줄에 \\begin{align*} 같은 수식 환경을 쓰면 모드를 '환경 그대로'로 바꾼다.
        환경 이름이 바뀔 때만 작동하므로, 사용자가 나중에 직접 고른 모드는 유지된다."""
        first = self.source.toPlainText().split("\n", 1)[0]
        m = re.match(r"\s*\\begin\s*\{([A-Za-z]+\*?)\}", first)
        name = m.group(1) if m and m.group(1) in MATH_MODE_ENVS else None
        if name and name != self._first_env:
            i = self.mode.findData("env")
            if i >= 0 and self.mode.currentIndex() != i:
                self.mode.setCurrentIndex(i)      # → _request 가 호출된다
        self._first_env = name

    def _on_changed(self):
        self._auto_env_mode()
        self._dirty = True
        self._update_title()
        self._request()

    def _on_preview_status(self, msg: str, is_err: bool, line: int):
        probs = getattr(self.source, "bracket_problems", 0)
        extra = f"   ⚠ 짝이 안 맞는 괄호 {probs}곳" if probs else ""
        self.msg.setText(("⚠ " if is_err else "") + msg + extra)

    def _update_pos(self):
        c = self.source.textCursor()
        self.pos.setText(f"{c.blockNumber() + 1}:{c.positionInBlock() + 1}")

    def _update_title(self):
        if self.embedded:
            self.setWindowTitle("수식 편집" + (" ●" if self._dirty else ""))
            return
        name = self.path.name if self.path else "(이름 없음)"
        self.setWindowTitle(f"{'● ' if self._dirty else ''}{name} — ndhmdMath {__version__}")

    def edit_grid(self):
        text = self.text()
        pos = self.source.textCursor().position()
        env = env_at(text, pos)
        if env is None:
            self.statusBar().showMessage(
                "커서가 행렬·cases·align 류 환경 안에 있어야 합니다", 4000)
            return
        dlg = GridEditorDialog(text, env, self)
        if dlg.exec() == QDialog.Accepted:
            new = dlg.result_text()
            cur = self.source.textCursor()
            cur.beginEditBlock()
            cur.select(QTextCursor.Document)
            cur.insertText(new)
            cur.endEditBlock()
            c = self.source.textCursor()
            c.setPosition(min(env.start, len(new)))
            self.source.setTextCursor(c)

    def _insert_symbol(self, text: str):
        self.source.insert_snippet(text)
        self.source.setFocus()

    def insert_env(self):
        dlg = NewEnvDialog(self)
        if dlg.exec() == QDialog.Accepted:
            self.source.insert_snippet(dlg.snippet())
            self.source.setFocus()

    def _copy(self, wrap):
        t = self.text().strip()
        if wrap == "inline":
            t = "$" + t + "$"
        elif wrap == "display":
            t = "\\[\n" + t + "\n\\]"
        QGuiApplication.clipboard().setText(t)
        self.statusBar().showMessage("클립보드에 복사했습니다", 2500)

    def paste_from_clipboard(self):
        t = QGuiApplication.clipboard().text()
        if t.strip():
            self.set_text(t)

    def open_file(self):
        if not self._confirm_discard():
            return
        name, _ = QFileDialog.getOpenFileName(self, "열기", str(self.path.parent if self.path else Path.home()),
                                              "수식 파일 (*.tex *.txt *.md);;모든 파일 (*)")
        if name:
            self.path = Path(name)
            self.set_text(self.path.read_text(encoding="utf-8"))

    def save_file(self):
        if self.path is None:
            return self.save_as()
        try:
            self.path.write_text(self.text(), encoding="utf-8")
        except OSError as e:
            QMessageBox.warning(self, "저장", f"저장하지 못했습니다: {e}")
            return False
        self._dirty = False
        self._update_title()
        self.statusBar().showMessage("저장했습니다", 2500)
        return True

    def save_as(self):
        name, _ = QFileDialog.getSaveFileName(self, "다른 이름으로 저장",
                                              str(self.path or Path.home() / "formula.tex"),
                                              "수식 파일 (*.tex *.txt)")
        if not name:
            return False
        self.path = Path(name)
        return self.save_file()

    def _confirm_discard(self) -> bool:
        if not self._dirty:
            return True
        if self.embedded:
            return QMessageBox.question(
                self, "수식 편집", "고친 내용을 버리고 닫을까요?",
                QMessageBox.Discard | QMessageBox.Cancel) == QMessageBox.Discard
        r = QMessageBox.question(self, "ndhmdMath", "저장하지 않은 변경이 있습니다. 저장할까요?",
                                 QMessageBox.Save | QMessageBox.Discard | QMessageBox.Cancel)
        if r == QMessageBox.Save:
            return bool(self.save_file())
        return r == QMessageBox.Discard

    def commit(self):
        """본문에 넣기: 결과를 알리고 창을 닫는다(변경 확인 없이)."""
        if not self.text().strip():
            self.statusBar().showMessage("비어 있는 수식은 넣을 수 없습니다", 3000)
            return
        self._committed = True
        self.committed.emit(self.text().strip("\n"), self.mode.currentData())
        self.close()

    def exec_modal(self) -> bool:
        """창을 모달로 띄우고 닫힐 때까지 기다린다. 넣었으면 True."""
        from PySide6.QtCore import QEventLoop
        self.setWindowModality(Qt.ApplicationModal)
        loop = QEventLoop(self)
        self.finished.connect(loop.quit)
        self.show()
        self.source.setFocus()
        loop.exec()
        return self._committed

    def keyPressEvent(self, event):
        if self.embedded and event.key() == Qt.Key_Escape:
            self.close()
            return
        super().keyPressEvent(event)

    def closeEvent(self, event):
        if not self._committed and not self._confirm_discard():
            event.ignore()
            return
        self.settings.setValue("geometry", self.saveGeometry())
        if not self.embedded:
            self.settings.setValue("mode", self.mode.currentData())
        self.settings.setValue("zoom", self.zoom.currentData())
        if not self.embedded:
            self.settings.setValue("preamble", self.pre_edit.toPlainText())
        self.settings.setValue("symbols", self.sym_dock.isVisible())
        self.settings.setValue("auto_pair", self.act_pair.isChecked())
        self.symbols.shutdown()
        self.preview.shutdown()
        super().closeEvent(event)
        self.finished.emit()



def split_math_delims(src: str):
    """원고의 수식 한 덩어리를 (모양, 여는 말, 닫는 말, 안쪽)으로 가른다.

    모양은 inline | display | env. 환경(\begin{align*}…)은 여는/닫는 말이 없고
    안쪽이 곧 전체다.
    """
    s = src.strip()
    for o, c, kind in (("$$", "$$", "display"), ("\\[", "\\]", "display"),
                       ("\\(", "\\)", "inline"), ("$", "$", "inline")):
        if len(s) >= len(o) + len(c) and s.startswith(o) and s.endswith(c):
            return kind, o, c, s[len(o):-len(c)]
    return "env", "", "", s


def wrap_math(text: str, mode: str, orig=None) -> str:
    """편집한 안쪽(text)을 모양에 맞게 다시 감싼다. 처음과 같은 모양이면
    원래의 구분자와 앞뒤 공백(줄바꿈)을 그대로 쓴다."""
    t = text.strip("\n")
    if mode == "env":
        return t
    if orig is not None:
        kind, o, c, inner = orig
        if kind == mode and o:
            lead = inner[:len(inner) - len(inner.lstrip())]
            trail = inner[len(inner.rstrip()):]
            return o + lead + t.strip() + trail + c
    if mode == "inline":
        return "$" + t.strip() + "$"
    return "$$\n" + t.strip() + "\n$$"

class MathSymbolPanel(QDialog):
    """[도구] ▸ 수식 기호. lshort(라텍 입문서)에 실린 수식 기호 목록을
    훑어 보여준다 — lsksymbols.py 원본의 데이터를 그대로 가져오고,
    비어 있던 유니코드 매핑 113개를 채웠다.

    비모달, 카테고리 콤보 + 검색으로 걸러 본다. "기호" 열을 클릭하면
    유니코드 문자를, "명령어" 열을 클릭하면 LaTeX 명령어 자체를 커서
    위치에 꽂는다(원본은 클립보드에 복사했지만, 이 앱의 다른 패널들과
    같은 방식 — 클릭하면 바로 커서 자리에 들어가는 쪽으로 맞췄다).
    """

    DATA = {
        '수식모드의 액센트': ['\\hat', '\\check', '\\tilde', '\\grave', '\\dot', '\\ddot', '\\bar', '\\vec', '\\widehat', '\\acute', '\\breve', '\\widetilde', '\\mathring'],
        '그리스 문자': ['\\alpha', '\\theta', 'o', '\\upsilon', '\\beta', '\\vartheta', '\\pi', '\\phi', '\\gamma', '\\iota', '\\varpi', '\\varphi', '\\delta', '\\kappa', '\\rho', '\\chi', '\\epsilon', '\\lambda', '\\varrho', '\\psi', '\\varepsilon', '\\mu', '\\sigma', '\\omega', '\\zeta', '\\nu', '\\varsigma', '\\eta', '\\xi', '\\tau', '\\Gamma', '\\Lambda', '\\Sigma', '\\Psi', '\\Delta', '\\Xi', '\\Upsilon', '\\Omega', '\\Theta', '\\Pi', '\\Phi'],
        '이항 관계 연산자': ['<', '>', '=', '\\leq', '\\le', '\\geq', '\\ge', '\\equiv', '\\ll', '\\gg', '\\doteq', '\\prec', '\\succ', '\\sim', '\\preceq', '\\succeq', '\\simeq', '\\subset', '\\supset', '\\approx', '\\subseteq', '\\supseteq', '\\cong', '\\sqsubset', '\\sqsupset', '\\Join', '\\sqsubseteq', '\\sqsupseteq', '\\bowtie', '\\in', '\\ni', '\\owns', '\\propto', '\\vdash', '\\dashv', '\\models', '\\mid', '\\parallel', '\\perp', '\\smile', '\\frown', '\\asymp', ':', '\\notin', '\\neq', '\\ne'],
        '이항 연산자': ['+', '-', '\\pm', '\\mp', '\\triangleleft', '\\cdot', '\\div', '\\triangleright', '\\times', '\\setminus', '\\star', '\\cup', '\\cap', '\\ast', '\\sqcup', '\\sqcap', '\\circ', '\\vee', '\\lor', '\\wedge', '\\land', '\\bullet', '\\oplus', '\\ominus', '\\diamond', '\\odot', '\\oslash', '\\uplus', '\\otimes', '\\bigcirc', '\\amalg', '\\bigtriangleup', '\\bigtriangledown', '\\dagger', '\\lhd', '\\rhd', '\\ddagger', '\\unlhd', '\\unrhd', '\\wr'],
        '큰 연산자': ['\\sum', '\\bigcup', '\\bigvee', '\\prod', '\\bigcap', '\\bigwedge', '\\coprod', '\\bigsqcup', '\\biguplus', '\\int', '\\oint', '\\bigodot', '\\bigoplus', '\\bigotimes'],
        '화살표': ['\\leftarrow', '\\gets', '\\longleftarrow', '\\rightarrow', '\\to', '\\longrightarrow', '\\leftrightarrow', '\\longleftrightarrow', '\\Leftarrow', '\\Longleftarrow', '\\Rightarrow', '\\Longrightarrow', '\\Leftrightarrow', '\\Longleftrightarrow', '\\mapsto', '\\longmapsto', '\\hookleftarrow', '\\hookrightarrow', '\\leftharpoonup', '\\rightharpoonup', '\\leftharpoondown', '\\rightharpoondown', '\\rightleftharpoons', '\\iff', '\\uparrow', '\\downarrow', '\\updownarrow', '\\Uparrow', '\\Downarrow', '\\Updownarrow', '\\nearrow', '\\searrow', '\\swarrow', '\\nwarrow', '\\leadsto'],
        '여닫는 부호': ['(', ')', '\\uparrow', '[', '\\lbrack', ']', '\\rbrack', '\\downarrow', '\\{', '\\lbrace', '\\}', '\\rbrace', '\\updownarrow', '\\langle', '\\rangle', '\\Uparrow', '|', '\\vert', '\\|', '\\Vert', '\\Downarrow', '/', '\\backslash', '\\Updownarrow', '\\lfloor', '\\rfloor', '\\lceil', '\\rceil'],
        '기타 부호': ['\\dots', '\\cdots', '\\vdots', '\\ddots', '\\hbar', '\\imath', '\\jmath', '\\ell', '\\Re', '\\Im', '\\aleph', '\\wp', '\\forall', '\\exists', '\\mho', '\\partial', "'", '\\prime', '\\emptyset', '\\infty', '\\nabla', '\\triangle', '\\Box', '\\Diamond', '\\bot', '\\top', '\\angle', '\\surd', '\\diamondsuit', '\\heartsuit', '\\clubsuit', '\\spadesuit', '\\neg', '\\lnot', '\\flat', '\\natural', '\\sharp'],
        '수학 기호가 아닌 것': ['\\dag', '\\S', '\\copyright', '\\textregistered', '\\ddag', '\\P', '\\pounds', '\\%'],
        'AmS: 기호 모음': ['\\leqslant', '\\geqslant', '\\lesssim', '\\gtrsim', '\\square', '\\blacksquare', '\\lozenge', '\\blacklozenge', '\\bigstar', '\\checkmark', '\\circledR', '\\diagup', '\\diagdown', '\\varnothing', '\\sphericalangle'],
    }
    UNICODE_MAP = {
        '\\alpha': 'α',
        '\\beta': 'β',
        '\\gamma': 'γ',
        '\\delta': 'δ',
        '\\epsilon': 'ε',
        '\\zeta': 'ζ',
        '\\eta': 'η',
        '\\theta': 'θ',
        '\\iota': 'ι',
        '\\kappa': 'κ',
        '\\lambda': 'λ',
        '\\mu': 'μ',
        '\\nu': 'ν',
        '\\xi': 'ξ',
        'o': 'o',
        '\\pi': 'π',
        '\\rho': 'ρ',
        '\\sigma': 'σ',
        '\\tau': 'τ',
        '\\upsilon': 'υ',
        '\\phi': 'ϕ',
        '\\chi': 'χ',
        '\\psi': 'ψ',
        '\\omega': 'ω',
        '\\varepsilon': 'ε',
        '\\vartheta': 'ϑ',
        '\\varpi': 'ϖ',
        '\\varrho': 'ϱ',
        '\\varsigma': 'ς',
        '\\varphi': 'φ',
        '\\Gamma': 'Γ',
        '\\Delta': 'Δ',
        '\\Theta': 'Θ',
        '\\Lambda': 'Λ',
        '\\Xi': 'Ξ',
        '\\Pi': 'Π',
        '\\Sigma': 'Σ',
        '\\Upsilon': 'Υ',
        '\\Phi': 'Φ',
        '\\Psi': 'Ψ',
        '\\Omega': 'Ω',
        '\\leq': '≤',
        '\\le': '≤',
        '\\geq': '≥',
        '\\ge': '≥',
        '\\equiv': '≡',
        '\\ll': '≪',
        '\\gg': '≫',
        '\\subset': '⊂',
        '\\supset': '⊃',
        '\\approx': '≈',
        '\\subseteq': '⊆',
        '\\supseteq': '⊇',
        '\\cong': '≅',
        '\\in': '∈',
        '\\ni': '∋',
        '\\owns': '∋',
        '\\propto': '∝',
        '\\neq': '≠',
        '\\ne': '≠',
        '<': '<',
        '>': '>',
        '=': '=',
        '\\times': '×',
        '\\div': '÷',
        '\\pm': '±',
        '\\mp': '∓',
        '\\cup': '∪',
        '\\cap': '∩',
        '+': '+',
        '-': '-',
        '\\cdot': '⋅',
        '\\ast': '∗',
        '\\circ': '∘',
        '\\oplus': '⊕',
        '\\otimes': '⊗',
        '\\sum': '∑',
        '\\prod': '∏',
        '\\int': '∫',
        '\\oint': '∮',
        '\\bigcup': '⋃',
        '\\bigcap': '⋂',
        '\\leftarrow': '←',
        '\\rightarrow': '→',
        '\\to': '→',
        '\\leftrightarrow': '↔',
        '\\Leftarrow': '⇐',
        '\\Rightarrow': '⇒',
        '\\Leftrightarrow': '⇔',
        '\\mapsto': '↦',
        '\\uparrow': '↑',
        '\\downarrow': '↓',
        '\\updownarrow': '↕',
        '\\Uparrow': '⇑',
        '\\Downarrow': '⇓',
        '\\Updownarrow': '⇕',
        '\\nearrow': '↗',
        '\\searrow': '↘',
        '\\swarrow': '↙',
        '\\nwarrow': '↖',
        '\\dots': '…',
        '\\cdots': '⋯',
        '\\vdots': '⋮',
        '\\ddots': '⋱',
        '\\partial': '∂',
        '\\emptyset': '∅',
        '\\hbar': 'ℏ',
        '\\angle': '∠',
        '\\surd': '√',
        '\\forall': '∀',
        '\\exists': '∃',
        '\\infty': '∞',
        '\\nabla': '∇',
        '\\Diamond': '◇',
        '\\Box': '□',
        '\\triangle': '△',
        '\\diamondsuit': '♢',
        '\\heartsuit': '♡',
        '\\clubsuit': '♣',
        '\\spadesuit': '♠',
        '\\neg': '¬',
        '\\lnot': '¬',
        '\\flat': '♭',
        '\\natural': '♮',
        '\\sharp': '♯',
        '\\dag': '†',
        '\\ddag': '‡',
        '\\S': '§',
        '\\P': '¶',
        '\\copyright': '©',
        '\\textregistered': '®',
        '\\pounds': '£',
        '\\%': '%',
        '(': '(',
        ')': ')',
        '[': '[',
        ']': ']',
        '\\{': '{',
        '\\}': '}',
        '\\lceil': '⌈',
        '\\rceil': '⌉',
        '\\lfloor': '⌊',
        '\\rfloor': '⌋',
        '\\langle': '⟨',
        '\\rangle': '⟩',
        '\\vert': '|',
        '\\|': '‖',
        '\\Vert': '‖',
        '\\leqslant': '⩽',
        '\\geqslant': '⩾',
        '\\lesssim': '≲',
        '\\gtrsim': '≳',
        '\\square': '□',
        '\\blacksquare': '■',
        '\\lozenge': '◊',
        '\\blacklozenge': '♦',
        '\\bigstar': '★',
        '\\varnothing': '∅',
        '\\hat': '̂',
        '\\check': '̌',
        '\\tilde': '̃',
        '\\grave': '̀',
        '\\dot': '̇',
        '\\ddot': '̈',
        '\\bar': '̄',
        '\\vec': '⃗',
        '\\widehat': '̂',
        '\\acute': '́',
        '\\breve': '̆',
        '\\widetilde': '̃',
        '\\mathring': '̊',
        '\\doteq': '≐',
        '\\prec': '≺',
        '\\succ': '≻',
        '\\sim': '∼',
        '\\preceq': '≼',
        '\\succeq': '≽',
        '\\simeq': '≃',
        '\\sqsubset': '⊏',
        '\\sqsupset': '⊐',
        '\\Join': '⨝',
        '\\sqsubseteq': '⊑',
        '\\sqsupseteq': '⊒',
        '\\bowtie': '⋈',
        '\\vdash': '⊢',
        '\\dashv': '⊣',
        '\\models': '⊨',
        '\\mid': '∣',
        '\\parallel': '∥',
        '\\perp': '⊥',
        '\\smile': '⌣',
        '\\frown': '⌢',
        '\\asymp': '≍',
        ':': ':',
        '\\notin': '∉',
        '\\triangleleft': '◁',
        '\\triangleright': '▷',
        '\\setminus': '∖',
        '\\star': '⋆',
        '\\sqcup': '⊔',
        '\\sqcap': '⊓',
        '\\vee': '∨',
        '\\lor': '∨',
        '\\wedge': '∧',
        '\\land': '∧',
        '\\bullet': '∙',
        '\\ominus': '⊖',
        '\\diamond': '⋄',
        '\\odot': '⊙',
        '\\oslash': '⊘',
        '\\uplus': '⊎',
        '\\bigcirc': '◯',
        '\\amalg': '⨿',
        '\\bigtriangleup': '△',
        '\\bigtriangledown': '▽',
        '\\dagger': '†',
        '\\lhd': '⊲',
        '\\rhd': '⊳',
        '\\ddagger': '‡',
        '\\unlhd': '⊴',
        '\\unrhd': '⊵',
        '\\wr': '≀',
        '\\bigvee': '⋁',
        '\\bigwedge': '⋀',
        '\\coprod': '∐',
        '\\bigsqcup': '⨆',
        '\\biguplus': '⨄',
        '\\bigodot': '⨀',
        '\\bigoplus': '⨁',
        '\\bigotimes': '⨂',
        '\\gets': '←',
        '\\longleftarrow': '⟵',
        '\\longrightarrow': '⟶',
        '\\longleftrightarrow': '⟷',
        '\\Longleftarrow': '⟸',
        '\\Longrightarrow': '⟹',
        '\\Longleftrightarrow': '⟺',
        '\\longmapsto': '⟼',
        '\\hookleftarrow': '↩',
        '\\hookrightarrow': '↪',
        '\\leftharpoonup': '↼',
        '\\rightharpoonup': '⇀',
        '\\leftharpoondown': '↽',
        '\\rightharpoondown': '⇁',
        '\\rightleftharpoons': '⇌',
        '\\iff': '⟺',
        '\\leadsto': '⇝',
        '\\lbrack': '[',
        '\\rbrack': ']',
        '\\lbrace': '{',
        '\\rbrace': '}',
        '|': '|',
        '/': '/',
        '\\backslash': '\\',
        '\\imath': 'ı',
        '\\jmath': 'ȷ',
        '\\ell': 'ℓ',
        '\\Re': 'ℜ',
        '\\Im': 'ℑ',
        '\\aleph': 'ℵ',
        '\\wp': '℘',
        '\\mho': '℧',
        "'": '′',
        '\\prime': '′',
        '\\bot': '⊥',
        '\\top': '⊤',
        '\\checkmark': '✓',
        '\\circledR': 'Ⓡ',
        '\\diagup': '╱',
        '\\diagdown': '╲',
        '\\sphericalangle': '∢',
    }

    def __init__(self, window: "MainWindow"):
        super().__init__(window, Qt.Tool)
        self._win = window
        self.setWindowTitle("수식 기호")
        self.resize(650, 550)

        control = QHBoxLayout()
        self.category_combo = QComboBox()
        self.category_combo.addItem("전체 보기")
        self.category_combo.addItems(list(self.DATA.keys()))
        self.category_combo.currentIndexChanged.connect(self._filter)
        control.addWidget(self.category_combo)

        self.search_edit = QLineEdit()
        self.search_edit.setPlaceholderText("검색(예: alpha, sum, ≤)…")
        self.search_edit.textChanged.connect(self._filter)
        control.addWidget(self.search_edit)

        self.table = QTableWidget()
        self.table.setColumnCount(3)
        self.table.setHorizontalHeaderLabels(["기호(클릭=삽입)", "명령어(클릭=삽입)", "카테고리"])
        self.table.horizontalHeader().setSectionResizeMode(0, QHeaderView.ResizeToContents)
        self.table.horizontalHeader().setSectionResizeMode(1, QHeaderView.Stretch)
        self.table.horizontalHeader().setSectionResizeMode(2, QHeaderView.ResizeToContents)
        self.table.setSelectionBehavior(QTableWidget.SelectItems)
        self.table.setEditTriggers(QTableWidget.NoEditTriggers)
        self.table.itemClicked.connect(self._insert_clicked)

        hint = QLabel("기호 열을 클릭하면 유니코드가, 명령어 열을 클릭하면 "
                      "LaTeX 코드가 커서 위치에 들어갑니다.")
        hint.setWordWrap(True)
        hint.setStyleSheet("color: palette(mid); font-size: 11px;")

        box = QVBoxLayout(self)
        box.addLayout(control)
        box.addWidget(self.table, 1)
        box.addWidget(hint)

        self._populate()

    def _populate(self):
        total = sum(len(cmds) for cmds in self.DATA.values())
        self.table.setRowCount(total)
        font_large = QFont()
        font_large.setPointSize(16)
        row = 0
        for category, commands in self.DATA.items():
            for command in commands:
                unicode_char = self.UNICODE_MAP.get(
                    command, command if not command.startswith("\\") else "")
                sym_item = QTableWidgetItem(unicode_char)
                sym_item.setFont(font_large)
                sym_item.setTextAlignment(Qt.AlignCenter)
                cmd_item = QTableWidgetItem(command)
                cat_item = QTableWidgetItem(category)
                self.table.setItem(row, 0, sym_item)
                self.table.setItem(row, 1, cmd_item)
                self.table.setItem(row, 2, cat_item)
                row += 1

    def _filter(self):
        category = self.category_combo.currentText()
        query = self.search_edit.text().strip().lower()
        for row in range(self.table.rowCount()):
            sym_item = self.table.item(row, 0)
            cmd_item = self.table.item(row, 1)
            cat_item = self.table.item(row, 2)
            if not (sym_item and cmd_item and cat_item):
                continue
            cat_ok = category == _T("전체 보기") or cat_item.text() == category
            q_ok = True
            if query:
                q_ok = query in cmd_item.text().lower() or query in sym_item.text()
            self.table.setRowHidden(row, not (cat_ok and q_ok))

    def _insert_clicked(self, item: QTableWidgetItem):
        col = item.column()
        if col == 2 or not item.text():
            return
        self._win.editor.insertPlainText(item.text())
        self._win.activateWindow()
        self._win.editor.setFocus()


class NotePanel(QDialog):
    """문서에 딸린 메모. 비모달 — 메모가 있는 파일을 열면 자동으로 같이
    뜬다. 태그처럼 워크스페이스 사이드카에 저장한다(파일 내용에는 안
    남는다 — 파일을 옮기면 메모는 안 따라간다, 그게 의도다).

    inline 표기 규칙 같은 것, "이번 주까지 끝내야 한다" 같은 것을
    적어 두는 자리다. 타이핑을 멈추면 잠깐 뒤에 조용히 저장된다 —
    따로 저장 버튼을 누를 필요가 없다.
    """

    def __init__(self, window: "MainWindow"):
        super().__init__(window, Qt.Tool)
        self._win = window
        self._current_path = None

        self.text = QTextEdit()
        self.text.setPlaceholderText(
            "이 문서에 대한 메모 — inline 표기 규칙, 마감일 같은 것들")
        self.text.textChanged.connect(self._schedule_save)

        self._save_timer = QTimer(self)
        self._save_timer.setSingleShot(True)
        self._save_timer.setInterval(600)
        self._save_timer.timeout.connect(self._save_now)

        delete_btn = QToolButton()
        delete_btn.setText("🗑")
        delete_btn.setToolTip("이 메모 삭제")
        delete_btn.setAutoRaise(True)
        delete_btn.clicked.connect(self._delete)

        btn_row = QHBoxLayout()
        btn_row.addStretch(1)
        btn_row.addWidget(delete_btn)

        box = QVBoxLayout(self)
        box.addWidget(self.text, 1)
        box.addLayout(btn_row)
        self.resize(320, 200)

        # PySide6 부모 창 기준 왼쪽 아래로 위치 설정
        if self._win:
            # frameGeometry()를 사용하면 윈도우 창 테두리(프레임)를 포함한 정확한 위치를 가져옵니다.
            parent_geo = self._win.frameGeometry()
            x = parent_geo.x() - 10
            y = parent_geo.y() + parent_geo.height() - 210
            self.move(x, y)

        self.load_for_current()
        self.apply_theme(window._theme)

    def apply_theme(self, theme: Theme):
        """편집창(bg)과 구분되도록 panel_bg 를 쓴다 — 다른 패널들과
        같은 자리(테마 전환 시 MainWindow._apply_theme() 가 다시
        불러 준다)."""
        self.setStyleSheet(f"QDialog {{ background: {theme.panel_bg}; }}")
        self.text.setStyleSheet(f"""
            QTextEdit {{
                background: {theme.panel_bg}; color: {theme.fg};
                border: 1px solid {theme.gutter_fg};
            }}
        """)

    def load_for_current(self):
        """지금 편집창에 열려 있는 파일 기준으로 다시 읽는다. 파일을
        전환할 때마다 MainWindow 가 이걸 불러 준다."""
        path = self._win._path
        self._current_path = path
        note = self._win.notes.get(path) if path else ""
        self.text.blockSignals(True)
        self.text.setPlainText(note)
        self.text.blockSignals(False)
        self.setWindowTitle(f"메모 — {path.name}" if path else "메모")

    def _schedule_save(self):
        self._save_timer.start()

    def _save_now(self):
        if self._current_path is None:
            return
        self._win.notes.set(self._current_path, self.text.toPlainText())
        self._win.refresh_drawer()   # 서랍의 메모 표시를 갱신한다

    def _delete(self):
        if self._current_path is None:
            return
        r = QMessageBox.question(
            self, "메모 삭제", "이 문서의 메모를 지울까요?",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if r != QMessageBox.Yes:
            return
        self._save_timer.stop()
        self._win.notes.set(self._current_path, "")
        self.text.blockSignals(True)
        self.text.clear()
        self.text.blockSignals(False)
        self._win.refresh_drawer()
        self.hide()


class CitationPanel(QDialog):
    """bib 인용 삽입. 비모달 — 작업공간의 .bib 파일들을 훑어 citekey(+있으면
    제목)를 보여주고, 클릭하면 그 citekey 자체를 커서 위치에 꽂는다 —
    `[@citekey]` 같은 ndhmd 자체 인용 문법이 있으니, LaTeX cite 명령으로 감싸는
    것까지는 이 패널이 할 일이 아니다.

    BibTeX 편집기를 새로 만들지 않는다 — JabRef 같은 전용 도구가 이미
    훨씬 낫다. 이건 "이 작업공간에 어떤 문헌이 있었더라"를 훑어보고
    바로 인용해 넣기 위한 참조용 창일 뿐이다.

    .bib 이 둘 이상 발견되면 어느 파일을 훑을지 체크박스로 고르게
    한다 — bibtex/biber, biblatex 어느 쪽을 쓰든 이 앱이 알 바 아니고,
    그건 전적으로 LaTeX 쪽에 맡긴다.
    """

    def __init__(self, window: "MainWindow"):
        super().__init__(window, Qt.Tool)
        self._win = window
        self.setWindowTitle("bib 인용 삽입")
        self.resize(360, 460)

        self.file_box = QWidget()
        self.file_box_layout = QVBoxLayout(self.file_box)
        self.file_box_layout.setContentsMargins(0, 0, 0, 0)
        self._file_checks = []   # [(QCheckBox|None, Path), ...]
        self._all_entries = []   # [(citekey, title, author), ...] — 지금 고른 파일들 전부

        self.hint = QLabel()
        self.hint.setWordWrap(True)
        self.hint.setStyleSheet("color: palette(mid); font-size: 11px;")

        #: .bib 하나에 수십~수백 개가 흔해서, 훑어보는 것만으로는 금방
        #: 못 쓰게 된다. citekey·제목·저자 어디에든 걸리면 보여준다.
        self.filter_edit = QLineEdit()
        self.filter_edit.setPlaceholderText("저자·제목·citekey 로 걸러 보기")
        self.filter_edit.setClearButtonEnabled(True)
        self.filter_edit.textChanged.connect(self._apply_filter)

        self.list = QListWidget()
        self.list.itemClicked.connect(self._on_click)

        refresh_btn = QPushButton("새로고침")
        refresh_btn.clicked.connect(self.refresh)

        box = QVBoxLayout(self)
        box.addWidget(self.hint)
        box.addWidget(self.file_box)
        box.addWidget(self.filter_edit)
        box.addWidget(self.list, 1)
        box.addWidget(refresh_btn)

        self.refresh()

    def _bib_files(self) -> list:
        if not self._win.workspace:
            return []
        return [p for p in self._win.workspace.aux_files()
               if p.suffix.lower() == ".bib"]

    def refresh(self):
        """작업공간을 다시 훑는다 — 몇 개가 있는지가 바뀌었을 수 있으니
        파일 선택 체크박스부터 새로 만든다."""
        while self.file_box_layout.count():
            item = self.file_box_layout.takeAt(0)
            if item.widget():
                item.widget().deleteLater()
        self._file_checks = []

        bib_files = self._bib_files()
        if not bib_files:
            self.hint.setText("작업공간에 .bib 파일이 없습니다.")
            self.list.clear()
            return

        if len(bib_files) > 1:
            self.file_box_layout.addWidget(QLabel("훑을 파일:"))
            for p in bib_files:
                cb = QCheckBox(p.name)
                cb.setChecked(True)
                cb.toggled.connect(self._rebuild_list)
                self.file_box_layout.addWidget(cb)
                self._file_checks.append((cb, p))
        else:
            self._file_checks = [(None, bib_files[0])]

        self._rebuild_list()

    def _selected_files(self) -> list:
        if len(self._file_checks) == 1 and self._file_checks[0][0] is None:
            return [self._file_checks[0][1]]
        return [p for cb, p in self._file_checks if cb.isChecked()]

    def _rebuild_list(self):
        """고른 파일들에서 항목을 전부 다시 읽는다. 필터 텍스트가
        바뀔 때마다 파일을 다시 읽을 필요는 없으므로, 필터 적용은
        _apply_filter() 로 따로 뺐다."""
        files = self._selected_files()
        self._all_entries = []
        for p in files:
            try:
                text = read_manuscript(p)
            except (OSError, UnicodeDecodeError):
                continue
            self._all_entries.extend(extract_bib_entries(text))
        self._apply_filter()

    def _apply_filter(self):
        """citekey·제목·저자 중 어디든 필터 글자가 들어 있으면 보여준다
        (대소문자 구분 안 함). 파일을 다시 읽지 않는다 — _all_entries
        에서 걸러 다시 그릴 뿐이다."""
        self.list.clear()
        needle = self.filter_edit.text().strip().lower()
        shown = 0
        for key, title, author in self._all_entries:
            haystack = " ".join(s for s in (key, title, author) if s).lower()
            if needle and needle not in haystack:
                continue
            parts = [key] + [s for s in (author, title) if s]
            it = QListWidgetItem(" — ".join(parts))
            it.setData(Qt.UserRole, key)
            tooltip = key
            if author:
                tooltip += f"\n저자: {author}"
            if title:
                tooltip += f"\n제목: {title}"
            it.setToolTip(tooltip)
            self.list.addItem(it)
            shown += 1

        files = self._selected_files()
        plural = f"{len(files)}개 파일" if len(files) != 1 else (files[0].name if files else "")
        total = len(self._all_entries)
        if needle:
            self.hint.setText(f"{plural}에서 문헌 {total}개 중 {shown}개 표시")
        else:
            self.hint.setText(f"{plural}에서 문헌 {total}개")

    def _on_click(self, item: QListWidgetItem):
        key = item.data(Qt.UserRole)
        self._win.editor.insertPlainText(key)
        self._win.activateWindow()
        self._win.editor.setFocus()


class BibliographyGridDialog(QDialog):
    """[참고문헌] 버튼을 누르면 뜨는 그리드. LyX 의 WYSIWYM 을 참고했다 —
    `:::{thebibliography}` 블록은 편집창에서 버튼 하나로 접혀 있고, 실제
    편집은 여기서 한다.

    citekey·option·author·그밖에 네 열, 행 수 제한 없음. 셀을 클릭하면
    그 칸의 "편집 상태"로 들어간다(QTableWidget 기본 동작 그대로) —
    본문에 삽입하는 것과는 다른 동작이므로, 그건 우클릭 메뉴로 뺐다.

    thebibliography 는 책 전체에 하나 있는 것으로 본다 — 지금 편집
    중인 파일과 다른 장에 있어도(target_path) 상관없다. 우클릭 —
    citekey 삽입은 항상 지금 커서 위치(지금 열려 있는 파일)에 넣는다
    — 그래야 다른 장을 편집하면서도 참조를 걸 수 있다. 반대로 적용
    (저장)은 target_path 쪽에 쓰고, 그게 지금 파일이 아니었으면
    저장 직후 그 자리로 커서를 옮긴다(Alt+Left 로 되돌아올 수 있다).
    """

    COLUMNS = ["citekey", "option", "author", "그밖에"]

    def __init__(self, window: "MainWindow", target_path: Path = None):
        super().__init__(window, Qt.Tool)
        self._win = window
        self.target_path = target_path if target_path is not None else window._path
        self.setWindowTitle("참고문헌 편집")
        self.resize(560, 420)

        self.table = QTableWidget(0, len(self.COLUMNS))
        self.table.setHorizontalHeaderLabels(self.COLUMNS)
        self.table.horizontalHeader().setStretchLastSection(True)
        self.table.setSelectionBehavior(QTableWidget.SelectRows)
        self.table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.table.customContextMenuRequested.connect(self._menu)

        add_btn = QPushButton("행 추가")
        add_btn.clicked.connect(lambda: self._append_row())
        del_btn = QPushButton("선택 행 삭제")
        del_btn.clicked.connect(self.delete_selected_rows)

        delim_label = QLabel("author 구분자:")
        self.delim_combo = QComboBox()
        self.delim_combo.addItem(", (쉼표)", ",")
        self.delim_combo.addItem(". (마침표)", ".")
        idx = self.delim_combo.findData(self._win.prefs.bib_delimiter())
        self.delim_combo.setCurrentIndex(max(0, idx))
        self.delim_combo.currentIndexChanged.connect(self._save_delimiter)

        apply_btn = QPushButton("적용")
        apply_btn.setDefault(True)
        apply_btn.clicked.connect(self.apply_and_close)
        close_btn = QPushButton("닫기")
        close_btn.clicked.connect(self.close)

        btn_row = QHBoxLayout()
        btn_row.addWidget(add_btn)
        btn_row.addWidget(del_btn)
        btn_row.addStretch(1)
        btn_row.addWidget(delim_label)
        btn_row.addWidget(self.delim_combo)
        btn_row.addSpacing(12)
        btn_row.addWidget(apply_btn)
        btn_row.addWidget(close_btn)

        hint = QLabel("우클릭 — 본문 커서 위치에 그 citekey 삽입")
        hint.setStyleSheet("color: palette(mid); font-size: 11px;")

        box = QVBoxLayout(self)
        box.addWidget(self.table, 1)
        box.addWidget(hint)
        box.addLayout(btn_row)

        self._update_title()
        self.load_from_document()

    # -- 문서 <-> 그리드 --------------------------------------------------

    def _update_title(self):
        """target_path 가 지금 열려 있는 파일이 아니면 제목에 그
        파일명을 보여준다 — 안 그러면 어느 장의 참고문헌을 고치는
        중인지 헷갈린다."""
        if self._win.workspace and self.target_path != self._win._path:
            rel = self._win.workspace.relative(self.target_path)
            self.setWindowTitle(f"참고문헌 편집 — {rel}")
        else:
            self.setWindowTitle("참고문헌 편집")

    def set_target(self, target_path: Path):
        """다른 위치(책의 다른 장 등)의 참고문헌으로 바꿔서 다시
        연다."""
        self.target_path = target_path
        self._update_title()
        self.load_from_document()

    def _save_delimiter(self):
        self._win.prefs.write(bib_delimiter=self.delim_combo.currentData())

    def load_from_document(self):
        """target_path 의 :::{thebibliography} 를 다시 읽어 그리드를
        채운다 — 지금 열려 있는 파일이면 편집창에서(저장 전 변경도
        반영해야 하므로), 아니면 디스크에서 직접 읽는다."""
        self.table.setRowCount(0)
        if self.target_path == self._win._path:
            lines = self._win.editor.toPlainText().splitlines()
        else:
            try:
                lines = read_manuscript(self.target_path).splitlines()
            except (OSError, UnicodeDecodeError):
                lines = []
        rng = find_bibliography_range_in_lines(lines)
        if rng is None:
            return
        open_n, close_n = rng
        entry_lines = lines[open_n + 1: close_n]
        delim = self._win.prefs.bib_delimiter()
        for option, key, author, others in parse_bibitem_lines(entry_lines, delim):
            self._append_row(key, option, author, others)

    def _append_row(self, key="", option="", author="", others=""):
        row = self.table.rowCount()
        self.table.insertRow(row)
        for col, val in enumerate((key, option, author, others)):
            self.table.setItem(row, col, QTableWidgetItem(val))

    def delete_selected_rows(self):
        rows = sorted({idx.row() for idx in self.table.selectedIndexes()}, reverse=True)
        for r in rows:
            self.table.removeRow(r)

    # -- 우클릭 — 본문에 삽입 -------------------------------------------------

    def _menu(self, pos):
        item = self.table.itemAt(pos)
        if item is None:
            return
        row = item.row()
        key_item = self.table.item(row, 0)
        key = key_item.text().strip() if key_item else ""
        menu = QMenu(self)
        act = menu.addAction("본문에 citekey 삽입")
        act.setEnabled(bool(key))
        act.triggered.connect(lambda: self._insert_key(key))
        menu.exec(self.table.viewport().mapToGlobal(pos))

    def _insert_key(self, key: str):
        self._win.editor.insertPlainText(f"[@{key}]")
        # 이 창도 별도의 최상위 창이라, 편집창 setFocus() 만으로는 OS
        # 차원의 활성 창이 안 바뀐다.
        self._win.activateWindow()
        self._win.editor.setFocus()

    # -- 적용 -----------------------------------------------------------------

    def _row_values(self):
        def cell(r, c):
            it = self.table.item(r, c)
            return it.text().strip() if it else ""
        rows = []
        for r in range(self.table.rowCount()):
            key = cell(r, 0)
            if not key:
                continue      # citekey 없는 행은 저장하지 않는다
            rows.append((key, cell(r, 1), cell(r, 2), cell(r, 3)))
        return rows

    def _commit_open_editor(self):
        """지금 어느 칸이 "편집 상태"(타이핑 중, 아직 Tab/Enter 로
        확정 안 함)이면 강제로 확정시킨다. 그냥 두면 Qt 의 오래된
        동작 때문에 그 칸에 방금 쓴 내용이 사라진다 — 적용을 누르는
        순간에는 항상 이걸 먼저 부른다.
        """
        editor = self.table.focusWidget()
        if editor is not None and self.table.isAncestorOf(editor):
            self.table.commitData(editor)
            self.table.closeEditor(editor, QAbstractItemDelegate.NoHint)

    def apply_and_close(self):
        self._commit_open_editor()
        rows = self._row_values()

        seen = {}
        for key, *_ in rows:
            seen[key] = seen.get(key, 0) + 1
        dups = sorted(k for k, c in seen.items() if c > 1)
        if dups:
            r = QMessageBox.warning(
                self, "중복된 citekey",
                "다음 citekey가 중복됩니다:\n" + "\n".join(dups) +
                "\n\n그래도 저장할까요?",
                QMessageBox.Yes | QMessageBox.Cancel)
            if r != QMessageBox.Yes:
                return

        self._win.write_bibliography(rows, self.target_path)
        self.close()


class CrossRefCheckDialog(QDialog):
    """컴파일 ▸ 상호참조 점검. 책 전체에서 쓰인 [프리픽스라벨] 참조를
    전부 보여준다 — 죽은 것(\\label이 없는 것)을 붉은 글씨로 먼저,
    그다음 살아 있는 나머지를 보여준다.
    그 아래에 구분선을 긋고 인용([@키] 류)도 같은 방식으로 보여준다(문헌 항목이
    없는 것을 붉게 먼저; 문헌 원본을 못 찾으면 '?' 로만 표시). 라벨 날개([보기] ▸ 라벨 날개)
    가 "이 라벨의 이름이 뭐였더라"를 위한 것이라면, 이건 반대
    방향이다 — "이미 써넣은 참조가 실제로 유효한가"를 확인한다.

    "참조"는 언제나 책 전체가 기본 감시 단위다 — 지금 파일만 보지
    않는다(find_all_references() 의 원칙 그대로다).

    비모달 — 목록을 보며 원고를 계속 고칠 수 있다. 더블클릭(또는 [참조
    위치로])하면 그 참조 자신이 쓰인 자리로, [정의 위치로](우클릭 메뉴에도
    있다)는 라벨이 선언된 자리로 간다.
    """

    def __init__(self, window: "MainWindow", focus=None):
        """focus = (path, 파일 행, prefix, label): 열면서 그 참조 항목을 골라 둔다."""
        super().__init__(window, Qt.Tool)
        self.win = window
        self._focus = focus
        self.setWindowTitle("상호참조 점검")
        self.resize(480, 420)

        self.hint = QLabel()
        self.hint.setWordWrap(True)
        self.hint.setStyleSheet("color: palette(mid); font-size: 11px;")

        refresh_btn = QToolButton()
        refresh_btn.setText("⟳")
        refresh_btn.setToolTip("다시 읽기 — 원고를 고친 뒤 목록을 새로 만든다"
                               "(자동으로 갱신되지는 않는다)")
        refresh_btn.setAutoRaise(True)
        refresh_btn.clicked.connect(self.refresh)

        top_row = QHBoxLayout()
        top_row.addWidget(self.hint, 1)
        top_row.addWidget(refresh_btn, 0, Qt.AlignTop)

        self.list = QListWidget()
        self.list.itemDoubleClicked.connect(self._on_item_double_clicked)
        self.list.setContextMenuPolicy(Qt.CustomContextMenu)
        self.list.customContextMenuRequested.connect(self._menu)
        self.list.currentItemChanged.connect(lambda *_: self._sync_buttons())

        self.ref_btn = QPushButton("참조 위치로")
        self.ref_btn.setToolTip("이 참조가 쓰인 자리로 간다 (더블클릭과 같다)")
        self.ref_btn.clicked.connect(lambda: self._go_ref(self.list.currentItem()))
        self.def_btn = QPushButton("정의 위치로")
        self.def_btn.setToolTip("이 라벨이 선언된 자리로 간다 (죽은 참조는 정의가 없다)")
        self.def_btn.clicked.connect(lambda: self._go_def(self.list.currentItem()))
        btns = QHBoxLayout()
        btns.addWidget(self.ref_btn)
        btns.addWidget(self.def_btn)
        btns.addStretch(1)

        box = QVBoxLayout(self)
        box.addLayout(top_row)
        box.addWidget(self.list, 1)
        box.addLayout(btns)

        # 키보드: Enter = 참조 위치로, Alt+↓/↑ = 같은 라벨의 다음/이전 참조로 이동
        for key in ("Return", "Enter"):
            sc = QShortcut(QKeySequence(key), self.list)
            sc.setContext(Qt.WidgetShortcut)
            sc.activated.connect(lambda: self._go_ref(self.list.currentItem()))
        for key, step in (("Alt+Down", 1), ("Alt+Up", -1)):
            sc = QShortcut(QKeySequence(key), self)
            sc.setContext(Qt.WidgetWithChildrenShortcut)
            sc.activated.connect(lambda st=step: self._step_same_label(st))
        self.ref_btn.setToolTip(self.ref_btn.toolTip() + " · Enter")
        self.list.setToolTip("Enter: 참조 위치로 · Alt+↓/↑: 같은 라벨의 다음/이전 참조")

        self.refresh()
        self._sync_buttons()

    def refresh(self):
        """책 전체의 참조를 다시 훑어 목록과 안내 줄을 새로 채운다.
        열려 있는 동안 원고가 바뀌어도 이 창은 저절로 따라가지 않는다
        — 이 버튼(또는 창을 다시 여는 것)으로만 갱신된다."""
        window = self.win
        refs = find_all_references(window)
        cites, cite_keys, cite_sources, cite_decls = find_all_citations(window)
        dead_count = sum(1 for *_, is_dead in refs if is_dead)
        # 죽은 것 먼저, 그다음 나머지 — 각 그룹 안에서는 책을 훑은
        # 순서(파일 순서 → 그 안의 줄 순서) 그대로 유지한다. sorted()
        # 는 안정 정렬이라 이게 그냥 된다.
        ordered = sorted(refs, key=lambda r: not r[4])
        cite_dead = sum(1 for c in cites if c[4] == "dead")
        cite_order = sorted(cites, key=lambda c: c[4] != "dead")
        theme = window.prefs.resolved_theme()
        warn_color = QColor(theme.warn)

        lines = []
        if refs:
            if dead_count:
                lines.append(
                    f"참조 {len(refs)}개 중 죽은 것 {dead_count}개(붉은 글씨) — "
                    f"\\label이 없는 [프리픽스라벨]입니다.")
            else:
                lines.append(f"참조 {len(refs)}개 — 전부 대응하는 라벨이 있습니다.")
        if cites:
            if not cite_sources:
                lines.append(
                    f"인용 {len(cites)}개 — 참고문헌 원본(:::{{thebibliography}}·.bib)을 찾지 못해 "
                    f"존재 여부는 확인하지 못했습니다.")
            else:
                src = ", ".join(cite_sources)
                if cite_dead:
                    lines.append(f"인용 {len(cites)}개 중 문헌 항목이 없는 것 {cite_dead}개(붉은 글씨) — {src}에서 찾지 못했습니다.")
                else:
                    lines.append(f"인용 {len(cites)}개 — 전부 문헌 항목이 있습니다({src}).")
        if not lines:
            lines.append("책에서 [프리픽스라벨]·[@키] 형태의 참조를 찾지 못했습니다.")
        self.hint.setText("\n".join(lines))

        self.list.clear()

        def add(path, line, prefix, label, is_dead, cite=None, unknown=False):
            rel = window.workspace.relative(path) if window.workspace else str(path)
            mark = "? " if unknown else ""
            it = QListWidgetItem(f"{mark}{ref_display(prefix, label)}   {rel}:{line}")
            it.setData(Qt.UserRole, (str(path), line, label, is_dead))
            it.setData(Qt.UserRole + 1, cite)
            if is_dead:
                it.setForeground(warn_color)
            elif unknown:
                it.setForeground(QColor(theme.marker))
            self.list.addItem(it)
            if self._focus == (path, line, prefix, label) and self.list.currentRow() < 0:
                self.list.setCurrentItem(it)
                self.list.scrollToItem(it, QAbstractItemView.PositionAtCenter)

        for path, line, prefix, label, is_dead in ordered:
            add(path, line, prefix, label, is_dead)

        if cites:
            if refs:
                sep = QListWidgetItem("────────  인용 (cite)  ────────")
                sep.setFlags(Qt.NoItemFlags)
                sep.setTextAlignment(Qt.AlignCenter)
                sep.setForeground(QColor(theme.marker))
                self.list.addItem(sep)
            for path, line, prefix, key, state in cite_order:
                d = cite_keys.get(key)
                loc = (str(d[0]), d[1]) if d else None
                decl = None
                if d and Path(d[0]).suffix.lower() == ".bib":
                    try:
                        dd = cite_decls.get(Path(d[0]).resolve())
                    except OSError:
                        dd = None
                    decl = (str(dd[0]), dd[1]) if dd else None
                add(path, line, prefix, key, state == "dead",
                    cite=("cite", loc, decl), unknown=(state == "unknown"))

    def _on_item_double_clicked(self, item: QListWidgetItem):
        self._go_ref(item)

    def _go_ref(self, item):
        if item is None:
            return
        path_str, line, _label, _dead = item.data(Qt.UserRole)
        self.win.open_at(Path(path_str), line)

    def _go_def(self, item):
        """그 라벨이 선언된 자리로. 책 전체에서 찾는다(라벨 날개의 '정의 위치로
        가기'와 같은 길)."""
        if item is None:
            return
        _path, _line, label, dead = item.data(Qt.UserRole)
        cite = item.data(Qt.UserRole + 1)
        if cite:
            loc = cite[1]
            if loc is None:
                self.win.statusBar().showMessage(
                    f"인용 '{label}' 의 문헌 항목을 찾을 수 없습니다.", 5000)
                return
            self.win.open_at(Path(loc[0]), loc[1])
            if Path(loc[0]).suffix.lower() != ".bib":
                self.win.statusBar().showMessage(
                    f"문헌 항목 '{label}' — 참고문헌 블록입니다(접혀 있으면 📚 참고문헌 줄, "
                    f"Ctrl+Alt+G 로 편집).", 6000)
            return
        if dead:
            self.win.statusBar().showMessage(
                f"라벨 '{label}' 은 선언된 곳이 없습니다(죽은 참조).", 5000)
            return
        self.win.jump_to_label(label)

    def _go_decl(self, item):
        """.bib 에서 찾은 인용 — 그 .bib 를 `\\addbibresource`/`\\bibliography` 로 선언한 줄로."""
        if item is None:
            return
        cite = item.data(Qt.UserRole + 1)
        decl = cite[2] if cite and len(cite) > 2 else None
        if decl is None:
            self.win.statusBar().showMessage(
                "이 .bib 를 선언한 줄(\\addbibresource·\\bibliography)이 원고에 없습니다.", 5000)
            return
        self.win.open_at(Path(decl[0]), decl[1])

    def _step_same_label(self, step: int):
        """지금 고른 항목과 같은 라벨의 다음(1)/이전(-1) 참조를 고르고 그 자리로 간다.
        프리픽스가 달라도([#a] 와 [page:a]) 라벨이 같으면 한 무리다. 끝에서는 돌아 이어진다."""
        cur = self.list.currentRow()
        n = self.list.count()
        if cur < 0 or n == 0:
            return
        cur_item = self.list.item(cur)
        label = cur_item.data(Qt.UserRole)[2]
        kind = bool(cur_item.data(Qt.UserRole + 1))     # 인용끼리, 참조끼리
        same = [i for i in range(n)
                if self.list.item(i).data(Qt.UserRole) is not None
                and self.list.item(i).data(Qt.UserRole)[2] == label
                and bool(self.list.item(i).data(Qt.UserRole + 1)) == kind]
        if len(same) < 2:
            self.win.statusBar().showMessage(
                f"'{label}' 의 참조는 이 하나뿐입니다.", 3000)
            return
        nxt = same[(same.index(cur) + step) % len(same)]
        self.list.setCurrentRow(nxt)
        self._go_ref(self.list.item(nxt))
        # 이동하면 편집창이 포커스를 가져가므로, 연달아 Alt+↓/↑ 를 누를 수 있게
        # 점검 창으로 되돌려 둔다.
        self.activateWindow()
        self.list.setFocus()
        self.win.statusBar().showMessage(
            f"'{label}' 참조 {same.index(nxt) + 1}/{len(same)}", 3000)

    def _sync_buttons(self):
        it = self.list.currentItem()
        self.ref_btn.setEnabled(it is not None)
        if it is None:
            self.def_btn.setEnabled(False)
            return
        cite = it.data(Qt.UserRole + 1)
        self.def_btn.setEnabled(cite[1] is not None if cite
                                else not it.data(Qt.UserRole)[3])

    def _menu(self, pos):
        item = self.list.itemAt(pos)
        if item is None:
            return
        self.list.setCurrentItem(item)
        label, dead = item.data(Qt.UserRole)[2], item.data(Qt.UserRole)[3]
        cite = item.data(Qt.UserRole + 1)
        menu = QMenu(self)
        menu.addAction("참조 위치로 가기", lambda: self._go_ref(item))
        a = menu.addAction("문헌 항목으로 가기" if cite else "정의 위치로 가기",
                           lambda: self._go_def(item))
        a.setEnabled(cite[1] is not None if cite else not dead)
        if cite and cite[1] is not None and Path(cite[1][0]).suffix.lower() == ".bib":
            b = menu.addAction(".bib 선언 줄로 가기", lambda: self._go_decl(item))
            b.setEnabled(cite[2] is not None)
        menu.addSeparator()
        menu.addAction("인용 키 복사" if cite else "라벨 이름 복사",
                       lambda: QApplication.clipboard().setText(label))
        menu.exec(self.list.viewport().mapToGlobal(pos))
        menu.deleteLater()


class ImageCheckDialog(QDialog):
    """컴파일 전 그림 점검. 비모달 — 목록을 보며 원고를 계속 고칠 수 있다.

    로컬 그림은 "문제 있는 것만"이 아니라 책에 선언된 것 전부를 보여
    준다 — 존재 여부와, 찾았으면 작업공간 기준 상대 경로까지 같이
    보여준다. 항목을 더블클릭하면 그 그림이 선언된 소스 행으로 바로
    간다(로컬·원격 둘 다).
    """

    def __init__(self, window: "MainWindow"):
        super().__init__(window, Qt.Tool)
        self.win = window
        self.setWindowTitle("그림 점검")
        self.resize(600, 400)
        self.book_dir = LabelIndex.book_files(window.index, window._path)[0].parent

        remote, local = scan_image_sources(window)
        self.remote = remote
        self.local_paths = {src: window._resolve_image(src) for src in local}
        self.local_locs = local

        self.list = QListWidget()
        self.list.itemDoubleClicked.connect(self._on_item_double_clicked)
        self.remote_items = {}
        self.convert_items = {}

        for url in sorted(remote):
            cached = cached_image(url, self.book_dir) is not None
            it = QListWidgetItem(self._remote_label(url, cached))
            it.setData(Qt.UserRole, url)
            self.list.addItem(it)
            self.remote_items[url] = it

        for src in sorted(local):
            path = self.local_paths[src]
            if path is None:
                it = QListWidgetItem(f"✗ 찾지 못함   {src}")
                it.setData(Qt.UserRole, src)
                self.list.addItem(it)
                continue
            kind = classify_local_image(path)
            it = QListWidgetItem(self._local_label(src, path, kind))
            it.setData(Qt.UserRole, src)
            self.list.addItem(it)
            if kind == "needs_convert":
                self.convert_items[src] = it

        self.summary = QLabel()
        self.fetch_btn = QPushButton("받지 않은 원격 그림 모두 가져오기")
        self.fetch_btn.clicked.connect(self._fetch_missing)
        self.convert_btn = QPushButton("변환 필요한 그림 모두 변환하기")
        self.convert_btn.clicked.connect(self._convert_needed)
        close_btn = QPushButton("닫기")
        close_btn.clicked.connect(self.close)

        row = QHBoxLayout()
        row.addWidget(self.fetch_btn)
        row.addWidget(self.convert_btn)
        row.addStretch(1)
        row.addWidget(close_btn)

        box = QVBoxLayout(self)
        box.addWidget(self.summary)
        box.addWidget(self.list, 1)
        box.addLayout(row)

        self._signals = FetchSignals()
        self._signals.done.connect(self._on_fetch_done)
        self._pool = QThreadPool(self)
        self._pool.setMaxThreadCount(3)
        self._req_url = {}
        self._req_id = 0
        self._fetch_total = self._fetch_done_count = 0

        self._update_buttons()

    # -- 표시 ---------------------------------------------------------------

    def _remote_label(self, url: str, cached: bool) -> str:
        n = len(self.remote[url])
        mark = "✓ 캐시됨" if cached else "○ 받지 않음"
        return f"{mark}   {url}   ({n}곳)"

    def _local_label(self, src: str, path: Path, kind: str) -> str:
        n = len(self.local_locs[src])
        rel = self.win.workspace.relative(path) if self.win.workspace else str(path)
        if kind == "ready":
            return f"✓ 준비됨   {src}   [{rel}]   ({n}곳)"
        if kind == "needs_convert":
            return f"△ 변환 필요   {src}   [{rel}]   →  {path.stem}{path.suffix.replace('.', '-')}.png   ({n}곳)"
        if kind == "handoff":
            return f"✗ LaTeX이 못 받는 형식   {src}   [{rel}]   ({n}곳)"
        return f"? 확인 필요   {src}   [{rel}]   ({n}곳)"

    def _on_item_double_clicked(self, item: QListWidgetItem):
        """이 그림이 선언된 소스 위치로 간다. 한 그림이 여러 곳에서
        쓰였으면 그중 첫 번째로 간다."""
        src = item.data(Qt.UserRole)
        if src is None:
            return
        locs = self.local_locs.get(src) or self.remote.get(src)
        if not locs:
            return
        path, line = locs[0]
        self.win.open_at(path, line)

    def _missing_urls(self):
        return [u for u in self.remote if cached_image(u, self.book_dir) is None]

    def _update_buttons(self):
        missing = self._missing_urls()
        self.fetch_btn.setEnabled(bool(missing))
        if not self.remote:
            self.fetch_btn.setText("원격 그림 없음")
        elif not missing:
            self.fetch_btn.setText("모두 받아 두었습니다")
        else:
            self.fetch_btn.setText(f"받지 않은 원격 그림 모두 가져오기 ({len(missing)}개)")

        if not self.convert_items:
            self.convert_btn.setEnabled(False)
            self.convert_btn.setText("변환 필요한 그림 없음")
        elif not pillow_available():
            self.convert_btn.setEnabled(False)
            self.convert_btn.setText("Pillow 없음 — pip install Pillow")
            self.convert_btn.setToolTip(
                "webp/tiff/gif 를 png 로 바꾸려면 Pillow 가 필요합니다.\n"
                "ndhmd4tex 컴파일도 같은 이유로 Pillow 를 요구합니다.")
        else:
            self.convert_btn.setEnabled(True)
            self.convert_btn.setText(f"변환 필요한 그림 모두 변환하기 ({len(self.convert_items)}개)")

        ready = len(self.remote) - len(missing) + sum(
            1 for src in self.local_paths.values()
            if src is not None and classify_local_image(src) == "ready")
        total = len(self.remote) + len(self.local_paths)
        self.summary.setText(
            f"그림 {total}개 중 컴파일 준비됨 {ready}개"
            f"{'' if not missing else f' · 원격 미수신 {len(missing)}개'}"
            f"{'' if not self.convert_items else f' · 변환 필요 {len(self.convert_items)}개'}")

    # -- 원격 가져오기 -----------------------------------------------------------

    def _fetch_missing(self):
        pending = self._missing_urls()
        if not pending:
            return
        self.fetch_btn.setEnabled(False)
        self._fetch_total, self._fetch_done_count = len(pending), 0
        self.fetch_btn.setText(f"받는 중… (0/{self._fetch_total})")
        for url in pending:
            self._req_id += 1
            self._req_url[self._req_id] = url
            self._pool.start(FetchTask(self._req_id, url, self.book_dir, self._signals))

    @Slot(int, str, str, str)
    def _on_fetch_done(self, req_id: int, url: str, status: str, payload: str):
        if req_id not in self._req_url:
            return
        del self._req_url[req_id]
        item = self.remote_items.get(url)
        if item is not None:
            if status == "ok":
                item.setText(self._remote_label(url, True))
            else:
                item.setText(f"✗ 실패   {url}   — {payload.splitlines()[0]}")
        self._fetch_done_count += 1
        if self._fetch_done_count < self._fetch_total:
            self.fetch_btn.setText(f"받는 중… ({self._fetch_done_count}/{self._fetch_total})")
        else:
            self._update_buttons()
            self.win._preview_key = None
            self.win._schedule_preview()

    # -- 로컬 변환 ---------------------------------------------------------------

    def _convert_needed(self):
        if not pillow_available():
            return                      # 버튼이 이미 비활성이니 정상적으론 안 옴
        failed = []
        for src, item in list(self.convert_items.items()):
            path = self.local_paths[src]
            try:
                convert_local_image(path)
                item.setText(self._local_label(src, path, classify_local_image(path)))
                del self.convert_items[src]
            except Exception as e:
                failed.append(f"{src}: {e}")
        self._update_buttons()
        if failed:
            QMessageBox.warning(self, "일부 변환 실패", "\n".join(failed[:8]))
        self.win._preview_key = None
        self.win._schedule_preview()


# ===========================================================================
#: 한자 변환 사전(hanja.txt)의 저작권 표시와 BSD 조건. 이진 배포에는 문서에 이 문구를 다시 실어야 한다.
HANJA_DICT_NOTICE = (
    "한자 변환 사전: libhangul 의 hanja.txt, 기호 사전 mssymbol.txt (BSD 라이선스)",
    'Copyright (c) 2005,2006 Choe Hwanjin (hanja.txt) / Copyright (c) 2005-2014 Choe Hwanjin (mssymbol.txt). All rights reserved.',
    'Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:',
    '1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer. 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution. 3. Neither the name of the author nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.',
    'THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.',
)

# 9-o. 도움말
# ===========================================================================

APP_AUTHOR = "Nova de Hi"
APP_LICENSE = "MIT"

#: (분류, [(동작, 단축키), ...])
SHORTCUT_GROUPS = (
    ("파일", (
        ("작업공간 열기", "Ctrl+Shift+O"),
        ("새 원고", "Ctrl+N"),
        ("열기", "Ctrl+O"),
        ("저장 / 다른 이름으로 저장", "Ctrl+S / Ctrl+Shift+S"),
        ("이 파일 다시 읽기 / 서랍 다시 읽기", "F5 / Ctrl+Shift+R"),
    )),
    ("편집", (
        ("실행 취소 / 다시 실행", "Ctrl+Z / Ctrl+Y"),
        ("찾기 / 바꾸기", "Ctrl+F / Ctrl+H (macOS는 메뉴로만)"),
        ("작업공간에서 찾기", "Ctrl+Shift+F"),
        ("목록 · 코드펜스 · 인용문 · 환경으로 감싸기 / 풀기", "Ctrl+Alt+L/N/K/Q/E / Ctrl+Alt+U"),
        ("선택한 줄 통째로 들여쓰기 / 내어쓰기(리스트 안 가림)", "Ctrl+] / Ctrl+["),
        ("문단 재배열", "Ctrl+Alt+R"),
        ("장/절 표제 수준 증가 / 감소(선택이 있으면 선택 범위, 없으면 현재 행)", "Ctrl+Alt+] / Ctrl+Alt+["),
        ("인터넷 주소 열기 — [글자](URL)·[글자][표지]·맨 주소(그림은 제외)", "Ctrl+클릭"),
        ("이전 위치로 / 다음 위치로", "Alt+←  /  Alt+→"),
    )),
    ("보기", (
        ("서랍 / 라벨 날개 / TOC / 미리보기",
         "Ctrl+B / Ctrl+Shift+L / Ctrl+Shift+C / Ctrl+Shift+P"),
        ("프론트매터 접기", "Ctrl+Shift+Y"),
        ("코드 펜스·`:::{환경}` 접기/펴기(커서 위치)", "Ctrl+Alt+Shift+H"),
        ("전체화면", "F11"),
    )),
    ("도구", (
        ("보조 입력(라틴 확장·문장부호·IPA)", "Ctrl+Alt+A"),
        ("수식 기호(lshort 기호 모음)", "Ctrl+Alt+S"),
        ("수식 편집기(커서가 수식 위면 고치고, 아니면 새로 넣는다)", "Ctrl+M"),
        ("색상 팔레트(xcolor 기본·SVG·Nine Colors)", "Ctrl+Alt+D"),
        ("커서 위치 코드포인트 보기", "Ctrl+Alt+P"),
        ("메모(문서에 딸린 것 — 서랍의 📝 를 눌러도 열린다)", "Ctrl+Alt+M"),
        ("약어 슬롯 편집 / 슬롯 입력(1~5 전역, 6~0 현재 책)", "Ctrl+Alt+Y / Alt+1~0 (맥: Control+1~0)"),
        ("카드 보기(원고별 시놉시스 카드)", "Ctrl+Alt+V"),
        ("모든 카드 보기(작업공간 전체)", "Ctrl+Alt+Shift+V"),
        ("참조 ↔ 정의로 가기 (각주·[#라벨]·[@키]·그림 이름; Ctrl+클릭도 같다) / 같은 키의 다음 참조", "Ctrl+Alt+O / Ctrl+Alt+Shift+O"),
        ("주변 창 모두 닫기 (메인 창은 닫히지 않는다)", "Ctrl+W"),
        ("그림 들여오기", "Ctrl+Alt+I"),
        ("간단 표 편집기", "Ctrl+Shift+E"),
        ("조각 그림 만들기 / 커서 줄의 조각 그림 편집", "Ctrl+Alt+J / Ctrl+Alt+Shift+J"),
        ("bib 인용 삽입", "Ctrl+Alt+C"),
        ("참고문헌 편집(버튼 클릭도 가능)", "Ctrl+Alt+G"),
    )),
    ("컴파일", (
        ("마크업 점검", "Ctrl+Shift+K"),
        ("그림 점검", "Ctrl+Shift+U"),
        ("상호참조 점검(죽은 \\ref 찾기)", "Ctrl+Shift+X"),
        ("책 컴파일 / 이 파일만 컴파일", "Ctrl+Shift+B / Ctrl+Alt+B"),
        ("변환후 tex 열기 / 결과 tex 열기", "Ctrl+Alt+T / Ctrl+Shift+T"),
        ("PDF에서 이 위치 보기", "Ctrl+Alt+F"),
        ("작업공간 청소", "(메뉴에서)"),
    )),
    ("설정", (
        ("환경설정", "Ctrl+,"),
        ("테마 전환", "Ctrl+Shift+D"),
    )),
    ("도움말", (
        ("ndhmdWriter 정보 / 단축키", "F1"),
        ("Reference Manual", "(메뉴에서)"),
        ("ndhmarkdown 사양서 / 치트시트", "(메뉴에서)"),
    )),
)


class HelpDialog(QDialog):
    """F1. 비모달 — 단축키를 보면서 그대로 눌러볼 수 있어야 뜻이 있다."""

    def __init__(self, window: "MainWindow"):
        super().__init__(window, Qt.Tool)
        self.setWindowTitle("ndhmdWriter 도움말")
        self.resize(480, 560)

        rows = []
        for group, items in SHORTCUT_GROUPS:
            rows.append(f'<tr><td colspan="2" style="padding-top:10px">'
                       f'<b>{group}</b></td></tr>')
            for action, keys in items:
                rows.append(
                    f'<tr><td style="padding:2px 12px 2px 0">{action}</td>'
                    f'<td style="padding:2px 0; color:#7a7368"><code>{keys}</code></td></tr>')

        html = f"""
        <h2 style="margin-bottom:2px">ndhmdWriter</h2>
        <div style="color:#7a7368">버전 {__version__}</div>
        <div style="color:#7a7368; font-size:11px">Powered by ndhmd4tex 0.20.0, ndhmdsync 0.5.6, ksruncltex and TeXLive 2026</div>
        <p>
        지은이: {APP_AUTHOR}<br>
        라이선스: {APP_LICENSE}
        </p>
        <p style="color:#7a7368; font-size:11px">
        MIT 라이선스로 배포하기 위해 PySide6를 사용했습니다.
        </p>
        <p style="color:#7a7368; font-size:11px">
        한자 변환 사전은 <b>libhangul</b>의 <code>hanja.txt</code>(Copyright (c) 2005, 2006 Choe Hwanjin)와
        기호 사전 <code>mssymbol.txt</code>(Copyright (c) 2005-2014 Choe Hwanjin)입니다.
        All rights reserved. (BSD 라이선스)
        </p>
        <div style="color:#7a7368; font-size:10px">
        {"".join("<p>%s</p>" % _html.escape(t) for t in HANJA_DICT_NOTICE[1:])}
        </div>
        <p style="font-size:11px">
        PDF 뷰어와 오가는 동기화(정방향·역방향 검색)를 쓰려면, 환경설정의
        "PDF 뷰어 역방향 검색" 행에서 <b>지금 등록</b> 버튼을 한 번 눌러
        두십시오. 정방향 검색은 컴파일 메뉴나 편집창 우클릭 메뉴의
        "PDF에서 이 위치 보기"(<code>Ctrl+Alt+F</code>)로 부릅니다.
        </p>
        <h3>단축키 요약</h3>
        <table cellspacing="0">{"".join(rows)}</table>
        """

        view = QTextEdit()
        view.setReadOnly(True)
        view.setHtml(html)

        box = QVBoxLayout(self)
        box.addWidget(view, 1)
        close_btn = QPushButton("닫기")
        close_btn.clicked.connect(self.close)
        box.addWidget(close_btn, 0, Qt.AlignRight)

_TBLR_RE = re.compile(r"\\begin\{tblr\}\{[^\n]*\}\s*\n(.*?)\\end\{tblr\}", re.DOTALL)
_TBL_RULE_RE = re.compile(r"\\(?:toprule|midrule|bottomrule)\b")
_UNESC_PIPE_RE = re.compile(r"(?<!\\)\|")
_UNESC_AMP_RE = re.compile(r"(?<!\\)&")


def markdown_cells_to_tex(tool, rows: list, workdir: Path, frontmatter: str = ""):
    """표 셀 안의 마크다운을 ndhmd4tex 가 실제 변환하는 그대로 LaTeX 로 바꾼다.

    ndhmd4tex 는 파이프 표를 언제나 `\\begin{tblr}` 로 내고 한 행을 한 줄에,
    셀을 ` & `, 행 끝을 `\\\\` 로 가른다(& 는 \\& 로 이스케이프된다). 그래서
    파이프 표를 임시 .md 로 써서 변환시킨 뒤 셀 내용만 되읽는다 — 표의 껍데기
    (tblr, \\toprule …)는 버리고 셀만 쓴다. 직접 변환 함수를 두면 ndhmd4tex
    의 인라인 규칙이 바뀔 때마다 어긋나므로 진짜 변환기를 부른다.

    frontmatter 를 같이 쓰는 것은 setup:/mappingrule: 이 이스케이프 규칙에
    영향을 주기 때문이다. 임시 파일은 workdir(현재 파일이 있는 폴더) 안에
    만든다 — setup: 의 상대 경로가 거기서 풀리기 때문이다.

    (변환된 셀 목록, "") 또는 (None, 오류 메시지) 를 돌려준다.
    """
    if not rows:
        return rows, ""
    ncol = len(rows[0])
    def esc(cell):
        return _UNESC_PIPE_RE.sub(r"\\|", cell.replace("\n", " "))
    lines = []
    if frontmatter.strip():
        lines += ["---", frontmatter.strip("\n"), "---", ""]
    else:
        lines += ["---", "title: t", "---", ""]
    lines.append("| " + " | ".join(esc(c) for c in rows[0]) + " |")
    lines.append("|" + "|".join(["---"] * ncol) + "|")
    for row in rows[1:]:
        cells = (list(row) + [""] * ncol)[:ncol]
        lines.append("| " + " | ".join(esc(c) for c in cells) + " |")
    stem = f".ndhmd_table_{os.getpid()}"
    md = Path(workdir) / (stem + ".md")
    tex = Path(workdir) / (stem + ".tex")
    cmd = tool.command(["-o", tex.name, md.name]) if tool else None
    if cmd is None:
        return None, "ndhmd4tex 를 찾지 못했습니다."
    try:
        md.write_text("\n".join(lines) + "\n", encoding="utf-8")
        run = subprocess.run(cmd, cwd=workdir, capture_output=True, timeout=60,
                             creationflags=_NO_WINDOW)
        if run.returncode != 0 or not tex.is_file():
            out = decode_subprocess_output(run.stdout + run.stderr).strip()
            return None, "ndhmd4tex 가 표를 변환하지 못했습니다.\n" + out[-600:]
        text = tex.read_text(encoding="utf-8", errors="replace")
    except (OSError, subprocess.SubprocessError) as e:
        return None, f"ndhmd4tex 를 실행하지 못했습니다: {e}"
    finally:
        for f in (md, tex):
            try:
                f.unlink()
            except OSError:
                pass
    m = _TBLR_RE.search(text)
    if m is None:
        return None, "변환 결과에서 표(tblr)를 찾지 못했습니다. ndhmd4tex 의 출력 형식이 달라졌을 수 있습니다."
    body = _TBL_RULE_RE.sub("", m.group(1))
    out_rows = []
    for chunk in body.split("\\\\"):
        chunk = chunk.strip()
        if not chunk:
            continue
        out_rows.append([c.strip() for c in _UNESC_AMP_RE.split(chunk)])
    if len(out_rows) != len(rows) or any(len(r) != ncol for r in out_rows):
        return None, ("변환 결과의 행·열 수가 원래 표와 맞지 않습니다. "
                      "셀 안에 표를 깨뜨리는 내용이 있는지 확인해 주세요.")
    return out_rows, ""


class _CellEdit(QLineEdit):
    """간단 표 편집기의 데이터 칸. 칸마다 **항상 떠 있는** 줄 편집기이다.

    QTableWidget 의 기본 편집(칸을 고르고 글자를 치면 그때 편집기를 만들었다가 확정하면 지운다)은
    한글 입력(조합 중인 글자)과 맞물릴 때 맥에서 앱이 죽는다는 보고가 있었다 — 입력기가 조합을 이어 가는
    도중에 편집기가 생겼다 사라지는 것이 의심스럽다. 그래서 편집기를 만들고 지우는 일 자체를 없앴다.
    Enter/↓ 는 아래 칸, ↑ 는 위 칸, Tab/Shift+Tab 은 오른쪽/왼쪽 칸으로 옮긴다(조합 중일 때는
    입력기가 키를 먼저 받으므로 이 처리에 오지 않는다)."""

    move = Signal(int, int)           # (행 이동, 열 이동)
    paste_grid = Signal(str)          # 여러 칸짜리(탭·줄바꿈이 든) 붙여넣기 — 표로 붙인다

    def keyPressEvent(self, e):
        k = e.key()
        if e.matches(QKeySequence.Paste):
            text = QGuiApplication.clipboard().text()
            if "\t" in text or "\n" in text.strip("\r\n"):
                self.paste_grid.emit(text)
                return
        if k in (Qt.Key_Return, Qt.Key_Enter, Qt.Key_Down):
            self.move.emit(1, 0)
        elif k == Qt.Key_Up:
            self.move.emit(-1, 0)
        else:
            super().keyPressEvent(e)

    def focusNextPrevChild(self, nxt):
        self.move.emit(0, 1 if nxt else -1)
        return True


class TableEditorDialog(QDialog):
    """간단 표 편집기. 
    첫 행은 정렬(l, c, r)을 선택하는 콤보박스로 고정하고, 2행부터 실제 데이터를 입력합니다."""

    def __init__(self, window: "MainWindow"):
        super().__init__(window, Qt.Tool)
        self._win = window
        self.setWindowTitle("간단 표 편집기")
        self.resize(500, 400)

        # -- 옵션 영역 --
        opt_layout = QHBoxLayout()
        
        self.radio_md = QRadioButton("마크다운 표 (파이프)")
        self.radio_grid = QRadioButton("마크다운 표 (grid)")
        self.radio_grid.setToolTip(
            "pandoc 식 grid 표: +---+ 테두리와 | 로 그린 표. 머리글은 첫 행(아래에 +===+).\n"
            "칸 너비는 전각 글자를 2칸으로 세어 맞춥니다. 병합 셀·바닥글은 이 편집기로 못 만듭니다.")
        self.radio_tex = QRadioButton("LaTeX (tabular)")
        self.radio_md.setChecked(True)
        
        self.chk_convert = QCheckBox("셀의 마크다운을 LaTeX로 변환")
        self.chk_convert.setChecked(True)
        self.chk_convert.setToolTip(
            "LaTeX(tabular/tabularx)로 낼 때, 셀 안의 `코드`·**굵게**·*기울임*·"
            "[#라벨] 같은 마크다운과 _ % $ 같은 특수문자를 ndhmd4tex 가 변환하는 "
            "그대로 LaTeX 로 바꿉니다. 이미 LaTeX 로 쓴 셀이면 끄십시오.")

        self.spin_rows = QSpinBox()
        self.spin_rows.setRange(1, 50)
        self.spin_rows.setValue(3) # 데이터 행 3개 + 정렬 행 1개
        self.spin_rows.setPrefix("행: ")
        
        self.spin_cols = QSpinBox()
        self.spin_cols.setRange(1, 20)
        self.spin_cols.setValue(3)
        self.spin_cols.setPrefix("열: ")

        opt_layout.addWidget(self.radio_md)
        opt_layout.addWidget(self.radio_grid)
        opt_layout.addWidget(self.radio_tex)
        opt_layout.addWidget(self.chk_convert)
        opt_layout.addStretch(1)
        opt_layout.addWidget(self.spin_rows)
        opt_layout.addWidget(self.spin_cols)

        # -- 그리드(표) 영역 --
        self.table = QTableWidget()
        self.table.setSelectionBehavior(QTableWidget.SelectItems)
        self.table.setEditTriggers(QAbstractItemView.NoEditTriggers)   # 칸 편집은 _CellEdit 이 맡는다

        # 행/열 변경 이벤트 연결
        self.spin_rows.valueChanged.connect(self._rebuild_grid)
        self.spin_cols.valueChanged.connect(self._rebuild_grid)

        # -- 하단 버튼 --
        btn_layout = QHBoxLayout()
        paste_btn = QPushButton("클립보드의 표 붙이기")
        paste_btn.setToolTip(
            "엑셀·스프레드시트·TSV(탭으로 나뉜 글)를 복사해 둔 것을 표 전체로 가져옵니다.\n"
            "지금 표의 내용은 대체됩니다. 칸 안에서 Ctrl+V 를 누르면 그 칸부터 채웁니다.")
        paste_btn.clicked.connect(self._paste_whole)
        insert_btn = QPushButton("본문에 삽입")
        insert_btn.setDefault(True)
        insert_btn.clicked.connect(self._insert_table)
        cancel_btn = QPushButton("취소")
        cancel_btn.clicked.connect(self.close)
        
        btn_layout.addWidget(paste_btn)
        btn_layout.addStretch(1)
        btn_layout.addWidget(insert_btn)
        btn_layout.addWidget(cancel_btn)

        # -- 메인 레이아웃 --
        main_layout = QVBoxLayout(self)
        main_layout.addLayout(opt_layout)
        main_layout.addWidget(QLabel("첫 번째 행은 열의 정렬(l, c, r)을 지정합니다. 두 번째 행부터 제목과 내용을 입력하세요."))
        main_layout.addWidget(self.table, 1)
        main_layout.addLayout(btn_layout)

        self._rebuild_grid()

    def _commit_open_editor(self):
        """지금 어느 칸이 "편집 상태"(타이핑 중, 아직 Tab/Enter 로
        확정 안 함)이면 강제로 확정시킨다."""
        editor = self.table.focusWidget()
        if editor is not None and self.table.isAncestorOf(editor):
            self.table.commitData(editor)
            self.table.closeEditor(editor, QAbstractItemDelegate.NoHint)

    def _rebuild_grid(self):
        """행/열 개수에 맞춰 표를 다시 그립니다."""
        data_rows = self.spin_rows.value()
        total_rows = data_rows + 1  # 1행(인덱스 0)은 정렬 선택용이므로 실제 그릴 행은 +1
        cols = self.spin_cols.value()
        
        # 기존 데이터를 보존하면서 크기만 변경
        self.table.setRowCount(total_rows)
        self.table.setColumnCount(cols)
        
        # 세로 헤더(행 번호) 지정: 첫 행은 '정렬', 둘째 행(데이터 1행)부터 1, 2, 3...
        v_labels = ["정렬"] + [str(i) for i in range(1, total_rows)]
        self.table.setVerticalHeaderLabels(v_labels)
        
        # 첫 번째 행은 항상 정렬 선택 콤보박스로 설정
        for col in range(cols):
            # 셀 위젯이 없을 때만 콤보박스를 생성 (사용자의 기존 선택 유지)
            if not isinstance(self.table.cellWidget(0, col), QComboBox):
                combo = QComboBox()
                combo.addItems(["c (가운데)", "l (왼쪽)", "r (오른쪽)", "X (비례)"])
                self.table.setCellWidget(0, col, combo)
            
            # 가로 헤더 이름 변경
            item = QTableWidgetItem(f"열 {col+1}")
            self.table.setHorizontalHeaderItem(col, item)

        # 데이터 칸마다 줄 편집기를 상시 둔다(_CellEdit 참고). 이미 있는 칸은 그대로 둔다.
        for row in range(1, total_rows):
            for col in range(cols):
                if not isinstance(self.table.cellWidget(row, col), _CellEdit):
                    ed = _CellEdit()
                    ed.setFrame(False)
                    ed.move.connect(lambda dr, dc, w=ed: self._move_from(w, dr, dc))
                    ed.paste_grid.connect(lambda text, w=ed: self._paste_at(w, text))
                    self.table.setCellWidget(row, col, ed)

    @staticmethod
    def parse_tsv(text: str) -> list:
        """탭으로 나뉜 글(엑셀·구글 시트·TSV)을 행×열 목록으로. 따옴표로 감싼 칸 안의 탭·줄바꿈과
        `""` 이스케이프를 지키고(칸 안 줄바꿈은 공백이 된다), 끝의 빈 줄과 빈 꼬리 칸은 버린다."""
        import csv
        import io
        rows = []
        for rec in csv.reader(io.StringIO(text.replace("\r\n", "\n").replace("\r", "\n")), delimiter="\t"):
            rows.append([" ".join(c.split()) for c in rec])
        while rows and not any(rows[-1]):
            rows.pop()
        return rows

    def _fit_grid(self, rows: int, cols: int):
        """데이터 행 rows, 열 cols 가 들어가도록 늘린다(줄이지는 않는다). 한도를 넘으면 잘린 크기를 돌려준다."""
        rows_ok = min(rows, self.spin_rows.maximum())
        cols_ok = min(cols, self.spin_cols.maximum())
        if rows_ok > self.spin_rows.value():
            self.spin_rows.setValue(rows_ok)
        if cols_ok > self.spin_cols.value():
            self.spin_cols.setValue(cols_ok)
        return rows_ok, cols_ok

    def _fill(self, grid: list, r0: int, c0: int):
        """grid(문자열 행렬)를 (r0, c0)(데이터 칸 기준, r0 >= 1)부터 채운다. 표가 모자라면 늘린다."""
        need_r = r0 - 1 + len(grid)
        need_c = c0 + max((len(r) for r in grid), default=0)
        rows_ok, cols_ok = self._fit_grid(need_r, need_c)
        for i, row in enumerate(grid):
            for j, val in enumerate(row):
                r, c = r0 + i, c0 + j
                if r <= rows_ok and c < cols_ok:
                    w = self.table.cellWidget(r, c)
                    if isinstance(w, _CellEdit):
                        w.setText(val)
        cut = []
        if need_r > rows_ok:
            cut.append(f"행 {need_r - rows_ok}개")
        if need_c > cols_ok:
            cut.append(f"열 {need_c - cols_ok}개")
        if cut:
            self._win.statusBar().showMessage(
                "표 크기 한도(행 50·열 20)를 넘어 " + "·".join(cut) + "를 가져오지 못했습니다.", 6000)
        else:
            self._win.statusBar().showMessage(
                f"{len(grid)}행 × {max((len(r) for r in grid), default=0)}열을 붙였습니다.", 3000)

    def _pos_of(self, edit):
        for r in range(1, self.table.rowCount()):
            for c in range(self.table.columnCount()):
                if self.table.cellWidget(r, c) is edit:
                    return r, c
        return None

    def _paste_at(self, edit, text: str):
        """칸 안에서 Ctrl+V: 여러 칸짜리 클립보드를 그 칸부터 채운다(스프레드시트처럼)."""
        pos = self._pos_of(edit)
        grid = self.parse_tsv(text)
        if pos is None or not grid:
            return
        self._fill(grid, pos[0], pos[1])

    def _paste_whole(self):
        """버튼: 클립보드의 표로 지금 내용을 통째로 바꾼다(정렬 선택은 남는 열에 한해 유지)."""
        grid = self.parse_tsv(QGuiApplication.clipboard().text())
        if not grid:
            self._win.statusBar().showMessage("클립보드에 붙일 표 데이터가 없습니다.", 4000)
            return
        for r in range(1, self.table.rowCount()):
            for c in range(self.table.columnCount()):
                w = self.table.cellWidget(r, c)
                if isinstance(w, _CellEdit):
                    w.clear()
        # 크기를 데이터에 맞춘다(늘리기도 줄이기도).
        cols = min(max(len(r) for r in grid), self.spin_cols.maximum())
        rows = min(len(grid), self.spin_rows.maximum())
        self.spin_cols.setValue(max(cols, 1))
        self.spin_rows.setValue(max(rows, 1))
        self._fill(grid, 1, 0)

    def _move_from(self, edit, dr: int, dc: int):
        """줄 편집기 `edit` 가 있는 칸에서 (dr, dc) 만큼 옮긴 칸의 편집기로 포커스를 준다.
        Tab 으로 줄 끝을 넘어가면 다음 줄 첫 칸으로(Shift+Tab 은 반대로). 데이터 칸 밖은 막는다."""
        rows, cols = self.table.rowCount(), self.table.columnCount()
        pos = None
        for r in range(1, rows):
            for c in range(cols):
                if self.table.cellWidget(r, c) is edit:
                    pos = (r, c)
        if pos is None:
            return
        r, c = pos[0] + dr, pos[1] + dc
        if dc and c >= cols:
            r, c = r + 1, 0
        elif dc and c < 0:
            r, c = r - 1, cols - 1
        if not (1 <= r < rows and 0 <= c < cols):
            return
        target = self.table.cellWidget(r, c)
        if target is not None:
            self.table.setCurrentCell(r, c)
            target.setFocus()
            target.selectAll()

    def _insert_table(self):
        # 텍스트 삽입 전, 편집 중인 셀이 있다면 강제로 입력을 확정합니다.
        self._commit_open_editor()

        rows = self.table.rowCount()
        cols = self.table.columnCount()
        
        alignments = [self._get_alignment(c) for c in range(cols)]
        
        # 데이터 행 수집 (1번 행부터)
        data_rows = []
        for r in range(1, rows):
            row_data = [self._get_cell_text(r, c) for c in range(cols)]
            data_rows.append(row_data)

        out_lines = []
        use_tabularx = "X" in alignments
        #: X(비례 너비)는 마크다운 표로는 표현할 방법이 없다 — 마크다운을
        #: 골랐어도 X가 섞여 있으면 LaTeX tabularx 로 낼 수밖에 없다.
        md_like = self.radio_md.isChecked() or self.radio_grid.isChecked()
        forced_latex = use_tabularx and md_like

        if self.radio_grid.isChecked() and not use_tabularx:
            if len(data_rows) < 1:
                return
            out_lines = format_grid_table(alignments, data_rows)
            out_lines.append("")            # 표 끝난 후 빈 줄
        elif self.radio_md.isChecked() and not use_tabularx:
            # 마크다운 표 생성 (정렬을 구분선 줄의 콜론으로 표현)
            if not data_rows:
                return

            # 첫 행은 제목줄로 처리
            header = data_rows[0]
            out_lines.append("| " + " | ".join(header) + " |")
            
            # 구분선(정렬) 생성
            sep_row = []
            for align in alignments:
                if align == 'l': sep_row.append(":---")
                elif align == 'r': sep_row.append("---:")
                else: sep_row.append(":---:") # center
            out_lines.append("|" + "|".join(sep_row) + "|")
            
            # 본문 데이터 추가
            for r in data_rows[1:]:
                out_lines.append("| " + " | ".join(r) + " |")
                
            out_lines.append("") # 표 끝난 후 빈 줄
            
        else:
            # LaTeX (tabular/tabularx) 생성. 정렬자 중 X(비례 너비)가
            # 하나라도 있으면 tabularx 로 바꾼다 — 따로 라디오 버튼을
            # 두지 않고 X 포함 여부만으로 판정한다.
            if self.chk_convert.isChecked() and data_rows:
                converted, err = self._win.convert_table_cells(data_rows)
                if converted is None:
                    QMessageBox.warning(
                        self, "표 변환 실패",
                        err + "\n\n표를 넣지 않았습니다. 셀을 이미 LaTeX 로 썼다면 "
                        "'셀의 마크다운을 LaTeX로 변환'을 끄고 다시 넣으십시오.")
                    return
                data_rows = converted
                if any("\\footnote" in c for r_ in data_rows for c in r_):
                    self._win.statusBar().showMessage(
                        "셀 안의 각주는 tabular 안에서 동작하지 않습니다.", 6000)
            align_str = "|" + "|".join(alignments) + "|"
            if use_tabularx:
                out_lines.append(f"\\begin{{tabularx}}{{\\textwidth}}{{{align_str}}}")
            else:
                out_lines.append(f"\\begin{{tabular}}{{{align_str}}}")
            out_lines.append("\\hline") # 표 맨 처음에 \hline
            
            for r_data in data_rows:
                # 각 행 끝에 \\ 와 \hline 추가
                line = " & ".join(r_data) + " \\\\ \\hline"
                out_lines.append(line)
                
            out_lines.append(f"\\end{{tabularx}}" if use_tabularx else "\\end{tabular}")
            out_lines.append("")

        # 본문에 텍스트 삽입
        result_text = "\n".join(out_lines)
        cursor = self._win.editor.textCursor()
        if cursor.hasSelection():
            # 이미 있는 표를 고치는 경우(표를 선택해 편집기로 보낸 것) — 표 끝에 빈 줄을
            # 새로 끼우지 않는다. 표 바로 아래의 옵션 줄 `{label=…}` 이 떨어져 나가기 때문이다.
            tail = "\n" if cursor.selectedText().endswith("\u2029") else ""
            cursor.insertText(result_text.rstrip("\n") + tail)
        else:
            cursor.insertText(result_text + "\n")

        if forced_latex:
            self._win.statusBar().showMessage(
                "X(비례 너비) 정렬은 마크다운 표로 표현할 수 없어 "
                "LaTeX tabularx로 대신 냈습니다.", 5000)

        self._win.activateWindow()
        self._win.editor.setFocus()
        self.close()

    def _get_alignment(self, col: int) -> str:
        """첫 행의 콤보박스에서 정렬 문자(l, c, r)를 추출합니다."""
        widget = self.table.cellWidget(0, col)
        if isinstance(widget, QComboBox):
            # "c (가운데)" -> "c"
            return widget.currentText()[0]
        return "c"

    def _get_cell_text(self, row: int, col: int) -> str:
        w = self.table.cellWidget(row, col)
        return w.text().strip() if isinstance(w, _CellEdit) else ""

    def load_data(self, format_type: str, alignments: list, rows: list):
        """파싱된 데이터를 에디터 그리드에 로드합니다."""
        if format_type == "markdown":
            self.radio_md.setChecked(True)
        elif format_type == "grid":
            self.radio_grid.setChecked(True)
        else:
            self.radio_tex.setChecked(True)
        #: LaTeX 에서 가져온 셀은 이미 LaTeX 이므로 다시 변환하면 망가진다.
        self.chk_convert.setChecked(format_type in ("markdown", "grid"))

        cols = len(alignments)
        data_row_count = len(rows)

        self.spin_cols.blockSignals(True)
        self.spin_rows.blockSignals(True)

        self.spin_cols.setValue(cols)
        self.spin_rows.setValue(data_row_count)

        self.spin_cols.blockSignals(False)
        self.spin_rows.blockSignals(False)

        self._rebuild_grid()

        # 첫 행(정렬) 콤보박스 설정
        for col, align in enumerate(alignments):
            combo = self.table.cellWidget(0, col)
            if isinstance(combo, QComboBox):
                if align == 'l': combo.setCurrentIndex(1)
                elif align == 'r': combo.setCurrentIndex(2)
                elif align == 'X': combo.setCurrentIndex(3)
                else: combo.setCurrentIndex(0) # c

        # 데이터 행 채우기
        for r_idx, row_data in enumerate(rows):
            for c_idx, val in enumerate(row_data):
                w = self.table.cellWidget(r_idx + 1, c_idx)
                if c_idx < cols and isinstance(w, _CellEdit):
                    w.setText(val)

    @classmethod
    def parse_table_text(cls, text: str):
        """선택된 텍스트를 분석하여 (포맷, 정렬자목록, 데이터행목록)을 반환합니다.
        지원 불가한 경우 (None, None, 에러메시지)를 반환합니다."""
        lines = [line.strip() for line in text.strip().splitlines() if line.strip()]
        # 표 바로 아래의 옵션 줄 `{…}` 는 표 내용이 아니다(표 편집기는 옵션을 다루지 않는다).
        while (len(lines) > 1 and TABLE_OPT_RE.match(lines[-1])
               and (_is_table_row_text(lines[-2]) or GRID_BORDER_RE.match(lines[-2]))):
            lines.pop()
        if not lines:
            return None, None, "선택된 내용이 없습니다."

        # 0. grid 표(`+---+---+`로 시작): 간단한 것만 불러온다.
        if GRID_BORDER_RE.match(lines[0]):
            try:
                aligns, rows = parse_grid_simple(
                    [l.rstrip() for l in text.strip("\n").splitlines() if l.strip()
                     and not TABLE_OPT_RE.match(l.strip())])
            except GridTableError as e:
                return None, None, f"{e}. 더 복잡한 표는 전용 표 편집 프로그램을 이용하셔요"
            return "grid", aligns, rows

        # 1. 마크다운 표 판별 (첫 줄이 | 로 시작하고 끝나며, 둘째 줄이 구분선인 경우)
        if lines[0].startswith('|') and len(lines) > 1 and ('---' in lines[1]):
            try:
                raw_rows = []
                for l in lines:
                    if '---' in l:  # 구분선 행은 데이터에서 제외
                        continue
                    cells = [c.strip() for c in
                             _UNESC_PIPE_RE.split(re.sub(r"^\||(?<!\\)\|$", "", l))]
                    raw_rows.append(cells)
                
                if not raw_rows:
                    return None, None, "유효한 마크다운 표가 아닙니다."
                
                cols = len(raw_rows[0])
                sep_cells = [c.strip() for c in lines[1].strip('|').split('|')]
                alignments = []
                for sc in sep_cells:
                    if sc.startswith(':') and sc.endswith(':'): alignments.append('c')
                    elif sc.endswith(':'): alignments.append('r')
                    else: alignments.append('l')
                
                while len(alignments) < cols: alignments.append('c')
                
                return "markdown", alignments, raw_rows
            except Exception:
                return None, None, "마크다운 표 파싱 중 오류가 발생했습니다."

        # 2. LaTeX tabular/tabularx 판별
        joined_text = "".join(lines)
        is_tabularx = "\\begin{tabularx}" in joined_text and "\\end{tabularx}" in joined_text
        is_tabular = ("\\begin{tabular}" in joined_text and "\\end{tabular}" in joined_text
                     and not is_tabularx)
        if is_tabularx or is_tabular:
            env = "tabularx" if is_tabularx else "tabular"
            try:
                # 열 지시자 추출. tabularx 는 \begin{tabularx}{\textwidth}{|l|X|r|}
                # 처럼 너비 인자가 하나 더 있다.
                if env == "tabularx":
                    header_re = r"\\begin\{tabularx\}\{[^}]*\}\{([^}]+)\}"
                else:
                    header_re = r"\\begin\{tabular\}\{([^}]+)\}"
                match_col = re.search(header_re, joined_text)
                if not match_col:
                    return None, None, f"{env} 열 지시자를 찾을 수 없습니다."

                raw_col_spec = match_col.group(1)
                cleaned_spec = raw_col_spec.replace("|", "")
                #: X(비례 너비)는 tabularx 에서만 유효하다.
                valid_letters = "lcrX" if env == "tabularx" else "lcr"
                if not all(c in valid_letters for c in cleaned_spec):
                    return None, None, "더 복잡한 표는 전용 표 편집 프로그램을 이용하셔요"

                alignments = list(cleaned_spec)

                # 본문 행 추출: 열 지시자 닫는 } 다음부터 \end{env} 앞까지.
                end_idx = joined_text.find(f"\\end{{{env}}}")
                if end_idx == -1 or end_idx < match_col.end():
                    return None, None, f"{env} 본문을 찾을 수 없습니다."
                body_str = joined_text[match_col.end():end_idx]

                # 1단계: \hline, \toprule 등 테두리 명령어만 먼저 깨끗하게 지웁니다. (\\ 는 보존)
                cleaned_body = re.sub(r"\\(hline|toprule|midrule|bottomrule|cline)(\[[^\]]*\])?", "", body_str)
                
                # 2단계: 행 바꿈 문자(\\)를 기준으로 행을 분리합니다.
                row_chunks = cleaned_body.split("\\\\")
                data_rows = []
                
                for chunk in row_chunks:
                    row_str = chunk.strip()
                    if not row_str:
                        continue
                    
                    # '&'를 기준으로 셀 데이터를 분리합니다.
                    cells = [c.strip() for c in row_str.split('&')]
                    data_rows.append(cells)

                if not data_rows:
                    return None, None, f"{env} 데이터 행이 없습니다."

                return "latex", alignments, data_rows
            except Exception:
                return None, None, "더 복잡한 표는 전용 표 편집 프로그램을 이용하셔요"

        return None, None, "표 형식을 인식할 수 없습니다."

# ===========================================================================
# 9-p. 컴파일
# ===========================================================================
#
# sync(정방향/역방향 검색, 에디터 등록, 단일 인스턴스)는 전부 v0.3 에서
# 붙었다. forward_search()/open_path()/register_as_inverse_search_target()/
# process_argv() 를 보면 된다. 다만 여러 탭(같은 인스턴스 안에서 여러
# 파일을 동시에 편집)은 아직 없다 — 역방향 호출이 파일 하나를 열고 그
# 줄로 가는 것으로 충분해서, 지금 구조로도 문제없이 돌아간다.

#: ndhmd4tex 의 --pdfxe/--pdflatex/--pdflua 가 각 백엔드에 넘기는 실제
#: 엔진 플래그. 두 백엔드가 서로 다른 철자를 쓴다(ksruncltex 는 두 대시,
#: latexmk 는 한 대시) — ndhmd4tex 원본의 실제 호출부에서 그대로 옮겼다.
KSRUNCLTEX_ENGINE_FLAG = {"xelatex": "--xelatex", "lualatex": "--lualatex",
                          "pdflatex": "--pdflatex"}
LATEXMK_ENGINE_FLAG = {"xelatex": "-pdfxe", "lualatex": "-pdflua", "pdflatex": "-pdf"}

LOG_ERROR_RE = re.compile(r"^!\s*(.+)$")
LOG_LINE_RE = re.compile(r"^l\.(\d+)\b")


class NmdSync:
    """.nmdsync 를 읽어 tex 행번호를 원문 조각 파일의 행번호로 되짚는다.

    레코드는 `tex_start\\ttex_end\\tsource_file\\tsrc_start\\tsrc_end` 다섯
    필드. 구간 안이면 그 구간 내에서 비례 보간하고(문단 내 근사), 구간
    바깥이면 가장 가까운 구간의 시작점으로 붙인다 — 정확한 위치보다 "대략
    이 근처"를 보여주는 것으로 충분하다. 실시간 sync 가 아니라 오류 하나를
    눌러서 그 조각으로 가는 것뿐이므로, 이 근사는 --lint 결과를 여는 것과
    본질적으로 같은 동작이다.
    """

    def __init__(self, entries):
        self.entries = entries          # [(tex_start, tex_end, path, src_start, src_end), ...]

    @classmethod
    def load(cls, path: Path) -> "NmdSync":
        entries = []
        try:
            text = read_manuscript(path)
        except (OSError, UnicodeDecodeError):
            return cls(entries)
        for line in text.splitlines():
            if not line.strip() or line.strip().startswith("#"):
                continue
            parts = line.strip().split("\t")
            if len(parts) != 5:
                continue
            try:
                ts, te = int(parts[0]), int(parts[1])
                ss, se = int(parts[3]), int(parts[4])
            except ValueError:
                continue
            entries.append((ts, te, parts[2], ss, se))
        entries.sort(key=lambda e: e[0])          # ndhmdsync 와 같은 순서
        return cls(entries)

    def source_for(self, tex_line: int):
        """(경로, 원문 행번호). 대응을 못 찾으면 (None, None).

        ndhmdsync 의 find_source_location 과 같은 규칙이다 — 구간 안이면 비례 보간,
        밖이면 가장 가까운 구간(거리가 같으면 **뒤쪽** 구간)의 가까운 끝. 그래서
        `ndhmdsync --line N` 이 주는 위치와 같은 자리가 나온다.
        """
        for ts, te, src, ss, se in self.entries:
            if ts <= tex_line <= te:
                tex_span, src_span = te - ts, se - ss
                if tex_span > 0 and src_span > 0:
                    return Path(src), ss + round((tex_line - ts) / tex_span * src_span)
                return Path(src), ss
        if not self.entries:
            return None, None

        def dist(e):
            if tex_line < e[0]:
                return e[0] - tex_line
            if tex_line > e[1]:
                return tex_line - e[1]
            return 0

        ts, te, src, ss, se = min(self.entries, key=lambda e: (dist(e), -e[0]))
        return Path(src), (ss if abs(tex_line - ts) <= abs(tex_line - te) else se)


#: ndhmd4tex 은 --pdfxe 등을 줄 때, 사용자가 compileoption:/latexmkoption:
#: 에 synctex 옵션을 이미 넣었으면 그대로 두고 안 넣었으면 강제로 붙인다
#: (그래야 --syncinfo 로 만든 .nmdsync 가 나중에 헛돌지 않는다). 우리는
#: ndhmd4tex 의 그 내부 경로를 안 쓰고 latexmk/ksruncltex 을 직접 부르므로,
#: 같은 로직을 우리가 대신 해야 한다.
_SYNCTEX_RE = re.compile(r"^-{1,2}synctex(=.*)?$")


def set_frontmatter_key(path: Path, key: str, value: str | None):
    """front matter 에 key: value 를 쓰거나(값이 None이면) 지운다.

    서랍에서 장 파일을 책 사이로 옮길 때 ndhmain: 힌트를 관리하는 데
    쓴다 — 정방향 검색(ndhmdsync)이 장 파일 안에서 어느 책 소속인지
    알려면 이게 있어야 한다.

    표면적인 텍스트 편집이다. PyYAML 로 통째로 다시 읽고 써버리면
    나머지 키의 순서·주석·서식이 다 흐트러진다 — 그 줄 하나만 건드리고
    나머지는 그대로 둔다.
    """
    try:
        text = read_manuscript(path)
    except (OSError, UnicodeDecodeError):
        return
    lines = text.split("\n")
    fm_end = None
    if lines and lines[0].strip() == "---":
        for i in range(1, len(lines)):
            if lines[i].strip() == "---":
                fm_end = i
                break

    key_re = re.compile(rf"^\s*{re.escape(key)}\s*:")
    if fm_end is not None:
        fm_lines = lines[1:fm_end]
        idx = next((i for i, l in enumerate(fm_lines) if key_re.match(l)), None)
        if value is None:
            if idx is not None:
                del fm_lines[idx]
        else:
            new_line = f"{key}: {value}"
            if idx is not None:
                fm_lines[idx] = new_line
            else:
                fm_lines.append(new_line)
        if value is None and not any(l.strip() for l in fm_lines):
            # 프론트매터가 완전히 비면 통째로 없앤다.
            rest = lines[fm_end + 1:]
            while rest and not rest[0].strip():
                rest.pop(0)
            new_text = "\n".join(rest)
        else:
            new_text = "\n".join(["---", *fm_lines, "---", *lines[fm_end + 1:]])
    else:
        if value is None:
            return                      # 지울 프론트매터 자체가 없다
        new_text = f"---\n{key}: {value}\n---\n\n" + text

    try:
        path.write_text(new_text, encoding="utf-8")
    except OSError:
        pass



# ===========================================================================
# 장별로 자르기 · 하위 파일 합치기 — 순수 텍스트 처리
# ===========================================================================

def _scan_headings(text: str):
    """(줄 목록, 제목 목록 [(줄번호, 수준, 제목글)...], 문서 끝에 남길 첫 줄 번호).
    프론트매터·코드 펜스·`:::` 환경·`====` 틀·`$$` 수식·주석 안의 `#` 줄은 제목으로 보지 않는다."""
    lines = text.split("\n")
    i0 = 0
    if lines and lines[0].strip() == "---":
        for k in range(1, len(lines)):
            if lines[k].strip() == "---":
                i0 = k + 1
                break
    heads = []
    fence = None            # (문자, 길이)
    env = frame = 0
    math = comment = False
    for idx in range(i0, len(lines)):
        line = lines[idx]
        if comment:
            if "-->" in line:
                comment = False
            continue
        if fence:
            m = re.match(r"^ {0,3}(`{3,}|~{3,})[ \t]*$", line)
            if m and m.group(1)[0] == fence[0] and len(m.group(1)) >= fence[1]:
                fence = None
            continue
        m = re.match(r"^ {0,3}(`{3,}|~{3,})", line)
        if m:
            fence = (m.group(1)[0], len(m.group(1)))
            continue
        if math:
            if "$$" in line:
                math = False
            continue
        if line.count("$$") % 2 == 1:
            math = True
            continue
        if "<!--" in line and "-->" not in line.split("<!--", 1)[1]:
            comment = True
            continue
        if ENV_OPEN_RE.match(line):
            env += 1
            continue
        if ENV_CLOSE_RE.match(line):
            env = max(0, env - 1)
            continue
        if FRAME_OPEN_RE.match(line):
            frame += 1
            continue
        if FRAME_CLOSE_RE.match(line):
            frame = max(0, frame - 1)
            continue
        if env == 0 and frame == 0:
            m = HEADING_RE.match(line)
            if m:
                heads.append((idx, len(m.group(1)), m.group(2).strip()))
    mt = INLINE_TAGS_RE.search(text)
    if mt:
        tail = text[:mt.start()].count("\n")
    else:
        tail = len(lines)
        while tail > 0 and not lines[tail - 1].strip():
            tail -= 1                      # 끝의 빈 줄은 어느 쪽에도 속하지 않는다
    return lines, heads, tail


def split_chapter_sections(text: str, level: int | None = None):
    """문서를 한 수준의 제목마다 잘라 낼 계획을 세운다. level 이 None 이면 문서 안에서 가장 높은(# 수가 가장 적은)
    제목 수준이다. 그 수준의 제목이 둘 미만이면 None.

    구간은 그 제목부터, 같은 수준이거나 더 높은 수준의 다음 제목(없으면 문서 끝의 TAGS 주석 / 파일 끝) 앞까지다.
    더 높은 수준의 제목과 그 앞의 글은 원 문서에 남는다.
    돌려주는 값: {"lines","level","tail","sections":[{"start","end"(배타적),"title","includes":[이름...]}]}
    """
    lines, heads, tail = _scan_headings(text)
    if not heads:
        return None
    top = level if level is not None else min(h[1] for h in heads)
    tops = [h for h in heads if h[1] == top]
    if len(tops) < 2:
        return None
    sections = []
    for idx, _lv, title in tops:
        nxt = next((h[0] for h in heads if h[0] > idx and h[1] <= top), None)
        end = tail if nxt is None else nxt
        end = max(end, idx + 1)
        incs = [m.group(1).strip() for ln in lines[idx:end] if (m := INCLUDE_LINE_RE.match(ln))]
        sections.append({"start": idx, "end": end, "title": title, "includes": incs})
    return {"lines": lines, "level": top, "tail": tail, "sections": sections}


def next_split_level(text: str):
    """가장 높은 제목 수준이 하나뿐일 때, 한 단계 아래(존재하는 다음 수준)를 돌려준다.
    그 수준의 제목이 둘 이상일 때만, 아니면 None."""
    _lines, heads, _tail = _scan_headings(text)
    levels = sorted({h[1] for h in heads})
    if len(levels) < 2:
        return None
    nxt = levels[1]
    return nxt if sum(1 for h in heads if h[1] == nxt) >= 2 else None


def apply_chapter_split(plan: dict, names: list):
    """plan 과 새 파일 이름들(섹션 순서)로 (새 하위 파일 본문 목록, 고친 원 문서 본문)을 만든다."""
    lines, secs = plan["lines"], plan["sections"]
    bodies = ["\n".join(lines[s["start"]:s["end"]]).strip("\n") + "\n" for s in secs]
    chunks, pos = [], 0
    for sec, n in zip(secs, names):
        chunks.append(lines[pos:sec["start"]])
        chunks.append(["{{" + n + "}}"])
        pos = sec["end"]
    chunks.append(lines[pos:])
    out = []
    for k, ch in enumerate(chunks):
        ch = list(ch)
        while ch and not ch[-1].strip():
            ch.pop()
        if k:
            while ch and not ch[0].strip():
                ch.pop(0)
        if not ch:
            continue
        if out:
            out.append("")
        out.extend(ch)
    return bodies, "\n".join(out).rstrip("\n") + "\n"


def merge_child_text(child_text: str):
    """하위 파일 본문에서 합칠 부분(프론트매터와 끝의 TAGS 주석을 뺀 나머지)과,
    버려지는 프론트매터 키(ndhmain 제외) 목록을 돌려준다."""
    dropped = []
    m = FRONTMATTER_RE.match(child_text)
    body = child_text
    if m:
        for ln in m.group(1).splitlines():
            km = re.match(r"^([A-Za-z_][\w+-]*)\s*:", ln)
            if km and km.group(1) != "ndhmain":
                dropped.append(km.group(1))
        body = child_text[m.end():]
    mt = INLINE_TAGS_RE.search(body)
    if mt:
        rest = body[mt.start():]
        keep_incs = [ln for ln in rest.splitlines() if INCLUDE_LINE_RE.match(ln)]
        body = body[:mt.start()] + ("\n".join(keep_incs) + "\n" if keep_incs else "")
        dropped.append("TAGS 주석")
    return body.strip("\n"), dropped


class SplitChaptersDialog(QDialog):
    """장별로 자르기 — 접두어를 받고, 어떤 파일이 어떻게 만들어질지 미리 보여 준다."""

    def __init__(self, window: "MainWindow", doc: Path, plan: dict, default_prefix: str):
        super().__init__(window)
        self._doc = doc
        self._plan = plan
        self.setWindowTitle("장별로 자르기")
        self.resize(560, 420)
        self.prefix_edit = QLineEdit(default_prefix)
        self.prefix_edit.textChanged.connect(self._refresh)
        form = QFormLayout()
        form.addRow("하위 파일 접두어:", self.prefix_edit)
        self.info = QLabel()
        self.info.setWordWrap(True)
        self.preview = QPlainTextEdit()
        self.preview.setReadOnly(True)
        self.buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        self.buttons.accepted.connect(self.accept)
        self.buttons.rejected.connect(self.reject)
        box = QVBoxLayout(self)
        lvl = "#" * plan["level"]
        box.addWidget(QLabel(f"{doc.name} 을(를) 최상위 제목({lvl})마다 잘라 {{{{포함}}}} 줄로 바꿉니다 — 한 단계만."))
        box.addLayout(form)
        box.addWidget(self.info)
        box.addWidget(self.preview, 1)
        box.addWidget(self.buttons)
        self._refresh()

    def names(self) -> list:
        pre = self.prefix_edit.text().strip()
        return [f"{pre}-{i}.md" for i in range(1, len(self._plan["sections"]) + 1)]

    def prefix_ok(self) -> bool:
        pre = self.prefix_edit.text().strip()
        return bool(pre) and not re.search(r'[\\/:*?"<>|{}]', pre) and not pre.startswith(".")

    def _refresh(self):
        names = self.names()
        clash = [n for n in names if (self._doc.parent / n).exists()]
        ok = self.prefix_ok() and not clash
        rows = []
        for n, sec in zip(names, self._plan["sections"]):
            extra = f" · 포함 {len(sec['includes'])}개 딸려 감" if sec["includes"] else ""
            rows.append(f"{n}  ←  {sec['title'][:40]}  ({sec['end'] - sec['start']}줄{extra})")
        self.preview.setPlainText("\n".join(rows))
        if not self.prefix_ok():
            self.info.setText("접두어에 쓸 수 없는 글자가 있거나 비어 있습니다.")
        elif clash:
            self.info.setText("이미 있는 파일: " + ", ".join(clash[:5]) + " — 접두어를 바꿔 주세요.")
        else:
            self.info.setText(f"새 파일 {len(names)}개를 같은 폴더에 만들고, 이 문서에는 제목 앞의 글과 {{{{포함}}}} 줄만 남습니다.")
        self.buttons.button(QDialogButtonBox.Ok).setEnabled(ok)

    def prefix(self) -> str:
        return self.prefix_edit.text().strip()

def ensure_synctex_flag(args: list, flag: str) -> list:
    """args 에 이미 -synctex 계열 옵션이 있으면 그대로, 없으면 flag 를 붙인다."""
    if any(_SYNCTEX_RE.match(a) for a in args):
        return list(args)
    return [*args, flag]


class ShellCommandDialog(QDialog):
    """[도구] ▸ 셸 명령 실행. 임의의 셸 명령을 지금 파일이 있는 폴더에서
    돌린다. `{filename}` 이나 `%f` 를 넣으면 지금 열려 있는 파일의
    이름(확장자 제외)으로 바뀐다 — 예: `pdflatex {filename}.tex`.

    단축키를 일부러 안 뒀다 — 임의의 셸 명령을 실행하는 기능이라,
    실수로 눌리는 키 하나로 바로 뜨게 하고 싶지 않았다. 메뉴로만 연다.

    마지막에 쓴 명령을 기억해 뒀다가 다음에 열 때 미리 채워 둔다.
    """

    def __init__(self, window: "MainWindow"):
        super().__init__(window, Qt.Tool)
        self._win = window
        self._proc = None
        self.setWindowTitle("셸 명령 실행")
        self.resize(560, 420)

        current = f"지금 파일: {window._path.stem}" if window._path else "지금 열린 파일 없음"
        hint = QLabel(f"{{filename}} 또는 %f → 파일 이름(확장자 제외)으로 바뀝니다. {current}")
        hint.setWordWrap(True)
        hint.setStyleSheet("color: palette(mid); font-size: 11px;")

        self.cmd_edit = QLineEdit()
        self.cmd_edit.setText(window.prefs.last_shell_command())
        self.cmd_edit.setPlaceholderText("예: pdflatex {filename}.tex")
        self.cmd_edit.returnPressed.connect(self._run)

        run_btn = QPushButton("실행")
        run_btn.setDefault(True)
        run_btn.clicked.connect(self._run)
        close_btn = QPushButton("닫기")
        close_btn.clicked.connect(self.close)

        self.output = QTextEdit()
        self.output.setReadOnly(True)
        font = QFont("Menlo, Consolas, monospace")
        font.setStyleHint(QFont.Monospace)
        self.output.setFont(font)

        row = QHBoxLayout()
        row.addWidget(self.cmd_edit, 1)
        row.addWidget(run_btn)
        row.addWidget(close_btn)

        box = QVBoxLayout(self)
        box.addWidget(hint)
        box.addLayout(row)
        box.addWidget(self.output, 1)

    def _run(self):
        if self._proc is not None:
            self.output.append("(이미 실행 중인 명령이 끝나기를 기다리는 중)\n")
            return
        template = self.cmd_edit.text().strip()
        if not template:
            return

        path = self._win._path
        stem = path.stem if path else ""
        command = template.replace("{filename}", stem).replace("%f", stem)
        cwd = str(path.parent) if path else str(self._win.workspace.root)

        self._win.prefs.write(last_shell_command=template)
        self.output.append(f"$ {command}")

        if sys.platform == "win32":
            shell, flag = "cmd", "/c"
        else:
            shell, flag = "/bin/sh", "-c"

        proc = QProcess(self)
        proc.setWorkingDirectory(cwd)
        proc.setProcessChannelMode(QProcess.MergedChannels)
        proc.finished.connect(lambda code, st, p=proc: self._finished(p, code))
        proc.errorOccurred.connect(lambda e, p=proc: self._finished(p, None))
        self._proc = proc
        proc.start(shell, [flag, command])

    def _finished(self, proc, code):
        if proc is not self._proc:
            return
        self._proc = None
        raw = decode_subprocess_output(bytes(proc.readAllStandardOutput()))
        if raw:
            self.output.append(raw)
        status = f"[종료 코드 {code}]" if code is not None else "[실행 실패]"
        self.output.append(status + "\n" + "-" * 40)


class ConsoleOutputDialog(QDialog):
    """콘솔 출력을 그대로 보여준다. ksruncltex 실패처럼, 로그 형식을 몰라
    한 줄씩 되짚을 수 없을 때 쓰는 마지막 수단 — 파싱 대신 있는 그대로.

    locations = [(원고 경로, 원고 행, tex 행, 메시지), ...] 가 있으면 `오류 위치로`
    버튼이 생긴다 — 누를 때마다 다음 오류로(여럿이면 `(2/3)`처럼 순서가 붙는다).
    """

    def __init__(self, window, title: str, text: str, locations=None):
        super().__init__(window, Qt.Tool)
        self._win = window
        self._locations = list(locations or [])
        self._next = 0
        self.setWindowTitle(title)
        self.resize(760, 520)

        view = QTextEdit()
        view.setReadOnly(True)
        font = QFont("Menlo, Consolas, monospace")
        font.setStyleHint(QFont.Monospace)
        view.setFont(font)
        view.setPlainText(text)

        box = QVBoxLayout(self)
        box.addWidget(view, 1)
        row = QHBoxLayout()
        self.goto_btn = QPushButton()
        self.goto_btn.clicked.connect(self._goto_error)
        self.goto_btn.setVisible(bool(self._locations))
        self._sync_goto_text()
        row.addWidget(self.goto_btn)
        row.addStretch(1)
        close_btn = QPushButton("닫기")
        close_btn.clicked.connect(self.close)
        row.addWidget(close_btn)
        box.addLayout(row)

    def _sync_goto_text(self):
        n = len(self._locations)
        self.goto_btn.setText("오류 위치로" if n <= 1
                              else f"오류 위치로 ({self._next + 1}/{n})")
        if n:
            path, line, texline, msg = self._locations[self._next]
            self.goto_btn.setToolTip(
                f"tex {texline}행 → {path.name}:{line}\n{msg}")

    def _goto_error(self):
        if not self._locations:
            return
        path, line, texline, msg = self._locations[self._next]
        self._win.open_at(path, line)
        self._win.statusBar().showMessage(
            f"tex {texline}행 → {path.name}:{line}  {msg}", 8000)
        self._next = (self._next + 1) % len(self._locations)
        self._sync_goto_text()


# ===========================================================================
# 10. 창
# ===========================================================================

class FloatingPanelWindow(QWidget):
    """오른쪽 날개(라벨 날개·TOC)를 떼어내서 띄우는 창.

    QDialog 가 아니라 평범한 Tool 창이다 — QDialog 는 Esc 를 누르면
    closeEvent 없이 그냥 숨어 버려서, 메뉴의 체크 상태와 어긋난다.
    창의 [x] 는 패널의 [✕] 와 똑같이 "닫기"(= 메뉴 체크 해제)이고,
    원래 자리로 되돌리는 건 패널 머리줄의 [붙이기] 버튼이다.
    """

    def __init__(self, host: "MainWindow", key: str, panel: QWidget, title: str):
        super().__init__(host, Qt.Tool)
        self._host = host
        self._key = key
        self.panel = panel
        self.setWindowTitle(title)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.addWidget(panel)
        self.setMinimumSize(200, 200)

    def keyPressEvent(self, event):
        if event.key() == Qt.Key_Escape:
            self.close()                # 다른 도구 창들과 같이 Esc = 닫기
            return
        super().keyPressEvent(event)

    def closeEvent(self, event):
        self._host._on_floating_closed(self._key)
        event.accept()


class SynopsisCard(QFrame):
    """카드 한 장 = 원고 파일 하나. 제목(눌러서 열기), 파일·글자 수, 고칠 수 있는 시놉시스."""

    open_requested = Signal(object)          # Path
    menu_requested = Signal(object, object)  # Path, 화면 좌표(QPoint)
    drag_started = Signal()
    drag_finished = Signal()

    def __init__(self, path: Path, title: str, badge: str, chars: int, synopsis: str, store,
                 draggable: bool = True, preview: str = ""):
        super().__init__()
        self.path = path
        self.draggable = draggable
        self._press = None
        self._drop_mark = False
        self._paint_args = None
        self.setContextMenuPolicy(Qt.CustomContextMenu)
        self.customContextMenuRequested.connect(
            lambda pos: self.menu_requested.emit(self.path, self.mapToGlobal(pos)))
        self._store = store
        self.setObjectName("SynopsisCard")
        self.setFrameShape(QFrame.StyledPanel)
        self.setMinimumSize(190, 140)
        self.badge = QLabel(("⠿ " if draggable else "") + badge)
        if draggable:
            self.badge.setToolTip("끌어서 순서를 바꾸거나, 서랍으로 끌어 책에서 뺀다")
        self.title_btn = QPushButton(title)
        self.title_btn.setFlat(True)
        self.title_btn.setCursor(Qt.PointingHandCursor)
        self.title_btn.setToolTip("눌러서 이 원고를 연다")
        self.title_btn.clicked.connect(lambda: self.open_requested.emit(self.path))
        self.meta = QLabel(f"{path.name} · {chars:,}자")
        self.edit = QPlainTextEdit()
        # 시놉시스가 없으면 원고 앞부분을 흐리게 보인다(placeholder 라 저장되지 않고, 쓰기 시작하면 사라진다).
        self.edit.setPlaceholderText(preview or "시놉시스 — 이 원고를 한두 줄로")
        self.edit.setPlainText(synopsis)
        self.edit.setTabChangesFocus(True)
        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.setInterval(600)
        self._timer.timeout.connect(self.flush)
        self.edit.textChanged.connect(self._timer.start)
        top = QHBoxLayout()
        top.addWidget(self.badge)
        top.addWidget(self.title_btn, 1)
        box = QVBoxLayout(self)
        box.setContentsMargins(10, 8, 10, 8)
        box.setSpacing(4)
        box.addLayout(top)
        box.addWidget(self.meta)
        box.addWidget(self.edit, 1)

    # -- 끌기: 배지·파일 줄·카드 가장자리를 잡고 끈다(제목 단추와 입력칸은 제외) ----------------------

    def mousePressEvent(self, e):
        self._press = e.position().toPoint() if e.button() == Qt.LeftButton else None
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        if (self.draggable and self._press is not None and (e.buttons() & Qt.LeftButton)
                and (e.position().toPoint() - self._press).manhattanLength()
                >= QApplication.startDragDistance()):
            self._press = None
            md = QMimeData()
            md.setData(CARD_MIME, str(self.path).encode("utf-8"))
            drag = QDrag(self)
            drag.setMimeData(md)
            drag.setPixmap(self.grab().scaledToWidth(170, Qt.SmoothTransformation))
            self.drag_started.emit()
            try:
                drag.exec(Qt.MoveAction)
            finally:
                self.drag_finished.emit()
            return
        super().mouseMoveEvent(e)

    def mouseReleaseEvent(self, e):
        self._press = None
        super().mouseReleaseEvent(e)

    def set_drop_mark(self, on: bool):
        """끌어온 것이 놓일 자리(이 카드 앞)를 왼쪽 굵은 줄로 보인다."""
        if on != self._drop_mark:
            self._drop_mark = on
            if self._paint_args:
                self.paint_with(*self._paint_args)

    def flush(self):
        """고친 시놉시스를 저장한다(타이핑이 0.6초 멈추거나 창을 닫을 때)."""
        self._timer.stop()
        self._store.set(self.path, self.edit.toPlainText())

    def paint_with(self, theme: Theme, accent: str):
        """카드 바탕을 패널 바탕에 accent 색을 옅게 섞어 칠한다 — 어두운/밝은 테마 모두에서 글자가 읽히도록
        섞는 정도를 테마의 밝기에 맞춘다."""
        bg = QColor(theme.panel_bg)
        dark = QColor(theme.bg).lightness() < 128
        a = 0.26 if dark else 0.20
        ac = QColor(accent)
        mix = QColor(int(bg.red() * (1 - a) + ac.red() * a),
                     int(bg.green() * (1 - a) + ac.green() * a),
                     int(bg.blue() * (1 - a) + ac.blue() * a))
        edge = QColor(int(bg.red() * 0.5 + ac.red() * 0.5),
                      int(bg.green() * 0.5 + ac.green() * 0.5),
                      int(bg.blue() * 0.5 + ac.blue() * 0.5))
        field = "rgba(255,255,255,0.07)" if dark else "rgba(255,255,255,0.55)"
        self._paint_args = (theme, accent)
        left = f"border-left: 6px solid {theme.heading};" if self._drop_mark else ""
        self.setStyleSheet(f"""
            #SynopsisCard {{ background: {mix.name()}; border: 1px solid {edge.name()}; {left} border-radius: 6px; }}
            #SynopsisCard QLabel {{ color: {theme.gutter_fg_active}; background: transparent; }}
            #SynopsisCard QPushButton {{ color: {theme.fg}; background: transparent; border: none;
                                          text-align: left; font-weight: bold; padding: 0; }}
            #SynopsisCard QPlainTextEdit {{ color: {theme.fg}; background: {field};
                                            border: 1px solid {edge.name()}; }}
        """)


class SynopsisCardsDialog(QDialog):
    """카드 보기 — 책의 원고 파일을 책 순서대로 카드로 늘어놓고 시놉시스를 보고 고친다(Scrivener 의 코르크판처럼).
    단일 파일 책이면 카드가 한 장이다. 시놉시스는 .ndhmd/synopsis.json 에 저장되고 원고 파일에는 남지 않는다."""

    ACCENTS = ("#d9a441", "#5b9bd5", "#7fb069", "#c27ba0", "#9a82c8", "#e0735c")
    #: 카드 크기 (이름, 너비, 최소 높이). 고른 크기는 앱 설정에 기억한다.
    SIZES = (("small", "작게", 210, 150), ("normal", "기본", 270, 190), ("large", "크게", 360, 270))

    def __init__(self, window: "MainWindow"):
        super().__init__(window, Qt.Tool)
        self._win = window
        self._cards = []
        self._files = []
        self._root = None
        self._dragging = False
        self._reload_pending = False
        self._drop_card = None
        self._all = False                 # True: 작업공간의 모든 원고를 보인다(구조는 고치지 않음)
        self.setAcceptDrops(True)
        self.setWindowTitle("카드 보기")
        self.resize(940, 620)
        self.head = QLabel()
        add_btn = QPushButton("＋ 파일 추가")
        add_btn.setToolTip("서랍의 파일을 이 책의 마지막에 넣는다(서랍에서 끌어다 놓아도 된다)")
        add_btn.clicked.connect(self._add_menu)
        self._add_btn = add_btn
        refresh = QPushButton("새로 고침")
        refresh.clicked.connect(self.reload)
        top = QHBoxLayout()
        top.addWidget(self.head, 1)
        self.size_box = QComboBox()
        for key, label, _w, _h in self.SIZES:
            self.size_box.addItem("카드 " + label, key)
        saved = str(window._settings.value("cards/size", "normal"))
        self.size_box.setCurrentIndex(max(0, self.size_box.findData(saved)))
        self.size_box.currentIndexChanged.connect(self._on_size)
        top.addWidget(self.size_box)
        self.mode_btn = QPushButton("모든 카드 보기")
        self.mode_btn.setCheckable(True)
        self.mode_btn.setToolTip("작업공간 최상위의 모든 원고를 책별로 묶어 보인다. 이 상태에서는 카드를 옮기거나 책에서 빼지 못한다(시놉시스는 고칠 수 있다).")
        self.mode_btn.toggled.connect(self.set_all_mode)
        top.addWidget(self.mode_btn)
        top.addWidget(add_btn)
        top.addWidget(refresh)
        self.grid_host = QWidget()
        self.grid = QGridLayout(self.grid_host)
        self.grid.setContentsMargins(6, 6, 6, 6)
        self.grid.setSpacing(10)
        self.grid.setAlignment(Qt.AlignTop | Qt.AlignLeft)
        self.scroll = QScrollArea()
        self.scroll.setWidgetResizable(True)
        self.scroll.setWidget(self.grid_host)
        box = QVBoxLayout(self)
        box.addLayout(top)
        box.addWidget(self.scroll, 1)
        self.apply_theme(window._theme)
        self.reload()

    # -- 내용 -------------------------------------------------------------------

    _HEAD_RE = re.compile(r"^#{1,6}\s+(.*?)(?:\s+\{[^}]*\})?\s*$")

    @classmethod
    def _title_of(cls, text: str, fallback: str) -> str:
        body = FRONTMATTER_RE.sub("", text, count=1)
        fence = False
        for line in body.splitlines():
            if line.lstrip().startswith(("```", "~~~")):
                fence = not fence
                continue
            if fence:
                continue
            m = cls._HEAD_RE.match(line)
            if m and m.group(1).strip():
                return m.group(1).strip()
        return fallback

    @staticmethod
    def _fm_title(text: str) -> str:
        """머리말(frontmatter)의 최상위 `title:` 값(따옴표는 벗김). 없거나 비었거나 `|`·`>` 블록이면 ""."""
        m = FRONTMATTER_RE.match(text)
        if not m:
            return ""
        for line in m.group(1).splitlines():
            mm = re.match(r"^title\s*:\s*(.*?)\s*$", line)
            if mm:
                v = mm.group(1)
                if len(v) >= 2 and v[0] == v[-1] and v[0] in "\"'":
                    v = v[1:-1]
                return "" if v in ("|", ">", "|-", ">-") else v.strip()
        return ""

    @classmethod
    def _preview_of(cls, text: str, lines: int = 3, limit: int = 140) -> str:
        """머리말(frontmatter)과 제목줄·빈 줄·{{포함}} 줄을 빼고 본문 앞 두세 줄(최대 limit 자)."""
        body = FRONTMATTER_RE.sub("", text, count=1)
        out, total, fence = [], 0, False
        for line in body.splitlines():
            t = line.strip()
            if t.startswith(("```", "~~~")):
                fence = not fence
                continue
            if fence or not t or t.startswith("#") or INCLUDE_LINE_RE.match(line) or t.startswith("<!--"):
                continue
            out.append(t)
            total += len(t)
            if len(out) >= lines or total >= limit:
                break
        res = "\n".join(out)
        return res[:limit] + ("…" if len(res) > limit else "")

    def _text_of(self, path: Path) -> str:
        w = self._win
        if path == w._path:
            return w.editor.toPlainText()
        try:
            return read_manuscript(path)
        except (OSError, UnicodeDecodeError):
            return ""

    def _depth_of(self, path: Path) -> int:
        w = self._win
        node = w.index.by_path.get(path)
        depth, seen = 0, set()
        while node is not None and node.parent is not None and node.path not in seen:
            seen.add(node.path)
            node = w.index.by_path.get(node.parent)
            depth += 1
        return depth

    def _gather(self):
        """보일 카드 목록 [(경로, 책 번호, 책 안 첫 파일인가, 그 책의 파일 수)]. 책 모드는 한 권, 모두 보기는 최상위 책 전부."""
        w = self._win
        if self._all:
            out = []
            for gi, rn in enumerate(w.index.roots):
                fl = LabelIndex.book_files(w.index, rn.path)
                out += [(p, gi, k == 0, len(fl)) for k, p in enumerate(fl)]
            return out
        anchor = self._root if self._root in w.index.by_path else w._path
        if anchor is None:
            return []
        files = LabelIndex.book_files(w.index, anchor)
        return [(p, 0, k == 0, len(files)) for k, p in enumerate(files)]

    def set_all_mode(self, on: bool):
        on = bool(on)
        if on != self._all:
            self._all = on
            self._root = None
        if self.mode_btn.isChecked() != on:
            self.mode_btn.blockSignals(True)
            self.mode_btn.setChecked(on)
            self.mode_btn.blockSignals(False)
        self._add_btn.setEnabled(not on)
        self.setWindowTitle("모든 카드 보기" if on else "카드 보기")
        self.reload()

    def reload(self):
        self.flush_all()
        for c in self._cards:
            self.grid.removeWidget(c)
            c.deleteLater()
        self._cards = []
        w = self._win
        if w._path is None:
            self.head.setText("원고를 연 뒤에 카드를 볼 수 있습니다.")
            return
        items = self._gather()
        files = [p for p, *_ in items]
        self._files = files
        if not self._all:
            self._root = files[0]
        theme = w._theme
        for n, (path, gi, first, size) in enumerate(items):
            depth = self._depth_of(path)
            badge = "" if size == 1 else ("책" if depth == 0 else ("장" if depth == 1 else "절"))
            text = self._text_of(path)
            body = FRONTMATTER_RE.sub("", text, count=1)
            chars = len("".join(body.split()))
            title = (self._fm_title(text) if first else "") or self._title_of(text, path.stem)
            card = SynopsisCard(path, title, badge, chars,
                                w.synopsis.get(path), w.synopsis,
                                draggable=(not self._all and n > 0),
                                preview=self._preview_of(text))
            card.open_requested.connect(self._open)
            card.menu_requested.connect(self._card_menu)
            card.drag_started.connect(self._on_drag_started)
            card.drag_finished.connect(self._on_drag_finished)
            card.paint_with(theme, self.ACCENTS[(gi if self._all else n) % len(self.ACCENTS)])
            self._cards.append(card)
        self._layout_cards()
        if self._all:
            books = sum(1 for _p, _g, f, sz in items if f and sz > 1)
            self.head.setText(f"{w.workspace.name} — 모든 원고 {len(files)}개"
                              + (f" (책 {books}권)" if books else ""))
        else:
            root = files[0].name
            self.head.setText(f"{root} — 원고 {len(files)}개" if len(files) > 1 else f"{root} — 단일 파일")

    def _card_dims(self):
        key = self.size_box.currentData()
        for k, _label, w, h in self.SIZES:
            if k == key:
                return w, h
        return 270, 190

    def _on_size(self, _i=None):
        self._win._settings.setValue("cards/size", self.size_box.currentData())
        self._layout_cards()

    def _layout_cards(self):
        card_w, card_h = self._card_dims()
        cols = max(1, (self.scroll.viewport().width() - 12) // (card_w + 10))
        for c in self._cards:
            self.grid.removeWidget(c)
        for i, c in enumerate(self._cards):
            c.setFixedWidth(card_w)
            c.setMinimumHeight(card_h)
            self.grid.addWidget(c, i // cols, i % cols)
        # 아래쪽에 늘어나는 빈 줄을 두어, 카드가 한 줄뿐이어도 창 높이만큼 늘어나지 않게 한다.
        for r in range(self.grid.rowCount() + 1):
            self.grid.setRowStretch(r, 0)
        self.grid.setRowStretch((len(self._cards) + cols - 1) // cols, 1)

    def resizeEvent(self, e):
        super().resizeEvent(e)
        if self._cards:
            self._layout_cards()

    # -- 구조 바꾸기: 끌어놓기·우클릭 -------------------------------------------------------------
    # 카드의 진실은 책 파일의 {{}} 줄이다. 여기서는 서랍과 같은 함수로 그 줄을 고치기만 하고,
    # 고친 뒤에는 서랍 갱신(refresh_drawer)이 structure_maybe_changed 로 카드를 다시 그린다.
    # 맨 첫 카드(책 뿌리)는 옮기지도 빼지도 못한다.

    def reanchor(self):
        self._root = None

    def structure_maybe_changed(self):
        if self._win._path is None:
            return
        if [p for p, *_ in self._gather()] != self._files:
            self.request_reload()

    def request_reload(self):
        if self._dragging:
            self._reload_pending = True      # 끄는 동안에는 끌고 있는 카드를 지우지 않는다
        else:
            self.reload()

    def _on_drag_started(self):
        self._dragging = True

    def _on_drag_finished(self):
        self._dragging = False
        self._set_drop_mark(None)
        if self._reload_pending:
            self._reload_pending = False
            QTimer.singleShot(0, self.reload)

    def _set_drop_mark(self, card):
        if card is not self._drop_card:
            if self._drop_card is not None:
                try:
                    self._drop_card.set_drop_mark(False)
                except RuntimeError:
                    pass
            self._drop_card = card
            if card is not None:
                card.set_drop_mark(True)

    def _card_at(self, pos):
        """대화상자 좌표 pos 아래의 카드(없으면 None)."""
        for c in self._cards:
            if not c.isVisible():
                continue
            top_left = c.mapTo(self, QPoint(0, 0))
            if QRect(top_left, c.size()).contains(pos):
                return c
        return None

    @staticmethod
    def _mime_paths(md):
        if md.hasFormat(CARD_MIME):
            raw = bytes(md.data(CARD_MIME)).decode("utf-8")
        elif md.hasFormat(DRAWER_MIME):
            raw = bytes(md.data(DRAWER_MIME)).decode("utf-8")
        else:
            return None
        return [Path(x) for x in raw.split("\n") if x]

    def dragEnterEvent(self, e):
        if self._mime_paths(e.mimeData()) is not None and self._files and not self._all:
            e.acceptProposedAction()
        else:
            super().dragEnterEvent(e)

    def dragMoveEvent(self, e):
        if self._mime_paths(e.mimeData()) is None or self._all:
            super().dragMoveEvent(e)
            return
        card = self._card_at(e.position().toPoint())
        # 책 뿌리 카드 위나 빈 곳 = 맨 뒤에 넣기, 그 밖의 카드 위 = 그 카드 앞에 넣기
        self._set_drop_mark(card if card is not None and card.path != self._root else None)
        e.acceptProposedAction()

    def dragLeaveEvent(self, e):
        self._set_drop_mark(None)
        super().dragLeaveEvent(e)

    def dropEvent(self, e):
        paths = self._mime_paths(e.mimeData())
        if paths is None or self._all:
            super().dropEvent(e)
            return
        card = self._card_at(e.position().toPoint())
        before = card.path if card is not None and card.path != self._root else None
        self._set_drop_mark(None)
        e.setDropAction(Qt.IgnoreAction)      # 서랍 쪽 항목을 Qt 가 지우지 못하게 한다
        e.accept()
        QTimer.singleShot(0, lambda: self._do_drop(paths, before))

    def _do_drop(self, paths: list, before):
        """before 가 있으면 그 카드 앞에, 없으면 책 뿌리의 맨 뒤에 넣는다."""
        w = self._win
        self.flush_all()
        root = self._root
        srcs = [p for p in paths if p in w.index.by_path and p != root]
        if not srcs:
            return
        if before is not None:
            w.handle_drawer_drop_multi(srcs, before, False, False)
            return
        w.handle_drawer_drop_multi(srcs, root, True, False)
        # 이미 책 안에 있던 카드는 위 처리로는 제자리에 남으므로, 책 바로 아래 자식이면 맨 뒤로 보낸다.
        kids = [p for p in srcs if (n := w.index.by_path.get(p)) is not None and n.parent == root]
        if kids:
            names = [n for n in w.index.read_includes(root) if n not in {k.name for k in kids}]
            names += [k.name for k in kids]
            w._rewrite_includes(root, names)

    def _siblings(self, path: Path):
        w = self._win
        node = w.index.by_path.get(path)
        if node is None or node.parent is None:
            return None, [], -1
        names = w.index.read_includes(node.parent)
        try:
            return node.parent, names, names.index(path.name)
        except ValueError:
            return node.parent, names, -1

    def _move_sibling(self, path: Path, how: str):
        self.flush_all()
        parent, names, i = self._siblings(path)
        if parent is None or i < 0:
            return
        n = names.pop(i)
        j = {"first": 0, "prev": max(0, i - 1), "next": min(len(names), i + 1), "last": len(names)}[how]
        names.insert(j, n)
        if names != self._win.index.read_includes(parent):
            self._win._rewrite_includes(parent, names)

    def _card_menu(self, path: Path, gpos):
        menu = QMenu(self)
        open_act = menu.addAction("열기(&O)")
        acts = {}
        if not self._all and path != self._root:
            parent, names, i = self._siblings(path)
            menu.addSeparator()
            for key, label, ok in (("first", "맨 앞으로(&F)", i > 0), ("prev", "앞으로 한 칸(&P)", i > 0),
                                   ("next", "뒤로 한 칸(&N)", 0 <= i < len(names) - 1),
                                   ("last", "맨 뒤로(&L)", 0 <= i < len(names) - 1)):
                a = menu.addAction(label)
                a.setEnabled(ok)
                acts[a] = key
            menu.addSeparator()
            out_act = menu.addAction("책에서 빼기(&X)")
            out_act.setToolTip("파일은 지우지 않고 책의 {{}} 줄에서만 뺀다")
        else:
            out_act = None
        chosen = menu.exec(gpos)
        if chosen is None:
            return
        if chosen == open_act:
            self._open(path)
        elif chosen in acts:
            self._move_sibling(path, acts[chosen])
        elif out_act is not None and chosen == out_act:
            self.flush_all()
            self._win.handle_card_drop_on_drawer([path], None)
            self._win.statusBar().showMessage(f"{path.name} 을(를) 책에서 뺐습니다(파일은 그대로 있습니다).", 4000)

    def _add_menu(self):
        """책에 아직 없는 최상위 파일들 가운데서 골라 맨 뒤에 넣는다."""
        w = self._win
        if not self._files:
            return
        root = self._root
        inside = set(self._files)
        cands = [n.path for n in w.index.roots
                 if n.path not in inside and not n.children and n.path.parent == root.parent]
        menu = QMenu(self)
        if not cands:
            menu.addAction("넣을 수 있는 파일이 없습니다").setEnabled(False)
        for c in sorted(cands, key=lambda p: p.name.lower())[:60]:
            menu.addAction(c.name).setData(str(c))
        chosen = menu.exec(self._add_btn.mapToGlobal(QPoint(0, self._add_btn.height())))
        if chosen is not None and chosen.data():
            self._do_drop([Path(chosen.data())], None)

    def _open(self, path):
        self.flush_all()
        self._win.open_from_drawer(path)

    def flush_all(self):
        for c in self._cards:
            if c._timer.isActive():
                c.flush()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key_Escape:
            self.close()                # Esc 는 hide 만 하므로 closeEvent(저장)를 거치도록 close 로
            return
        super().keyPressEvent(e)

    def closeEvent(self, e):
        self.flush_all()
        super().closeEvent(e)

    def apply_theme(self, theme: Theme):
        self.setStyleSheet(f"QDialog {{ background: {theme.bg}; }} QLabel {{ color: {theme.fg}; }}")
        self.grid_host.setStyleSheet(f"background: {theme.bg};")
        for n, c in enumerate(self._cards):
            c.paint_with(theme, self.ACCENTS[n % len(self.ACCENTS)])


# ===========================================================================
# AI 도우미 (실험) — 설치된 명령행 도구(claude, agy, codex)에 지시문과 선택한 글을 넘겨 답을 받는다.
# 앱은 API 키를 다루지 않는다: 도구가 이미 로그인된 것을 그대로 쓴다. 도구는 원고와 무관한 빈 임시 폴더에서
# 실행하고(원고 파일을 읽거나 고치지 못하게), 답은 원고에 바로 쓰지 않고 결과 창에서 확인한 뒤 반영한다.
# ===========================================================================

AI_REPLACE, AI_ADVICE = "replace", "advice"
AI_TOOLS = ("claude", "agy", "codex")
#: {프롬프트} 가 지시문으로 바뀐다. 선택한 글은 표준 입력으로 간다.
#: claude: 도구 전부 끔(--tools ""), 설정·세션 안 읽음/안 남김. gemini: 도구 제한 옵션은 확인하지 못해 기본값만 둔다
#: (비대화 모드에서는 승인이 필요한 도구가 실행되지 않는 것으로 알지만 확인 필요).
AI_DEFAULT_ARGS = {
    "claude": '-p {프롬프트} --tools "" --no-session-persistence --setting-sources "" --output-format text',
    # agy(Google Antigravity CLI, 옛 gemini 대체): 표준 입력 결합 방식이 문서에 없어 선택한 글을 지시문 뒤에 직접 붙인다({선택}).
    # --mode plan 은 실행·편집 없는 계획 모드(공개 문서 기준, 읽기 전용인지는 확인 필요).
    "agy": '-p "{프롬프트}{선택}" --mode plan',
    # codex(OpenAI Codex CLI): exec 는 비대화형. git 저장소가 아니어도 실행, 세션 파일 안 남김, 읽기 전용 샌드박스, 색 끔.
    # 선택한 글은 표준 입력으로 가서 <stdin> 블록으로 덧붙는다. 답은 표준 출력으로 나온다(확인 필요).
    "codex": "exec --skip-git-repo-check --ephemeral -s read-only --color never {프롬프트}",
}
AI_NO_TOOLS = ("명령 실행·파일 열기·웹 검색 같은 도구는 쓸 수 없다(쓰려 하면 거부되어 답이 비게 된다). "
               "도구를 쓰지 말고 지금 알고 있는 지식만으로 곧바로 답한다.")
AI_REPLACE_SUFFIX = (
    "\n\n[출력 규칙] 표준 입력으로 들어온 글을 위 지시대로 고친 결과 글만 출력한다. 서두·설명·따옴표·코드펜스를 붙이지 않는다. "
    "입력과 같은 언어(한국어)로 쓰고, 줄바꿈 구조와 마크다운 표지(`{{…}}` `[^…]` `[#…]` `[@…]` `{#…}` 등)는 그대로 둔다. "
    + AI_NO_TOOLS)
AI_ADVICE_SUFFIX = ("\n\n[출력 규칙] 한국어로 간결하게, 항목별로 답한다. 확신이 없는 사실은 '확인 필요'라고 표시한다. "
                    + AI_NO_TOOLS)
AI_DEFAULT_PROMPTS = [
    {"name": "윤문 (뜻은 그대로)", "mode": AI_REPLACE,
     "prompt": "표준 입력의 글을 뜻과 어조는 그대로 두고 문장만 자연스럽게 다듬어라."},
    {"name": "문어체로", "mode": AI_REPLACE, "prompt": "표준 입력의 글을 뜻은 그대로 두고 문어체(~다, ~이다)로 바꿔라."},
    {"name": "구어체로", "mode": AI_REPLACE, "prompt": "표준 입력의 글을 뜻은 그대로 두고 자연스러운 구어체로 바꿔라."},
    {"name": "더 간결하게", "mode": AI_REPLACE,
     "prompt": "표준 입력의 글에서 군더더기를 덜어 더 간결하게 줄여라. 내용은 빼지 않는다."},
    {"name": "묘사 보강", "mode": AI_REPLACE,
     "prompt": "표준 입력의 글에 감각적 묘사를 조금 더하라. 사실이나 사건을 새로 지어내지 않는다."},
    {"name": "조언 (문제점과 개선 제안)", "mode": AI_ADVICE,
     "prompt": "표준 입력의 글을 읽고 문장·구성·어조의 문제점과 구체적인 개선 제안을 말해 줘라."},
    {"name": "자료 보충 (확인할 사실)", "mode": AI_ADVICE,
     "prompt": "표준 입력의 글에 나오는 사실·용어·배경 가운데 보충하거나 확인할 만한 것을 짚고, 찾아볼 방향을 제안해 줘라."},
]


def _ai_extra_dirs() -> list:
    home = Path.home()
    dirs = [home / ".local" / "bin", Path("/opt/homebrew/bin"), Path("/usr/local/bin"),
            home / ".npm-global" / "bin", home / ".claude" / "local", home / ".volta" / "bin",
            home / "AppData" / "Roaming" / "npm"]
    dirs += [Path(p) for p in sorted(glob.glob(str(home / ".nvm" / "versions" / "node" / "*" / "bin")))]
    appdata = os.environ.get("APPDATA")
    if appdata:
        dirs.append(Path(appdata) / "npm")
    return [str(d) for d in dirs if d.is_dir()]


def find_ai_tool(name: str, configured: str = "") -> str:
    """명령 실행 파일 경로(없으면 ""). 지정한 경로 → PATH → 흔한 설치 위치 순. macOS 의 Finder 로 연 앱은 PATH 가 짧다."""
    if configured:
        return configured if os.path.isfile(configured) else ""
    path = os.pathsep.join([os.environ.get("PATH", "")] + _ai_extra_dirs())
    return shutil.which(name, path=path) or ""


def ai_build_command(exe: str, args_template: str, prompt: str, text: str = ""):
    """(프로그램, 인자 목록, 글을 표준 입력으로 보내는가). 템플릿의 {프롬프트} 를 지시문으로 바꾼다.
    템플릿에 {선택} 이 있으면 선택한 글을 그 자리에(앞에 빈 줄과 --- 를 두고) 직접 넣고 표준 입력은 쓰지 않는다
    (표준 입력을 못 받는 도구용). 템플릿이 잘못이면 ValueError."""
    if "{프롬프트}" not in args_template:
        raise ValueError("인자에 {프롬프트} 가 있어야 합니다.")
    inline = "{선택}" in args_template
    parts = shlex.split(args_template, posix=True)
    args = [p.replace("{프롬프트}", prompt).replace("{선택}", "\n\n---\n" + text) for p in parts]
    if sys.platform == "win32" and exe.lower().endswith((".cmd", ".bat")):
        return "cmd.exe", ["/c", exe] + args, not inline
    return exe, args, not inline


class AiRunner(QObject):
    """명령 하나를 빈 임시 폴더에서 돌리고 표준 입력에 글을 넣는다. 끝나면 done(성공, 출력, 오류글)."""

    done = Signal(bool, str, str)

    def __init__(self, parent=None):
        super().__init__(parent)
        self._proc = None
        self._tmp = None
        self._finished = False
        self._cancelled = False
        self._input = None
        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.timeout.connect(self._on_timeout)

    def start(self, program: str, args: list, text, exe_dir: str, timeout_s: int):
        """text 가 None 이면 표준 입력으로 보낼 것이 없다(글을 인자에 넣은 경우)."""
        self._tmp = tempfile.mkdtemp(prefix="ndhmd_ai_")
        p = QProcess(self)
        self._proc = p
        p.setWorkingDirectory(self._tmp)
        env = QProcessEnvironment.systemEnvironment()
        # 앱이 직접 만든 빈 임시 폴더이므로 신뢰해도 안전하다. gemini 는 신뢰하지 않는 폴더에서는 실행을 거부한다.
        env.insert("GEMINI_CLI_TRUST_WORKSPACE", "true")
        env.insert("NO_COLOR", "1")
        # 파이썬으로 만든 도구가 윈도에서 cp949 로 입출력하지 않게 한다.
        env.insert("PYTHONUTF8", "1")
        env.insert("PYTHONIOENCODING", "utf-8")
        env.insert("PATH", os.pathsep.join(
            [x for x in [exe_dir] + _ai_extra_dirs() + [env.value("PATH")] if x]))
        p.setProcessEnvironment(env)
        self._input = text
        p.started.connect(self._on_started)
        p.finished.connect(self._on_finished)
        p.errorOccurred.connect(self._on_error)
        self._timer.start(max(10, timeout_s) * 1000)
        p.start(program, args)

    def _on_started(self):
        p = self._proc
        if p is None or self._finished or self._cancelled:
            return
        if self._input is not None:
            p.write(self._input.encode("utf-8"))
        p.closeWriteChannel()

    def _finish(self, ok: bool, out: str, err: str):
        if self._finished:
            return
        self._finished = True
        self._timer.stop()
        if self._tmp:
            shutil.rmtree(self._tmp, ignore_errors=True)
            self._tmp = None
        self.done.emit(ok, out, err)

    def _on_finished(self, code, _status):
        p = self._proc
        ansi = re.compile(r"\x1b\[[0-9;?]*[ -/]*[@-~]")
        out = ansi.sub("", decode_subprocess_output(bytes(p.readAllStandardOutput())))
        err = ansi.sub("", decode_subprocess_output(bytes(p.readAllStandardError()))).strip()
        if self._cancelled:
            self._finish(False, "", "취소했습니다.")
        elif code == 0 and out.strip():
            self._finish(True, out.strip("\n"), err)
        else:
            self._finish(False, out, err or f"종료 코드 {code}, 출력이 없습니다.")

    def _on_error(self, error):
        if error == QProcess.FailedToStart:
            self._finish(False, "", "실행하지 못했습니다. 경로와 설치를 확인하세요.")

    def _on_timeout(self):
        if self._proc is not None and not self._finished:
            self._kill_tree()
            self._finish(False, "", "시간이 너무 오래 걸려 중단했습니다.")

    def _kill_tree(self):
        """도구와 그 하위 프로세스를 모두 끝낸다. QProcess.kill() 은 맨 위 프로세스만 죽여서,
        Node 기반 도구가 띄운 자식이 남아 앱이 끝난 뒤에도 돌 수 있다."""
        p = self._proc
        if p is None or p.state() == QProcess.NotRunning:
            return
        pid = int(p.processId())
        try:
            if sys.platform == "win32":
                subprocess.run(["taskkill", "/T", "/F", "/PID", str(pid)],
                               capture_output=True, timeout=5, creationflags=_NO_WINDOW)
            else:
                out = subprocess.run(["ps", "-axo", "pid=,ppid="], capture_output=True,
                                     text=True, timeout=5).stdout
                kids = {}
                for line in out.splitlines():
                    a = line.split()
                    if len(a) == 2 and a[0].isdigit() and a[1].isdigit():
                        kids.setdefault(int(a[1]), []).append(int(a[0]))
                order, stack = [], [pid]
                while stack:
                    cur = stack.pop()
                    for k in kids.get(cur, []):
                        order.append(k)
                        stack.append(k)
                for k in reversed(order):          # 깊은 쪽부터
                    try:
                        os.kill(k, signal.SIGKILL)
                    except OSError:
                        pass
        except (OSError, subprocess.SubprocessError, ValueError):
            pass
        p.kill()

    def cancel(self):
        self._cancelled = True
        if self._proc is not None and self._proc.state() != QProcess.NotRunning:
            self._kill_tree()
            self._proc.waitForFinished(500)
        elif not self._finished:
            self._finish(False, "", "취소했습니다.")


class AiResultDialog(QDialog):
    """AI 도우미 결과 창(비모달). 원문과 결과를 나란히 보이고, 반영은 사용자가 고른다. 교체는 실행 취소 한 번으로 취소된다."""

    def __init__(self, window: "MainWindow", item: dict, cursor: QTextCursor):
        super().__init__(window)
        self._win = window
        self._item = item
        self._mode = item.get("mode", AI_REPLACE)
        self._doc = window.editor.document()
        self._sel = QTextCursor(cursor)
        self._orig = cursor.selectedText()          # 줄바꿈이 U+2029 로 들어 있다
        self._plain = self._orig.replace(" ", "\n")
        self._runner = None
        self.setAttribute(Qt.WA_DeleteOnClose, True)
        self.setWindowTitle(f"AI 도우미(실험) — {item.get('name', '')}")
        self.resize(860, 480)
        self.head = QLabel()
        self.src = QPlainTextEdit(self._plain)
        self.src.setReadOnly(True)
        self.out = QPlainTextEdit()
        self.out.setReadOnly(True)
        self.out.setPlaceholderText("답을 기다리는 중…")
        split = QSplitter()
        for title, w in (("원문", self.src), ("결과 (고칠 수 있습니다)", self.out)):
            box = QWidget()
            lay = QVBoxLayout(box)
            lay.setContentsMargins(0, 0, 0, 0)
            lay.addWidget(QLabel(title))
            lay.addWidget(w, 1)
            split.addWidget(box)
        self.status = QLabel()
        self.status.setWordWrap(True)
        self.btn_replace = QPushButton("선택 범위를 이 결과로 교체")
        self.btn_insert = QPushButton("선택 범위 아래에 삽입")
        self.btn_copy = QPushButton("복사")
        self.btn_retry = QPushButton("다시 시도")
        self.btn_cancel = QPushButton("중단")
        self.btn_replace.clicked.connect(self._replace)
        self.btn_insert.clicked.connect(self._insert)
        self.btn_copy.clicked.connect(lambda: QApplication.clipboard().setText(self.out.toPlainText()))
        self.btn_retry.clicked.connect(self._run)
        self.btn_cancel.clicked.connect(self._cancel_or_close)
        row = QHBoxLayout()
        if self._mode == AI_REPLACE:
            row.addWidget(self.btn_replace)
        row.addWidget(self.btn_insert)
        row.addWidget(self.btn_copy)
        row.addWidget(self.btn_retry)
        row.addStretch(1)
        row.addWidget(self.btn_cancel)
        box = QVBoxLayout(self)
        box.addWidget(self.head)
        box.addWidget(split, 1)
        box.addWidget(self.status)
        box.addLayout(row)
        self._set_busy(True)
        QTimer.singleShot(0, self._run)

    def _set_busy(self, busy: bool):
        for b in (self.btn_replace, self.btn_insert, self.btn_copy, self.btn_retry):
            b.setEnabled(not busy)
        self.btn_cancel.setText("중단" if busy else "닫기")
        self.out.setReadOnly(busy)

    def _run(self):
        w = self._win
        cfg = w.ai_config()
        tool = cfg["tool"]
        exe = find_ai_tool(tool, cfg[f"{tool}_path"])
        if not exe:
            self.status.setText(f"{tool} 실행 파일을 찾지 못했습니다. 도구 ▶ AI 도우미 설정에서 경로를 지정하세요.")
            self._set_busy(False)
            self.btn_retry.setEnabled(True)
            return
        suffix = AI_REPLACE_SUFFIX if self._mode == AI_REPLACE else AI_ADVICE_SUFFIX
        prompt = self._item.get("prompt", "").strip() + suffix
        try:
            program, args, use_stdin = ai_build_command(exe, cfg[f"{tool}_args"], prompt, self._plain)
        except ValueError as e:
            self.status.setText(str(e))
            self._set_busy(False)
            self.btn_retry.setEnabled(True)
            return
        self.head.setText(f"<b>{_html.escape(self._item.get('name', ''))}</b> · {tool} · 선택 {len(self._plain):,}자")
        self.out.setPlainText("")
        self.status.setText("답을 기다리는 중… (몇 초 걸립니다)")
        self._set_busy(True)
        self._runner = AiRunner(self)
        self._runner.done.connect(self._on_done)
        self._runner.start(program, args, self._plain if use_stdin else None,
                           os.path.dirname(exe), cfg["timeout"])

    def _on_done(self, ok: bool, out: str, err: str):
        self._set_busy(False)
        if ok:
            self.out.setPlainText(out)
            self.status.setText("완료. 결과를 확인하고 반영하세요." + (f"  (도구 메시지: {err[:200]})" if err else ""))
        else:
            self.out.setPlainText(out)
            self.status.setText("실패: " + (err[:600] or "알 수 없는 오류"))
            self.btn_replace.setEnabled(False)
            self.btn_insert.setEnabled(bool(out.strip()))
        self.out.setReadOnly(False)

    def _cancel_or_close(self):
        if self._runner is not None and not self._runner._finished:
            self._runner.cancel()
        else:
            self.close()

    def _selection_intact(self) -> bool:
        w = self._win
        if w.editor.document() is not self._doc or not self._sel.hasSelection():
            return False
        return self._sel.selectedText() == self._orig

    def _replace(self):
        text = self.out.toPlainText()
        if not text.strip():
            return
        if not self._selection_intact():
            self.status.setText("원문이 바뀌었거나 다른 파일로 옮겨 교체하지 않았습니다. '선택 범위 아래에 삽입'이나 복사를 쓰세요.")
            return
        c = QTextCursor(self._sel)
        c.beginEditBlock()
        c.insertText(text)
        c.endEditBlock()
        self._win.statusBar().showMessage("AI 결과로 교체했습니다(Ctrl+Z 로 되돌립니다).", 5000)
        self.close()

    def _insert(self):
        text = self.out.toPlainText().strip("\n")
        if not text:
            return
        if self._win.editor.document() is not self._doc:
            self.status.setText("다른 파일로 옮겨 삽입하지 않았습니다. 복사를 쓰세요.")
            return
        c = QTextCursor(self._sel)
        c.setPosition(max(c.position(), c.anchor()))
        c.movePosition(QTextCursor.EndOfBlock)
        c.beginEditBlock()
        c.insertText("\n\n" + text)
        c.endEditBlock()
        self._win.statusBar().showMessage("AI 결과를 선택 범위 아래에 넣었습니다(Ctrl+Z 로 되돌립니다).", 5000)
        self.close()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key_Escape:
            self.close()                # Esc 는 hide 만 하므로 closeEvent(실행 중단)를 거치도록 close 로
            return
        super().keyPressEvent(e)

    def closeEvent(self, e):
        if self._runner is not None and not self._runner._finished:
            self._runner.cancel()
        super().closeEvent(e)


# ===========================================================================
# 사전 찾기 (우클릭 "찾아보기… > 사전에서 찾기")
# ===========================================================================

#: 기본 사전 목록. 주소의 `{q}` 자리에 선택한 글이 URL 인코딩되어 들어간다.
DICT_DEFAULTS = [
    {"name": "네이버 국어사전", "url": "https://ko.dict.naver.com/#/search?query={q}"},
    {"name": "네이버 영한사전", "url": "https://en.dict.naver.com/#/search?query={q}"},
    {"name": "네이버 한자사전", "url": "https://hanja.dict.naver.com/#/search?query={q}"},
]
DICT_SETTING = "lookup/dictionaries"


def load_dictionaries(settings) -> list:
    """저장된 사전 목록(없거나 깨졌으면 기본값)."""
    try:
        raw = settings.value(DICT_SETTING, "")
        items = json.loads(raw) if raw else None
    except (ValueError, TypeError):
        items = None
    if not isinstance(items, list):
        return [dict(d) for d in DICT_DEFAULTS]
    out = [{"name": str(x["name"]), "url": str(x["url"])} for x in items
           if isinstance(x, dict) and x.get("name") and x.get("url")]
    return out        # 사용자가 모두 지웠으면 빈 목록 그대로 둔다


def dictionary_url(template: str, text: str) -> str:
    return template.replace("{q}", urllib.parse.quote(text, safe=""))


# ---------------------------------------------------------------------------
# 외부 도구 — 선택한 글(없으면 현재 파일 전체)을 사용자가 등록한 명령행 프로그램에
# 표준 입력으로 보내고, 표준 출력을 결과로 받는다. 철자 검사기·문단 이어 붙이기
# (hgwordstitcher) 같은 것을 앱 밖에 맡기려는 것이다. AI 도우미와 같은 실행기
# (AiRunner)·결과 창(AiResultDialog)을 쓴다. 책 전체에는 적용하지 않는다.
# ---------------------------------------------------------------------------
EXT_TOOLS_KEY = "exttools/items"
EXT_PROPOSE, EXT_APPLY = "propose", "apply"
EXT_MODE_LABELS = {EXT_PROPOSE: "교체 제안", EXT_APPLY: "바로 적용"}


def ext_tool_search_dirs(extra: str = "") -> list:
    """도구를 찾을 폴더: 사용자가 적은 폴더 → 흔한 설치 폴더 → PATH."""
    dirs = [os.path.expanduser(x.strip()) for x in re.split(r"[;\n]|" + re.escape(os.pathsep), extra or "")
            if x.strip()]
    dirs += _ai_extra_dirs()
    dirs += [d for d in os.environ.get("PATH", "").split(os.pathsep) if d]
    return dirs


def ext_tool_resolve(command: str, extra_dirs: str = ""):
    """명령을 (실행 파일 전체 경로, 인자 목록)으로 푼다. 잘못이면 ValueError."""
    command = (command or "").strip()
    if not command:
        raise ValueError("명령이 비어 있습니다.")
    try:
        parts = shlex.split(command, posix=(sys.platform != "win32"))
    except ValueError as e:
        raise ValueError(f"명령을 읽을 수 없습니다: {e}")
    if sys.platform == "win32":           # 비 POSIX 분할은 따옴표를 남긴다
        parts = [x[1:-1] if len(x) >= 2 and x[0] == x[-1] and x[0] in "\"'" else x for x in parts]
    if not parts:
        raise ValueError("명령이 비어 있습니다.")
    prog = parts[0]
    if os.sep in prog or (os.altsep and os.altsep in prog):
        exe = os.path.expanduser(prog)
        if not os.path.isfile(exe):
            raise ValueError(f"실행 파일이 없습니다: {prog}")
    else:
        exe = shutil.which(prog, path=os.pathsep.join(ext_tool_search_dirs(extra_dirs)))
        if not exe:
            raise ValueError(f"{prog} 을(를) 찾지 못했습니다. PATH 나 '추가 검색 폴더'에 두세요.")
    return exe, parts[1:]


def ext_tool_build(command: str, text: str, extra_dirs: str = ""):
    """(프로그램, 인자 목록, 표준 입력 글 또는 None, 임시 입력 파일 또는 None).

    명령의 첫 낱말이 프로그램이다. 경로가 없으면 사용자 폴더·PATH 에서 찾는다.
    인자에 {입력} 이 있으면 글을 임시 파일(UTF-8)에 쓰고 그 경로를 넣는다 —
    이때는 표준 입력을 쓰지 않는다. 잘못이면 ValueError."""
    exe, args = ext_tool_resolve(command, extra_dirs)
    tmp = None
    use_stdin = True
    if any("{입력}" in a for a in args):
        fd, tmp = tempfile.mkstemp(prefix="ndhmd_in_", suffix=".txt")
        with os.fdopen(fd, "w", encoding="utf-8", newline="") as f:
            f.write(text)
        args = [a.replace("{입력}", tmp) for a in args]
        use_stdin = False
    if sys.platform == "win32" and exe.lower().endswith((".cmd", ".bat")):
        return "cmd.exe", ["/c", exe] + args, (text if use_stdin else None), tmp
    return exe, args, (text if use_stdin else None), tmp


def ext_tool_fit_output(orig: str, out: str) -> str:
    """AiRunner 는 출력 끝의 줄바꿈을 떼므로, 원문 끝의 줄바꿈 수를 되돌려 준다."""
    tail = len(orig) - len(orig.rstrip("\n"))
    return out.rstrip("\n") + "\n" * tail


def diff_chars_html(a: str, b: str, limit: int = 40000) -> str:
    """원문 a 와 결과 b 의 달라진 곳을 글자 단위로 칠한 HTML.
    먼저 줄 단위로 맞추고, 바뀐 줄 묶음 안에서만 글자 단위로 맞춘다(전체를 글자 단위로 하면 느리다)."""
    esc = _html.escape
    DEL = '<span style="background-color:#fdb8c0;color:#000;text-decoration:line-through">%s</span>'
    INS = '<span style="background-color:#a6e3a1;color:#000">%s</span>'
    la, lb = a.splitlines(keepends=True), b.splitlines(keepends=True)
    out = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, la, lb, autojunk=False).get_opcodes():
        A, B = "".join(la[i1:i2]), "".join(lb[j1:j2])
        if tag == "equal":
            out.append(esc(A))
        elif tag == "delete":
            out.append(DEL % esc(A))
        elif tag == "insert":
            out.append(INS % esc(B))
        elif len(A) + len(B) > limit:
            out.append(DEL % esc(A) + INS % esc(B))
        else:
            for t, a1, a2, b1, b2 in difflib.SequenceMatcher(None, A, B, autojunk=False).get_opcodes():
                if t == "equal":
                    out.append(esc(A[a1:a2]))
                    continue
                if a2 > a1:
                    out.append(DEL % esc(A[a1:a2]))
                if b2 > b1:
                    out.append(INS % esc(B[b1:b2]))
    return '<pre style="white-space:pre-wrap;font-family:monospace">' + "".join(out) + "</pre>"


class ExtToolResultDialog(AiResultDialog):
    """외부 도구 결과 창(교체 제안). AI 도우미 창과 같되 '변경점 보기'가 있다."""

    def __init__(self, window: "MainWindow", item: dict, cursor: QTextCursor):
        item = dict(item)
        item["mode"] = AI_REPLACE
        super().__init__(window, item, cursor)
        self.setWindowTitle(f"외부 도구 — {item.get('name', '')}")
        self.diff = QTextBrowser()
        self.diff.setVisible(False)
        self.out.parentWidget().layout().addWidget(self.diff, 1)
        self.chk_diff = QCheckBox("변경점 보기 (글자 단위)")
        self.chk_diff.setEnabled(False)
        self.chk_diff.toggled.connect(self._toggle_diff)
        self.layout().insertWidget(2, self.chk_diff)

    def _toggle_diff(self, on: bool):
        if on:
            self.diff.setHtml(diff_chars_html(self._plain, self.out.toPlainText()))
        self.diff.setVisible(on)
        self.out.setVisible(not on)

    def _run(self):
        w = self._win
        try:
            program, args, stdin_text, tmp = ext_tool_build(
                self._item.get("command", ""), self._plain, w.ext_tool_dirs())
        except ValueError as e:
            self.status.setText(str(e))
            self._set_busy(False)
            self.btn_retry.setEnabled(True)
            return
        self._tmp_in = tmp
        self.head.setText(f"<b>{_html.escape(self._item.get('name', ''))}</b> · "
                          f"{_html.escape(self._item.get('command', ''))} · 입력 {len(self._plain):,}자")
        self.out.setPlainText("")
        self.chk_diff.setChecked(False)
        self.chk_diff.setEnabled(False)
        self.status.setText("실행 중…")
        self._set_busy(True)
        self._runner = AiRunner(self)
        self._runner.done.connect(self._on_done)
        self._runner.start(program, args, stdin_text, os.path.dirname(program), w.ext_tool_timeout())

    def _on_done(self, ok: bool, out: str, err: str):
        tmp = getattr(self, "_tmp_in", None)
        if tmp:
            try:
                os.remove(tmp)
            except OSError:
                pass
            self._tmp_in = None
        if ok:
            out = ext_tool_fit_output(self._plain, out)
        super()._on_done(ok, out, err)
        if ok:
            self.status.setText("완료. 변경점을 보고 반영하세요." + (f"  (도구 메시지: {err[:200]})" if err else ""))
            self.chk_diff.setEnabled(True)
        self.btn_insert.setEnabled(False)       # 외부 도구는 교체만 한다


class ExtToolConfirmDialog(QDialog):
    """실행 직전에 명령줄(옵션)을 확인·수정하는 창. 수정은 이번 한 번에만 쓰이며,
    '도구에 저장'을 고르면 등록된 명령도 바뀐다. '옵션 도움말'은 프로그램에 --help 를 준다."""

    def __init__(self, window: "MainWindow", item: dict, scope: str, nchars: int):
        super().__init__(window)
        self._win = window
        self._runner = None
        self.setWindowTitle(f"외부 도구 실행 — {item.get('name', '')}")
        self.resize(680, 150)
        lay = QVBoxLayout(self)
        info = _T("대상: {}").format(_T(scope)) + f" · {nchars:,}" + _T("자")
        lay.addWidget(QLabel(f"<b>{_html.escape(item.get('name', ''))}</b> · {_html.escape(info)}"))
        self.edit = QLineEdit(item.get("command", ""))
        mono = QFont("monospace")
        mono.setStyleHint(QFont.Monospace)
        self.edit.setFont(mono)
        self.edit.textChanged.connect(self._check)
        lay.addWidget(self.edit)
        self.note = QLabel()
        self.note.setWordWrap(True)
        lay.addWidget(self.note)
        self.help = QPlainTextEdit()
        self.help.setReadOnly(True)
        self.help.setFont(mono)
        self.help.setVisible(False)
        lay.addWidget(self.help, 1)
        self.chk_save = QCheckBox("이 명령을 도구에 저장")
        lay.addWidget(self.chk_save)
        row = QHBoxLayout()
        self.btn_help = QPushButton("옵션 도움말 (--help)")
        self.btn_help.clicked.connect(self._show_help)
        row.addWidget(self.btn_help)
        row.addStretch(1)
        self.box = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        self.box.button(QDialogButtonBox.Ok).setText("실행")
        self.box.accepted.connect(self.accept)
        self.box.rejected.connect(self.reject)
        row.addWidget(self.box)
        lay.addLayout(row)
        self._check()

    def command(self) -> str:
        return self.edit.text().strip()

    def save_requested(self) -> bool:
        return self.chk_save.isChecked()

    def _check(self):
        ok = True
        try:
            exe, _ = ext_tool_resolve(self.command(), self._win.ext_tool_dirs())
            self.note.setText(f"실행 파일: {exe}")
        except ValueError as e:
            ok = False
            self.note.setText(f'<span style="color:#c0392b">{_html.escape(_i18n_translate(str(e)))}</span>')
        self.box.button(QDialogButtonBox.Ok).setEnabled(ok)
        self.btn_help.setEnabled(ok and self._runner is None)

    def _show_help(self):
        try:
            exe, _ = ext_tool_resolve(self.command(), self._win.ext_tool_dirs())
        except ValueError:
            return
        self.help.setVisible(True)
        self.help.setPlainText("불러오는 중…")
        self.resize(self.width(), max(self.height(), 460))
        self.btn_help.setEnabled(False)
        self._runner = AiRunner(self)
        self._runner.done.connect(self._help_done)
        prog, args = exe, ["--help"]
        if sys.platform == "win32" and exe.lower().endswith((".cmd", ".bat")):
            prog, args = "cmd.exe", ["/c", exe, "--help"]
        self._runner.start(prog, args, None, os.path.dirname(exe), 30)

    def _help_done(self, ok, out, err):
        self.help.setPlainText(out.strip() or err or "도움말을 얻지 못했습니다.")
        if self._runner is not None:
            self._runner.deleteLater()
            self._runner = None
        self._check()

    def done(self, r):
        if self._runner is not None:
            self._runner.cancel()
        super().done(r)


class ExtToolSettingsDialog(QDialog):
    """외부 도구 목록: 이름·명령·방식, 추가 검색 폴더, 제한 시간."""

    def __init__(self, window: "MainWindow"):
        super().__init__(window)
        self._win = window
        self.setWindowTitle("외부 도구 설정")
        self.resize(760, 420)
        lay = QVBoxLayout(self)
        lay.addWidget(QLabel(
            "선택한 글(없으면 현재 파일 전체)을 명령의 표준 입력으로 보내고, 표준 출력으로 글을 바꿉니다.\n"
            "인자에 {입력} 이 있으면 글을 임시 파일(UTF-8)에 쓰고 그 경로를 넣습니다(표준 입력은 쓰지 않음).\n"
            "예: hgwordstitcher   ·   aspell --lang=en pipe   ·   \"C:\\tools\\fix.exe\" {입력}"))
        self.table = QTableWidget(0, 4)
        self.table.setHorizontalHeaderLabels(["이름", "명령", "방식", "실행 전 확인"])
        self.table.horizontalHeader().setStretchLastSection(False)
        self.table.horizontalHeader().setSectionResizeMode(1, QHeaderView.Stretch)
        self.table.setColumnWidth(0, 150)
        self.table.setColumnWidth(2, 110)
        self.table.setColumnWidth(3, 100)
        self.table.setSelectionBehavior(QAbstractItemView.SelectRows)
        lay.addWidget(self.table, 1)
        row = QHBoxLayout()
        for text, fn in (("추가", self._add), ("삭제", self._delete),
                         ("위로", lambda: self._move(-1)), ("아래로", lambda: self._move(1))):
            b = QPushButton(text)
            b.clicked.connect(fn)
            row.addWidget(b)
        row.addStretch(1)
        lay.addLayout(row)
        form = QFormLayout()
        self.dirs = QLineEdit(window.ext_tool_dirs())
        self.dirs.setPlaceholderText("비워 두면 PATH 와 흔한 설치 위치에서 찾습니다 (여러 폴더는 ; 로 구분)")
        form.addRow("추가 검색 폴더", self.dirs)
        self.timeout = QSpinBox()
        self.timeout.setRange(10, 3600)
        self.timeout.setSuffix(" 초")
        self.timeout.setValue(window.ext_tool_timeout())
        form.addRow("기다리는 한도", self.timeout)
        lay.addLayout(form)
        box = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        box.accepted.connect(self._accept)
        box.rejected.connect(self.reject)
        lay.addWidget(box)
        for it in window.ext_tools():
            self._add_row(it["name"], it["command"], it["mode"], it["confirm"])

    def _combo(self, mode):
        c = QComboBox()
        for k, label in EXT_MODE_LABELS.items():
            c.addItem(label, k)
        c.setCurrentIndex(max(0, c.findData(mode)))
        return c

    def _add_row(self, name="", command="", mode=EXT_PROPOSE, confirm=True):
        r = self.table.insertRow(self.table.rowCount()) or self.table.rowCount() - 1
        self.table.setItem(r, 0, QTableWidgetItem(name))
        self.table.setItem(r, 1, QTableWidgetItem(command))
        self.table.setCellWidget(r, 2, self._combo(mode))
        chk = QCheckBox()
        chk.setChecked(bool(confirm))
        holder = QWidget()
        hl = QHBoxLayout(holder)
        hl.setContentsMargins(0, 0, 0, 0)
        hl.setAlignment(Qt.AlignCenter)
        hl.addWidget(chk)
        holder._chk = chk
        self.table.setCellWidget(r, 3, holder)
        return r

    def _add(self):
        r = self._add_row()
        self.table.setCurrentCell(r, 0)
        self.table.editItem(self.table.item(r, 0))

    def _delete(self):
        r = self.table.currentRow()
        if r >= 0:
            self.table.removeRow(r)

    def _row(self, r):
        return (self.table.item(r, 0).text(), self.table.item(r, 1).text(),
                self.table.cellWidget(r, 2).currentData(), self.table.cellWidget(r, 3)._chk.isChecked())

    def _move(self, step):
        r = self.table.currentRow()
        t = r + step
        if r < 0 or not 0 <= t < self.table.rowCount():
            return
        a, b = self._row(r), self._row(t)
        for row, (n, c, m, k) in ((r, b), (t, a)):
            self.table.item(row, 0).setText(n)
            self.table.item(row, 1).setText(c)
            self.table.cellWidget(row, 2).setCurrentIndex(self.table.cellWidget(row, 2).findData(m))
            self.table.cellWidget(row, 3)._chk.setChecked(k)
        self.table.setCurrentCell(t, 0)

    def _accept(self):
        items = []
        for r in range(self.table.rowCount()):
            n, c, m, k = self._row(r)
            n, c = n.strip(), c.strip()
            if not n or not c:
                QMessageBox.warning(self, "외부 도구 설정", f"{r + 1}번째 줄: 이름과 명령을 모두 적어 주세요.")
                return
            items.append({"name": n, "command": c, "mode": m, "confirm": k})
        st = self._win._settings
        st.setValue(EXT_TOOLS_KEY, json.dumps(items, ensure_ascii=False))
        st.setValue("exttools/dirs", self.dirs.text().strip())
        st.setValue("exttools/timeout", self.timeout.value())
        self.accept()


class DictionarySettingsDialog(QDialog):
    """사전 이름·주소 목록 편집. 주소에는 `{q}` 가 꼭 있어야 한다."""

    def __init__(self, window: "MainWindow"):
        super().__init__(window)
        self._win = window
        self.setWindowTitle("사전 설정")
        self.resize(640, 320)
        lay = QVBoxLayout(self)
        lay.addWidget(QLabel(
            "주소의 {q} 자리에 선택한 글이 들어갑니다. 예: https://ko.dict.naver.com/#/search?query={q}"))
        self.table = QTableWidget(0, 2)
        self.table.setHorizontalHeaderLabels(["이름", "주소"])
        self.table.horizontalHeader().setStretchLastSection(True)
        self.table.setColumnWidth(0, 160)
        self.table.setSelectionBehavior(QAbstractItemView.SelectRows)
        lay.addWidget(self.table, 1)
        row = QHBoxLayout()
        for text, fn in (("추가", self._add), ("삭제", self._delete),
                         ("위로", lambda: self._move(-1)), ("아래로", lambda: self._move(1)),
                         ("기본값으로", self._reset)):
            b = QPushButton(text)
            b.clicked.connect(fn)
            row.addWidget(b)
        row.addStretch(1)
        lay.addLayout(row)
        box = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        box.accepted.connect(self._accept)
        box.rejected.connect(self.reject)
        lay.addWidget(box)
        self._fill(load_dictionaries(window._settings))

    def _fill(self, items):
        self.table.setRowCount(0)
        for d in items:
            self._add_row(d["name"], d["url"])

    def _add_row(self, name="", url=""):
        r = self.table.rowCount()
        self.table.insertRow(r)
        self.table.setItem(r, 0, QTableWidgetItem(name))
        self.table.setItem(r, 1, QTableWidgetItem(url))
        return r

    def _add(self):
        r = self._add_row("", "https://")
        self.table.setCurrentCell(r, 0)
        self.table.editItem(self.table.item(r, 0))

    def _delete(self):
        r = self.table.currentRow()
        if r >= 0:
            self.table.removeRow(r)

    def _move(self, step):
        r = self.table.currentRow()
        t = r + step
        if r < 0 or not 0 <= t < self.table.rowCount():
            return
        a = (self.table.item(r, 0).text(), self.table.item(r, 1).text())
        b = (self.table.item(t, 0).text(), self.table.item(t, 1).text())
        for row, (n, u) in ((r, b), (t, a)):
            self.table.item(row, 0).setText(n)
            self.table.item(row, 1).setText(u)
        self.table.setCurrentCell(t, 0)

    def _reset(self):
        self._fill(DICT_DEFAULTS)

    def items(self) -> list:
        return [{"name": self.table.item(r, 0).text().strip(),
                 "url": self.table.item(r, 1).text().strip()}
                for r in range(self.table.rowCount())]

    def _accept(self):
        items = self.items()
        for i, d in enumerate(items, 1):
            bad = (not d["name"] and "이름이 비어 있습니다"
                   or not re.match(r"https?://", d["url"]) and "주소는 http:// 또는 https:// 로 시작해야 합니다"
                   or "{q}" not in d["url"] and "주소에 {q} 가 없습니다")
            if bad:
                QMessageBox.warning(self, "사전 설정", f"{i}번째 줄: {bad}.")
                return
        self._win._settings.setValue(DICT_SETTING, json.dumps(items, ensure_ascii=False))
        self.accept()


class AiSettingsDialog(QDialog):
    """AI 도우미 설정: 사용할 도구·경로·인자, 지시문 목록."""

    def __init__(self, window: "MainWindow"):
        super().__init__(window)
        self._win = window
        self.setWindowTitle("AI 도우미 설정 (실험)")
        self.resize(760, 640)
        cfg = window.ai_config()
        self._items = [dict(x) for x in window.ai_prompts()]
        self._cur = -1
        warn = QLabel(
            "실험 기능입니다. 선택한 글이 <b>설치된 명령행 도구를 통해 외부 AI 서비스로 전송</b>됩니다. 공개 전 원고라면 "
            "서비스의 약관과 데이터 사용 방식을 확인하고 쓰세요. 도구는 원고와 무관한 빈 임시 폴더에서 실행됩니다.")
        warn.setWordWrap(True)
        self.tool = QComboBox()
        self.tool.addItems(AI_TOOLS)
        self.tool.setCurrentText(cfg["tool"])
        form = QFormLayout()
        form.addRow("사용할 도구", self.tool)
        self.path, self.args, self.found = {}, {}, {}
        for t in AI_TOOLS:
            pe = QLineEdit(cfg[f"{t}_path"])
            pe.setPlaceholderText("비워 두면 PATH 와 흔한 설치 위치에서 찾습니다")
            ae = QLineEdit(cfg[f"{t}_args"])
            fl = QLabel()
            fl.setWordWrap(True)
            self.path[t], self.args[t], self.found[t] = pe, ae, fl
            pe.textChanged.connect(self._refresh_found)
            form.addRow(f"{t} 경로", pe)
            form.addRow("", fl)
            form.addRow(f"{t} 인자", ae)
        hint = QLabel("인자에서 {프롬프트} 는 지시문으로 바뀌고, 선택한 글은 표준 입력으로 갑니다. 모델을 고르려면 인자에 "
                      "--model(claude·agy) 또는 -m(codex) 을 덧붙이세요. 인자에 {선택} 이 있으면 선택한 글을 표준 입력 대신 그 자리에 "
                      "넣습니다(agy 기본). agy 의 읽기 전용 옵션은 확인하지 못했습니다.")
        hint.setWordWrap(True)
        self.timeout = QSpinBox()
        self.timeout.setRange(10, 900)
        self.timeout.setSuffix(" 초")
        self.timeout.setValue(cfg["timeout"])
        form.addRow("기다리는 한도", self.timeout)
        self.listw = QListWidget()
        self.listw.currentRowChanged.connect(self._on_row)
        self.name = QLineEdit()
        self.mode = QComboBox()
        self.mode.addItem("교체 제안 (결과가 글을 대신함)", AI_REPLACE)
        self.mode.addItem("조언 (참고용 답)", AI_ADVICE)
        self.prompt = QPlainTextEdit()
        self.prompt.setPlaceholderText("지시문. 선택한 글은 따로 붙으므로 '표준 입력의 글을 …' 처럼 쓰세요.")
        for w in (self.name,):
            w.textEdited.connect(self._store)
        self.mode.currentIndexChanged.connect(self._store)
        self.prompt.textChanged.connect(self._store)
        btns = QHBoxLayout()
        for label, fn in (("추가", self._add), ("삭제", self._del), ("위로", lambda: self._move(-1)),
                          ("아래로", lambda: self._move(1)), ("기본 목록으로", self._defaults)):
            b = QPushButton(label)
            b.clicked.connect(fn)
            btns.addWidget(b)
        left = QVBoxLayout()
        left.addWidget(self.listw, 1)
        left.addLayout(btns)
        right = QFormLayout()
        right.addRow("이름", self.name)
        right.addRow("방식", self.mode)
        right.addRow("지시문", self.prompt)
        row = QHBoxLayout()
        row.addLayout(left, 1)
        row.addLayout(right, 2)
        box = QDialogButtonBox(QDialogButtonBox.Save | QDialogButtonBox.Cancel)
        box.accepted.connect(self._save)
        box.rejected.connect(self.reject)
        lay = QVBoxLayout(self)
        lay.addWidget(warn)
        lay.addLayout(form)
        lay.addWidget(hint)
        lay.addWidget(QLabel("지시문 목록 (편집창 우클릭 ▶ AI 도우미에 나타납니다)"))
        lay.addLayout(row, 1)
        lay.addWidget(box)
        self._reload_list(0)
        self._refresh_found()

    def _refresh_found(self):
        for t in AI_TOOLS:
            exe = find_ai_tool(t, self.path[t].text().strip())
            self.found[t].setText(f"찾음: {exe}" if exe else "찾지 못했습니다(설치되어 있지 않거나 경로가 다릅니다).")

    def _reload_list(self, row):
        self.listw.blockSignals(True)
        self.listw.clear()
        for it in self._items:
            self.listw.addItem(it["name"])
        self.listw.blockSignals(False)
        self._cur = -1
        if self._items:
            self.listw.setCurrentRow(min(row, len(self._items) - 1))
            self._on_row(self.listw.currentRow())
        else:
            self._on_row(-1)

    def _on_row(self, row):
        self._cur = row
        on = 0 <= row < len(self._items)
        for w in (self.name, self.mode, self.prompt):
            w.setEnabled(on)
        for w in (self.name, self.mode, self.prompt):
            w.blockSignals(True)
        if on:
            it = self._items[row]
            self.name.setText(it["name"])
            self.mode.setCurrentIndex(max(0, self.mode.findData(it["mode"])))
            self.prompt.setPlainText(it["prompt"])
        else:
            self.name.clear()
            self.prompt.clear()
        for w in (self.name, self.mode, self.prompt):
            w.blockSignals(False)

    def _store(self, *_):
        if not (0 <= self._cur < len(self._items)):
            return
        it = self._items[self._cur]
        it["name"] = self.name.text() or "(이름 없음)"
        it["mode"] = self.mode.currentData()
        it["prompt"] = self.prompt.toPlainText()
        self.listw.item(self._cur).setText(it["name"])

    def _add(self):
        self._items.append({"name": "새 지시문", "mode": AI_REPLACE, "prompt": ""})
        self._reload_list(len(self._items) - 1)

    def _del(self):
        if 0 <= self._cur < len(self._items):
            del self._items[self._cur]
            self._reload_list(self._cur)

    def _move(self, d):
        i, j = self._cur, self._cur + d
        if 0 <= i < len(self._items) and 0 <= j < len(self._items):
            self._items[i], self._items[j] = self._items[j], self._items[i]
            self._reload_list(j)

    def _defaults(self):
        if QMessageBox.question(self, "기본 목록", "지시문 목록을 기본값으로 되돌립니다. 지금 목록은 사라집니다.") \
                == QMessageBox.Yes:
            self._items = [dict(x) for x in AI_DEFAULT_PROMPTS]
            self._reload_list(0)

    def _save(self):
        for t in AI_TOOLS:
            if "{프롬프트}" not in self.args[t].text():
                QMessageBox.warning(self, "인자", f"{t} 인자에 {{프롬프트}} 가 있어야 합니다.")
                return
        self._win.ai_save_config(
            {"tool": self.tool.currentText(), "timeout": self.timeout.value(),
             **{f"{t}_path": self.path[t].text().strip() for t in AI_TOOLS},
             **{f"{t}_args": self.args[t].text().strip() for t in AI_TOOLS}},
            self._items)
        self.accept()


class SlotDialog(QDialog):
    """약어 슬롯 10개 편집. 1~5번은 전역, 6~9·0번은 현재 책. 문자열에 `{선택}`·`{커서}` 를 쓸 수 있다."""

    def __init__(self, window: "MainWindow"):
        super().__init__(window)
        self._win = window
        self.setWindowTitle("약어 슬롯")
        self.resize(520, 560)
        lay = QVBoxLayout(self)
        info = QLabel(
            "편집창에서 슬롯 단축키를 누르면 등록한 문자열이 커서 자리에 들어갑니다.\n"
            "1~5번은 모든 책에서 같고, 6~9·0번은 지금 연 책에만 적용됩니다.\n"
            "`{선택}` = 선택했던 글, `{커서}` = 넣은 뒤 커서가 놓일 자리  (예: 「{선택}」{커서})")
        info.setWordWrap(True)
        lay.addWidget(info)
        self.edits = {}
        form = QFormLayout()
        for key in SlotStore.KEYS:
            e = QPlainTextEdit()
            e.setFixedHeight(46)
            e.setTabChangesFocus(True)
            e.setPlainText(window.slots.get(key))
            scope = "전역" if SlotStore.is_global(key) else "이 책"
            if not SlotStore.is_global(key) and not window.slots.book_available():
                e.setEnabled(False)
                e.setPlaceholderText("책(작업공간)을 연 뒤에 쓸 수 있습니다")
            form.addRow(f"{window.slot_key_name(key)}  ({scope})", e)
            self.edits[key] = e
        inner = QWidget()
        inner.setLayout(form)
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setWidget(inner)
        lay.addWidget(scroll, 1)
        box = QDialogButtonBox(QDialogButtonBox.Save | QDialogButtonBox.Cancel)
        box.accepted.connect(self._save)
        box.rejected.connect(self.reject)
        lay.addWidget(box)

    def _save(self):
        failed = []
        for key, e in self.edits.items():
            if not e.isEnabled():
                continue
            if not self._win.slots.set(key, e.toPlainText().strip("\n")):
                failed.append(key)
        if failed:
            QMessageBox.warning(self, "약어 슬롯", f"저장하지 못한 슬롯: {', '.join(failed)}")
            return
        self.accept()


class MainWindow(QMainWindow):

    ORG, APP = "ktug.org", "ndhmdWriter"
    #: 작업공간 전체 검색에서 한 번에 모을 최대 결과 수. 저술 작업공간은
    #: 보통 수백 파일이라 동기로 훑어도 체감이 없지만, 상한은 둔다.
    MAX_HITS = 2000

    def __init__(self):
        super().__init__()
        self._theme = LIGHT
        self._path: Path | None = None
        self._dirty = False
        self._baseline_text = ""    # 지금 문서가 로드/저장된 시점의 내용
        self._title_dirty = False
        self._fake_fullscreen = False
        self._pre_fullscreen_geometry = None
        self._settings = QSettings(self.ORG, self.APP)
        self.prefs = Prefs(self._settings)

        saved = self._settings.value("workspace/root", "")
        self.workspace = Workspace(Path(saved)) if saved else Workspace()

        self.index = BookIndex(self.workspace)
        self.tags = TagStore(self.workspace)
        self.notes = NoteStore(self.workspace)
        self.synopsis = SynopsisStore(self.workspace)
        self.slots = SlotStore(self.workspace, self._settings)

        self.editor = Editor(self._theme)
        self.editor._host = self
        self.editor._apply_font(self.prefs.font_family(), self.prefs.font_size())
        self._apply_item_gap(force=True)
        self.editor.apply_tab_spaces(self.prefs.tab_spaces())
        self.editor.tab_to_spaces_enabled = self.prefs.tab_to_spaces()
        self.editor.smart_quotes_style = self.prefs.smart_quotes_style()
        self.editor.smart_punctuation = self.prefs.smart_punctuation()
        self.editor.set_fullscreen_column(self.prefs.fullscreen_column())
        self.editor.setLineWrapMode(
            QPlainTextEdit.WidgetWidth if self.prefs.word_wrap() else QPlainTextEdit.NoWrap)
        self.tag_bar = TagBar(self)
        self.find_bar = FindBar(self)
        self.results = ResultsPanel(self)
        self.drawer = Drawer(self)
        self.wing = LabelWing(self)
        self.toc = TocPanel(self)
        self.preview = PreviewPanel(self)
        self.issues = IssuePanel(self)
        self.issues.hide()
        self.tool = Ndhmd4tex(self._settings)
        self.sync_tool = NdhmdSyncTool(self._settings)
        self._lint_proc = None
        self._compile_proc = None
        self._compile_target = None
        self.find_bar.hide()
        self.results.hide()

        #: 뛴 자리를 되짚는 스택 둘. 라벨·검색·sync 는 다른 파일로 건너뛰므로
        #: 쓰던 자리로 돌아오는 길이 없으면 쓸모가 반감된다.
        #:
        #: 커서 하나를 목록 안에서 움직이는 방식(색인 하나로 관리)은 "지금
        #: 위치가 목록에 있는가" 라는 애매한 상태를 만든다. 뒤/앞 스택 둘로
        #: 나누면 그 애매함이 사라진다 — 뒤로 가면 지금 자리를 앞 스택에
        #: 얹고 뒤 스택에서 꺼낸다. 그뿐이다.
        self._back, self._forward = [], []
        self._jumping = False
        self._pane_memory = {}
        #: 서랍의 "부속 파일" 구역 접힘 상태. refresh_drawer() 가 매번
        #: 트리를 통째로 다시 그리므로, 이걸 따로 기억해 두지 않으면
        #: 사용자가 접어 둔 게 새로고침마다 도로 펼쳐진다.
        self._aux_expanded = True
        #: "자료 창고"(_assets/) 구역도 마찬가지 이유로 따로 기억해 둔다.
        self._assets_expanded = True
        self._notes_expanded = True       # 컴파일 참고 구역 — 알려야 하는 것이라 기본은 펼침
        #: 하위 폴더 구역들 — 폴더마다 접힘 상태가 다를 수 있어 경로
        #: 문자열을 키로 한다. 기본은 접힘(자료 창고와 달리, 하위
        #: 폴더는 책의 구조가 아니라 그냥 곁다리 자료라서 처음엔
        #: 안 보이는 쪽이 낫다고 봤다).
        self._subfolder_expanded = {}
        #: 책·장 항목 가운데 사용자가 접어 둔 것의 경로 문자열. 서랍은 파일을 열 때마다
        #: 다시 그려지므로, 여기에 기억해 두지 않으면 접은 것이 매번 풀린다. 앱을 끌 때까지만 기억한다.
        self._collapsed_books = set()

        #: 단일 인스턴스. 다른 인스턴스가 --goto 등을 들고 오면 여기로
        #: 온다 — 새 창을 띄우는 대신 이 창에서 처리한다.
        QLocalServer.removeServer(_IPC_KEY)   # 비정상 종료로 남은 소켓 정리
        self._ipc_server = QLocalServer(self)
        self._ipc_server.newConnection.connect(self._on_ipc_connection)
        self._ipc_server.listen(_IPC_KEY)
        self.setWindowIcon(_app_icon())

        #: v0.3 부터 파일을 옮겨 다닐 때 저장 여부를 묻지 않는다. 작업공간을
        #: 하나의 스페이스로 보는 철학의 연장이다 — 미저장 편집은 그
        #: QTextDocument 객체째로 여기 들고 있다가(실행 취소 이력까지
        #: 살아있다) 컴파일/닫기 같은 관문에서만 한꺼번에 처리한다.
        #: 깨끗한 파일은 문서를 들고 있을 이유가 없으니 커서 줄만 따로
        #: 기억해 둔다(_cursor_memory) — 다음에 열 때는 디스크를 다시
        #: 읽는다, 그 사이 바깥에서 바뀌었을 수도 있고 잃을 편집도 없다.
        self._dirty_docs = {}       # Path -> QTextDocument
        self._src_enc = {}          # Path -> 읽을 때의 인코딩(utf-8·utf-8-sig·utf-16·cp949)
        self._cursor_memory = {}    # Path -> 블록 번호
        #: setDocument() 로 문서를 갈아 끼우는 동안은 True. Qt 가 그때
        #: textChanged 를 한 번 쏘는데, _mark_dirty() 가 그걸 사용자
        #: 편집으로 착각하면 옛 경로에 새 문서를 잘못 등록해 버린다.
        self._switching_document = False

        #: 편집 중 라벨 목록을 다시 훑는 디바운스. 글자마다 훑으면 느리다.
        self._label_timer = QTimer(self)
        self._label_timer.setSingleShot(True)
        self._label_timer.setInterval(450)
        self._label_timer.timeout.connect(self.refresh_labels)

        #: 미리보기. 커서가 멈춘 뒤에만 훑고, 렌더는 풀에서 돌린다.
        self._preview_timer = QTimer(self)
        self._preview_timer.setSingleShot(True)
        self._preview_timer.setInterval(350)
        self._preview_timer.timeout.connect(self.update_preview)
        #: 자동 미리보기([환경설정]에서 켜야 동작한다) — 커서가 수식·
        #: 그림 위에서 일정 시간 머물면 미리보기 패널을 스스로 열고,
        #: 벗어나면(자기가 연 것이었다면) 스스로 닫는다.
        self._auto_preview_timer = QTimer(self)
        self._auto_preview_timer.setSingleShot(True)
        self._auto_preview_timer.timeout.connect(self._on_auto_preview_timeout)
        #: 지금 보이는 미리보기 패널이 자동으로 열린 것인지 — 그래야
        #: 벗어났을 때 스스로 닫아도 되는지(= 사용자가 Ctrl+Shift+P
        #: 로 직접 켜 둔 게 아닌지) 판단할 수 있다.
        self._preview_auto_shown = False
        self._render_signals = RenderSignals()
        self._render_signals.done.connect(self._on_render_done)
        self._render_pool = QThreadPool(self)
        self._render_pool.setMaxThreadCount(1)
        self._render_id = 0
        self._render_cache = {}
        self._render_dir = Path(tempfile.mkdtemp(prefix="ndhmd-preview-"))
        self._preview_key = None
        self._accent_panel = None
        self._help_dialog = None

        #: 원격 그림 다운로드. 렌더 풀과 분리해 둔다 — 네트워크가 느릴 때
        #: 수식 렌더 대기열까지 밀리면 안 된다.
        self._fetch_signals = FetchSignals()
        self._fetch_signals.done.connect(self._on_fetch_done)
        self._fetch_pool = QThreadPool(self)
        self._fetch_pool.setMaxThreadCount(2)
        self._fetch_id = 0

        self.vsplit = QSplitter(Qt.Vertical)
        self.vsplit.addWidget(self.editor)
        self.vsplit.addWidget(self.preview)
        self.vsplit.setStretchFactor(0, 1)
        self.vsplit.setCollapsible(0, False)

        right = QWidget()
        box = QVBoxLayout(right)
        box.setContentsMargins(0, 0, 0, 0)
        box.setSpacing(0)
        box.addWidget(self.vsplit, 1)
        box.addWidget(self.tag_bar)
        box.addWidget(self.issues)
        box.addWidget(self.results)
        box.addWidget(self.find_bar)

        self.splitter = QSplitter(Qt.Horizontal)
        self.splitter.addWidget(self.drawer)
        self.splitter.addWidget(right)
        self.wing_box = QWidget()
        self._wing_layout = QVBoxLayout(self.wing_box)
        self._wing_layout.setContentsMargins(0, 0, 0, 0)
        self._wing_layout.setSpacing(4)
        self._wing_layout.addWidget(self.wing, 1)
        self._wing_layout.addWidget(self.toc, 1)
        #: 떼어내서 떠다니는 중인 날개들 — {"wing"|"toc": FloatingPanelWindow}
        self._floating = {}
        self.splitter.addWidget(self.wing_box)
        self.splitter.setStretchFactor(1, 1)
        self.splitter.setCollapsible(1, False)
        self.splitter.setSizes([230, 720, 250])
        self.setCentralWidget(self.splitter)

        self._build_menu()
        self._build_status()

        self.editor.cursorPositionChanged.connect(self._update_status)
        self.editor.cursorPositionChanged.connect(self._schedule_preview)
        self.editor.cursorPositionChanged.connect(self._schedule_auto_preview)
        self.editor.textChanged.connect(self._mark_dirty)

        self.resize(1200, 820)
        self._restore_panes()
        self._apply_theme(self.prefs.resolved_theme())
        self.refresh_drawer()
        self.wing.setVisible(self._act_wing.isChecked())
        self.toc.setVisible(self._act_toc.isChecked())
        self._sync_wing_pane_visibility()
        self._ensure_pane(2)
        QTimer.singleShot(0, self._restore_floating)
        self.preview.setVisible(self._act_preview.isChecked())
        self._restore_vsplit()
        self._update_title()
        self._refresh_result_action()

        if self.prefs.remember_geometry():
            saved = self._settings.value("window/geometry")
            if saved is not None:
                self.restoreGeometry(saved)

    # -- 메뉴 ---------------------------------------------------------------

    def _build_menu(self):
        def act(menu, text, seq, slot):
            a = QAction(text, self)
            if seq:
                a.setShortcut(seq)
            a.triggered.connect(slot)
            menu.addAction(a)
            return a

        m = self.menuBar().addMenu("파일(&F)")
        act(m, "작업공간 열기(&W)…", "Ctrl+Shift+O", self.choose_workspace)
        self._workspace_history_menu = m.addMenu("작업공간 이력")
        self._workspace_history_menu.aboutToShow.connect(
            self._populate_workspace_history_menu)
        self._recent_label = act(m, "작업공간 폴더 보기", None, self.reveal_workspace)
        m.addSeparator()
        act(m, "새 원고(&N)…", QKeySequence.New, self.new_file)
        act(m, "열기(&O)…", QKeySequence.Open, self.open_file)
        act(m, "들여오기(&I)…", None, self.import_file)
        act(m, "저장(&S)", QKeySequence.Save, self.save_file)
        act(m, "다른 이름으로 저장(&A)…", "Ctrl+Shift+S", self.save_file_as)
        m.addSeparator()
        act(m, "이 파일 다시 읽기(&R)", "F5", self.reload_current_file)
        act(m, "서랍 다시 읽기", "Ctrl+Shift+R", self.refresh_drawer)
        m.addSeparator()
        act(m, "장별로 자르기(&C)…", None, self.split_into_chapters)
        act(m, "하위 파일 합치기(&M)…", None, self.merge_subfiles)
        m.addSeparator()
        export_menu = m.addMenu("내보내기")
        export_menu.addAction("한 개 파일로 내보내기…").triggered.connect(self.export_as_one_file)
        export_menu.addAction("장별 파일로 내보내기…").triggered.connect(self.export_as_chapter_files)
        m.addSeparator()
        act(m, "닫기(&Q)", QKeySequence.Quit, self.close)

        m = self.menuBar().addMenu("편집(&E)")
        act(m, "실행 취소", QKeySequence.Undo, self.editor.undo)
        act(m, "다시 실행", QKeySequence.Redo, self.editor.redo)
        m.addSeparator()
        act(m, "잘라내기", QKeySequence.Cut, self.editor.cut)
        act(m, "복사", QKeySequence.Copy, self.editor.copy)
        act(m, "붙여넣기", QKeySequence.Paste, self.editor.paste)
        m.addSeparator()
        act(m, "찾기(&F)…", QKeySequence.Find, lambda: self.open_find(False, False))
        act(m, "바꾸기(&R)…", QKeySequence.Replace, lambda: self.open_find(True, False))
        act(m, "작업공간에서 찾기(&W)…", "Ctrl+Shift+F",
            lambda: self.open_find(True, True))
        act(m, "다음 찾기", QKeySequence.FindNext, lambda: self.find_step(False))
        act(m, "이전 찾기", QKeySequence.FindPrevious, lambda: self.find_step(True))
        m.addSeparator()
        self._act_word_wrap = QAction("워드랩(&P)", self, checkable=True)
        self._act_word_wrap.setChecked(self.prefs.word_wrap())
        self._act_word_wrap.toggled.connect(self.toggle_word_wrap)
        m.addAction(self._act_word_wrap)
        m.addSeparator()
        smart_menu = m.addMenu("스마트 문장부호")
        quote_group = QActionGroup(self)
        quote_group.setExclusive(True)
        quote_options = [
            ("off", "끄기(곧은 따옴표 \" ')"),
            ("curly", "유니코드 따옴표(\u201c\u201d \u2018\u2019)"),
            ("cjk", "CJK 낫표(\u300e\u300f \u300c\u300d)"),
            ("french", "프랑스식 기메(\u00ab\u00bb \u2039\u203a)"),
        ]
        current_style = self.prefs.smart_quotes_style()
        self._smart_quote_actions = {}
        for key, label in quote_options:
            qa = QAction(label, self, checkable=True)
            qa.setChecked(key == current_style)
            qa.triggered.connect(lambda checked, k=key: self.set_smart_quotes_style(k))
            quote_group.addAction(qa)
            smart_menu.addAction(qa)
            self._smart_quote_actions[key] = qa
        smart_menu.addSeparator()
        self._act_smart_punct = QAction(
            "마침표·쉼표를 고리점·모점으로(\u3002\u3001)", self, checkable=True)
        self._act_smart_punct.setChecked(self.prefs.smart_punctuation())
        self._act_smart_punct.toggled.connect(self.toggle_smart_punctuation)
        smart_menu.addAction(self._act_smart_punct)
        smart_menu.addSeparator()
        _hint = smart_menu.addAction(
            "곧은 따옴표: Alt+' / Alt+Shift+'   곧은 마침표·쉼표: Alt+. / Alt+,")
        _hint.setEnabled(False)
        m.addSeparator()
        act(m, "글머리 기호 목록으로", "Ctrl+Alt+L", lambda: self._transform(SelectionTransform.to_bullet_list))
        act(m, "번호 매긴 목록으로", "Ctrl+Alt+N", lambda: self._transform(SelectionTransform.to_numbered_list))
        act(m, "코드펜스로 감싸기", "Ctrl+Alt+K", lambda: self._transform(SelectionTransform.to_code_fence))
        act(m, "인용문으로 감싸기", "Ctrl+Alt+Q", lambda: self._transform(SelectionTransform.to_blockquote))
        act(m, "환경으로 감싸기(&V)…", "Ctrl+Alt+E", self.wrap_in_environment)
        act(m, "감싼 것 풀기", "Ctrl+Alt+U", self.unwrap_selection)
        act(m, "문단 재배열", "Ctrl+Alt+R", self.reflow_selection)
        self.add_heading_shift_menus(m)
        # 단축키는 메뉴 항목이 아니라 보이지 않는 동작에 단다 — 선택이 있으면
        # 선택 범위, 없으면 현재 행이라는 "알아서" 동작이라 세 범위 중
        # 어느 하나의 항목 이름을 붙이면 거짓말이 되기 때문이다.
        for seq, delta in (("Ctrl+Alt+]", -1), ("Ctrl+Alt+[", 1)):
            hidden = QAction(self)
            hidden.setShortcut(seq)
            hidden.triggered.connect(lambda _=False, d=delta: self.shift_heading_level(d, "auto"))
            self.addAction(hidden)
        m.addSeparator()
        self._act_back = act(m, "이전 위치로", "Alt+Left", self.jump_back)
        self._act_fwd = act(m, "다음 위치로", "Alt+Right", self.jump_forward)
        act(m, "참조 ↔ 정의로 가기", "Ctrl+Alt+O", self.follow_reference)
        act(m, "같은 키의 다음 참조로", "Ctrl+Alt+Shift+O", lambda: self.follow_reference(True))

        m = self.menuBar().addMenu("도구(&T)")
        act(m, "보조 입력(&X)…", "Ctrl+Alt+A", self.open_accent_panel)
        act(m, "수식 기호(&S)…", "Ctrl+Alt+S", self.open_math_symbol_panel)
        act(m, "수식 편집·삽입(&Y)…", "Ctrl+M", self.edit_math_at_cursor)
        act(m, "색상 팔레트(&D)…", "Ctrl+Alt+D", self.open_color_palette)
        act(m, "커서 위치 코드포인트 보기", "Ctrl+Alt+P", self.show_codepoint_at_cursor)
        act(m, "메모(&M)…", "Ctrl+Alt+M", self.open_note_panel)
        act(m, "약어 슬롯(&Y)…", "Ctrl+Alt+Y", self.open_slot_dialog)
        act(m, "AI 도우미 설정(실험)…", None, self.open_ai_settings)
        self._ext_menu = m.addMenu("외부 도구(&Z)")
        self._ext_menu.aboutToShow.connect(lambda: self.fill_ext_tool_menu(self._ext_menu))
        self.fill_ext_tool_menu(self._ext_menu)
        act(m, "카드 보기(시놉시스)(&V)…", "Ctrl+Alt+V", self.open_cards)
        act(m, "모든 카드 보기(작업공간 전체)…", "Ctrl+Alt+Shift+V", self.open_all_cards)
        # 슬롯 10개: Alt+1 … Alt+0 (맥은 물리 Control — Qt 에서는 Meta 라 부른다).
        self._slot_shortcuts = []
        for _k in SlotStore.KEYS:
            _sc = QShortcut(QKeySequence(("Meta+" if sys.platform == "darwin" else "Alt+") + _k), self)
            _sc.activated.connect(lambda k=_k: self.insert_slot(k, from_shortcut=True))
            self._slot_shortcuts.append(_sc)
        act(m, "한중일 pm 입력기…", "Ctrl+Alt+H", self.open_pmime_panel)
        act(m, "선택을 pm 변환 (현재 설정으로 바로)", "Ctrl+Shift+H", self.convert_selection_pmime)
        self._act_hanja = act(m, "한자 변환(&K)", "F9", self.convert_hanja)
        self._act_hanja.setShortcuts([QKeySequence("F9"), QKeySequence("Ctrl+\\")])
        # 숨은 개발용 단축키 — 메뉴에는 넣지 않는다: 한자 사전 DB 지우기(다음 F9 에서 다시 만듦).
        self._sc_hanja_reset = QShortcut(QKeySequence("Ctrl+Shift+Alt+F9"), self)
        self._sc_hanja_reset.setContext(Qt.ApplicationShortcut)
        self._sc_hanja_reset.activated.connect(self.reset_hanja_dict)
        m.addSeparator()
        act(m, "그림 들여오기(&I)…", "Ctrl+Alt+I", self.open_image_import)
        act(m, "간단 표 편집기(&T)…", "Ctrl+Shift+E", self.open_table_editor)
        act(m, "조각 그림 만들기(&J)…", "Ctrl+Alt+J", lambda: self.open_jigsaw_dialog())
        act(m, "조각 그림 편집(&E)…", "Ctrl+Alt+Shift+J", self.edit_jigsaw_at_cursor)
        m.addSeparator()
        act(m, "bib 인용 삽입(&C)…", "Ctrl+Alt+C", self.open_citation_panel)
        act(m, "참고문헌 편집(&G)…", "Ctrl+Alt+G", self.open_bibliography_editor)
        m.addSeparator()
        act(m, "셸 명령 실행(&H)…", None, self.open_shell_command_dialog)
        act(m, "tblrDoumi 실행(&Y)", None, self.launch_tblrdoumi)

        m = self.menuBar().addMenu("보기(&V)")
        self._act_drawer = QAction("서랍 보이기(&D)", self, checkable=True)
        self._act_drawer.setShortcut("Ctrl+B")
        self._act_drawer.setChecked(True)
        self._act_drawer.triggered.connect(self.toggle_drawer)
        m.addAction(self._act_drawer)
        self._act_drawer_sort_mtime = QAction("서랍을 최신 수정순으로 정렬(&M)", self, checkable=True)
        self._act_drawer_sort_mtime.setChecked(self.prefs.drawer_sort() == "mtime")
        self._act_drawer_sort_mtime.triggered.connect(self.toggle_drawer_sort)
        m.addAction(self._act_drawer_sort_mtime)
        m.addSeparator()
        act_close_periph = QAction("주변 창 모두 닫기(&W)", self)
        act_close_periph.setShortcut("Ctrl+W")
        # 주변 창이 포커스를 가진 채로도 눌려야 하므로 앱 전체 단축키로 둔다.
        act_close_periph.setShortcutContext(Qt.ApplicationShortcut)
        act_close_periph.triggered.connect(self.close_peripheral_windows)
        m.addAction(act_close_periph)
        self._act_close_periph = act_close_periph
        self._act_wing = QAction("라벨 날개(&L)", self, checkable=True)
        self._act_wing.setShortcut("Ctrl+Shift+L")
        self._act_wing.setChecked(
            self._settings.value("view/wing", True, type=bool))
        self._act_wing.triggered.connect(self.toggle_wing)
        m.addAction(self._act_wing)
        self._act_toc = QAction("TOC 보기(&C)", self, checkable=True)
        self._act_toc.setShortcut("Ctrl+Shift+C")
        self._act_toc.setChecked(
            self._settings.value("view/toc", True, type=bool))
        self._act_toc.triggered.connect(self.toggle_toc)
        m.addAction(self._act_toc)
        self._act_preview = QAction("미리보기 패널(&P)", self, checkable=True)
        self._act_preview.setShortcut("Ctrl+Shift+P")
        self._act_preview.setChecked(
            self._settings.value("view/preview", True, type=bool))
        self._act_preview.triggered.connect(self.toggle_preview)
        m.addAction(self._act_preview)
        m.addSeparator()
        self._act_fold = QAction("프론트매터 접기(&Y)", self, checkable=True)
        self._act_fold.setShortcut("Ctrl+Shift+Y")
        self._act_fold.setChecked(
            self._settings.value("view/fold_frontmatter", True, type=bool))
        self._act_fold.triggered.connect(self.toggle_frontmatter_fold)
        m.addAction(self._act_fold)
        act(m, "펜스·환경 접기/펴기(커서 위치)", "Ctrl+Alt+Shift+H", self.toggle_fence_here)
        act(m, "펜스·환경 모두 접기", None, lambda: self.fold_all_fences(True))
        act(m, "펜스·환경 모두 펴기", None, lambda: self.fold_all_fences(False))
        m.addSeparator()
        self._act_fullscreen = QAction("전체화면(&F)", self, checkable=True)
        self._act_fullscreen.setShortcut("F11")
        self._act_fullscreen.triggered.connect(self.toggle_fullscreen)
        m.addAction(self._act_fullscreen)

        m = self.menuBar().addMenu("컴파일(&C)")
        act(m, "마크업 점검(&K)", "Ctrl+Shift+K", self.run_lint)
        act(m, "그림 점검(&U)…", "Ctrl+Shift+U", self.open_image_check)
        act(m, "상호참조 점검(&X)…", "Ctrl+Shift+X", self.open_crossref_check)
        act(m, "프론트매터 덤프", None, self.run_dump_meta)  # 이 줄을 새로 추가합니다.
        m.addSeparator()
        act(m, "책 컴파일(&B)", "Ctrl+Shift+B", lambda: self.run_compile("book"))
        act(m, "이 파일만 컴파일(&F)", "Ctrl+Alt+B", lambda: self.run_compile("file"))
        m.addSeparator()
        act(m, "변환후 tex 열기(&V)", "Ctrl+Alt+T", self.convert_and_open_tex)
        self._act_open_tex = act(m, "결과 tex 열기(&X)", "Ctrl+Shift+T",
                                 self.open_result_tex)
        m.addSeparator()
        act(m, "PDF에서 이 위치 보기(&V)", "Ctrl+Alt+F", self.forward_search)
        m.addSeparator()
        act(m, "작업공간 청소(&C)…", None, self.clean_workspace)

        m = self.menuBar().addMenu("설정(&S)")
        act(m, "환경설정(&P)…", "Ctrl+,", self.open_preferences)
        m.addSeparator()
        act(m, "테마 전환(&T)", "Ctrl+Shift+D", self.toggle_theme)
        act(m, "글자 크게", QKeySequence.ZoomIn, lambda: self._zoom(0.5))
        act(m, "글자 작게", QKeySequence.ZoomOut, lambda: self._zoom(-0.5))
        m.addSeparator()
        lang_menu = m.addMenu("언어 / Language(&L)")
        lang_group = QActionGroup(self)
        lang_group.setExclusive(True)
        for code, label in (("ko", "한국어"), ("en", "English")):
            a = lang_menu.addAction(label)
            a.setCheckable(True)
            a.setChecked(ui_language() == code)
            a.triggered.connect(lambda _=False, c=code: self.set_ui_language(c))
            lang_group.addAction(a)

        m = self.menuBar().addMenu("도움말(&H)")
        act(m, "ndhmdWriter 정보 / 단축키(&H)", "F1", self.open_help)
        act(m, "Reference Manual(&R)", None, lambda: self.open_guide("manual"))
        m.addSeparator()
        guide_menu = m.addMenu("ndhmarkdown")
        act(guide_menu, "사양서(&S)", None, lambda: self.open_guide("guide"))
        act(guide_menu, "치트시트(&C)", None, lambda: self.open_guide("cheatsheet"))

    def set_ui_language(self, code: str):
        """화면 언어를 저장한다. 메뉴·대화상자 글은 만들 때 정해지므로
        다시 시작해야 적용된다(실행 중 바꾸기는 하지 않는다)."""
        if code == ui_language():
            return
        QSettings(self.ORG, self.APP).setValue("ui/language", code)
        QMessageBox.information(
            self, "Language / 언어",
            "언어를 바꿨습니다. ndhmdWriter 를 다시 시작하면 적용됩니다.\n"
            "Language changed. Restart ndhmdWriter to apply it.")

    def _build_status(self):
        bar = QStatusBar()
        self._ws_label = QLabel()
        self._env_label = QLabel()
        self._pos_label = QLabel()
        bar.addPermanentWidget(self._ws_label)
        bar.addPermanentWidget(self._env_label)
        bar.addPermanentWidget(self._pos_label)
        self.setStatusBar(bar)
        self._update_status()

    # -- 작업공간 -----------------------------------------------------------

    def choose_workspace(self):
        start = str(self.workspace.root) if self.workspace else str(Path.home())
        name = QFileDialog.getExistingDirectory(self, "작업공간 폴더 선택", start)
        if not name:
            return
        self.switch_workspace(Path(name))

    def switch_workspace(self, root: Path):
        """다른 작업공간으로 전환한다 — 작업공간 열기 대화상자와
        [파일] ▸ 작업공간 이력 메뉴가 둘 다 이걸 부른다."""
        if not self.confirm_discard_all("작업공간 전환"):
            return
        self.workspace = Workspace(root)
        self._settings.setValue("workspace/root", str(self.workspace.root))
        self.index = BookIndex(self.workspace)
        self.tags = TagStore(self.workspace)
        self.notes = NoteStore(self.workspace)
        self.synopsis = SynopsisStore(self.workspace)
        self.slots = SlotStore(self.workspace, self._settings)
        self.tag_bar.set_tags([])
        self._path = None
        self.editor.setPlainText("")
        self._dirty = False
        self._refresh_result_action()
        self.close_find()
        self._update_title()
        self._update_status()
        self.refresh_drawer()
        self._record_recent_workspace(self.workspace.root)
        self.statusBar().showMessage(
            f"작업공간: {self.workspace.root}  (원고 "
            f"{sum(1 for _ in self.workspace.source_files())}개)", 6000)

    def _record_recent_workspace(self, root: Path):
        """방금 연 작업공간을 이력 맨 앞에 올린다. 이미 있었으면 그
        자리에서 빼고 다시 맨 앞에 둔다(중복 없이 최신순). 10개까지만
        남긴다."""
        recent = self._settings.value("workspace/recent", [], type=list)
        root_str = str(root)
        recent = [r for r in recent if r != root_str]
        recent.insert(0, root_str)
        self._settings.setValue("workspace/recent", recent[:10])

    def _populate_workspace_history_menu(self):
        """[파일] ▸ 작업공간 이력 서브메뉴를 열 때마다 다시 채운다 —
        그래야 방금 전환한 작업공간도 바로 반영된다."""
        menu = self._workspace_history_menu
        menu.clear()
        recent = self._settings.value("workspace/recent", [], type=list)
        if not recent:
            empty_act = menu.addAction("(최근 연 작업공간 없음)")
            empty_act.setEnabled(False)
            return
        for root_str in recent:
            root = Path(root_str)
            label = root_str if root.is_dir() else f"{root_str} (없음)"
            act = menu.addAction(label)
            act.setEnabled(root.is_dir())
            act.triggered.connect(lambda checked=False, r=root: self.switch_workspace(r))
        menu.addSeparator()
        menu.addAction("이력 지우기").triggered.connect(self._clear_workspace_history)

    def _clear_workspace_history(self):
        self._settings.setValue("workspace/recent", [])

    def reveal_in_file_manager(self, path: Path):
        """서랍 우클릭 ▸ 탐색기/파인더에서 보기.

        폴더만 여는 게 아니라 그 파일을 골라서 보여준다 — macOS 는
        `open -R`, Windows 는 `explorer /select,`가 정확히 이 일을
        한다. 리눅스는 이런 동작을 표준으로 정해 둔 게 없어서(데스크톱
        환경마다 다르다) 폴더를 여는 것으로 물러난다.

        Windows 쪽은 QProcess.startDetached() 를 안 쓴다. 그 함수는
        인자 목록을 자기 방식대로 다시 따옴표 처리해서 넘기는데,
        explorer.exe 의 `/select,"경로"` 구문은 따옴표 없이 매끄럽게
        이어붙인 원래 형태를 그대로 받아야 한다 — 한 번 더 감싸이면
        explorer 가 그 인자를 못 알아듣고 조용히 기본 폴더(문서)로
        물러난다. 어떤 파일을 골라도 항상 "문서" 폴더만 열리는 증상이
        정확히 이것이다. subprocess 로 raw 명령줄 문자열을 셸에 그대로
        넘기면 재처리 없이 원래 형태 그대로 전달된다.
        """
        if not path.exists():
            self.statusBar().showMessage(f"파일을 찾지 못했습니다: {path}", 6000)
            return
        if sys.platform == "darwin":
            QProcess.startDetached("open", ["-R", str(path)])
        elif sys.platform == "win32":
            subprocess.Popen(f'explorer /select,"{path}"', shell=True,
                             creationflags=_NO_WINDOW)
        else:
            QDesktopServices.openUrl(QUrl.fromLocalFile(str(path.parent)))

    def peek_file(self, path: Path):
        """자료 창고·하위 폴더 항목을 편집창에 안 띄우고 내용만
        훑어본다. 매번 새 창으로 연다 — 여러 개를 동시에 훑어봐도
        서로 안 헷갈리게."""
        dlg = FilePeekDialog(self, path)
        dlg.show()

    def move_to_workspace_root(self, path: Path):
        """자료 창고·하위 폴더 항목을 작업공간 최상위로 옮긴다.
        "폴더로 이동"(임의의 다른 폴더 하나를 골라 옮기는 것)은 이제
        지원하지 않는다 — 그럴 일이 있으면 파인더/탐색기로 직접
        옮기면 된다. 여기서는 "밖으로 완전히 꺼내는" 이 한 가지
        방향만 다룬다."""
        target = self.workspace.root / path.name
        if target.exists():
            r = QMessageBox.question(
                self, "작업공간으로 이동",
                f"작업공간에 이미 '{path.name}' 이(가) 있습니다. 덮어쓸까요?",
                QMessageBox.Yes | QMessageBox.Cancel)
            if r != QMessageBox.Yes:
                return
        try:
            shutil.move(str(path), str(target))
        except OSError as e:
            QMessageBox.warning(self, "작업공간으로 이동", f"옮기지 못했습니다: {e}")
            return
        self.refresh_drawer()
        self.statusBar().showMessage(f"{path.name} → 작업공간 최상위", 4000)

    def move_to_assets(self, path: Path):
        """서랍의 원고·부속 파일을 "자료 창고"(_assets/)로 옮긴다 —
        move_to_workspace_root() 의 반대 방향이다. 자료 창고 자체는 이
        앱이 관리하는 고정 자리라, "있는 폴더로만" 이라는 제약 없이
        없으면 만든다. {{}} 로 포함돼 있었으면(장이었으면) 삭제 때와
        같이 부모에서 먼저 뗀다 — 안 그러면 죽은 포함이 남는다.
        지금 열려 있는 파일을 옮기면 편집 상태를 정리한다 — 자료
        창고 안 파일은 이 앱에서 다시 여는 대상이 아니다.
        """
        assets_dir = self.workspace.root / Workspace.ASSETS_DIR
        target = assets_dir / path.name
        if target.exists():
            r = QMessageBox.question(
                self, "자료 창고로 이동",
                f"자료 창고에 이미 '{path.name}' 이(가) 있습니다. 덮어쓸까요?",
                QMessageBox.Yes | QMessageBox.Cancel)
            if r != QMessageBox.Yes:
                return

        node = self.index.by_path.get(path)
        if node is not None and node.parent is not None:
            self._detach(path)

        try:
            assets_dir.mkdir(exist_ok=True)
            shutil.move(str(path), str(target))
        except OSError as e:
            QMessageBox.warning(self, "자료 창고로 이동", f"옮기지 못했습니다: {e}")
            return

        self.tags.set(path, [])
        if self._path == path:
            self._clear_editor_state()
        self.refresh_drawer()
        self.refresh_labels()
        self.refresh_toc()
        self.statusBar().showMessage(f"{path.name} → {Workspace.ASSETS_DIR}/", 4000)

    def _redirect_into_export_dir(self, chosen: Path) -> Path:
        """내보내기 목적지가 작업공간 "안"이면 _export/ 로 통째로
        돌린다 — 정확히 어디를 골랐는지는 안 따지고, 작업공간 밖이
        아니면 무조건 _export/ 밑으로 모은다(원고 파일들 사이에
        내보낸 결과물이 흩어지지 않게)."""
        if not self.workspace:
            return chosen
        try:
            chosen.resolve().relative_to(self.workspace.root.resolve())
        except ValueError:
            return chosen   # 작업공간 밖 -- 고른 그대로 쓴다
        export_root = self.workspace.root / Workspace.EXPORT_DIR
        try:
            chosen.resolve().relative_to(export_root.resolve())
            return chosen   # 이미 _export 안 -- 그대로
        except ValueError:
            return export_root / chosen.name

    def export_as_one_file(self):
        """[파일] ▸ 내보내기 ▸ 한 개 파일로 내보내기.

        md 로만 내보내는 것이므로(docx 같은 다른 형식으로 바꾸는 게
        아니다) 항상 책 전체 기준이다 — {{}} 로 이어지는 포함을
        몇 겹이든 전부 풀어 파일 하나로 병합한다.
        """
        if self._path is None:
            QMessageBox.information(self, "내보내기", "먼저 원고를 열어 주세요.")
            return
        if not self.confirm_discard_all("내보내기"):
            return
        root_file = LabelIndex.book_files(self.index, self._path)[0]
        try:
            text = read_manuscript(root_file)
        except (OSError, UnicodeDecodeError) as e:
            QMessageBox.warning(self, "내보내기", f"{root_file.name} 을(를) 읽지 못했습니다: {e}")
            return
        merged, missing = flatten_all_includes(text, root_file.parent)

        default_name = root_file.stem + "_export.md"
        start_dir = str(self.workspace.root / default_name) if self.workspace else default_name
        chosen, _ = QFileDialog.getSaveFileName(
            self, "한 개 파일로 내보내기", start_dir, "마크다운 (*.md)")
        if not chosen:
            return
        dest = self._redirect_into_export_dir(Path(chosen))
        try:
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_text(merged, encoding="utf-8")
        except OSError as e:
            QMessageBox.warning(self, "내보내기", f"쓰지 못했습니다: {e}")
            return

        msg = f"내보냈습니다: {dest}"
        if missing:
            msg += "\n\n못 찾았거나 순환 포함이라 그대로 남은 것: " + ", ".join(missing)
        QMessageBox.information(self, "내보내기", msg)

    def export_as_chapter_files(self):
        """[파일] ▸ 내보내기 ▸ 장별 파일로 내보내기.

        ndhmd4tex 이 그대로 처리할 수 있는 정도로만 내보낸다 — 책
        루트는 그대로 두어({{}} 로 장을 가리키는 구조를 유지) 파일이
        분리된 채 남고, 각 장(1단계)에는 자신의 하위(2단계)를 병합해
        넣는다. 2단계 파일 자신은 따로 내보내지 않는다 — 병합 대상
        이지 독립 파일이 아니다("모든 파일을 낱개로 내보내는" 동작은
        만들지 않는다).
        """
        if self._path is None:
            QMessageBox.information(self, "내보내기", "먼저 원고를 열어 주세요.")
            return
        if not self.confirm_discard_all("내보내기"):
            return
        files = LabelIndex.book_files(self.index, self._path)
        root_path = files[0]

        start_dir = str(self.workspace.root) if self.workspace else ""
        chosen_dir = QFileDialog.getExistingDirectory(
            self, "장별 파일로 내보낼 폴더", start_dir)
        if not chosen_dir:
            return
        dest_dir = self._redirect_into_export_dir(Path(chosen_dir))

        missing_all = []
        written = []
        try:
            dest_dir.mkdir(parents=True, exist_ok=True)
            for path in files:
                node = self.index.by_path.get(path)
                if path == root_path:
                    # 책 루트 -- 그대로(장을 가리키는 {{}} 구조를 유지).
                    try:
                        text = read_manuscript(path)
                    except (OSError, UnicodeDecodeError):
                        continue
                    (dest_dir / path.name).write_text(text, encoding="utf-8")
                    written.append(path.name)
                elif node is not None and node.parent == root_path:
                    # 1단계(장) -- 자신의 2단계를 병합해 넣는다.
                    merged, missing = self._merge_own_children(node)
                    missing_all.extend(missing)
                    (dest_dir / path.name).write_text(merged, encoding="utf-8")
                    written.append(path.name)
                # 그 외(2단계)는 따로 안 내보낸다 -- 부모 장에 이미 병합됐다.
        except OSError as e:
            QMessageBox.warning(self, "내보내기", f"쓰지 못했습니다: {e}")
            return

        msg = (f"{dest_dir} 에 {len(written)}개 파일을 내보냈습니다:\n"
              + "\n".join(f"  · {n}" for n in written))
        if missing_all:
            msg += "\n\n못 찾았거나 순환 포함이라 그대로 남은 것: " + ", ".join(missing_all)
        QMessageBox.information(self, "내보내기", msg)

    def _merge_own_children(self, node: "Node"):
        """node(1단계 파일) 자신의 {{}} 자식(2단계)만 골라 병합한다.
        node.children(이미 검증된, 진짜 자식 목록)에 있는 이름만
        펴고, 그 밖의 {{이름}}(엉뚱한 걸 가리키는 경우)은 그대로
        둔다.
        """
        try:
            text = read_manuscript(node.path)
        except (OSError, UnicodeDecodeError):
            return "", []
        missing = []
        child_names = {c.name for c in node.children}

        def repl(m):
            name = m.group(1).strip()
            if name not in child_names:
                return m.group(0)   # node 의 자식이 아니면 그대로 둔다
            target = (node.path.parent / name).resolve()
            try:
                sub_text = read_manuscript(target)
            except (OSError, UnicodeDecodeError):
                missing.append(name)
                return m.group(0)
            return FRONTMATTER_RE.sub("", sub_text, count=1)

        merged = INCLUDE_RE.sub(repl, text)
        return merged, missing

    def reveal_workspace(self):
        """파일 ▸ 작업공간 폴더 보기.

        그냥 보여주기 전에 죽은 상태부터 정리한다 — 저장 안 된 편집
        캐시나 태그가 이제 존재하지 않는 파일을 계속 가리키고 있을 수
        있다(작업공간 밖에서 파일이 지워지거나 옮겨진 경우). 지우는 건
        캐시·태그 항목뿐이고, 진짜 저장 안 된 편집(아직 파일이 살아있는
        것)은 안 건드린다.
        """
        if not self._require_workspace():
            return

        stale_docs = [p for p in list(self._dirty_docs) if not p.is_file()]
        for p in stale_docs:
            self._dirty_docs.pop(p, None)
        stale_cursor = [p for p in list(self._cursor_memory) if not p.is_file()]
        for p in stale_cursor:
            self._cursor_memory.pop(p, None)
        removed_tags = self.tags.prune()
        removed_notes = self.notes.prune() + self.synopsis.prune()

        total_files = sum(1 for _ in self.workspace.source_files())
        pending = len(self.pending_saves())

        lines = [
            str(self.workspace.root), "",
            f"원고 {total_files}개",
            f"저장하지 않은 편집 {pending}개",
        ]
        cleaned = len(stale_docs) + len(stale_cursor) + removed_tags + removed_notes
        if cleaned:
            lines.append(
                f"정리함 — 죽은 캐시 {len(stale_docs) + len(stale_cursor)}개, "
                f"죽은 태그 {removed_tags}개, 죽은 메모 {removed_notes}개")

        box = QDialog(self)
        box.setWindowTitle("작업공간")
        label = QLabel("\n".join(lines))
        open_btn = QPushButton("열기")
        close_btn = QPushButton("닫기")
        close_btn.setDefault(True)
        open_btn.clicked.connect(box.accept)
        close_btn.clicked.connect(box.reject)

        btn_row = QHBoxLayout()
        btn_row.addStretch(1)
        btn_row.addWidget(open_btn)
        btn_row.addWidget(close_btn)

        v = QVBoxLayout(box)
        v.addWidget(label)
        v.addLayout(btn_row)

        if box.exec() == QDialog.Accepted:
            # reveal_in_file_manager() 는 "이 파일을 그 부모 폴더 안에서
            # 골라 보여주기" 용이라 폴더 자체엔 안 맞는다 — 여기서는
            # 그 폴더의 내용을 그냥 연다.
            QDesktopServices.openUrl(QUrl.fromLocalFile(str(self.workspace.root)))

    def _require_workspace(self) -> bool:
        """작업공간이 없으면 먼저 고르게 한다."""
        if self.workspace:
            return True
        QMessageBox.information(
            self, "작업공간이 필요합니다",
            "열기·저장·찾기는 작업공간 안에서만 이루어집니다.\n"
            "먼저 작업공간 폴더를 지정해 주세요.")
        self.choose_workspace()
        return bool(self.workspace)

    def _guard_inside(self, path: Path) -> bool:
        if self.workspace.contains(path):
            return True
        QMessageBox.warning(
            self, "작업공간 밖입니다",
            f"원고는 작업공간 안에만 둘 수 있습니다.\n\n"
            f"작업공간: {self.workspace.root}\n선택한 경로: {path}")
        return False

    # -- 파일 ---------------------------------------------------------------

    def new_file(self):
        if not self._require_workspace():
            return
        name, ok = QInputDialog.getText(
            self, "새 원고", "파일 이름:", text="새 원고.md")
        if not ok or not name.strip():
            return
        name = name.strip()
        if not name.lower().endswith(Workspace.SUFFIXES):
            name += ".md"
        path = self.workspace.root / name
        if not self._guard_inside(path):
            return
        if path.exists():
            QMessageBox.warning(self, "이미 있습니다", f"{name} 이(가) 이미 있습니다.")
            return
        try:
            path.write_text("", encoding="utf-8")
        except OSError as e:
            QMessageBox.warning(self, "만들기 실패", str(e))
            return
        self.open_path(path)

    def import_file(self):
        """[파일] ▸ 들여오기 — 작업공간 밖에 있는 원고 파일(.txt/.md/
        .nmd/.mmd)을 작업공간 안으로 복사해 들여온다. "열기"와
        비슷하지만, 고른 파일을 제자리에서 여는 게 아니라 작업공간
        최상위로 복사한 뒤 그 복사본을 연다."""
        if not self._require_workspace():
            return
        pattern = " ".join(f"*{s}" for s in Workspace.SUFFIXES)
        start_dir = str(self.workspace.root.parent) if self.workspace.root.parent.is_dir() \
            else str(Path.home())
        name, _ = QFileDialog.getOpenFileName(
            self, "들여오기", start_dir, f"원고 ({pattern})")
        if not name:
            return
        src = Path(name)
        if self.workspace.contains(src):
            QMessageBox.information(self, "들여오기", "이미 작업공간 안에 있는 파일입니다.")
            return
        dest = self.workspace.root / src.name
        if dest.exists():
            new_name, ok = QInputDialog.getText(
                self, "들여오기",
                f"작업공간에 이미 '{src.name}' 이(가) 있습니다.\n다른 이름으로 들여올 이름:",
                text=src.name)
            if not ok or not new_name.strip():
                return
            dest = self.workspace.root / new_name.strip()
            if not dest.suffix:
                dest = dest.with_suffix(src.suffix)
            if dest.exists():
                QMessageBox.warning(self, "들여오기", f"{dest.name} 이(가) 이미 있습니다.")
                return
        try:
            shutil.copy2(str(src), str(dest))
        except OSError as e:
            QMessageBox.warning(self, "들여오기", f"복사하지 못했습니다: {e}")
            return
        self.refresh_drawer()
        self.open_path(dest)
        self.statusBar().showMessage(f"{src.name} 을(를) 작업공간으로 들여왔습니다.", 4000)

    def open_file(self):
        if not self._require_workspace():
            return
        name, _ = QFileDialog.getOpenFileName(
            self, "열기", str(self.workspace.root),
            Workspace.name_filter())
        if not name:
            return
        path = Path(name)
        if self._guard_inside(path):
            if self._path is None or path.resolve() != self._path:
                self._close_doc_tools()
            self.open_path(path)

    def _new_document(self, text: str) -> QTextDocument:
        """QPlainTextEdit 에 물릴 새 문서를 만든다.

        그냥 QTextDocument() 로 만들면 QPlainTextDocumentLayout 이 안
        붙어서 QPlainTextEdit.setDocument() 에 넘겼을 때 경고가 뜨고
        레이아웃이 어긋난다 — 실행 취소가 안 먹거나 내용이 안 갱신되는
        것처럼 보이는 등 증상이 다양하게 나타난다.

        부모는 self.editor 가 아니라 self(MainWindow) 로 둔다. 편집창을
        부모로 주면 Qt 가 "이 위젯의 자식이던 문서니 다른 문서로 바뀌면
        필요 없겠지" 하고 setDocument() 호출 시 옛 문서를 자동으로
        지워 버린다 — _dirty_docs 에 파이썬 참조를 들고 있어도 그 밑의
        C++ 객체가 이미 죽어 있으면 소용없다. MainWindow 는 편집창의
        "현재 문서"가 바뀌는 것과 무관하게 계속 살아있으므로 이 문제가
        없다.

        마지막으로 clearUndoRedoStack() 을 불러서, 본문을 채운 것은
        아예 되돌릴 거리에도 안 들어가게 한다 — 사용자가 아직 아무것도
        안 쳤는데 Ctrl+Z 가 먹는 것도 이상하다.

        (행간을 QTextBlockFormat.setLineHeight() 로 넓히는 시도를 한
        적이 있었는데, QPlainTextEdit 은 이 서식을 아예 무시한다 —
        QTBUG-51891, Qt 5.3부터 미해결. QTextEdit 로 바꾸면 되지만 이
        앱의 거터·접기 기능이 QPlainTextEdit 전용 API 에 의존하고
        있어 그 정도까지는 하지 않기로 했다.)
        """
        doc = QTextDocument(self)
        doc.setDocumentLayout(QPlainTextDocumentLayout(doc))
        doc.setPlainText(text)
        doc.clearUndoRedoStacks()
        return doc

    def load(self, path: Path):
        """디스크에서 새로 읽어 온다 — 항상 새 QTextDocument 로 시작한다.

        내부적으로 우리 자신이 방금 파일을 고쳐서(포함 줄 재배열, 이름
        변경 등) 다시 반영해야 할 때 쓰는 경로이기도 하다. 그런 경우는
        "다른 파일로 옮겨간다"가 아니라 "이 파일이 바뀌었으니 다시
        본다"이므로 open_path() 의 캐시·커서기억 로직을 타지 않는다.
        """
        try:
            text, enc = read_manuscript_ex(path)
        except (OSError, UnicodeDecodeError) as e:
            QMessageBox.warning(self, "열기 실패", str(e))
            return
        self._src_enc[path.resolve()] = enc
        self._attach_document(path.resolve(), self._new_document(text), dirty=False)

    def _attach_document(self, path: Path, doc: QTextDocument, dirty: bool):
        """편집창에 문서를 물리고, load() 가 하던 뒷정리를 전부 한다.

        setDocument() 자신은 물론, 뒤이은 여백·행간 재계산도 문서 서식을
        건드려 textChanged 를 또 쏜다 — 게다가 한 번에 끝나지 않고
        지연되어 나중에 한 번 더 새기도 한다(Qt 내부 사정으로 보인다).
        _switching_document 가드는 동기적으로 오는 것만 잡아 준다.

        그래서 진짜 안전망은 _baseline_text 비교다. _mark_dirty() 가
        실제로 글자가 기준과 달라졌는지까지 확인하므로, 신호가 몇 번을
        새든 포맷팅만 바뀐 거라면 절대 dirty 로 등록되지 않는다.
        """
        self._remember_last_file(path, 1)
        self._switching_document = True
        try:
            self.editor.setDocument(doc)
            self.editor.highlighter.set_kind(NdhmdHighlighter.kind_for_path(path))
            self.editor.highlighter.setDocument(doc)
            self.editor.clear_search_matches()
            self._clear_scope()
            if self.find_bar.is_selection():           # 범위가 속한 문서를 떠났다 — 현재 파일로 돌린다
                self.find_bar.scope.blockSignals(True)
                self.find_bar.scope.setCurrentIndex(FindBar.SCOPE_FILE)
                self.find_bar.scope.blockSignals(False)
        finally:
            self._switching_document = False
        # 폰트·탭 너비는 위젯 속성이라 문서를 바꿔도 원래 안 풀린다(직접
        # 확인함). 그래도 값싸고 안전망이 되니 여기서도 한 번 더 걸어
        # 둔다 — setFont()/setTabStopDistance() 는 textChanged 를 안
        # 쏘니 방금 고친 스퓨리어스 dirty 문제와도 무관하다.
        self.editor._apply_font(self.prefs.font_family(), self.prefs.font_size())
        # rehighlight 는 서식만 바꿔도 textChanged 를 쏜다. 아직 _path/_baseline_text 가
        # 이전 파일 것이므로 가드 없이 걸면 새 문서가 "이전 파일의 미저장 편집"으로
        # 캐시(_dirty_docs)에 잘못 들어간다.
        self._switching_document = True
        try:
            self._apply_item_gap(force=True)
        finally:
            self._switching_document = False
        self.editor.apply_tab_spaces(self.prefs.tab_spaces())
        self.editor.tab_to_spaces_enabled = self.prefs.tab_to_spaces()
        self.editor.smart_quotes_style = self.prefs.smart_quotes_style()
        self.editor.smart_punctuation = self.prefs.smart_punctuation()
        # 문서 여백(documentMargin)은 위젯이 아니라 문서 자신의 속성이라,
        # 새 문서는 항상 Qt 기본값(4.0)으로 시작한다 — 우리가 계산해 둔
        # 값은 리사이즈나 blockCountChanged 가 일어나야 다시 걸린다.
        # 창 크기가 안 바뀌는 상황(파일 전환 등)에서는 뭔가 그걸
        # 우연히 건드리기 전까지 여백이 어긋난 채로 남는다 — 실제로
        # 보고된 증상("타이핑해야 제자리를 찾아간다")이 정확히 이것이다.
        # 여기서 매번 직접 다시 계산해 바로 건다.
        self.editor._relayout_text_column()
        self._path = path
        self._dirty = dirty
        self._baseline_text = doc.toPlainText()
        self._update_title()
        self._update_status()
        self._refresh_result_action()
        self._sync_fold_action()
        self.editor.set_bibliography_folded(True)   # 있으면 접고, 없으면 조용히 무시된다
        self._sync_note_panel()
        self.tag_bar.set_tags(self.tags.get_active(self._path, self._live_reader))
        self.refresh_drawer()
        self.refresh_labels()
        self.refresh_toc()
        if getattr(self, "_image_import_panel", None) is not None \
                and self._image_import_panel.isVisible():
            self._image_import_panel.refresh()
        if getattr(self, "_bib_dialog", None) is not None \
                and self._bib_dialog.isVisible():
            self._bib_dialog.load_from_document()
        self._preview_key = None
        self._schedule_preview()
        if self.find_bar.isVisible() and not self.find_bar.is_workspace():
            self.on_query_changed()

    def open_path(self, path: Path, line: int | None = None):
        """다른 파일로 옮겨간다 — 저장 여부를 묻지 않는다.

        지금 파일이 깨끗하면 커서 줄만 기억해 두고, 미저장 편집이
        있으면(_dirty_docs 에 이미 들어 있다 — _mark_dirty() 가 실시간
        으로 등록해 둔다) 그 문서 객체를 그대로 들고 다른 파일로 넘어간다.
        나중에 다시 이 파일을 열면 _dirty_docs 에서 그대로 찾아 쓰므로
        실행 취소 이력도 살아있다.

        다만 지금이 "이름 없는" 편집 상태(self._path 가 None — 맨 처음
        빈 편집창에 뭔가 쓴 경우)라면 이 캐시 매커니즘 자체가 안 통한다.
        경로가 없으니 무엇으로 키를 잡을 수도 없다. 그래서 이 경우만은
        여기서 결판을 낸다 — 그냥 넘어가면 그 편집은 영영 사라진다.
        """
        if self._path is None and self._has_unsaved():
            if not self._resolve_untitled_before_leaving():
                return

        path = path.resolve()
        if self._path is not None and self._path == path:
            if line is not None:
                self.editor.goto_file_line(line)
            self.editor.setFocus()
            return
        if self._path is not None:
            self._cursor_memory[self._path] = self.editor.textCursor().blockNumber()

        cached = self._dirty_docs.get(path)
        if cached is not None:
            self._attach_document(path, cached, dirty=True)
        else:
            if not path.exists():
                self.statusBar().showMessage(f"파일을 찾지 못했습니다: {path}", 6000)
                return
            try:
                text, enc = read_manuscript_ex(path)
            except (OSError, UnicodeDecodeError) as e:
                QMessageBox.warning(self, "열기 실패", str(e))
                return
            self._src_enc[path] = enc
            self._attach_document(path, self._new_document(text), dirty=False)
            self._announce_source_encoding(path, enc)

        target_line = line if line is not None else self._cursor_memory.get(path, 0) + 1
        self.editor.goto_file_line(target_line)
        self.editor.setFocus()

    def _resolve_untitled_before_leaving(self) -> bool:
        """이름 없는 편집 상태(self._path 가 None)에 뭔가 써 있는데 다른
        파일로 넘어가려 한다. 경로가 없어 다른 파일들처럼 캐시해 둘 수도
        없으니, 새 원고를 만들 때처럼 여기서 이름을 정해 저장할지
        결판을 낸다. 취소하면 False — 호출한 쪽은 이동을 그만둬야 한다.
        """
        r = QMessageBox.question(
            self, "저장하지 않은 원고",
            "지금 쓰신 내용에 아직 이름이 없습니다. 다른 파일을 열기 전에 "
            "저장할까요?",
            QMessageBox.Save | QMessageBox.Discard | QMessageBox.Cancel)
        if r == QMessageBox.Cancel:
            return False
        if r == QMessageBox.Discard:
            return True
        return self.save_file_as()

    def pending_saves(self) -> list:
        """지금 어딘가에 미저장 편집이 남아 있는 파일들. 컴파일/닫기 같은
        관문에서 한꺼번에 확인할 때 쓴다."""
        return [p for p, d in self._dirty_docs.items()
               if bool(d.toPlainText().strip())]

    def confirm_discard_all(self, what: str) -> bool:
        """여러 파일에 걸친 미저장 편집을 한 번에 확인한다.

        개별 파일마다 따로 물으면 번거롭다 — 목록을 보여주고 한 번에
        저장하거나, 계속 진행하거나, 취소한다.

        이름 없는 편집 상태는 _dirty_docs 에 안 잡히므로(경로가 없다)
        따로 먼저 처리한다.
        """
        if self._path is None and self._has_unsaved():
            r = QMessageBox.question(
                self, "저장하지 않은 원고",
                f"{what} 전에, 아직 이름이 없는 지금 편집 내용을 저장할까요?",
                QMessageBox.Save | QMessageBox.Discard | QMessageBox.Cancel)
            if r == QMessageBox.Cancel:
                return False
            if r == QMessageBox.Save and not self.save_file_as():
                return False

        pending = self.pending_saves()
        if not pending:
            return True
        names = "\n".join(f"  · {self.workspace.relative(p)}" for p in pending[:10])
        r = QMessageBox.question(
            self, "저장하지 않은 원고",
            f"{what} 전에 다음 원고를 저장할까요?\n\n{names}\n\n"
            + (f"저장하지 않고 종료하면 그 편집은 사라집니다."
             if what == "앱 종료" else
             f"저장하지 않으면 그 편집은 앱을 여는 동안에는 남아 있지만,\n"
             f"이 작업에는 반영되지 않습니다."),
            QMessageBox.Save | QMessageBox.Discard | QMessageBox.Cancel)
        if r == QMessageBox.Cancel:
            return False
        if r == QMessageBox.Discard:
            return True
        # 저장 — 지금 열려 있는 파일 포함, 전부 디스크에 쓴다.
        failed = []
        for p in list(pending):
            if p == self._path:
                if not self.save_file():
                    failed.append(p.name)
                continue
            doc = self._dirty_docs.get(p)
            if doc is None:
                continue
            if not self._confirm_encoding_change(p):
                failed.append(p.name)
                continue
            try:
                p.write_text(doc.toPlainText(), encoding="utf-8")
                self._src_enc[p.resolve()] = "utf-8"
                self._dirty_docs.pop(p, None)
            except OSError:
                failed.append(p.name)
        self.refresh_toc()      # 열려 있지 않던 파일들도 디스크에 써졌다
        if failed:
            QMessageBox.warning(self, "일부 저장 실패", "\n".join(failed))
            return False
        return True

    # -- 서랍 -----------------------------------------------------------------

    def handle_card_drop_on_drawer(self, paths: list, target):
        """카드 보기의 카드를 서랍에 떨어뜨렸을 때. 항목 위면 그 항목 아래로 넣고, 빈 곳이면 책에서 뺀다.
        책 뿌리(맨 첫 카드)는 옮기지 않는다."""
        srcs = []
        for p in paths:
            node = self.index.by_path.get(p)
            if node is not None and node.parent is not None:
                srcs.append(p)
        if not srcs:
            return
        if target is None:
            self.handle_drawer_drop_multi(srcs, None, False, True)
        else:
            self.handle_drawer_drop_multi(srcs, target, True, False)

    def refresh_drawer(self):
        self._refresh_drawer_impl()
        dlg = getattr(self, "_cards_dialog", None)
        if dlg is not None and dlg.isVisible():
            dlg.structure_maybe_changed()

    def _refresh_drawer_impl(self):
        """파일에서 구조를 다시 읽어 서랍을 그린다.

        화면을 먼저 고치고 파일을 나중에 맞추는 일이 없도록, 어떤 변경이든
        끝나면 항상 이 함수로 되돌아온다. 진실은 언제나 {{}} 줄이다.
        """
        if not self.workspace:
            self.drawer.tree.clear()
            return
        self.tags.prune()
        self.drawer.refresh_tags()
        roots = self.index.scan()
        if self.prefs.drawer_sort() == "mtime":
            def _mtime_key(node):
                try:
                    return node.path.stat().st_mtime
                except OSError:
                    return 0
            roots = sorted(roots, key=_mtime_key, reverse=True)
        needle = self.drawer.filter.text().strip()

        tree = self.drawer.tree
        tree.blockSignals(True)
        tree.clear()
        current = self._path

        def keep(path: Path) -> bool:
            if not needle:
                return True
            tokens = needle.split()
            tag_tokens = [t for t in tokens if t.startswith("#")]
            if tag_tokens and len(tag_tokens) == len(tokens):
                # 전부 #태그 토큰이면(콤보에서 태그를 이어 골랐을 때
                # 생기는 모양 — "#초고 #검토") OR 로 묶어, 하나라도
                # 걸리면 통과시킨다. 태그 하나뿐이어도 이 경로를 타고
                # 결과는 그대로다(기존 동작과 같다).
                return any(self.tags.matches(path, t) for t in tag_tokens)
            low = needle.lower()
            return (low in path.name.lower()
                    or self.tags.matches(path, needle))

        match_cache = {}

        def subtree_matches(node) -> bool:
            """node 자신이나 그 자손(재귀, 몇 단계든) 중 하나라도
            필터에 걸리면 True다 — 필터링된 트리에서 "자손 중에 걸리는
            게 있으면 그 조상도 보여준다"는 규칙을, 2단계까지 있는
            지금 구조에서도 제대로 적용하려면 한 단계만 봐서는 안
            된다(예전엔 장까지만 봐서, 태그가 2단계 파일에만 있으면
            그 장 자체가 안 걸려 통째로 안 보였다)."""
            if node.path in match_cache:
                return match_cache[node.path]
            result = keep(node.path)
            if not result:
                for child_path in node.children:
                    child_node = self.index.by_path.get(child_path)
                    if child_node is not None and subtree_matches(child_node):
                        result = True
                        break
            match_cache[node.path] = result
            return result

        for node in roots:
            node_matches = keep(node.path)
            if not node_matches and not subtree_matches(node):
                continue
            top = QTreeWidgetItem(tree, [self._drawer_label(node)])
            top.setData(0, Qt.UserRole, str(node.path))
            top.setFlags(top.flags() | Qt.ItemIsDropEnabled | Qt.ItemIsDragEnabled)
            self._mark_nmd_item(top, node.path)

            def add_book_child(parent_item, child_path, force_show):
                """장(1단계)이든 그 하위(2단계)든 같은 방식으로 그린다
                — {{}} 로 몇 단계든 표현되므로 재귀로 충분하다(이
                앱은 can_nest() 로 2단계까지만 만들어지게 막는다).

                force_show 가 True 면(조상 쪽이 이미 필터에 걸려서
                그 밑 전체를 보여주기로 한 경우) 자신도 무조건
                보여준다 — 안 그러면 자기 자신이나 자손 중 하나가
                걸릴 때만 보여준다.
                """
                child_node = self.index.by_path.get(child_path)
                if child_node is None:
                    return
                self_matches = keep(child_path)
                if not force_show and not self_matches and not subtree_matches(child_node):
                    return
                it = QTreeWidgetItem(parent_item, [self._drawer_label(child_node)])
                it.setData(0, Qt.UserRole, str(child_path))
                # 장도 하위 항목도 전부 드롭을 받는다 — 그 위에 놓으면
                # 그 항목의 자식(한 단계 더)으로 붙는다.
                it.setFlags(it.flags() | Qt.ItemIsDragEnabled | Qt.ItemIsDropEnabled)
                self._mark_nmd_item(it, child_path)
                if current and child_path == current:
                    tree.setCurrentItem(it)
                show_all_children = force_show or self_matches
                for grandchild in child_node.children:
                    add_book_child(it, grandchild, show_all_children)
                it.setExpanded(str(child_path) not in self._collapsed_books)

            for child in node.children:
                add_book_child(top, child, node_matches)
            top.setExpanded(str(node.path) not in self._collapsed_books)
            if current and node.path == current:
                tree.setCurrentItem(top)

        note_paths = list(self.workspace.reference_files())
        if note_paths:
            sep_n = QTreeWidgetItem(tree)
            sep_n.setFlags(Qt.NoItemFlags)
            line_n = QFrame()
            line_n.setFrameShape(QFrame.HLine)
            line_n.setFrameShadow(QFrame.Sunken)
            tree.setItemWidget(sep_n, 0, line_n)

            compiler_notes = [p for p in note_paths if p.name in Workspace.COMPILE_NOTE_NAMES]
            notes_header = QTreeWidgetItem(
                tree, [f"{'⚠ ' if compiler_notes else ''}컴파일 참고 ({len(note_paths)})"])
            notes_header.setData(0, Qt.UserRole, DrawerTree.NOTES_HEADER_MARKER)
            notes_header.setFlags(Qt.ItemIsEnabled)
            fnt = notes_header.font(0)
            fnt.setItalic(True)
            notes_header.setFont(0, fnt)
            if compiler_notes:      # 컴파일러가 남긴 보고가 있을 때만 경고색
                notes_header.setForeground(0, QColor(self.prefs.resolved_theme().warn))
            for p in note_paths:
                it = QTreeWidgetItem(notes_header, [p.name])
                it.setData(0, Qt.UserRole, str(p))
                it.setData(0, Qt.UserRole + 1, "note")
                if p.name in Workspace.COMPILE_NOTE_NAMES:
                    tip = "컴파일 참고 파일 — 클릭하면 내용을 훑어봅니다"
                elif p.suffix.lower() in (".sty", ".cls"):
                    tip = "스타일·클래스 파일 — 클릭하면 내용을 훑어보고, 우클릭으로 시스템 편집기로 열 수 있습니다"
                else:
                    tip = ("컴파일되지 않은 .tex (같은 이름의 원고도 .pdf 도 없음) — "
                           "클릭하면 훑어보고, 우클릭으로 시스템 편집기로 열 수 있습니다")
                it.setToolTip(0, tip)
                it.setFlags(Qt.ItemIsEnabled | Qt.ItemIsSelectable)
            notes_header.setExpanded(self._notes_expanded)

        aux_paths = [p for p in self.workspace.aux_files() if keep(p)]
        if aux_paths:
            separator = QTreeWidgetItem(tree)
            separator.setFlags(Qt.NoItemFlags)
            line = QFrame()
            line.setFrameShape(QFrame.HLine)
            line.setFrameShadow(QFrame.Sunken)
            tree.setItemWidget(separator, 0, line)

            header = QTreeWidgetItem(tree, [f"부속 파일 ({len(aux_paths)})"])
            header.setData(0, Qt.UserRole, DrawerTree.AUX_HEADER_MARKER)
            header.setFlags(Qt.ItemIsEnabled)   # 선택·드래그·드롭 다 안 됨 — 순수 구역 표시
            font = header.font(0)
            font.setItalic(True)
            header.setFont(0, font)
            for p in aux_paths:
                it = QTreeWidgetItem(header, [p.name])
                it.setData(0, Qt.UserRole, str(p))
                it.setFlags(Qt.ItemIsEnabled | Qt.ItemIsSelectable)
                if current and p == current:
                    tree.setCurrentItem(it)
            header.setExpanded(self._aux_expanded)

        asset_paths = list(self.workspace.asset_files())
        if asset_paths:
            separator2 = QTreeWidgetItem(tree)
            separator2.setFlags(Qt.NoItemFlags)
            line2 = QFrame()
            line2.setFrameShape(QFrame.HLine)
            line2.setFrameShadow(QFrame.Sunken)
            tree.setItemWidget(separator2, 0, line2)

            assets_header = QTreeWidgetItem(tree, [f"자료 창고 ({len(asset_paths)})"])
            assets_header.setData(0, Qt.UserRole, DrawerTree.ASSETS_HEADER_MARKER)
            assets_header.setFlags(Qt.ItemIsEnabled)
            font2 = assets_header.font(0)
            font2.setItalic(True)
            assets_header.setFont(0, font2)
            for p in asset_paths:
                rel = p.relative_to(self.workspace.root / Workspace.ASSETS_DIR)
                it = QTreeWidgetItem(assets_header, [str(rel)])
                it.setData(0, Qt.UserRole, str(p))
                it.setData(0, Qt.UserRole + 1, "asset")
                it.setFlags(Qt.ItemIsEnabled | Qt.ItemIsSelectable)
            assets_header.setExpanded(self._assets_expanded)

        gp_names = Preamble.graphicspath(self.index, self._path, self._live_reader) \
            if self._path else []
        gp_dirs = {(self.workspace.root / gp).resolve() for gp in gp_names}
        for folder, files in self.workspace.subfolder_groups(exclude_dirs=gp_dirs):
            if not files:
                continue
            separator3 = QTreeWidgetItem(tree)
            separator3.setFlags(Qt.NoItemFlags)
            line3 = QFrame()
            line3.setFrameShape(QFrame.HLine)
            line3.setFrameShadow(QFrame.Sunken)
            tree.setItemWidget(separator3, 0, line3)

            rel_folder = self.workspace.relative(folder)
            folder_header = QTreeWidgetItem(tree, [f"{rel_folder}/ ({len(files)})"])
            folder_header.setData(0, Qt.UserRole, DrawerTree.SUBFOLDER_HEADER_MARKER)
            folder_header.setData(0, Qt.UserRole + 2, str(folder))
            folder_header.setFlags(Qt.ItemIsEnabled)
            font3 = folder_header.font(0)
            font3.setItalic(True)
            folder_header.setFont(0, font3)
            for p in files:
                rel = p.relative_to(folder)
                it = QTreeWidgetItem(folder_header, [str(rel)])
                it.setData(0, Qt.UserRole, str(p))
                it.setData(0, Qt.UserRole + 1, "subfolder")
                it.setFlags(Qt.ItemIsEnabled | Qt.ItemIsSelectable)
            folder_header.setExpanded(
                self._subfolder_expanded.get(str(folder), False))

        tree.blockSignals(False)

    def _mark_nmd_item(self, item: QTreeWidgetItem, path: Path):
        """`.nmd`(스타일·템플릿으로 쓰는 원고)는 파란 글자로 보여, 이름이 길어
        확장자가 가려져도 `.md` 원고와 구별되게 한다. 부속 파일로 취급하지는
        않는다(원고 그대로 포함·컴파일에 참여한다)."""
        if path.suffix.lower() != ".nmd":
            return
        bg = QColor(self.prefs.resolved_theme().bg)
        item.setForeground(0, QColor("#6CB6FF" if bg.lightness() < 128 else "#1F6FD0"))
        item.setToolTip(0, f"{path.name} — .nmd (스타일·템플릿 원고)")

    def _drawer_label(self, node: Node) -> str:
        name = node.path.name
        bits = []
        if node.parent is not None and node.children:
            # ndhmd4tex 는 {{}} 단계에 제한이 없다(기본 20단계). 이 표시는
            # 컴파일 문제가 아니라, 이 앱이 구조로 다루는 깊이(2단계)까지만
            # 지원한다는 알림이다.
            bits.append("⚠ 2단계 포함")
        if node.children:
            bits.append(_T(f"{len(node.children)}장"))
        if node.missing:
            bits.append(f"없는 포함 {len(node.missing)}")
        tags = self.tags.get_active(node.path, self._live_reader)
        if tags:
            bits.append(TagStore.format(tags))
        # 메모 표시는 파일 이름 앞에 둔다(눌러서 메모 창으로 갈 수 있다 — DrawerTree).
        if self.notes.has(node.path):
            name = f"{DrawerTree.NOTE_MARK} {name}"
        return f"{name}   {'  ·  '.join(bits)}" if bits else name

    def sync_drawer_selection(self):
        """서랍의 선택 표시를 지금 편집 중인 파일에 맞춘다. 이미 맞으면 아무 것도 안 한다.
        편집 중인 파일이 서랍에 없으면(필터에 걸렸거나 이름 없는 문서) 선택을 비운다."""
        tree = self.drawer.tree
        want = str(self._path) if self._path else None

        def find(item):
            if (want and item.data(0, Qt.UserRole) == want
                    and item.data(0, Qt.UserRole + 1) not in ("note", "asset", "subfolder")):
                return item
            for i in range(item.childCount()):
                r = find(item.child(i))
                if r is not None:
                    return r
            return None

        target = None
        for i in range(tree.topLevelItemCount()):
            target = find(tree.topLevelItem(i))
            if target is not None:
                break
        cur = tree.currentItem()
        if target is not None:
            if cur is target and len(tree.selectedItems()) == 1:
                return
            tree.clearSelection()
            tree.setCurrentItem(target)
        elif cur is not None or tree.selectedItems():
            tree.clearSelection()
            tree.setCurrentItem(None)

    def open_from_drawer(self, path: Path):
        if self._path == path:
            return
        self._close_doc_tools()
        self.open_path(path)

    def _close_doc_tools(self):
        """사용자가 다른 원고로 옮겨 갈 때(서랍 클릭·열기) 현재 문서/책에 묶인 점검·편집 도구를
        닫는다 — 상호참조 점검·그림 점검·그림 들여오기·참고문헌 편집. 옛 문서의 내용을 보여 주거나
        엉뚱한 파일에 넣을 위험이 있고, 따라가며 갱신하느니 닫는 편이 낫다. 도구가 스스로
        다른 파일로 뛰는 것(점검 창의 더블클릭 이동 등)은 이 길을 타지 않아 닫히지 않는다.
        팔레트류(기호·악센트·pm 입력기 등)나 표·조각 그림 편집기는 문서에 묶이지 않거나
        작업 중인 내용이 있어 그대로 둔다."""
        tools = list(getattr(self, "_check_dialogs", []))
        for name in ("_image_import_panel", "_bib_dialog"):
            d = getattr(self, name, None)
            if d is not None:
                tools.append(d)
        for d in tools:
            try:
                if d.isVisible():
                    d.close()
            except RuntimeError:
                pass
        self._check_dialogs = [d for d in getattr(self, "_check_dialogs", [])
                               if _qt_alive(d) and d.isVisible()]

    def _book_root_name(self, path: Path) -> str:
        """path 가 속한 책의 최상위(0단계) 파일 이름을 찾는다 — 몇 단계를
        거슬러 올라가든 상관없다. path 자신이 최상위면 그 이름 그대로."""
        node = self.index.by_path.get(path)
        if node is None:
            return path.name
        seen = {node.path}
        while node.parent is not None:
            nxt = self.index.by_path.get(node.parent)
            if nxt is None or nxt.path in seen:
                break
            node = nxt
            seen.add(node.path)
        return node.path.name

    def _resync_descendant_ndhmain(self, src: Path):
        """src 를 옮긴 뒤, src 의 모든 자손(재귀)의 ndhmain: 을 src 가
        지금 속한 책의 진짜 루트 이름으로 맞춘다.

        src 를 밖(0단계)으로 꺼내면 src 자신이 새 루트가 되므로
        자손들은 이제 src 를 따라야 하고, src 를 다른 책의 장으로
        옮기면 그 책의 진짜 루트를 따라야 한다 — 어느 쪽이든
        _book_root_name(src) 하나로 정확히 계산된다.

        self.index 가 이 호출 시점에 최신이어야 한다(옮기는 쪽에서
        _rewrite_includes 의 기본 refresh=True 로 이미 다시 스캔한
        뒤에 부르는 것을 전제한다).
        """
        node = self.index.by_path.get(src)
        if node is None or not node.children:
            return
        root_name = self._book_root_name(src)

        def walk(n):
            for child_path in n.children:
                self._set_ndhmain_hint(child_path, root_name)
                child_node = self.index.by_path.get(child_path)
                if child_node is not None:
                    walk(child_node)

        walk(node)

    def handle_drawer_drop(self, src: Path, target: Path | None,
                           on_item: bool, on_viewport: bool):
        """서랍에서 항목을 떨어뜨렸을 때 {{}} 줄을 고친다.

        1단계·2단계 구분 없이 전부 같은 {{}} 메커니즘이다(ndhmd4tex
        이 이제 몇 단계든 직접 푼다) — can_nest() 가 깊이 제한(이
        앱은 2단계까지만 허용)을 검증한다.
        """
        src_node = self.index.by_path.get(src)
        if src_node is None:
            return

        # 1) 항목 위에 떨어뜨렸다 → 그 항목의 자식으로 넣는다. 그
        # 항목이 이미 2단계(더 못 들어감)면 그 부모의 형제로 넣는다.
        if on_item and target is not None:
            parent = target
            p_node = self.index.by_path.get(target)
            if p_node is not None and p_node.parent is not None:
                grandparent = self.index.by_path.get(p_node.parent)
                if grandparent is not None and grandparent.parent is not None:
                    parent = p_node.parent   # target 이 이미 2단계 -- 그 형제로
            ok, why = self.index.can_nest(src, parent)
            if not ok:
                if why:
                    QMessageBox.information(self, "묶을 수 없습니다", why)
                return
            self._detach(src)
            names = self.index.read_includes(parent) + [src.name]
            self._rewrite_includes(parent, names)
            self._set_ndhmain_hint(src, self._book_root_name(parent))
            self._resync_descendant_ndhmain(src)
            return

        # 2) 빈 곳에 떨어뜨렸다 → 최상위로 뺀다.
        if on_viewport or target is None:
            if src_node.parent is None:
                return
            self._detach(src)
            self.refresh_drawer()      # _detach 는 갱신하지 않는다
            self._resync_descendant_ndhmain(src)
            return

        # 3) 항목 사이에 떨어뜨렸다 → 그 부모 안에서 순서를 바꾸거나 옮긴다.
        tgt_node = self.index.by_path.get(target)
        if tgt_node is None:
            return
        parent = tgt_node.parent
        if parent is None:
            # 최상위 항목들 사이 → 최상위로 빼는 것과 같다.
            if src_node.parent is not None:
                self._detach(src)
                self.refresh_drawer()
                self._resync_descendant_ndhmain(src)
            return
        ok, why = self.index.can_nest(src, parent)
        if not ok and src_node.parent != parent:
            if why:
                QMessageBox.information(self, "묶을 수 없습니다", why)
            return
        if src_node.parent not in (None, parent):
            self._detach(src)
        names = [n for n in self.index.read_includes(parent) if n != src.name]
        try:
            at = names.index(target.name)
        except ValueError:
            at = len(names)
        names.insert(at, src.name)
        self._rewrite_includes(parent, names)
        self._set_ndhmain_hint(src, self._book_root_name(parent))
        self._resync_descendant_ndhmain(src)

    def handle_drawer_drop_multi(self, srcs: list, target: Path | None,
                                 on_item: bool, on_viewport: bool):
        """여러 항목을 한꺼번에 끌어놓았을 때. handle_drawer_drop 과 같은
        판단을 각 항목에 그대로 적용하되, 파일 쓰기와 화면 갱신은 끝에
        한 번만 한다 — 항목마다 다시 쓰고 다시 그리면 몇 배 느려진다.

        일부만 실패해도(예: 이미 다른 책을 포함한 파일을 넣으려 함)
        나머지는 그대로 처리하고, 실패한 것만 모아 한 번에 알린다.
        """
        srcs = [s for s in srcs if s != target]
        if not srcs:
            return
        if len(srcs) == 1:
            self.handle_drawer_drop(srcs[0], target, on_item, on_viewport)
            return

        failed = []

        # 1) 항목 위에 떨어뜨렸다 → 전부 그 항목의 자식으로 넣는다.
        # 그 항목이 이미 2단계면 그 부모의 형제로 넣는다.
        if on_item and target is not None:
            parent = target
            p_node = self.index.by_path.get(target)
            if p_node is not None and p_node.parent is not None:
                grandparent = self.index.by_path.get(p_node.parent)
                if grandparent is not None and grandparent.parent is not None:
                    parent = p_node.parent   # target 이 이미 2단계 -- 그 형제로
            names = self.index.read_includes(parent)
            succeeded = []
            for src in srcs:
                ok, why = self.index.can_nest(src, parent)
                if not ok:
                    if why:
                        failed.append(f"{src.name}: {why}")
                    continue
                node = self.index.by_path.get(src)
                if node is not None and node.parent not in (None, parent):
                    self._detach(src)
                    names = self.index.read_includes(parent)
                if src.name not in names:
                    names.append(src.name)
                succeeded.append(src)
            self._rewrite_includes(parent, names)
            for src in succeeded:
                self._set_ndhmain_hint(src, self._book_root_name(parent))
                self._resync_descendant_ndhmain(src)
            self._report_batch_failures(failed)
            return

        # 2) 빈 곳에 떨어뜨렸다 → 전부 최상위로 뺀다.
        if on_viewport or target is None:
            moved = []
            for src in srcs:
                node = self.index.by_path.get(src)
                if node is not None and node.parent is not None:
                    self._detach(src)
                    moved.append(src)
            self.refresh_drawer()
            for src in moved:
                self._resync_descendant_ndhmain(src)
            return

        # 3) 항목 사이에 떨어뜨렸다 → 그 책 안으로 순서대로 삽입한다.
        tgt_node = self.index.by_path.get(target)
        if tgt_node is None:
            return
        parent = tgt_node.parent
        if parent is None:
            # 최상위 항목들 사이 → 전부 최상위로 빼는 것과 같다.
            moved = []
            for src in srcs:
                node = self.index.by_path.get(src)
                if node is not None and node.parent is not None:
                    self._detach(src)
                    moved.append(src)
            self.refresh_drawer()
            for src in moved:
                self._resync_descendant_ndhmain(src)
            return

        succeeded = []
        for src in srcs:
            node = self.index.by_path.get(src)
            already_here = node is not None and node.parent == parent
            ok, why = self.index.can_nest(src, parent)
            if not ok and not already_here:
                if why:
                    failed.append(f"{src.name}: {why}")
                continue
            if node is not None and node.parent not in (None, parent):
                self._detach(src)
            succeeded.append(src)

        names = [n for n in self.index.read_includes(parent)
                if n not in {s.name for s in succeeded}]
        try:
            at = names.index(target.name)
        except ValueError:
            at = len(names)
        for i, s in enumerate(succeeded):
            names.insert(at + i, s.name)
        self._rewrite_includes(parent, names)
        for src in succeeded:
            self._set_ndhmain_hint(src, self._book_root_name(parent))
            self._resync_descendant_ndhmain(src)
        self._report_batch_failures(failed)

    def _report_batch_failures(self, failed: list):
        if failed:
            QMessageBox.information(
                self, "일부 항목을 옮기지 못했습니다", "\n".join(failed[:10]))

    def _set_ndhmain_hint(self, src: Path, main_name: str | None):
        """서랍에서 책 사이로 옮길 때, 정방향 검색이 쓰는 ndhmain: 힌트를
        함께 관리한다. 이게 없으면 장 파일 안에서 정방향 검색을 했을 때
        어느 책 소속인지 몰라 실패한다(장이 main.md 를 직접 컴파일하는
        게 아니라, main.md 가 이 장을 포함하는 것뿐이라 장 파일 스스로는
        알 길이 없다).

        지금 열려 있는 파일이면 화면도 새로 읽어 반영한다. 다른 곳에
        미저장 편집으로 캐시되어 있는 파일이면(_dirty_docs) 그 캐시는
        건드리지 않는다 — 지우면 사용자의 편집이 사라진다. 그 경우
        이번 변경은 디스크에만 남고, 나중에 그 파일을 저장하면 덮어써질
        수 있다는 것만 감안한다.
        """
        set_frontmatter_key(src, "ndhmain", main_name)
        if self._path == src and src not in self._dirty_docs:
            self.load(src)

    def _detach(self, src: Path):
        """현재 부모에서 {{src}} 줄을 빼고, ndhmain: 힌트도 지운다."""
        node = self.index.by_path.get(src)
        if node is None or node.parent is None:
            return
        parent = node.parent
        names = [n for n in self.index.read_includes(parent) if n != src.name]
        self._rewrite_includes(parent, names, refresh=False)
        self._set_ndhmain_hint(src, None)

    def _rewrite_includes(self, parent: Path, names: list, refresh: bool = True):
        """부모 파일의 포함 줄을 새로 쓴다. 열려 있으면 다시 읽어 온다."""
        if self._path == parent and self._dirty:
            r = QMessageBox.question(
                self, "저장 후 진행",
                f"{parent.name} 에 저장하지 않은 변경이 있습니다.\n"
                f"구조를 바꾸려면 먼저 저장해야 합니다. 저장할까요?",
                QMessageBox.Save | QMessageBox.Cancel)
            if r != QMessageBox.Save or not self.save_file():
                return
        if not BookIndex.set_includes(parent, names):
            QMessageBox.warning(self, "쓰기 실패", f"{parent.name} 을(를) 고치지 못했습니다.")
            return
        if self._path == parent:
            line = self.editor.file_line()
            self.load(parent)
            self.editor.goto_file_line(line)
        if refresh:
            self.refresh_drawer()


    # -- 분할 칸 ---------------------------------------------------------------
    #
    # QSplitter.saveState/restoreState 는 칸 수가 바뀌어도 아무 말 없이 복원을
    # 시도하고, 모자란 칸에 폭 0 을 준다. 그러면 위젯은 isVisible()==True 인데
    # 화면에는 한 픽셀도 없는 상태가 되어, 토글을 눌러도 아무 일이 없다.
    # 그래서 폭을 직접 숫자 목록으로 저장하고 칸 수가 맞을 때만 되돌린다.

    PANE_MIN = 170

    def _save_panes(self):
        sizes = [int(x) for x in self.splitter.sizes()]
        for i, width in self._pane_memory.items():
            if 0 <= i < len(sizes) and sizes[i] == 0:
                sizes[i] = int(width)   # 접힌 칸은 기억된 폭으로 남긴다
        self._settings.setValue("view/panes", sizes)

    def _restore_panes(self):
        saved = self._settings.value("view/panes")
        if not saved:
            return
        try:
            sizes = [int(x) for x in saved]
        except (TypeError, ValueError):
            return
        if len(sizes) != self.splitter.count():
            return                      # 칸 구성이 바뀌었다 — 기본값을 쓴다
        self.splitter.setSizes(sizes)

    def _remember_pane(self, index: int):
        """접기 직전의 폭을 기억한다. 다시 펼 때 그 폭으로 돌아온다."""
        width = self.splitter.sizes()[index]
        if width >= self.PANE_MIN:
            self._pane_memory[index] = width

    def _ensure_pane(self, index: int):
        """펴기로 한 칸이 폭 0 이면 가운데 칸에서 자리를 떼어 준다.

        isVisible() 이 아니라 isHidden() 을 보는 것이 중요하다. 창을 show()
        하기 전에는 자식이 전부 isVisible()==False 라, 시작할 때의 보정이
        통째로 건너뛰어진다. isHidden() 은 "명시적으로 감췄는가" 만 뜻한다.
        """
        widget = self.splitter.widget(index)
        if widget is None or widget.isHidden():
            return
        sizes = self.splitter.sizes()
        if sizes[index] >= self.PANE_MIN:
            return
        want = self._pane_memory.get(index)
        if not want:
            want = max(self.PANE_MIN, widget.sizeHint().width())
        take = min(want - sizes[index], max(0, sizes[1] - 360))
        if take <= 0:
            return
        sizes[index] += take
        sizes[1] -= take
        self.splitter.setSizes(sizes)

    # -- 미리보기 ---------------------------------------------------------------

    PREVIEW_HEIGHT = 190

    def toggle_preview(self, on: bool):
        #: 이 호출이 자동 미리보기 자신이 아니라 메뉴·단축키 등 다른
        #: 경로로 들어온 것이면, "자동으로 연 것"이라는 꼬리표부터
        #: 지운다 — _on_auto_preview_timeout() 이 바로 다음 줄에서
        #: 자기가 연 것이면 다시 True 로 되돌려 놓는다. 이렇게 안
        #: 하면, 전에 자동으로 열렸던 패널을 사용자가 직접 다시 켰을
        #: 때도 옛 꼬리표가 남아 있어 나중에 커서가 멀어지면 사용자
        #: 의도와 달리 제멋대로 닫혀 버린다.
        self._preview_auto_shown = False
        self.preview.setVisible(on)
        self._settings.setValue("view/preview", on)
        if on:
            sizes = self.vsplit.sizes()
            if sizes[1] < 60:
                self.vsplit.setSizes([max(120, sizes[0] - self.PREVIEW_HEIGHT),
                                      self.PREVIEW_HEIGHT])
            self.update_preview()
        self.editor.setFocus()

    def _restore_vsplit(self):
        saved = self._settings.value("view/vsplit")
        try:
            sizes = [int(x) for x in saved] if saved else None
        except (TypeError, ValueError):
            sizes = None
        if sizes and len(sizes) == self.vsplit.count() and sizes[1] >= 60:
            self.vsplit.setSizes(sizes)
        else:
            self.vsplit.setSizes([600, self.PREVIEW_HEIGHT])

    @Slot()
    def _schedule_preview(self):
        if self._act_preview.isChecked():
            self._preview_timer.start()

    @Slot()
    def _schedule_auto_preview(self):
        """자동 미리보기([환경설정]에서 켜져 있을 때만) — 커서가
        움직일 때마다 타이머를 다시 시작한다. 그래서 실제로는 "커서가
        멈춘 뒤 설정된 시간"이 지나야 _on_auto_preview_timeout() 이
        불린다."""
        self._auto_preview_timer.stop()
        if not self.prefs.auto_preview():
            return
        self._auto_preview_timer.setInterval(int(self.prefs.auto_preview_delay() * 1000))
        self._auto_preview_timer.start()

    def _on_auto_preview_timeout(self):
        """커서가 자동 미리보기 지연 시간만큼 멈춰 있었다. 그 자리에
        수식·그림·표가 있으면 미리보기 패널을 스스로 연다. 없으면 —
        그 패널이 스스로 연 것이었을 때만 — 스스로 닫는다(사용자가
        Ctrl+Shift+P 로 직접 켜 둔 거라면 그대로 둔다)."""
        if not self.prefs.auto_preview():
            return
        text = self.editor.toPlainText()
        pos = self.editor.textCursor().position()
        target = PreviewScanner.find(text, pos)
        if target is not None:
            if not self._act_preview.isChecked():
                self._act_preview.setChecked(True)
                self.toggle_preview(True)
                self._preview_auto_shown = True
        elif self._act_preview.isChecked() and self._preview_auto_shown:
            self._act_preview.setChecked(False)
            self.toggle_preview(False)
            self._preview_auto_shown = False

    def update_preview(self):
        if not self._act_preview.isChecked():
            return
        text = self.editor.toPlainText()
        pos = self.editor.textCursor().position()
        target = PreviewScanner.find(text, pos)
        if target is None:
            self._preview_key = None
            self.preview.set_message(
                "미리보기", "커서를 수식·그림·표(파이프·grid) 위에 두면 여기에 나옵니다.")
            return
        if target.kind == "image":
            self._preview_image(target)
        elif target.kind == "table":
            self._preview_table(target)
        else:
            self._preview_math(target)

    # -- 그림 -------------------------------------------------------------------

    def _live_reader(self, path: Path):
        """지금 편집창에 열려 있는 파일이면 그 내용을, 아니면 None 을 준다.

        Preamble 이 이 함수를 받아, 저장 전 변경도 즉시 반영해 읽는다.
        """
        if self._path is not None and path.resolve() == self._path:
            return self.editor.toPlainText()
        return None

    def _resolve_image(self, name: str):
        r"""{{포함}} 과 그림 검색 규칙을 함께 따른다.

        `graphicspath:` 가 있으면 \graphicspath 와 같은 순서로, **그 목록의
        순서를 그대로** 따라 찾는다. `["./", "figures/"]` 면 같은 폴더를
        먼저 보고 figures/ 를 나중에 본다 — 순서가 뒤바뀌면 두 폴더에 같은
        이름의 파일이 있을 때 조판 결과와 다른 쪽을 보여주게 된다.

        graphicspath 를 다 뒤져도 없으면 책 폴더(컴파일이 실제로 실행되는
        위치이므로 kpathsea 가 기본으로 보는 곳이다)를 마지막으로 본다.
        graphicspath 자체가 없으면 옛 동작 그대로 책 폴더만 본다.
        """
        if self._path is None:
            return None
        root = LabelIndex.book_files(self.index, self._path)[0]
        book_dir = root.parent

        ordered = [book_dir / gp / name
                  for gp in Preamble.graphicspath(self.index, self._path, self._live_reader)]
        ordered.append(book_dir / name)          # graphicspath 밖의 최종 대비
        if self.workspace:
            ordered.append(self.workspace.root / name)

        seen = set()
        for c in ordered:
            if c in seen:
                continue
            seen.add(c)
            try:
                if c.is_file():
                    return c
            except OSError:
                continue
        return None

    def _image_diagnostic(self, name: str) -> str:
        """찾지 못했을 때 이유를 그대로 보여준다.

        graphicspath 가 "선언 안 함"인지 "선언은 했는데 다른 이유로 안
        먹힘"인지가 겉으로는 똑같이 빈 목록이라, 어느 파일을 책 최상위로
        보고 있는지와 실제로 시도한 경로까지 다 보여줘야 원인을 좁힐 수
        있다.
        """
        if self._path is None:
            return f"파일을 찾지 못했습니다: {name}"
        Preamble.LAST_ERROR = ""
        gp = Preamble.graphicspath(self.index, self._path, self._live_reader)
        root = LabelIndex.book_files(self.index, self._path)[0]
        lines = [f"파일을 찾지 못했습니다: {name}",
                f"책 최상위로 인식한 파일: {self.workspace.relative(root)}"]
        if Preamble.LAST_ERROR:
            lines.append(f"프론트매터 해석 오류 — {Preamble.LAST_ERROR}")
        lines.append(f"graphicspath: {', '.join(gp) if gp else '(감지되지 않음)'}")
        tried = [root.parent / g / name for g in gp] + [root.parent / name]
        lines.append("시도한 경로:")
        lines.extend(f"  · {self.workspace.relative(c)}" for c in tried[:6])
        return "\n".join(lines)

    def _preview_image(self, target: PreviewTarget):
        key = ("image", target.source)
        if key == self._preview_key:
            return
        self._preview_key = key
        head = f"그림 · {target.caption or target.source}"

        if is_image_url(target.source):
            self._preview_remote_image(target.source, head)
            return

        path = self._resolve_image(target.source)
        if path is None:
            self.preview.set_message(head, self._image_diagnostic(target.source))
            return
        suffix = path.suffix.lower()
        if suffix in PreviewPanel.IMAGE_DIRECT:
            self.preview.set_image(str(path), f"{head}   ({path.name})")
            return
        if suffix in PreviewPanel.IMAGE_CONVERT:
            self._preview_converted(path, head)
            return
        self.preview.set_message(head, f"미리보기를 지원하지 않는 형식입니다 ({suffix}).")

    def _preview_remote_image(self, url: str, head: str):
        """URL 그림. 캐시 조회는 네트워크가 아니니 항상 하고, 실제
        다운로드는 설정이 켜져 있거나 사용자가 버튼을 눌러야 나간다.
        """
        book_dir = LabelIndex.book_files(self.index, self._path)[0].parent
        hit = cached_image(url, book_dir)
        if hit is not None:
            self.preview.set_image(str(hit), f"{head}   (캐시됨 · {hit.name})")
            return

        if self.prefs.auto_fetch_images():
            self._start_fetch(url, book_dir, head)
            return

        # url 은 공백이 없는 한 덩어리라 word wrap 으로 안 꺾인다 —
        # 패널 너비에 맞춰 가운데를 생략해 둔다(창 크기가 바뀌면
        # 다음 번에 다시 지날 때 새로 계산된다).
        metrics = self.preview.body.fontMetrics()
        avail = max(20, self.preview.width() - 40)
        shown_url = metrics.elidedText(url, Qt.ElideMiddle, avail)
        self.preview.set_fetch_prompt(
            head,
            f"원격 그림입니다. 아직 내려받지 않았습니다.\n{shown_url}\n\n"
            f"눌러서 받으면 {IMAGE_CACHE_DIR}/ 에 저장되고, 다음부터는 "
            f"네트워크 없이 이 파일을 씁니다.",
            lambda: self._start_fetch(url, book_dir, head))

    def _start_fetch(self, url: str, book_dir: Path, head: str):
        self._fetch_id += 1
        self.preview.set_fetching(head)
        task = FetchTask(self._fetch_id, url, book_dir, self._fetch_signals)
        self._fetch_pool.start(task)

    @Slot(int, str, str, str)
    def _on_fetch_done(self, req_id: int, url: str, status: str, payload: str):
        if self._preview_key != ("image", url):
            return                      # 그 사이 커서가 다른 곳으로 옮겨갔다
        if status == "ok":
            self.preview.set_image(payload, f"그림 · {url}   (방금 받음)")
        else:
            self.preview.set_message(f"그림 · {url}", payload)

    def _preview_converted(self, path: Path, head: str):
        """PDF/EPS 처럼 변환이 필요한 로컬 그림."""
        key = ("convert", str(path))
        cached = self._render_cache.get(key)
        if cached:
            self.preview.set_image(cached, f"{head}   ({path.name})")
            return
        out = self._render_dir / hashlib.sha1(str(path).encode()).hexdigest()[:16]
        out.mkdir(parents=True, exist_ok=True)
        dst = out / "img.svg"
        try:
            rc = subprocess.run(["pdftocairo", "-svg", str(path), str(dst)],
                                capture_output=True, timeout=20,
                                creationflags=_NO_WINDOW).returncode
        except (OSError, subprocess.SubprocessError):
            rc = 1
        if rc == 0 and dst.exists():
            self._render_cache[key] = str(dst)
            self.preview.set_image(str(dst), f"{head}   ({path.name})")
        else:
            self.preview.set_message(head, f"{path.name} 을(를) 그리지 못했습니다.")

    # -- 수식 -------------------------------------------------------------------

    # -- 파이프 표 ---------------------------------------------------------------

    _MD_INLINE = (
        (re.compile(r"`([^`\n]+)`"), r"<code>\1</code>"),
        (re.compile(r"\*\*([^*\n]+)\*\*"), r"<b>\1</b>"),
        (re.compile(r"(?<![*\w])\*([^*\n]+)\*(?![*\w])"), r"<i>\1</i>"),
        (re.compile(r"~~([^~\n]+)~~"), r"<s>\1</s>"),
    )

    @classmethod
    def _md_inline_html(cls, escaped: str) -> str:
        """이미 HTML 이스케이프된 셀 글에 굵게·기울임·코드·취소선을 흉내 낸다."""
        for rx, rep_ in cls._MD_INLINE:
            escaped = rx.sub(rep_, escaped)
        return escaped

    @classmethod
    def pipe_table_html(cls, source: str, fg: str = "#222222") -> str:
        """파이프 표 원문 → 미리보기용 HTML. LaTeX 을 부르지 않는 근사다:
        굵게·기울임·코드·취소선만 흉내 내고 수식·\\ref 따위는 원문 그대로 둔다."""
        import html as _html
        rows, aligns = [], []
        for raw in source.splitlines():
            line = raw.strip()
            if not line:
                continue
            core = re.sub(r"^\||(?<!\\)\|$", "", line)
            if TABLE_SEP_RE.match(line) and "-" in line and not aligns:
                for sc in core.split("|"):
                    sc = sc.strip()
                    aligns.append("center" if sc.startswith(":") and sc.endswith(":")
                                  else "right" if sc.endswith(":") else "left")
                continue
            rows.append([c.strip() for c in _UNESC_PIPE_RE.split(core)])
        if not rows:
            return ""
        ncol = max(len(r) for r in rows)
        aligns += ["left"] * (ncol - len(aligns))

        def cell(txt: str) -> str:
            t = _html.escape(txt.replace("\\|", "|"))
            for rx, rep in cls._MD_INLINE:
                t = rx.sub(rep, t)
            return t or "&nbsp;"

        out = [f'<table border="1" cellspacing="0" cellpadding="5" '
               f'style="color:{fg}; border-collapse:collapse;">']
        for i, r in enumerate(rows):
            tag = "th" if i == 0 else "td"
            out.append("<tr>" + "".join(
                f'<{tag} align="{aligns[j]}">{cell(c)}</{tag}>'
                for j, c in enumerate(r + [""] * (ncol - len(r)))) + "</tr>")
        out.append("</table>")
        return "".join(out)

    def _preview_table(self, target: PreviewTarget):
        digest = hashlib.sha1(target.source.encode("utf-8")).hexdigest()
        key = ("table", digest)
        if key == self._preview_key:
            return
        self._preview_key = key
        first = target.source.lstrip().split("\n", 1)[0].strip()
        if GRID_BORDER_RE.match(first):
            html = grid_table_html(target.source.splitlines(), inline=self._md_inline_html)
        else:
            html = self.pipe_table_html(target.source)
        if not html:
            self.preview.set_message("표", "표를 읽을 수 없습니다.")
            return
        doc = QTextDocument()
        doc.setDefaultFont(self.editor.font())
        doc.setHtml(html)
        avail = max(200, self.preview.scroll.viewport().width() - 30)
        doc.setTextWidth(-1)
        doc.setTextWidth(min(max(doc.idealWidth(), 50), avail))
        size = doc.size().toSize()
        dpr = self.devicePixelRatioF()
        pm = QPixmap(int((size.width() + 16) * dpr), int((size.height() + 16) * dpr))
        pm.setDevicePixelRatio(dpr)
        pm.fill(QColor(PreviewPanel.CANVAS_BG))
        painter = QPainter(pm)
        painter.translate(8, 8)
        doc.drawContents(painter)
        painter.end()
        self.preview.set_pixmap(pm, "표   (근사 미리보기 — 실제 조판은 컴파일해야 보입니다)")

    def _preview_math(self, target: PreviewTarget):
        preamble = (Preamble.collect(self.index, self._path, self._live_reader)
                    if self._path is not None else "")
        digest = hashlib.sha1(
            (preamble + "\x00" + target.source).encode("utf-8")).hexdigest()
        key = ("math", digest)
        if key == self._preview_key:
            return
        self._preview_key = key

        cached = self._render_cache.get(key)
        if cached:
            self.preview.set_image(cached[0], f"수식   ({cached[1]})   ·   Ctrl+M 으로 편집")
            return

        self._render_id += 1
        self.preview.set_message("수식", "조판하는 중…")
        task = RenderTask(self._render_id, target.source, preamble,
                          self._render_dir / digest[:16], self._render_signals)
        self._render_pool.start(task)

    @Slot(int, str, str, str)
    def _on_render_done(self, req_id: int, status: str, payload: str, stage: str):
        if req_id != self._render_id:
            return                      # 그 사이 커서가 옮겨갔다 — 버린다
        if status == "ok":
            if self._preview_key:
                self._render_cache[self._preview_key] = (payload, stage)
            self.preview.set_image(payload, f"수식   ({stage})   ·   Ctrl+M 으로 편집")
        else:
            self.preview.set_message("수식 — 조판 실패", payload)

    # -- 라벨 날개 -------------------------------------------------------------

    def close_peripheral_windows(self) -> int:
        """떠 있는 주변 창(도구 창·떼어낸 날개·카드 보기·AI 결과 창 등)을 모두 닫는다. 메인 창과
        모달 대화상자(설정 등)는 건드리지 않는다. 닫은 개수를 돌려준다."""
        if QApplication.activeModalWidget() is not None:
            return 0                    # 모달 대화상자가 떠 있으면 그 대화상자의 몫이다
        n = 0
        for w in list(QApplication.topLevelWidgets()):
            if w is self or not w.isVisible() or not w.isWindow():
                continue
            if w.windowType() in (Qt.Popup, Qt.ToolTip, Qt.SplashScreen):
                continue
            if not isinstance(w, (QDialog, FloatingPanelWindow)) or (isinstance(w, QDialog) and w.isModal()):
                continue
            w.close()
            n += 1
        self.statusBar().showMessage(
            f"주변 창 {n}개를 닫았습니다." if n else "닫을 주변 창이 없습니다.", 2500)
        self.editor.setFocus()
        return n

    def toggle_drawer(self, on: bool):
        if not on:
            self._remember_pane(0)
        self.drawer.setVisible(on)
        if on:
            self._ensure_pane(0)

    def toggle_drawer_sort(self, mtime_first: bool):
        self.prefs.write(drawer_sort="mtime" if mtime_first else "name")
        self.refresh_drawer()
        self.editor.setFocus()

    def _sync_wing_pane_visibility(self):
        """라벨 날개와 TOC 를 감싼 wing_box — 둘 다 숨겨져 있으면 이
        컨테이너도 숨겨서 splitter 칸 자체가 접히게 한다. 하나라도
        보이면 컨테이너도 보인다.

        isVisible() 이 아니라 isHidden() 을 봐야 한다 — 창을 show()
        하기 전에는 자식이 전부 isVisible()==False 라(_ensure_pane()
        의 문서화된 것과 같은 함정), 시작할 때 이 계산이 통째로
        틀어진다. isHidden() 은 "명시적으로 감췄는가"만 뜻한다.
        """
        docked_wing = "wing" not in self._floating and not self.wing.isHidden()
        docked_toc = "toc" not in self._floating and not self.toc.isHidden()
        self.wing_box.setVisible(docked_wing or docked_toc)

    def toggle_wing(self, on: bool):
        if not on:
            self._remember_pane(2)
        self.wing.setVisible(on)
        if "wing" in self._floating:
            self._floating["wing"].setVisible(on)   # 떠 있으면 그 창도 같이
        self._sync_wing_pane_visibility()
        self._settings.setValue("view/wing", on)
        if on:
            if "wing" not in self._floating:
                self._ensure_pane(2)
            self.refresh_labels()
            self.wing.filter.setFocus()
        else:
            self.editor.setFocus()

    def toggle_toc(self, on: bool):
        if not on:
            self._remember_pane(2)
        self.toc.setVisible(on)
        if "toc" in self._floating:
            self._floating["toc"].setVisible(on)
        self._sync_wing_pane_visibility()
        self._settings.setValue("view/toc", on)
        if on:
            if "toc" not in self._floating:
                self._ensure_pane(2)
            self.refresh_toc()

    # -- 날개 떼어내기 ---------------------------------------------------------

    _FLOAT_TITLES = {"wing": "라벨 날개", "toc": "TOC"}

    def _panel_for(self, key: str):
        return self.wing if key == "wing" else self.toc

    def toggle_float_panel(self, key: str):
        """패널 머리줄의 [떼어내기/붙이기] 버튼."""
        if key in self._floating:
            self.dock_panel(key)
        else:
            self.float_panel(key)

    def float_panel(self, key: str):
        """key("wing"|"toc") 패널을 오른쪽 날개 영역에서 빼내 따로 떠
        다니는 창에 담는다. 원래 칸에 남은 게 없으면 그 칸은 접힌다."""
        if key in self._floating:
            return
        panel = self._panel_for(key)
        self._remember_pane(2)
        self._wing_layout.removeWidget(panel)
        win = FloatingPanelWindow(self, key, panel, self._FLOAT_TITLES[key])
        self._floating[key] = win
        panel.float_btn.setText("⊡")
        panel.float_btn.setToolTip("붙이기 — 원래 자리로")
        panel.setVisible(True)
        geom = self._settings.value(f"view/{key}_float_geom")
        if geom is not None and win.restoreGeometry(geom):
            pass
        else:
            win.resize(300, 520)
            g = self.geometry()
            win.move(g.right() - 320, g.top() + 80)
        self._settings.setValue(f"view/{key}_floating", True)
        self._sync_wing_pane_visibility()
        win.show()

    def dock_panel(self, key: str):
        """떠 있는 패널을 오른쪽 날개 영역의 제자리로 되돌린다."""
        win = self._floating.pop(key, None)
        if win is None:
            return
        self._settings.setValue(f"view/{key}_float_geom", win.saveGeometry())
        self._settings.setValue(f"view/{key}_floating", False)
        panel = win.panel
        win.layout().removeWidget(panel)
        # 라벨 날개가 위, TOC 가 아래 — 순서를 지켜서 다시 끼운다.
        for p in (self.wing, self.toc):
            if p is not panel and self._wing_layout.indexOf(p) >= 0:
                self._wing_layout.removeWidget(p)
        for k, p in (("wing", self.wing), ("toc", self.toc)):
            if k not in self._floating:
                self._wing_layout.addWidget(p, 1)
        panel.float_btn.setText("⧉")
        panel.float_btn.setToolTip("떼어내기 — 따로 떠다니는 창으로")
        act = self._act_wing if key == "wing" else self._act_toc
        panel.setVisible(act.isChecked())
        win.hide()
        win.deleteLater()
        self._sync_wing_pane_visibility()
        if act.isChecked():
            self._ensure_pane(2)

    def _on_floating_closed(self, key: str):
        """떠 있는 창의 [x] — 패널의 [✕] 와 같다(메뉴 체크 해제). 떠 있다는
        상태는 그대로 두어서, 다음에 다시 열면 같은 자리에 뜬다."""
        act = self._act_wing if key == "wing" else self._act_toc
        act.setChecked(False)
        (self.toggle_wing if key == "wing" else self.toggle_toc)(False)

    def _restore_floating(self):
        """지난번에 떠 있던 날개를 다시 띄운다(열려 있는 것만)."""
        for key, act in (("wing", self._act_wing), ("toc", self._act_toc)):
            if act.isChecked() and self._settings.value(
                    f"view/{key}_floating", False, type=bool):
                self.float_panel(key)

    def refresh_toc(self):
        if self._act_toc.isChecked():
            self.toc.refresh()

    def refresh_labels(self):
        if not self._act_wing.isChecked() or self._path is None:
            return
        tree = self.wing.tree
        tree.clear()
        needle = self.wing.needle()

        if self.wing.is_book():
            files = LabelIndex.book_files(self.index, self._path)
        else:
            files = [self._path]

        total = 0
        for path in files:
            if path == self._path:
                # 열려 있는 파일은 디스크가 아니라 편집창에서 읽는다.
                # 방금 적은 라벨이 저장 전에도 보여야 한다.
                hits = LabelIndex.scan_lines(
                    self.editor.toPlainText().splitlines(), path)
            else:
                hits = LabelIndex.scan_file(path)
            hits = [h for h in hits
                    if not needle or needle in h.label.lower()
                    or needle in h.context.lower()]
            if not hits:
                continue
            if len(files) > 1:
                parent = QTreeWidgetItem(tree, [
                    f"{path.name}   ({len(hits)})"])
                parent.setData(0, Qt.UserRole, None)
                parent.setExpanded(True)
                container = parent
            else:
                container = tree
            for h in hits:
                it = QTreeWidgetItem(container, [f"{h.label}    {h.kind}"])
                it.setToolTip(0, f"{path.name}:{h.line}\n{h.context}")
                it.setData(0, Qt.UserRole, (h.label, str(h.path), h.line))
                total += 1
        self.wing.hint.setText(
            f"참조점 {total}개 · 더블클릭 → [#라벨] 삽입 · 우클릭 → 형식"
            if total else "참조점이 없습니다")

    def insert_reference(self, hit, prefix: str):
        """커서 자리에 [프리픽스라벨] 을 꽂는다. 커서는 그대로 둔다."""
        label = hit[0]
        cursor = self.editor.textCursor()
        cursor.insertText(f"[{prefix}{label}]")
        self.editor.setTextCursor(cursor)
        self.editor.setFocus()
        self.statusBar().showMessage(f"[{prefix}{label}] 삽입", 2000)

    def jump_to_label(self, label: str):
        """[글자](#라벨) 을 Ctrl+클릭했을 때: 그 라벨이 선언된 곳으로 간다.
        책 전체(포함 파일 포함)에서 찾고, 열린 파일은 편집창의 내용으로 읽는다."""
        if self._path is None:
            return
        for path in LabelIndex.book_files(self.index, self._path):
            if path == self._path:
                hits = LabelIndex.scan_lines(
                    self.editor.toPlainText().splitlines(), path)
            else:
                hits = LabelIndex.scan_file(path)
            for h in hits:
                if h.label == label:
                    self.goto_label((h.label, str(h.path), h.line))
                    return
        self.statusBar().showMessage(f"라벨 '{label}' 의 정의를 찾지 못했습니다.", 5000)

    # -- 정의 ↔ 참조 이동 (각주·상호참조·문헌 인용·이름 붙은 그림) -------------------------------

    REF_KIND_NAMES = {"fn": "각주", "label": "상호참조 라벨", "cite": "문헌", "figref": "참조 표지"}

    def _nav_book_lines(self):
        """이동에 쓸 책 전체의 (path, 줄 목록). 편집 중인 파일은 편집창에서 읽는다.
        .bib 처럼 책 밖의 파일에 있을 때는 마지막으로 있던 책을 기준으로 삼는다."""
        if self._path is not None and self._path in self.index.by_path:
            self._nav_root = LabelIndex.book_files(self.index, self._path)[0]
        root = getattr(self, "_nav_root", None)
        if self._path in self.index.by_path or root not in self.index.by_path:
            files = LabelIndex.book_files(self.index, self._path) if self._path else []
        else:
            files = LabelIndex.book_files(self.index, root)
        out = []
        for path in files:
            if path == self._path:
                out.append((path, self.editor.toPlainText().splitlines()))
            else:
                try:
                    out.append((path, read_manuscript(path).splitlines()))
                except (OSError, UnicodeDecodeError):
                    continue
        if self._path is not None and all(p != self._path for p, _ in out):
            out.insert(0, (self._path, self.editor.toPlainText().splitlines()))
        return out

    def _ref_context(self):
        """커서 자리의 (종류, 키, 정의인가). 없으면 None."""
        c = self.editor.textCursor()
        text, pos = c.block().text(), c.positionInBlock()
        tok = ref_token_at(text, pos)
        if tok:
            return tok
        if FOOTNOTE_DEF_RE.match(text):          # 정의 줄 어디에 있어도 그 정의
            return "fn", FOOTNOTE_DEF_RE.match(text).group(0)[2:text.index("]")], True
        if self._path is not None:
            line_no = c.blockNumber() + 1
            for h in LabelIndex.scan_lines(self.editor.toPlainText().splitlines(), self._path):
                if h.line == line_no:
                    return "label", h.label, True
        bm = BIB_ENTRY_RE.search(text)
        if bm and bm.group(1).lower() not in BIB_SKIP_TYPES:
            return "cite", bm.group(2), True
        im = BIBITEM_ANY_RE.search(text)
        if im:
            return "cite", im.group(1), True
        rm = REF_DEF_LINE_RE.match(text)
        if rm:
            return "figref", rm.group(1).strip().lower(), True
        return None

    def _ref_defs(self, kind, key, book_lines):
        out = []
        if kind == "cite":
            keys = collect_citation_keys(self, book_lines)[0]
            if key in keys:
                path, line = keys[key]
                out.append((path, line, 0))
            return out
        for path, lines in book_lines:
            if kind == "label":
                out += [(path, h.line, 0) for h in LabelIndex.scan_lines(lines, path) if h.label == key]
                continue
            for i, raw in _nonfence_lines(lines):
                if kind == "fn":
                    m = FOOTNOTE_DEF_RE.match(raw)
                    if m and raw[2:raw.index("]")] == key:
                        out.append((path, i + 1, 0))
                elif kind == "figref":
                    m = REF_DEF_LINE_RE.match(raw)
                    if m and m.group(1).strip().lower() == key:
                        out.append((path, i + 1, 0))
        return out

    def _ref_uses(self, kind, key, book_lines):
        out = []
        for path, lines in book_lines:
            for i, raw in _nonfence_lines(lines):
                for t in refs_in_line(raw):
                    if t[0] == kind and t[1] == key:
                        out.append((path, i + 1, t[2]))
        return out

    def _go_ref(self, path, line, col):
        self.open_at(path, line)
        c = self.editor.textCursor()
        c.setPosition(c.block().position() + min(col, max(0, c.block().length() - 1)))
        self.editor.setTextCursor(c)
        self.editor.centerCursor()

    def follow_reference(self, next_only: bool = False):
        """커서 자리의 참조 ↔ 정의로 간다(각주·`[#라벨]`·`[@키]`·`![캡션][키]`).
        참조 위 → 정의로, 정의 위 → 첫 참조로. next_only 면 같은 키의 다음 참조로(끝에서는 처음으로 돈다)."""
        ctx = self._ref_context()
        if ctx is None:
            self.statusBar().showMessage(
                "커서가 참조·정의 표지(각주 [^이름], [#라벨], [@키], ![캡션][이름]) 위에 있지 않습니다.", 4000)
            return
        self.jump_reference(*ctx, next_only=next_only)

    def jump_reference(self, kind: str, key: str, is_def: bool, next_only: bool = False):
        if self._path is None:
            return
        name = self.REF_KIND_NAMES.get(kind, "참조")
        book_lines = self._nav_book_lines()
        order = {p: n for n, (p, _) in enumerate(book_lines)}
        c = self.editor.textCursor()
        here = (order.get(self._path, -1), c.blockNumber() + 1, c.positionInBlock())
        if is_def or next_only:
            uses = self._ref_uses(kind, key, book_lines)
            if not uses:
                self.statusBar().showMessage(f"{name} [{key}] 의 참조를 찾지 못했습니다.", 5000)
                return
            uses.sort(key=lambda u: (order.get(u[0], 0), u[1], u[2]))
            pick = uses[0]
            if next_only and not is_def:
                for u in uses:
                    if (order.get(u[0], 0), u[1], u[2]) > here:
                        pick = u
                        break
            self._go_ref(*pick)
            if len(uses) > 1:
                n = uses.index(pick) + 1
                self.statusBar().showMessage(
                    f"{name} [{key}] 참조 {n}/{len(uses)} (Ctrl+Alt+Shift+O: 다음 참조)", 5000)
            return
        defs = self._ref_defs(kind, key, book_lines)
        if not defs:
            self.statusBar().showMessage(f"{name} [{key}] 의 정의를 찾지 못했습니다.", 5000)
            return
        self._go_ref(*defs[0])
        if len(defs) > 1:
            self.statusBar().showMessage(f"{name} [{key}] 의 정의가 {len(defs)}곳입니다(첫 곳으로 이동).", 5000)

    def goto_label(self, hit):
        _, path_str, line = hit
        self.open_at(Path(path_str), line)

    # -- 뛴 자리 되짚기 ---------------------------------------------------------

    def _here(self):
        if self._path is None:
            return None
        return (self._path, self.editor.textCursor().blockNumber())

    def push_location(self):
        """지금 위치를 뒤 스택에 얹는다. 다른 곳으로 뛰기 직전에 부른다."""
        here = self._here()
        if here is None or self._jumping:
            return
        if self._back and self._back[-1] == here:
            return
        self._back.append(here)
        if len(self._back) > 100:
            self._back.pop(0)
        self._forward.clear()

    def _go_to(self, loc) -> bool:
        path, block = loc
        if not path.exists():
            return False
        self._jumping = True
        try:
            self.open_path(path, block + 1)
        finally:
            self._jumping = False
        return True

    def jump_back(self):
        here = self._here()
        while self._back:
            target = self._back.pop()
            if self._go_to(target):
                if here:
                    self._forward.append(here)
                return
        self.statusBar().showMessage("더 돌아갈 위치가 없습니다", 1500)

    def jump_forward(self):
        here = self._here()
        while self._forward:
            target = self._forward.pop()
            if self._go_to(target):
                if here:
                    self._back.append(here)
                return
        self.statusBar().showMessage("더 나아갈 위치가 없습니다", 1500)

    # -- 서랍 우클릭: 이름 변경 / 복제 / 삭제 -------------------------------------

    def _unique_name(self, folder: Path, stem: str, suffix: str) -> str:
        candidate = f"{stem} 사본{suffix}"
        n = 2
        while (folder / candidate).exists():
            candidate = f"{stem} 사본 {n}{suffix}"
            n += 1
        return candidate

    def _clear_editor_state(self):
        """지금 열려 있던 파일이 사라졌을 때 편집창을 새 문서 상태로 되돌린다."""
        self.editor.setPlainText("")
        self._path = None
        self._dirty = False
        self.tag_bar.set_tags([])
        self._update_title()
        self._refresh_result_action()

    def rename_item(self, path: Path):
        """부속 파일(.yaml/.bib 등)은 BookIndex 에 없어(node 가 None)
        {{}} 를 고칠 부모도 없다 — 그냥 파일 이름만 바꾼다."""
        is_aux = path.suffix.lower() in Workspace.AUX_SUFFIXES
        node = self.index.by_path.get(path)
        if (node is None and not is_aux) or not path.exists():
            self.refresh_drawer()
            return
        old_name = path.name
        new_name, ok = QInputDialog.getText(
            self, "이름 변경", "새 이름:", text=old_name)
        new_name = new_name.strip()
        if not ok or not new_name or new_name == old_name:
            return
        valid_suffixes = Workspace.AUX_SUFFIXES if is_aux else Workspace.SUFFIXES
        if not new_name.lower().endswith(tuple(s.lower() for s in valid_suffixes)):
            new_name += path.suffix
        new_path = path.parent / new_name
        if new_path.exists():
            QMessageBox.warning(self, "이름 변경 실패", f"{new_name} 이(가) 이미 있습니다.")
            return

        # 부모가 있으면 부모의 {{}} 줄부터 새 이름으로 고친다 — 파일을
        # 먼저 옮기면 그 순간 부모의 포함이 깨진 상태가 잠깐이라도 생긴다.
        if node is not None and node.parent is not None:
            names = [new_name if n == old_name else n
                    for n in self.index.read_includes(node.parent)]
            if not self._rewrite_includes_for_rename(node.parent, names):
                return

        # 이 파일이 책 루트(0단계, 부모 없음)이고 장이 있으면, 그 책의
        # 모든 하위 파일(1단계·2단계)이 ndhmain: 으로 이 파일 이름을
        # 가리키고 있다 — 이름이 바뀌기 전에 그 목록을 미리 구해
        # 둔다(바뀐 뒤에는 옛 이름 기준으로 더는 못 찾는다).
        ndhmain_targets = []
        if node is not None and node.parent is None and node.children:
            ndhmain_targets = [p for p in LabelIndex.book_files(self.index, path) if p != path]

        try:
            path.rename(new_path)
        except OSError as e:
            QMessageBox.warning(self, "이름 변경 실패", str(e))
            return

        old_tags = self.tags.get(path)
        if old_tags:
            self.tags.set(path, [])          # 옛 키 제거
            self.tags.set(new_path, old_tags)
        old_note = self.notes.get(path)
        if old_note:
            self.notes.set(path, "")         # 옛 키 제거
            self.notes.set(new_path, old_note)
        old_syn = self.synopsis.get(path)
        if old_syn:
            self.synopsis.set(path, "")
            self.synopsis.set(new_path, old_syn)

        if self._path == path:
            self.load(new_path)

        for p in ndhmain_targets:
            self._set_ndhmain_hint(p, new_name)

        self.refresh_drawer()

    def _rewrite_includes_for_rename(self, parent: Path, names: list) -> bool:
        if self._path == parent and self._dirty and not self.save_file():
            return False
        if not BookIndex.set_includes(parent, names):
            QMessageBox.warning(self, "쓰기 실패", f"{parent.name} 을(를) 고치지 못했습니다.")
            return False
        if self._path == parent:
            line = self.editor.file_line()
            self.load(parent)
            self.editor.goto_file_line(line)
        return True

    def duplicate_item(self, path: Path):
        """부속 파일은 node 가 없다 — 자식·부모 관련 처리를 전부 건너뛰고
        그냥 복제만 한다."""
        is_aux = path.suffix.lower() in Workspace.AUX_SUFFIXES
        node = self.index.by_path.get(path)
        if (node is None and not is_aux) or not path.exists():
            self.refresh_drawer()
            return
        try:
            text = read_manuscript(path)
        except (OSError, UnicodeDecodeError) as e:
            QMessageBox.warning(self, "복제 실패", str(e))
            return

        new_name = self._unique_name(path.parent, path.stem, path.suffix)
        new_path = path.parent / new_name
        had_children = bool(node.children) if node is not None else False
        try:
            new_path.write_text(text, encoding="utf-8")
        except OSError as e:
            QMessageBox.warning(self, "복제 실패", str(e))
            return
        if had_children:
            # 하위 장까지 복제하면 원본과 같은 자식을 두 책이 나눠 갖는
            # 셈이 되어 BookIndex 가 첫 부모만 인정한다. 혼란을 피하려고
            # 복제본은 포함 없이 시작한다.
            BookIndex.set_includes(new_path, [])

        old_tags = self.tags.get(path)
        if old_tags:
            self.tags.set(new_path, old_tags)

        if node is not None and node.parent is not None:
            names = self.index.read_includes(node.parent)
            try:
                at = names.index(path.name) + 1
            except ValueError:
                at = len(names)
            names.insert(at, new_name)
            self._rewrite_includes_for_rename(node.parent, names)
        else:
            self.refresh_drawer()

        self.open_path(new_path)
        if had_children:
            self.statusBar().showMessage(
                "하위 장은 복제되지 않았습니다 — 원본과 자식을 나눠 가지면 "
                "구조가 애매해지기 때문입니다.", 6000)

    def delete_item(self, path: Path):
        """부속 파일은 node 가 없다 — {{}} 뗄 부모도 없이 그냥 지운다."""
        is_aux = path.suffix.lower() in Workspace.AUX_SUFFIXES
        node = self.index.by_path.get(path)
        if (node is None and not is_aux) or not path.exists():
            self.refresh_drawer()
            return

        detail = ""
        if node is not None and node.children:
            detail = f"\n하위 장 {len(node.children)}개는 최상위로 남습니다."
        r = QMessageBox.question(
            self, "삭제",
            f"{path.name} 을(를) 삭제하시겠습니까?{detail}\n되돌릴 수 없습니다.",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if r != QMessageBox.Yes:
            return

        if node is not None and node.parent is not None:
            self._detach(path)              # 부모의 {{}} 줄에서 먼저 뺀다

        try:
            path.unlink()
        except OSError as e:
            QMessageBox.warning(self, "삭제 실패", str(e))
            return

        self.tags.set(path, [])
        if self._path == path:
            self._clear_editor_state()
        self.refresh_drawer()
        self.refresh_labels()
        self.refresh_toc()

    # -- 장별로 자르기 · 하위 파일 합치기 ----------------------------------------------

    def _doc_depth(self, path: Path) -> int:
        node = self.index.by_path.get(path)
        depth, seen = 0, set()
        while node is not None and node.parent is not None and node.path not in seen:
            seen.add(node.path)
            node = self.index.by_path.get(node.parent)
            depth += 1
        return depth

    def split_into_chapters(self):
        """현재 문서를 최상위 제목마다 잘라 하위 파일로 만들고 {{포함}} 줄로 바꾼다(한 단계만)."""
        if self._path is None or not self.workspace:
            QMessageBox.information(self, "장별로 자르기", "먼저 원고를 열어 주세요.")
            return
        doc = self._path
        node = self.index.by_path.get(doc)
        if node is None:
            QMessageBox.information(self, "장별로 자르기", "작업공간 최상위의 원고만 자를 수 있습니다.")
            return
        depth = self._doc_depth(doc)
        if depth >= 2:
            QMessageBox.information(
                self, "장별로 자르기",
                f"{doc.name} 은(는) 이미 2단계(하위 파일)라 더 자를 수 없습니다.\n포함은 2단계까지만 지원됩니다.")
            return
        if self._dirty and not self.save_file():
            return
        try:
            text = read_manuscript(doc)
        except (OSError, UnicodeDecodeError) as e:
            QMessageBox.warning(self, "장별로 자르기", f"읽지 못했습니다: {e}")
            return
        plan = split_chapter_sections(text)
        if plan is None:
            nxt = next_split_level(text)
            if nxt is None:
                QMessageBox.information(
                    self, "장별로 자르기",
                    "자를 곳이 없습니다 — 같은 수준의 제목이 둘 이상 있어야 합니다\n"
                    "(코드 펜스·환경 안의 # 줄은 세지 않습니다).")
                return
            _l, heads, _t = _scan_headings(text)
            n_next = sum(1 for h in heads if h[1] == nxt)
            box = QMessageBox(self)
            box.setWindowTitle("장별로 자르기")
            box.setIcon(QMessageBox.Information)
            box.setText(f"가장 높은 수준의 제목이 하나뿐이라 그 수준으로는 자를 수 없습니다.\n"
                        f"한 단계 아래({'#' * nxt}) 제목이 {n_next}개 있습니다 — 그 수준으로 자를까요?\n"
                        f"(더 높은 제목과 그 앞의 글은 이 문서에 남습니다.)")
            go = box.addButton(f"{nxt}수준({'#' * nxt})으로 자르기", QMessageBox.AcceptRole)
            box.addButton("닫기", QMessageBox.RejectRole)
            box.exec()
            if box.clickedButton() is not go:
                return
            plan = split_chapter_sections(text, level=nxt)
            if plan is None:
                return
        # 잘려 나가는 구간에 이미 {{포함}} 이 들어 있으면, 그것이 새 하위 파일의 자식이 되어 한 단계 깊어진다.
        for sec in plan["sections"]:
            for name in sec["includes"]:
                child = self.index.by_path.get((doc.parent / name).resolve())
                if depth >= 1 or (child is not None and child.children):
                    QMessageBox.information(
                        self, "장별로 자르기",
                        f"'{sec['title'][:30]}' 구간에 {{{{{name}}}}} 이(가) 들어 있어 자르면 포함이 3단계가 됩니다.\n"
                        f"포함은 2단계까지만 지원되므로 자르지 않습니다. 그 {{{{포함}}}} 줄을 제목 앞쪽으로 옮기거나 "
                        f"먼저 빼 주세요.")
                    return
        dlg = SplitChaptersDialog(self, doc, plan, doc.stem)
        if dlg.exec() != QDialog.Accepted:
            return
        names = dlg.names()
        bodies, new_text = apply_chapter_split(plan, names)
        written = []
        try:
            for n, body in zip(names, bodies):
                path = doc.parent / n
                if path.exists():
                    raise OSError(f"{n} 이(가) 이미 있습니다.")
                path.write_text(body, encoding="utf-8")
                written.append(path)
            doc.write_text(new_text, encoding="utf-8")
        except OSError as e:
            for pth in written:
                try:
                    pth.unlink()
                except OSError:
                    pass
            QMessageBox.warning(self, "장별로 자르기 실패", f"{e}\n만든 파일은 되돌렸습니다.")
            return
        root_name = self._book_root_name(doc)
        for pth in written:
            set_frontmatter_key(pth, "ndhmain", root_name)
        self.load(doc)
        self.refresh_drawer()
        self.refresh_labels()
        self.refresh_toc()
        self.statusBar().showMessage(
            f"{doc.name} 을(를) {len(written)}개 하위 파일로 잘랐습니다 ({names[0]} … {names[-1]}).", 8000)

    def merge_subfiles(self):
        """현재 문서의 {{포함}} 줄(직접 포함한 1단계 하위 파일만)을 그 파일의 내용으로 바꾸고 하위 파일은 지운다."""
        if self._path is None or not self.workspace:
            QMessageBox.information(self, "하위 파일 합치기", "먼저 원고를 열어 주세요.")
            return
        doc = self._path
        node = self.index.by_path.get(doc)
        if node is None or not node.children:
            QMessageBox.information(self, "하위 파일 합치기", f"{doc.name} 은(는) 포함한 하위 파일이 없습니다.")
            return
        if not self.confirm_discard_all("하위 파일 합치기"):
            return
        try:
            text = read_manuscript(doc)
        except (OSError, UnicodeDecodeError) as e:
            QMessageBox.warning(self, "하위 파일 합치기", f"읽지 못했습니다: {e}")
            return
        kids = {p.resolve(): p for p in node.children}
        contents, dropped_all = {}, []
        for rp, p in kids.items():
            try:
                body, dropped = merge_child_text(read_manuscript(p))
            except (OSError, UnicodeDecodeError) as e:
                QMessageBox.warning(self, "하위 파일 합치기", f"{p.name} 을(를) 읽지 못했습니다: {e}")
                return
            contents[rp] = body
            if dropped:
                dropped_all.append(f"  · {p.name}: {', '.join(sorted(set(dropped)))}")
        out, used = [], set()
        for line in text.split("\n"):
            m = INCLUDE_LINE_RE.match(line)
            rp = (doc.parent / m.group(1).strip()).resolve() if m else None
            if rp in contents:
                used.add(rp)
                out.append(contents[rp])
            else:
                out.append(line)
        grand = sum(len(self.index.by_path[p].children) for p in kids.values() if p in self.index.by_path)
        msg = (f"{doc.name} 에 포함된 하위 파일 {len(used)}개의 내용을 이 문서에 그대로 넣고, "
               f"그 파일들을 삭제합니다.\n\n" + "\n".join(f"  · {kids[r].name}" for r in used))
        if grand:
            msg += f"\n\n하위 파일 안의 {{{{포함}}}} 줄 {grand}개는 그대로 남아, 그 파일들이 이 문서의 하위 파일이 됩니다."
        if dropped_all:
            msg += "\n\n다음은 합치면서 사라집니다(프론트매터 키·태그 주석):\n" + "\n".join(dropped_all[:8])
        msg += "\n\n하위 파일에 붙인 태그·메모·시놉시스도 함께 사라집니다. 되돌릴 수 없습니다."
        if QMessageBox.question(self, "하위 파일 합치기", msg,
                                QMessageBox.Yes | QMessageBox.No, QMessageBox.No) != QMessageBox.Yes:
            return
        new_text = "\n".join(out)
        if not new_text.endswith("\n"):
            new_text += "\n"
        try:
            doc.write_text(new_text, encoding="utf-8")
        except OSError as e:
            QMessageBox.warning(self, "하위 파일 합치기", f"쓰지 못했습니다: {e}")
            return
        failed = []
        for rp in used:
            p = kids[rp]
            try:
                p.unlink()
            except OSError as e:
                failed.append(f"{p.name}: {e}")
                continue
            for ext in (".tex", ".nmdsync", ".synctex.gz", ".synctex"):
                try:
                    q = p.with_name(p.stem + ext)
                    if q.is_file():
                        q.unlink()
                except OSError:
                    pass
            self.tags.set(p, [])
        for store in (self.notes, self.synopsis):
            try:
                store.prune()
            except Exception:
                pass
        self.load(doc)
        self.refresh_drawer()
        self.refresh_labels()
        self.refresh_toc()
        if failed:
            QMessageBox.warning(self, "하위 파일을 지우지 못했습니다", "\n".join(failed[:8]))
        self.statusBar().showMessage(f"하위 파일 {len(used) - len(failed)}개를 합쳤습니다.", 8000)

    # -- 태그 -----------------------------------------------------------------

    def commit_tags(self):
        if self._path is None or not self.workspace:
            return
        new = self.tag_bar.tags()
        if new == self.tags.get_active(self._path, self._live_reader):
            return
        self.tags.set(self._path, new)
        self.refresh_drawer()

    # -- 마크업 점검 -------------------------------------------------------------

    def run_lint(self):
        """ndhmd4tex --lint 를 돌려 결과를 아래 패널에 붙인다.

        검사 대상은 **책의 최상위 파일**이다. --lint 가 {{포함}} 을 따라가며
        각주 정의를 파일 전체에서 모아 공유하기 때문이다. 장 하나만 따로
        검사하면 다른 파일에 정의된 각주가 전부 "정의 없음" 오탐이 된다.
        """
        if self._path is None:
            QMessageBox.information(self, "마크업 점검", "먼저 원고를 열어 주세요.")
            return
        if self._lint_proc is not None:
            return                       # 이미 돌고 있다
        if not self.confirm_discard_all("마크업 점검"):
            return
        if not self._ensure_tool():
            return

        target = LabelIndex.book_files(self.index, self._path)[0]
        cmd = self.tool.command(["--lint", str(target)])
        if cmd is None:
            return

        self.issues.populate([], f"{target.name} 검사 중…")
        proc = QProcess(self)
        proc.setWorkingDirectory(str(target.parent))
        proc.setProcessChannelMode(QProcess.MergedChannels)
        proc.finished.connect(
            lambda code, _st, p=proc, tgt=target: self._lint_finished(p, tgt))
        proc.errorOccurred.connect(lambda _e, p=proc: self._lint_failed(p))
        self._lint_proc = proc
        proc.start(cmd[0], cmd[1:])

    def _ensure_tool(self) -> bool:
        if self.tool.path() is not None:
            return True
        QMessageBox.information(
            self, "ndhmd4tex 를 찾지 못했습니다",
            "PATH 에 ndhmd4tex 가 없습니다. 위치를 지정해 주세요.")
        name, _ = QFileDialog.getOpenFileName(
            self, "ndhmd4tex 위치", str(Path.home()),
            "ndhmd4tex (ndhmd4tex ndhmd4tex.py);;모든 파일 (*)")
        if not name:
            return False
        self.tool.set_path(Path(name))
        return True

    def _lint_failed(self, proc):
        if proc is not self._lint_proc:
            return
        self._lint_proc = None
        self._compile_proc = None
        self._compile_target = None
        self.issues.setVisible(False)
        QMessageBox.warning(
            self, "실행 실패",
            "ndhmd4tex 를 실행하지 못했습니다.\n"
            "컴파일 ▸ 마크업 점검를 다시 눌러 위치를 지정할 수 있습니다.")
        self._settings.remove(Ndhmd4tex.SETTING)

    def _lint_finished(self, proc, target: Path):
        if proc is not self._lint_proc:
            return
        self._lint_proc = None
        self._compile_proc = None
        self._compile_target = None
        raw = decode_subprocess_output(bytes(proc.readAllStandardOutput()))
        issues, summary = [], ""
        for raw_line in raw.splitlines():
            line = strip_tool_prefix(raw_line)
            m = LINT_LINE_RE.match(line)
            if m:
                path = self._resolve_issue_path(m.group(1).strip(), target)
                issues.append((path, int(m.group(2)), m.group(3), m.group(4)))
            elif line.strip():
                summary = line.strip()

        if not issues:
            self.issues.setVisible(False)
            self.statusBar().showMessage(
                summary or f"{target.name}: 마크업 문제 없음", 5000)
            return
        n_err = sum(1 for _, _, lv, _ in issues if lv == "오류")
        self.issues.populate(
            issues,
            f"마크업 점검 — {target.name}   오류 {n_err} · 경고 {len(issues) - n_err}"
            f"   (누르면 그 줄로 갑니다)")

    def _resolve_issue_path(self, raw: str, target: Path) -> Path:
        """검사 결과의 경로를 실제 파일로 옮긴다.

        절대경로면 그대로, 상대경로면 대상 폴더 기준. 그래도 없으면 파일
        이름만 떼어 책 안에서 찾는다 — 도구가 어떤 형태로 경로를 찍든
        누르면 열리는 쪽이 낫다.
        """
        path = Path(raw)
        if not path.is_absolute():
            path = (target.parent / path)
        try:
            if path.exists():
                return path.resolve()
        except OSError:
            pass
        name = Path(raw).name
        for candidate in LabelIndex.book_files(self.index, target):
            if candidate.name == name:
                return candidate
        return path

    # dump-meta 
    def send_table_to_tblrdoumi(self, kind: str, source: str):
        """표를 `.tblr`(tblrDoumi 의 JSON 형식) 파일로 만들어 tblrDoumi 로 연다.
        병합 셀(행·열)과 열 정렬을 유지하고, 셀의 마크다운은 LaTeX 로 바꿔 넣는다
        (tblrDoumi 의 셀은 LaTeX 원문이다). 되돌려 받는 것은 tblrDoumi 에서 복사한
        LaTeX 를 이 창에 붙여넣는 것으로 한다 — ndhmd4tex 는 본문의 \\begin{tblr} 을 그대로 통과시킨다."""
        if kind == "grid":
            tbl, _ = parse_grid_table(source.splitlines())
            nrows, ncols = tbl["nrows"], tbl["ncols"]
            aligns = list(tbl["aligns"])
            matrix = [[""] * ncols for _ in range(nrows)]
            spans = {}
            for cl in tbl["cells"]:
                matrix[cl["row"]][cl["col"]] = " ".join(" ".join(cl["paras"]).split())
                spans[(cl["row"], cl["col"])] = (cl["rs"], cl["cs"])
        else:
            fmt, aligns, matrix = TableEditorDialog.parse_table_text(source)
            if fmt != "markdown":
                QMessageBox.information(self, "tblrDoumi", "이 표는 읽을 수 없습니다.")
                return
            nrows, ncols = len(matrix), len(aligns)
            matrix = [list(r) + [""] * (ncols - len(r)) for r in matrix]
            spans = {}
        if any(c.strip() for r in matrix for c in r):
            converted, err = self.convert_table_cells(matrix)
            if converted is None:
                QMessageBox.warning(self, "tblrDoumi", f"셀을 LaTeX 로 바꾸지 못했습니다.\n\n{err}")
                return
            matrix = converted
        cells = [[{"text": matrix[r][c],
                   "row_span": spans.get((r, c), (1, 1))[0],
                   "col_span": spans.get((r, c), (1, 1))[1]}
                  for c in range(ncols)] for r in range(nrows)]
        data = {"tblr_format_version": "3.9", "env_type": "tblr",
                "rows": nrows, "cols": ncols, "cells": cells,
                "colspec": "".join(a if a in "lcr" else "l" for a in aligns),
                "lines": "hlines", "radio_state": "manual"}
        folder = Path(tempfile.gettempdir()) / "ndhmd_tblr"
        folder.mkdir(parents=True, exist_ok=True)
        path = folder / f"table-{time.strftime('%H%M%S')}{int(time.time() * 1000) % 1000:03d}.tblr"
        path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        self.statusBar().showMessage(
            f"tblrDoumi 로 보냈습니다 — 거기서 LaTeX 를 복사해 이 창에 붙여넣으세요. ({path})", 10000)
        self.launch_tblrdoumi(str(path))

    def grid_table_to_tblrdoumi(self, lines: list):
        """grid 표를 TSV 로 클립보드에 넣고 tblrDoumi 를 띄운다. 거기서 붙여넣으면 된다."""
        try:
            tsv = grid_to_tsv(lines)
        except (GridTableError, ValueError) as e:
            QMessageBox.warning(self, "grid 표", f"표를 읽지 못했습니다: {e}")
            return
        QGuiApplication.clipboard().setText(tsv)
        merged = False
        try:
            tbl, _ = parse_grid_table(lines)
            merged = any(c["rs"] > 1 or c["cs"] > 1 for c in tbl["cells"])
        except (GridTableError, ValueError):
            pass
        self.statusBar().showMessage(
            "표를 TSV로 복사했습니다 — tblrDoumi 에서 붙여넣으세요"
            + (" (병합 셀은 풀려서 왼쪽 위 칸에만 글이 있습니다)" if merged else ""), 8000)
        self.launch_tblrdoumi()

    def launch_tblrdoumi(self, file: str = ""):
        """tblrDoumi(사용자가 따로 만든 독립 앱)를 외부 실행한다. 모듈로
        가져다 쓰지 않고 파일(.tblr, JSON)과 클립보드로만 주고받는다 —
        표를 보낼 때는 file 에 .tblr 경로를 주고(send_table_to_tblrdoumi),
        tblrDoumi 에서 만든 표는 복사해 이 창에 Ctrl+V 로 붙여넣는다.

        macOS 는 `open -a` 로 이름만 주고 LaunchServices 에 찾기를
        맡긴다. Windows 는 흔한 설치 자리 두 곳을 직접 본다. 둘 다
        실패하면(또는 그 외 플랫폼이면) 실행 파일을 직접 지정하게
        하고, 다음에는 그 자리를 먼저 써 본다.
        """
        override = self.prefs.tblrdoumi_path()
        if override:
            if Path(override).exists() and self._start_tblrdoumi_at(override, file):
                return
            # 저장해 둔 자리가 없어졌거나 더는 유효하지 않다 — 지우고 계속 진행한다
            self.prefs.write(tblrdoumi_path="")

        if sys.platform == "darwin":
            # 파일을 줄 때는 -n(새 인스턴스) --args 로 실행 인자로 넘긴다. 이미 떠 있는 앱에
            # `open -a 앱 파일` 하면 "파일 열기 이벤트"로 가는데 tblrDoumi 는 인자만 처리한다.
            args = ["-n", "-a", "tblrDoumi", "--args", file] if file else ["-a", "tblrDoumi"]
            if QProcess.startDetached("open", args):
                self.statusBar().showMessage("tblrDoumi 실행 중…", 3000)
                return
        elif sys.platform == "win32":
            found = locate_tblrdoumi()
            if found and self._start_tblrdoumi_at(found, file):
                self.prefs.write(tblrdoumi_path=found)
                return

        r = QMessageBox.question(
            self, "tblrDoumi",
            "tblrDoumi를 정해진 자리에서 찾지 못했습니다. "
            "실행 파일을 직접 지정할까요?",
            QMessageBox.Yes | QMessageBox.No)
        if r != QMessageBox.Yes:
            return
        name_filter = ("tblrDoumi (tblrDoumi.app)" if sys.platform == "darwin"
                       else "tblrDoumi (tblrDoumi.exe)")
        name, _ = QFileDialog.getOpenFileName(
            self, "tblrDoumi 실행 파일 선택", "", name_filter)
        if not name:
            return
        if self._start_tblrdoumi_at(name, file):
            self.prefs.write(tblrdoumi_path=name)
        else:
            QMessageBox.warning(self, "tblrDoumi", "실행하지 못했습니다.")

    @staticmethod
    def _start_tblrdoumi_at(path: str, file: str = "") -> bool:
        if sys.platform == "darwin":
            return bool(QProcess.startDetached(
                "open", ["-n", path, "--args", file] if file else [path]))
        return bool(QProcess.startDetached(path, [file] if file else []))

    def open_shell_command_dialog(self):
        # "지금 파일" 안내와 실행 폴더가 만들 때의 self._path 를 기준으로
        # 굳어지므로, 열려 있던 걸 재사용하지 않고 매번 새로 연다 —
        # 그래야 파일을 바꾼 뒤에도 안내가 맞다.
        old = getattr(self, "_shell_dialog", None)
        if old is not None:
            old.close()
        self._shell_dialog = ShellCommandDialog(self)
        self._shell_dialog.show()
        self._shell_dialog.raise_()

    def run_dump_meta(self):
        if self._path is None:
            QMessageBox.information(self, "프론트매터 덤프", "먼저 원고를 열어 주세요.")
            return
        if self._compile_proc is not None:
            return                       # 이미 다른 컴파일/변환이 진행 중
        if not self.confirm_discard_all("프론트매터 덤프"):
            return
        if not self._ensure_tool():
            return

        target = LabelIndex.book_files(self.index, self._path)[0]
        cmd = self.tool.command(["--dump-meta", "--dump-mapping", str(target)])
        if cmd is None:
            return

        self.statusBar().showMessage(f"{target.name} 메타데이터 덤프 중…")
        proc = QProcess(self)
        proc.setWorkingDirectory(str(target.parent))
        proc.setProcessChannelMode(QProcess.MergedChannels)
        proc.finished.connect(
            lambda code, st, p=proc, tgt=target: self._dump_meta_finished(p, tgt))
        proc.errorOccurred.connect(lambda e, p=proc: self._convert_failed(p))
        self._compile_proc = proc
        proc.start(cmd[0], cmd[1:])

    def _dump_meta_finished(self, proc, target: Path):
        if proc is not self._compile_proc:
            return
        self._compile_proc = None
        
        # 프로세스 출력을 가져와 디코딩합니다.
        raw = decode_subprocess_output(bytes(proc.readAllStandardOutput()))
        # 줄마다 붙은 `[ndhmd] ` 는 가리고 보여 준다. 뒤의 공백은 한 칸만
        # 떼어, 들여쓴 YAML 줄의 들여쓰기가 살아 있게 한다.
        raw = re.sub(r"^\[ndhmd\] ?", "", raw, flags=re.M)
        self.statusBar().showMessage("프론트매터 덤프 완료", 4000)
        
        # 기존에 정의된 ConsoleOutputDialog를 재사용하여 텍스트 위젯으로 표시합니다.
        ConsoleOutputDialog(self, f"프론트매터 덤프 결과 — {target.name}", raw).show()

    # -- 컴파일 -------------------------------------------------------------------

    def animation_args(self) -> list:
        """환경설정의 애니메이션 설정 → ndhmd4tex 인자. 꺼져 있으면 없다.
        `--animation` 은 값을 받을 수 있는 옵션이라 `=` 로 붙여야 한다 — 떼어 쓰면 뒤의
        원고 경로를 값으로 삼켜 버린다."""
        if not self.prefs.animation():
            return []
        n = self.prefs.animation_frames()
        return ["--animation=all" if n <= 0 else f"--animation={n}"]

    def run_compile(self, scope: str = "book"):
        """scope: 'book' — 책 최상위(포함을 다 펼친 전체),
                  'file' — 지금 연 파일만 낱장으로(자신의 front matter,
                  setup: 상속은 그대로 적용된다). 부모가 없는 파일이면
                  둘은 같은 대상이 된다.
        """
        if self._path is None:
            QMessageBox.information(self, "컴파일", "먼저 원고를 열어 주세요.")
            return
        if self._compile_proc is not None:
            return                       # 이미 진행 중
        if not self.confirm_discard_all("컴파일"):
            return
        if not self._ensure_tool():
            return
        target = (self._path if scope == "file"
                 else LabelIndex.book_files(self.index, self._path)[0])
        self._compile_target = target
        self._start_convert(target)

    def _start_convert(self, target: Path):
        cmd = self.tool.command(["--syncinfo", *self.animation_args(), str(target)])
        if cmd is None:
            return
        self.issues.setVisible(False)
        self.statusBar().showMessage(f"{target.name} 변환 중…")
        proc = QProcess(self)
        proc.setWorkingDirectory(str(target.parent))
        proc.setProcessChannelMode(QProcess.MergedChannels)
        proc.finished.connect(
            lambda code, st, p=proc, tgt=target: self._convert_finished(p, tgt))
        proc.errorOccurred.connect(lambda e, p=proc: self._convert_failed(p))
        self._compile_proc = proc
        proc.start(cmd[0], cmd[1:])

    def _convert_failed(self, proc):
        if proc is not self._compile_proc:
            return
        self._compile_proc = None
        QMessageBox.warning(self, "실행 실패", "ndhmd4tex 를 실행하지 못했습니다.")

    def _convert_finished(self, proc, target: Path):
        if proc is not self._compile_proc:
            return
        self._compile_proc = None
        raw = decode_subprocess_output(bytes(proc.readAllStandardOutput()))
        self._refresh_result_action()

        if proc.exitCode() != 0:
            issues = self._parse_issue_lines(raw, target)
            if issues:
                n_err = sum(1 for _, _, lv, _ in issues if lv == "오류")
                self.issues.populate(
                    issues, f"변환 실패 — {target.name}   오류 {n_err} · "
                           f"경고 {len(issues) - n_err}")
            else:
                ConsoleOutputDialog(
                    self, "변환 실패", "\n".join(
                        strip_tool_prefix(l) for l in raw.splitlines())).show()
            return

        self._start_build(target)

    def _parse_issue_lines(self, raw: str, target: Path) -> list:
        """--lint 와 --syncinfo 실패가 같은 `[ndhmd] 경로:줄: 등급: 메시지`
        형식을 쓰므로 파싱을 공유한다."""
        issues = []
        for raw_line in raw.splitlines():
            line = strip_tool_prefix(raw_line)
            m = LINT_LINE_RE.match(line)
            if m:
                path = self._resolve_issue_path(m.group(1).strip(), target)
                issues.append((path, int(m.group(2)), m.group(3), m.group(4)))
        return issues

    # -- 실제 조판 --------------------------------------------------------------

    def _start_build(self, target: Path):
        tex_path = target.with_suffix(".tex")
        if not tex_path.exists():
            QMessageBox.warning(self, "컴파일 실패",
                                f"{tex_path.name} 이(가) 생성되지 않았습니다.")
            return
        backend = self.prefs.compiler_backend()
        engine = self.prefs.tex_engine()
        cmd = (self._latexmk_command(tex_path, engine, target) if backend == "latexmk"
              else self._ksruncltex_command(tex_path, engine, target))
        if cmd is None:
            return

        self._build_started = time.time()
        self.statusBar().showMessage(f"{tex_path.name} 컴파일 중… ({backend})")
        proc = QProcess(self)
        proc.setWorkingDirectory(str(target.parent))
        proc.setProcessChannelMode(QProcess.MergedChannels)
        proc.finished.connect(
            lambda code, st, p=proc, tgt=target, be=backend: self._build_finished(p, tgt, be))
        proc.errorOccurred.connect(
            lambda e, p=proc, be=backend: self._build_failed(p, be))
        self._compile_proc = proc
        proc.start(cmd[0], cmd[1:])

    def _latexmk_command(self, tex_path: Path, engine: str, target: Path):
        latexmk_bin = shutil.which("latexmk")
        if latexmk_bin is None:
            QMessageBox.warning(
                self, "latexmk 를 찾지 못했습니다",
                "PATH 에 latexmk 가 없습니다. TeX Live/MiKTeX 설치를 확인하십시오.")
            return None
        flag = LATEXMK_ENGINE_FLAG.get(engine, "-pdfxe")
        meta = Preamble.meta(self.index, target, self._live_reader)
        raw_opts = meta.get("latexmkoption", "")
        opts = shlex.split(raw_opts) if isinstance(raw_opts, str) and raw_opts.strip() else []
        args = ensure_synctex_flag([flag, "-interaction=nonstopmode", *opts], "-synctex=1")
        return [latexmk_bin, *args, tex_path.name]

    def _locate_ksruncltex(self):
        """ndhmd4tex 이 자기 안에서 찾는 방식 그대로 — texlua + kpsewhich."""
        if sys.platform == "win32":
            found = shutil.which("ksruncltex.bat") or shutil.which("ksruncltex")
            return [found] if found else None
        texlua = shutil.which("texlua")
        if texlua is None:
            return None
        try:
            out = subprocess.run(["kpsewhich", "ksruncltex.lua"],
                                 capture_output=True, text=True, timeout=10,
                                 creationflags=_NO_WINDOW)
        except (OSError, subprocess.SubprocessError):
            return None
        path = out.stdout.strip()
        return [texlua, path] if path else None

    def _ksruncltex_command(self, tex_path: Path, engine: str, target: Path):
        base = self._locate_ksruncltex()
        if base is None:
            QMessageBox.warning(
                self, "ksruncltex 를 찾지 못했습니다",
                "texlua/kpsewhich 를 PATH 에서 찾지 못했거나 ksruncltex 이 "
                "설치돼 있지 않은 것 같습니다.")
            return None
        flag = KSRUNCLTEX_ENGINE_FLAG.get(engine, "--xelatex")
        meta = Preamble.meta(self.index, target, self._live_reader)
        raw_opts = meta.get("compileoption", "")
        opts = shlex.split(raw_opts) if isinstance(raw_opts, str) and raw_opts.strip() else []
        args = ensure_synctex_flag([flag, *opts], "--synctex=1")
        return [*base, *args, tex_path.name]

    def _check_compile_notes(self) -> str:
        """컴파일이 끝났으니 작업공간을 한 번 갱신해 컴파일 참고 파일
        (ksruncltex_missingchar.txt 등)이 서랍에 나타나게 한다. 이번 컴파일에 새로 만들어
        졌거나 고쳐진 것이 있으면 상태줄에 덧붙일 문구를 돌려준다(없으면 빈 문자열)."""
        self.refresh_drawer()
        started = getattr(self, "_build_started", 0) - 2     # 파일 시각의 오차 여유
        fresh = []
        for p in (self.workspace.compile_note_files() if self.workspace else ()):
            try:
                if p.stat().st_mtime >= started:
                    fresh.append(p.name)
            except OSError:
                pass
        if not fresh:
            return ""
        if not self.drawer.isVisible():
            return f"   ·   ⚠ {', '.join(fresh)} 생김"
        return f"   ·   ⚠ 서랍 ▸ 컴파일 참고: {', '.join(fresh)}"

    def delete_compile_note(self, path: Path):
        if QMessageBox.question(
                self, "컴파일 참고 삭제",
                f"{path.name} 을(를) 삭제할까요? 다음 컴파일에서 필요하면 다시 만들어집니다.",
                QMessageBox.Yes | QMessageBox.No, QMessageBox.No) != QMessageBox.Yes:
            return
        try:
            path.unlink()
        except OSError as e:
            QMessageBox.warning(self, "컴파일 참고 삭제", f"삭제하지 못했습니다: {e}")
            return
        self.refresh_drawer()

    def _build_failed(self, proc, backend: str):
        if proc is not self._compile_proc:
            return
        self._compile_proc = None
        QMessageBox.warning(self, "실행 실패", f"{backend} 를 실행하지 못했습니다.")

    def _build_finished(self, proc, target: Path, backend: str):
        if proc is not self._compile_proc:
            return
        self._compile_proc = None
        raw = decode_subprocess_output(bytes(proc.readAllStandardOutput()))
        ok = proc.exitStatus() == QProcess.NormalExit and proc.exitCode() == 0
        note = self._check_compile_notes()

        if ok:
            pdf = target.with_suffix(".pdf")
            cleaned = self._clean_sub_products(target)
            if cleaned:
                note += f"   ·   하위 파일 낡은 산출물 {cleaned}개 정리"
            self.statusBar().showMessage(f"컴파일 성공 — {pdf.name}{note}", 6000)
            if pdf.exists():
                self._open_compiled_pdf(pdf)
            return

        if backend == "latexmk":
            issues = self._parse_tex_log(target.with_suffix(".log"), target)
            if issues:
                self.issues.populate(
                    issues, f"컴파일 실패 — {target.name}   오류 {len(issues)}개   "
                           f"(누르면 그 줄로 갑니다)")
                return
        # ksruncltex 는 애초에 로그 형식을 모르므로 파싱하지 않는다 — 콘솔
        # 출력을 그대로 보여주는 것으로 대신한다. latexmk 도 .log 에서
        # 오류를 못 찾으면 같은 길로 떨어진다.
        locs = self.tex_error_locations(raw, target)
        if not locs and backend == "latexmk":
            try:
                locs = self.tex_error_locations(
                    target.with_suffix(".log").read_text(
                        encoding="utf-8", errors="replace"), target)
            except OSError:
                pass
        ConsoleOutputDialog(self, f"컴파일 실패 ({backend})", raw, locs).show()

    # -- 컴파일 뒤 PDF 열기 -------------------------------------------------------

    SUB_PRODUCT_EXT = (".tex", ".nmdsync", ".synctex.gz", ".synctex")

    def _clean_sub_products(self, target: Path) -> int:
        """책 최상위(target)를 방금 컴파일했으면, 그 책 하위 파일들의 단독
        산출물(.tex/.nmdsync/.synctex)을 지운다. 이전에 '이 파일만'으로 만든
        낡은 것이라 책 PDF 와 어긋난다. PDF 는 건드리지 않는다.
        지운 파일 수를 돌려준다."""
        if not self.prefs.clean_sub_products():
            return 0
        try:
            files = LabelIndex.book_files(self.index, target)
        except Exception:
            return 0
        if len(files) < 2 or files[0] != target:
            return 0                     # 하위 파일만 컴파일한 경우 등
        keep = {target.with_suffix(e) for e in self.SUB_PRODUCT_EXT}
        n = 0
        for sub in files[1:]:
            if sub.suffix.lower() != ".md":
                continue
            for e in self.SUB_PRODUCT_EXT:
                c = sub.with_suffix(e) if e == ".tex" or e == ".nmdsync" else \
                    sub.with_name(sub.stem + e)
                if c in keep:
                    continue
                try:
                    if c.is_file():
                        c.unlink()
                        n += 1
                except OSError:
                    pass
        return n

    def _open_compiled_pdf(self, pdf: Path):
        """컴파일이 성공한 뒤 PDF 를 연다. 기본은 정방향 검색이다.

        시스템 기본 PDF 뷰어와 정방향 검색용으로 등록한 뷰어가 다르면, 컴파일
        직후에 시스템 뷰어로 열고 나서 정방향 검색을 하면 뷰어가 둘 뜬다.
        그래서 열 때부터 정방향 검색(ndhmdsync)을 쓴다 — 그러면 등록한 뷰어
        하나만, 게다가 커서 위치에서 열린다.

        하위 원고를 따로 컴파일했을 때처럼 정방향 검색이 안 되는 경우에는
        (ndhmdsync 가 실패로 끝난다) PDF 만 연다. 그것도 등록한 뷰어가 있으면
        그 뷰어로 연다(`_open_pdf_plain`) — 시스템 뷰어로 돌아가면 다시 둘이 뜬다.
        """
        mode = self.prefs.after_compile()
        if mode == "none":
            return
        if mode == "system":
            QDesktopServices.openUrl(QUrl.fromLocalFile(str(pdf)))
            return
        cmd = None
        if self._path is not None:
            cmd = self.sync_tool.command([str(self._path), "--md-line",
                                          str(self.editor.file_line())])
        if cmd is None:
            self._open_pdf_plain(pdf)
            return
        proc = QProcess(self)
        proc.setProcessChannelMode(QProcess.MergedChannels)

        failed = []

        def fallback():
            self.statusBar().showMessage(
                "정방향 검색이 되지 않아 PDF 만 열었습니다 (하위 원고만 컴파일했을 수 있습니다)", 6000)
            self._open_pdf_plain(pdf)

        def done(_code=0, _st=None, p=proc):
            if failed:
                return                  # errorOccurred 가 이미 처리했다
            if p.exitStatus() == QProcess.NormalExit and p.exitCode() == 0:
                return
            fallback()

        def errored(_e=None):
            if not failed:
                failed.append(1)
                fallback()

        proc.finished.connect(done)
        proc.errorOccurred.connect(errored)
        proc.start(cmd[0], cmd[1:])

    def _open_pdf_plain(self, pdf: Path):
        """위치 없이 PDF 만 연다. 정방향 검색용으로 찾은 뷰어가 있으면 같은 뷰어로,
        없으면 시스템 기본 뷰어로 연다."""
        exe, _template = locate_pdf_viewer()
        args = None
        if exe:
            if sys.platform == "win32":
                args = [exe, "-reuse-instance", str(pdf)]        # SumatraPDF
            elif sys.platform == "darwin":
                args = ["open", "-a", "Skim", str(pdf)]
            else:
                args = [exe, "--unique", str(pdf)]               # Okular
        if args and QProcess.startDetached(args[0], args[1:]):
            return
        QDesktopServices.openUrl(QUrl.fromLocalFile(str(pdf)))

    def _parse_tex_log(self, log_path: Path, target: Path) -> list:
        try:
            lines = log_path.read_text(encoding="utf-8", errors="replace").splitlines()
        except OSError:
            return []
        sync = NmdSync.load(target.with_suffix(".nmdsync"))
        issues = []
        i = 0
        while i < len(lines):
            m = LOG_ERROR_RE.match(lines[i])
            if m:
                msg = m.group(1).strip()
                texline = None
                for j in range(i + 1, min(i + 8, len(lines))):
                    lm = LOG_LINE_RE.match(lines[j])
                    if lm:
                        texline = int(lm.group(1))
                        break
                src, srcline = (sync.source_for(texline) if texline is not None
                               else (None, None))
                path = src if src is not None else target.with_suffix(".tex")
                if not path.is_absolute():
                    path = (target.parent / path).resolve()
                issues.append((path, srcline or texline or 1, "오류", msg))
            i += 1
        return issues

    _TEX_FLE_RE = re.compile(r"^(.+?\.tex):(\d+):\s*(.*)$")

    def tex_error_locations(self, raw: str, target: Path) -> list:
        """컴파일 출력에서 tex 오류 위치를 찾아 원고 위치로 되짚는다.

        `./note1.tex:23: Undefined control sequence.` 꼴(file-line-error)과 옛 꼴
        (`! 메시지` 뒤의 `l.23 …`) 둘 다 읽는다. 변환한 그 .tex(책 최상위 또는 지금
        대상) 안의 행만 .nmdsync 로 원고 행에 되짚는다 — .sty 따위 다른 파일의 행은
        원고에 대응이 없으므로 뺀다. 같은 tex 행은 한 번만. 반환:
        [(원고 경로, 원고 행, tex 행, 메시지), ...] (출력에 나온 순서).
        """
        tex_name = target.with_suffix(".tex").name
        found, seen = [], set()

        def add(texline, msg):
            if texline in seen:
                return
            seen.add(texline)
            found.append((texline, msg))

        lines = raw.splitlines()
        for ln in lines:
            m = self._TEX_FLE_RE.match(strip_tool_prefix(ln).strip())
            if m and Path(m.group(1)).name == tex_name and not m.group(3).startswith("==>"):
                add(int(m.group(2)), m.group(3).strip())
        if not found:                                  # 옛 꼴: ! msg / l.N
            for i, ln in enumerate(lines):
                m = LOG_ERROR_RE.match(ln)
                if not m:
                    continue
                for j in range(i + 1, min(i + 8, len(lines))):
                    lm = LOG_LINE_RE.match(lines[j])
                    if lm:
                        add(int(lm.group(1)), m.group(1).strip())
                        break
        if not found:
            return []
        sync = NmdSync.load(target.with_suffix(".nmdsync"))
        out = []
        for texline, msg in found:
            src, srcline = sync.source_for(texline)
            if src is None:
                continue
            if not src.is_absolute():
                src = (target.parent / src).resolve()
            out.append((src, srcline, texline, msg))
        return out

    def close_issues(self):
        self.issues.setVisible(False)

    # -- 산출물 ---------------------------------------------------------------

    def result_tex_path(self) -> Path | None:
        """지금 컴파일 대상이 되는 .tex 경로.

        마크업 점검·그림 점검과 같은 기준(책 최상위)을 쓴다 — 컴파일도
        항상 책 전체를 대상으로 하므로, 장 파일을 보고 있어도 실제로
        만들어지는 것은 책 최상위 파일의 .tex 다. 나중에 "책 전체 / 이
        장만" 토글이 생기면 그 판단은 이 한 함수 안에서만 바뀐다.
        """
        if self._path is None:
            return None
        return LabelIndex.book_files(self.index, self._path)[0].with_suffix(".tex")

    def result_pdf_path(self) -> Path | None:
        tex = self.result_tex_path()
        return tex.with_suffix(".pdf") if tex else None

    def _refresh_result_action(self):
        tex = self.result_tex_path()
        self._act_open_tex.setEnabled(tex is not None and tex.exists())

    def convert_and_open_tex(self):
        """`ndhmd4tex {파일}.md` 만 실행해(컴파일 없이 변환만) 나온 .tex 를
        시스템 기본 편집기로 연다.

        책/이 파일 구분을 두지 않는다 — 지금 열려 있는 파일 하나만 대상이다.
        책 전체를 변환하고 싶으면 main 파일을 직접 열어서 이 메뉴를 쓰면
        되므로, 별도의 스코프 선택지가 필요 없다.
        """
        if self._path is None:
            QMessageBox.information(self, "변환후 tex 열기", "먼저 원고를 열어 주세요.")
            return
        if self._compile_proc is not None:
            return                       # 이미 다른 컴파일/변환이 진행 중
        if not self.confirm_discard_all("변환후 tex 열기"):
            return
        if not self._ensure_tool():
            return

        target = self._path
        cmd = self.tool.command([*self.animation_args(), str(target)])
        if cmd is None:
            return

        self.statusBar().showMessage(f"{target.name} 변환 중…")
        proc = QProcess(self)
        proc.setWorkingDirectory(str(target.parent))
        proc.setProcessChannelMode(QProcess.MergedChannels)
        proc.finished.connect(
            lambda code, st, p=proc, tgt=target: self._convert_open_finished(p, tgt))
        proc.errorOccurred.connect(lambda e, p=proc: self._convert_failed(p))
        self._compile_proc = proc
        proc.start(cmd[0], cmd[1:])

    def _convert_open_finished(self, proc, target: Path):
        if proc is not self._compile_proc:
            return
        self._compile_proc = None
        raw = decode_subprocess_output(bytes(proc.readAllStandardOutput()))

        if proc.exitCode() != 0:
            issues = self._parse_issue_lines(raw, target)
            if issues:
                n_err = sum(1 for _, _, lv, _ in issues if lv == "오류")
                self.issues.populate(
                    issues, f"변환 실패 — {target.name}   오류 {n_err} · "
                           f"경고 {len(issues) - n_err}")
            else:
                ConsoleOutputDialog(
                    self, "변환 실패", "\n".join(
                        strip_tool_prefix(l) for l in raw.splitlines())).show()
            return

        tex_path = target.with_suffix(".tex")
        self._refresh_result_action()
        if not tex_path.exists():
            QMessageBox.warning(self, "변환 실패",
                                f"{tex_path.name} 이(가) 생성되지 않았습니다.")
            return
        if not QDesktopServices.openUrl(QUrl.fromLocalFile(str(tex_path))):
            QMessageBox.warning(
                self, "열기 실패",
                f"시스템에 .tex 를 여는 기본 프로그램이 연결되어 있지 않은 것 "
                f"같습니다.\n\n{tex_path}")
            return
        self.statusBar().showMessage(f"열었습니다 — {tex_path.name}", 4000)

    #: latexmk -C 는 자기가 만들었다고 기억하는 것만 지운다. ksruncltex 로
    #: 만든 산출물이나 latexmk 의 기록(.fls/.fdb_latexmk)이 이미 지워진
    #: 뒤라면 놓칠 수 있으므로, 확장자로 한 번 더 확실히 훑는다.
    CLEAN_AUX_EXT = (
        ".pdf", ".log", ".aux", ".out", ".toc", ".lof", ".lot",
        ".fls", ".fdb_latexmk", ".synctex.gz", ".bbl", ".blg",
        ".idx", ".ind", ".ilg", ".nav", ".snm", ".vrb", ".xdv",
        ".bcf", ".run.xml",
        # SumatraPDF 가 역방향 검색을 한 번이라도 하면 .synctex.gz 를
        # 풀어서 이 이름으로 남겨 둔다. 그냥 편 것뿐이라 내용도 필요
        # 없다 — synctex 뷰어(dvisvgm 등)가 만드는 것과 달리 이건
        # 순수하게 뷰어 쪽 캐시다.
        ".synctex.gz.sum.synctex",
    )

    def clean_workspace(self):
        """작업공간의 모든 .tex 산출물을 지운다. md 원고와 _images/ 캐시는
        건드리지 않는다 — 후자는 빌드 부산물이 아니라 다시 받으려면
        네트워크가 필요한 캐시이기 때문이다.

        latexmk -C 로 각 .tex 가 만든 것을 먼저 지우게 하고(자기 기록을
        보고 정확하게 지운다), 그다음 .tex 자신과 .nmdsync 를 지우고,
        마지막으로 알려진 LaTeX 부산물 확장자를 한 번 더 훑어 ksruncltex
        로 만든 것처럼 latexmk 가 모르는 파일까지 마저 정리한다.
        """
        if not self.workspace:
            QMessageBox.information(self, "작업공간 청소", "먼저 작업공간을 열어 주세요.")
            return
        if self._compile_proc is not None:
            QMessageBox.information(
                self, "작업공간 청소",
                "컴파일이 진행 중입니다. 끝난 뒤 다시 시도해 주세요.")
            return

        tex_files = [
            p for p in self.workspace.root.rglob("*.tex")
            if p.with_suffix(".md").exists()      # 조각 그림의 .tex 는 소스이지 산출물이 아니다
            and not any(part in Workspace.SKIP_DIRS or part.startswith(".")
                        for part in p.relative_to(self.workspace.root).parts[:-1])]
        if not tex_files:
            QMessageBox.information(
                self, "작업공간 청소", "지울 산출물이 없습니다 — 원고(.md)에서 만들어진 .tex 가 없습니다.")
            return

        r = QMessageBox.question(
            self, "작업공간 청소",
            f"{len(tex_files)}개 원고의 .tex 와 그 산출물(pdf, log, aux 등)을 "
            f"모두 지웁니다.\nmd 원고는 건드리지 않습니다. 되돌릴 수 없습니다.\n"
            f"계속할까요?",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if r != QMessageBox.Yes:
            return

        latexmk_bin = shutil.which("latexmk")
        QApplication.setOverrideCursor(Qt.WaitCursor)
        removed, failed = 0, []
        try:
            for tex in tex_files:
                if latexmk_bin is not None:
                    try:
                        subprocess.run([latexmk_bin, "-C", tex.name],
                                       cwd=tex.parent, capture_output=True, timeout=30,
                                       creationflags=_NO_WINDOW)
                    except (OSError, subprocess.SubprocessError) as e:
                        failed.append(f"{tex.name}: latexmk -C 실패 ({e})")

                candidates = [tex, tex.with_suffix(".nmdsync")]
                candidates += [tex.with_suffix(ext) for ext in self.CLEAN_AUX_EXT]
                for c in candidates:
                    try:
                        if c.is_file():
                            c.unlink()
                            removed += 1
                    except OSError as e:
                        failed.append(f"{c.name}: {e}")
        finally:
            QApplication.restoreOverrideCursor()

        self._refresh_result_action()
        msg = f"작업공간 청소 완료 — 원고 {len(tex_files)}개, 파일 {removed}개 삭제"
        if failed:
            QMessageBox.warning(
                self, "작업공간 청소 — 일부 실패",
                msg + "\n\n" + "\n".join(failed[:8]))
        else:
            self.statusBar().showMessage(msg, 6000)

    def open_result_tex(self):
        """컴파일 결과 .tex 를 시스템 기본 프로그램으로 넘긴다.

        .tex 는 원고가 아니라 산출물이므로 이 앱에서 편집하지 않는다.
        작업공간의 SUFFIXES 에 .tex 가 없는 것도 같은 이유다.
        """
        tex = self.result_tex_path()
        if tex is None:
            QMessageBox.information(self, "결과 tex", "먼저 원고를 열어 주세요.")
            return
        if not tex.exists():
            QMessageBox.information(
                self, "결과 tex 없음",
                f"{tex.name} 이(가) 아직 없습니다.\n"
                f"원고를 컴파일하면 원고와 같은 폴더에 생깁니다.")
            return
        if not QDesktopServices.openUrl(QUrl.fromLocalFile(str(tex))):
            QMessageBox.warning(
                self, "열기 실패",
                f"시스템에 .tex 를 여는 기본 프로그램이 연결되어 있지 않은 것 "
                f"같습니다.\n\n{tex}")

    # -- sync ---------------------------------------------------------------

    def _on_ipc_connection(self):
        """다른 인스턴스가 --goto 등을 들고 왔다. 새 창을 띄우는 대신
        이 창에서 처리하고, 창을 앞으로 가져온다."""
        sock = self._ipc_server.nextPendingConnection()
        if sock is None:
            return
        if sock.waitForReadyRead(1000):
            data = bytes(sock.readAll()).decode("utf-8", "replace")
            argv = data.split("\x00") if data else []
            process_argv(self, argv)
        sock.disconnectFromServer()
        self.showNormal()
        self.raise_()
        self.activateWindow()

    def forward_search(self):
        """지금 커서 위치에서 PDF의 대응 위치를 연다.

        md->tex 줄 변환과 뷰어 호출은 ndhmdsync 가 전부 안다 — 이 앱은
        그 명령 하나를 실행할 뿐이다. ndhmdsync 는 디스크의 .md/.nmdsync
        를 읽으므로, 저장 안 한 편집은 반영되지 않는다 — 먼저 저장한다.
        """
        if self._path is None:
            return
        if self._dirty and not self.save_file():
            return
        extra = self._forward_product_args(self._path)
        cmd = self.sync_tool.command([str(self._path), "--md-line",
                                      str(self.editor.file_line()), *extra])
        if cmd is None:
            QMessageBox.warning(
                self, "ndhmdsync 를 찾지 못했습니다",
                "PATH 에 ndhmdsync 가 없습니다. 설정에서 위치를 지정하십시오.")
            return
        self._run_forward(cmd, retry_after_compile=True)

    def _forward_product_args(self, md: Path) -> list:
        """정방향 검색이 쓸 .nmdsync/.tex/.pdf 를 명시한다.

        하위 파일 자신의 .nmdsync 와 PDF 가 둘 다 있으면(= 책 컴파일 뒤에
        '이 파일만' 으로 만든 최신 단독 결과) 컴파일 없이 그쪽으로 싱크한다.
        아니면 책 최상위의 산출물을 가리킨다 — ndhmain: 힌트가 없는 하위
        파일도 책의 PDF 로 가게 된다. 책이 아니거나 최상위 파일이면 비워
        두어 ndhmdsync 의 기본 동작에 맡긴다."""
        try:
            files = LabelIndex.book_files(self.index, md)
        except Exception:
            return []
        if len(files) < 2 or files[0] == md:
            return []
        own_sync, own_pdf = md.with_suffix(".nmdsync"), md.with_suffix(".pdf")
        base = md if (own_sync.is_file() and own_pdf.is_file()) else files[0]
        return ["--sync-file", str(base.with_suffix(".nmdsync")),
                "--tex", str(base.with_suffix(".tex")),
                "--pdf", str(base.with_suffix(".pdf"))]

    def _run_forward(self, cmd: list, retry_after_compile: bool):
        proc = QProcess(self)
        proc.setProcessChannelMode(QProcess.MergedChannels)
        # _suppress_console() 는 일부러 안 건다. ndhmdsync 자신이 PDF
        # 뷰어를 또 자식 프로세스로 띄워야 하는데, 예전에 ndhmd4tex 를
        # 이걸로 감쌌다가 Windows 에서 표준입력이 애매해지며 멈췄던 것과
        # 같은 종류의 위험이 여기서는 더 크다 — 뷰어를 못 띄우고 조용히
        # 아무 반응이 없는 형태로 나타날 수 있다. 콘솔이 잠깐 깜빡이는
        # 것이, 정방향 검색이 아예 안 되는 것보다 훨씬 낫다.
        proc.finished.connect(
            lambda code, st, p=proc, c=cmd, r=retry_after_compile:
                self._forward_finished(p, c, r))
        proc.errorOccurred.connect(lambda e, p=proc: self._convert_failed(p))
        proc.start(cmd[0], cmd[1:])

    def _forward_finished(self, proc, cmd: list, retry_after_compile: bool):
        raw = decode_subprocess_output(bytes(proc.readAllStandardOutput()))
        if proc.exitCode() == 0:
            return
        # ndhmdsync 는 .nmdsync 자체가 없으면 "동기화 정보를 찾을 수
        # 없습니다"를, .nmdsync 는 있는데 PDF 만 없으면 "PDF 파일이
        # 없습니다"를 낸다(순서대로 검사하므로 후자는 전자를 통과한
        # 뒤에만 나온다) — 둘 다 결국 "아직 컴파일 안 함"이라 똑같이
        # 컴파일을 제안한다.
        NOT_COMPILED_YET = ("PDF 파일이 없습니다", "동기화 정보를 찾을 수 없습니다")
        if retry_after_compile and any(m in raw for m in NOT_COMPILED_YET):
            r = QMessageBox.question(
                self, "PDF 없음",
                "아직 컴파일한 적이 없어 PDF가 없습니다. 지금 컴파일할까요?",
                QMessageBox.Yes | QMessageBox.No)
            if r == QMessageBox.Yes:
                self._compile_then_forward_search(cmd)
            return
        ConsoleOutputDialog(self, "PDF에서 열지 못했습니다", raw).show()

    def _compile_then_forward_search(self, forward_cmd: list):
        """컴파일이 끝나면(성공이든 실패든) 정방향 검색을 한 번만 더
        시도한다 — 실패해도 두 번 세 번 반복해 괴롭히지 않는다.

        컴파일은 --syncinfo 변환(1단계)과 실제 조판(2단계)이 서로 다른
        QProcess 로 이어진다 — 1단계가 끝나면 self._compile_proc 이
        2단계의 새 QProcess 로 통째로 바뀐다. 그래서 1단계 QProcess 의
        finished 에 직접 연결하면 2단계가 끝나기 전에 너무 일찍 재시도
        하게 된다(연결한 신호의 정체가 이미 바뀌어 있으니 disconnect
        도 엉뚱한 대상에 걸린다). self._compile_proc 이 완전히 None이
        될 때까지 타이머로 지켜보는 쪽이 어느 단계가 몇 개든 안전하다.
        """
        if self._compile_proc is not None:
            return
        self.run_compile("book")

        timer = QTimer(self)
        timer.setInterval(200)

        def check():
            if self._compile_proc is not None:
                return                  # 아직 진행 중 — 다음 tick 에 다시 본다
            timer.stop()
            timer.deleteLater()
            self._run_forward(forward_cmd, retry_after_compile=False)

        timer.timeout.connect(check)
        timer.start()

    def _write_ndhmdsync_section(self, section: str, key: str, value: str) -> bool:
        """ndhmdsync.ini 의 한 섹션·키만 갱신한다. 다른 섹션(뷰어
        커스터마이즈, 에디터 등록 등)은 그대로 둔다. 에디터 등록과 PDF
        뷰어 등록이 이 로직을 그대로 같이 쓴다 — 섹션 이름과 값만
        다르다."""
        ini_path = ndhmdsync_config_path()
        config = configparser.ConfigParser(interpolation=None)
        if ini_path.is_file():
            try:
                config.read(ini_path, encoding="utf-8")
            except configparser.Error as e:
                QMessageBox.warning(
                    self, "등록 실패", f"{ini_path} 를 읽는 중 오류:\n{e}")
                return False
        if not config.has_section(section):
            config.add_section(section)
        config.set(section, key, value)
        try:
            ini_path.parent.mkdir(parents=True, exist_ok=True)
            with open(ini_path, "w", encoding="utf-8") as f:
                config.write(f)
        except OSError as e:
            QMessageBox.warning(
                self, "등록 실패", f"{ini_path} 에 쓰지 못했습니다:\n{e}")
            return False
        self.statusBar().showMessage(f"등록됨 — {ini_path}", 6000)
        return True

    def register_as_inverse_search_target(self):
        """ndhmdsync.ini 의 [EDITOR] command 에 나 자신을 등록한다."""
        self._write_ndhmdsync_section("EDITOR", "command", self_invoke_template())

    def register_pdf_viewer(self) -> bool:
        """ndhmdsync.ini 의 [PDFVIEW] command 에, OS 별 정해진 위치에서
        찾은 PDF 뷰어를 등록한다. 못 찾으면 그 자리들을 안내하고
        아무것도 쓰지 않는다.
        """
        exe, template = locate_pdf_viewer()
        if exe is None:
            if sys.platform == "win32":
                where = ("다음 위치만 확인합니다(포터블 설치는 지원하지 "
                        "않습니다):\n"
                        r"  C:\Program Files\SumatraPDF\SumatraPDF.exe" "\n"
                        r"  C:\Program Files (x86)\SumatraPDF\SumatraPDF.exe" "\n"
                        r"  %LOCALAPPDATA%\SumatraPDF\SumatraPDF.exe" "\n"
                        r"  %LOCALAPPDATA%\Programs\SumatraPDF\SumatraPDF.exe")
            elif sys.platform == "darwin":
                where = "/Applications/Skim.app 위치만 확인합니다."
            else:
                where = "PATH 에서 okular 를 찾지 못했습니다."
            QMessageBox.warning(self, "PDF 뷰어를 찾지 못했습니다", where)
            return False
        return self._write_ndhmdsync_section("PDFVIEW", "command", template)

    def open_at(self, path: Path, file_line: int):
        """검색 결과·라벨·컴파일 오류에서 파일의 특정 행으로 바로 간다.

        나중에 역방향 sync 가 붙을 때도 결국 같은 동작이다. 그래서
        Editor.goto_file_line() 을 거쳐 둔다 — front matter 를 숨기게 되면
        오프셋 보정이 여기 한 곳에서 해결된다.
        """
        if not path.exists():
            self.statusBar().showMessage(f"파일을 찾지 못했습니다: {path}", 6000)
            return
        self.push_location()
        self.open_path(path, file_line)
        if not self.find_bar.is_workspace():
            self.on_query_changed()

    def save_file(self) -> bool:
        if self._path is None:
            return self.save_file_as()
        return self._write(self._path)

    def save_file_as(self) -> bool:
        if not self._require_workspace():
            return False
        start = str(self._path.parent if self._path else self.workspace.root)
        name, _ = QFileDialog.getSaveFileName(
            self, "다른 이름으로 저장", start, Workspace.name_filter())
        if not name:
            return False
        path = Path(name)
        if not self._guard_inside(path):
            return False
        return self._write(path)

    def reload_current_file(self):
        """지금 파일을 디스크에서 다시 읽는다.

        밖에서 파일이 바뀌었을 때(다른 도구로 고쳤다거나) 쓴다. 또한
        :::{thebibliography} 를 편집창에 직접 타이핑해 넣었을 때 그
        자리에서 바로 버튼으로 접히지 않는 것도 이걸로 해결된다 —
        load() 가 _attach_document() 를 거치면서 참고문헌 블록을 다시
        훑기 때문이다.

        저장하지 않은 편집이 있으면 조용히 버리지 않는다 — 저장·버림·
        취소 중에서 고르게 한다.
        """
        if self._path is None:
            return
        if self._has_unsaved():
            r = QMessageBox.question(
                self, "다시 읽기",
                "저장하지 않은 편집이 있습니다. 저장하고 다시 읽을까요?\n"
                "버리면 지금 화면의 편집 내용은 사라지고 디스크의 것으로 "
                "돌아갑니다.",
                QMessageBox.Save | QMessageBox.Discard | QMessageBox.Cancel)
            if r == QMessageBox.Cancel:
                return
            if r == QMessageBox.Save and not self.save_file():
                return
        path = self._path
        self._dirty_docs.pop(path, None)   # 캐시도 버린다 — 디스크가 진실이 된다
        self.load(path)

    def _announce_source_encoding(self, path: Path, enc: str):
        """UTF-8 이 아닌 파일을 열었음을 알린다(저장하면 UTF-8 이 된다)."""
        if enc == "utf-8-sig":
            msg = f"{path.name}: UTF-8 BOM 을 떼고 열었습니다 — 저장하면 BOM 없이 저장됩니다"
        elif enc in NON_UTF8_ENCODINGS:
            msg = (f"{path.name}: {enc} 파일을 UTF-8 텍스트로 열었습니다 — "
                   f"저장하면 UTF-8 로 바뀝니다")
        else:
            return
        self.statusBar().showMessage(msg, 10000)

    def _confirm_encoding_change(self, path: Path) -> bool:
        """UTF-8 이 아니던 원고를 처음 저장할 때, 원본이 UTF-8 로 바뀐다고
        알리고 원본을 남길지 묻는다. False 면 저장을 그만둔다."""
        key = path.resolve()
        enc = self._src_enc.get(key)
        if enc not in NON_UTF8_ENCODINGS or not key.exists():
            return True
        box = QMessageBox(self)
        box.setIcon(QMessageBox.Question)
        box.setWindowTitle("인코딩이 바뀝니다")
        box.setText(f"{key.name} 은(는) {enc} 로 저장된 파일입니다.\n"
                    f"저장하면 UTF-8 로 바뀌며, 다시 {enc} 로 내보낼 수는 없습니다.")
        b_bak = box.addButton("원본을 남기고 저장", QMessageBox.AcceptRole)
        b_go = box.addButton("그냥 저장", QMessageBox.DestructiveRole)
        box.addButton("취소", QMessageBox.RejectRole)
        box.setDefaultButton(b_bak)
        box.exec()
        clicked = box.clickedButton()
        if clicked is b_bak:
            bak = key.with_name(f"{key.name}.{enc}.bak")
            try:
                shutil.copy2(key, bak)
            except OSError as e:
                QMessageBox.warning(self, "백업 실패", f"{bak.name}: {e}")
                return False
            return True
        return clicked is b_go

    def _write(self, path: Path) -> bool:
        if not self._confirm_encoding_change(path):
            return False
        try:
            path.write_text(self.editor.toPlainText(), encoding="utf-8")
        except OSError as e:
            QMessageBox.warning(self, "저장 실패", str(e))
            return False
        if self._path is not None:
            self._dirty_docs.pop(self._path, None)
        self._path = path.resolve()
        self._src_enc[self._path] = "utf-8"
        self._dirty = False
        self._baseline_text = self.editor.toPlainText()
        self._dirty_docs.pop(self._path, None)
        self._update_title()
        self._refresh_result_action()
        self.refresh_drawer()
        self.refresh_toc()      # 저장했으니 TOC 도 새로 읽는다(타이핑 중엔 안 한다)
        return True

    def _has_unsaved(self) -> bool:
        """정말로 잃을 것이 있는가.

        편집창이 비어 있으면(공백뿐이어도) 물어볼 이유가 없다. 디스크의
        파일은 그대로 있으므로 버려도 글이 사라지지 않는다 — 잃는 것은
        "지웠다"는 사실뿐이고 그건 한 번 더 지우면 된다.
        """
        return self._dirty and bool(self.editor.toPlainText().strip())

    def _remember_last_file(self, path: Path, line: int):
        """`마지막 원고 다시 열기`용 기록(켜져 있을 때만). 열 때는 줄 1로, 종료할 때
        실제 커서 줄로 덮어쓴다 — 갑자기 죽어도 파일만큼은 남는다."""
        if self.prefs.reopen_last():
            self._settings.setValue("session/last_file", str(path))
            self._settings.setValue("session/last_line", int(line))

    def restore_last_file(self):
        """시작할 때 직전 원고를 다시 연다(환경설정 `마지막 원고 다시 열기`, 기본 꺼짐).
        저장된 작업공간 안의 파일일 때만 연다 — 작업공간을 마음대로 바꾸지 않는다."""
        if not self.prefs.reopen_last() or not self.workspace:
            return
        saved = self._settings.value("session/last_file", "", type=str)
        if not saved:
            return
        path = Path(saved)
        if not path.is_file():
            self.statusBar().showMessage(
                f"마지막 원고를 찾지 못했습니다: {path.name}", 6000)
            return
        if not self.workspace.contains(path):
            return
        line = self._settings.value("session/last_line", 1, type=int)
        self.open_path(path, max(1, line))

    def closeEvent(self, event):
        if not self.confirm_discard_all("앱 종료"):
            event.ignore()
            return
        # 열려 있는 AI 도우미 창은 먼저 닫아 실행 중인 외부 도구(claude·codex·agy)를 중단한다.
        # 창과 그 안의 QProcess 는 이 창의 자식이라, 그냥 두면 앱이 해체되는 도중에 실행 중인
        # 프로세스가 같이 파괴된다(macOS 에서 종료할 때 충돌 알림이 뜬다는 보고).
        for dlg in self.findChildren(AiResultDialog):
            dlg.close()
        QApplication.processEvents()
        if self._path is not None:
            self._remember_last_file(self._path, self.editor.file_line())
        self.commit_tags()
        self._save_panes()
        for key, win in self._floating.items():
            self._settings.setValue(f"view/{key}_float_geom", win.saveGeometry())
        if self.prefs.remember_geometry():
            self._settings.setValue("window/geometry", self.saveGeometry())
        self._settings.setValue(
            "view/vsplit", [int(x) for x in self.vsplit.sizes()])
        shutil.rmtree(self._render_dir, ignore_errors=True)
        event.accept()

    # -- 찾기: 공통 ---------------------------------------------------------

    def open_find(self, with_replace: bool, workspace: bool):
        if workspace and not self._require_workspace():
            return
        self.find_bar.show_replace(with_replace)
        cursor = self.editor.textCursor()
        multi = (not workspace) and cursor.hasSelection() and "\u2029" in cursor.selectedText()
        # 여러 줄을 선택한 채로 열면 그 선택이 곧 찾을 범위이다(검색어로는 쓰지 않는다).
        self.find_bar.scope.setCurrentIndex(
            FindBar.SCOPE_WORKSPACE if workspace
            else FindBar.SCOPE_SELECTION if multi else FindBar.SCOPE_FILE)
        if multi:
            self._capture_scope()
        self.find_bar.show()
        if cursor.hasSelection():
            chunk = cursor.selectedText()
            if "\u2029" not in chunk:          # 여러 줄 선택은 검색어로 쓰지 않는다
                self.find_bar.query.setText(chunk)
        self.find_bar.query.setFocus()
        self.find_bar.query.selectAll()
        self.on_query_changed()

    def close_find(self):
        self.find_bar.hide()
        self.results.hide()
        self.editor.clear_search_matches()
        self.editor.setFocus()

    def focus_active_match(self):
        """찾기 바에서 Esc — 지금 찾은 위치로 커서를 옮긴다(호출한 쪽이 이어서
        막대를 닫는다). 찾은 게 없으면 그냥 지금 커서 위치에 둔다.
        """
        matches = self.editor._matches
        active = self.editor._active_match
        if matches and 0 <= active < len(matches):
            self.editor.setTextCursor(matches[active])
        self.editor.setFocus()

    def on_scope_changed(self):
        self.results.setVisible(self.find_bar.is_workspace())
        if self.find_bar.is_selection():
            self._capture_scope()            # 지금 선택해 둔 글이 범위가 된다(없으면 이전 범위 유지)
        else:
            self._clear_scope()
        self.on_query_changed()

    # -- 찾기: 선택 범위 ------------------------------------------------------

    def _capture_scope(self) -> bool:
        """편집창의 지금 선택을 찾기 범위로 잡는다. 선택이 없으면 이미 잡아 둔 범위를 그대로 쓰고,
        그것도 없으면 False. 범위는 문서의 편집을 따라 늘고 줄도록 contentsChange 로 좇는다."""
        cur = self.editor.textCursor()
        doc = self.editor.document()
        if cur.hasSelection():
            self._clear_scope(keep_ui=True)
            self._scope_doc = doc
            self._scope_lo, self._scope_hi = cur.selectionStart(), cur.selectionEnd()
            doc.contentsChange.connect(self._on_scope_contents)
            self.editor.set_scope_range((self._scope_lo, self._scope_hi))
            return True
        return getattr(self, "_scope_doc", None) is doc

    def _clear_scope(self, keep_ui: bool = False):
        d = getattr(self, "_scope_doc", None)
        if d is not None:
            try:
                d.contentsChange.disconnect(self._on_scope_contents)
            except (RuntimeError, TypeError):
                pass
        self._scope_doc = None
        if not keep_ui:
            self.editor.set_scope_range(None)

    def _scope_bounds(self):
        """(시작, 끝) 또는 None — 지금 문서에 유효한 선택 범위."""
        if getattr(self, "_scope_doc", None) is not self.editor.document():
            return None
        return self._scope_lo, self._scope_hi

    @Slot(int, int, int)
    def _on_scope_contents(self, pos, removed, added):
        lo, hi = self._scope_lo, self._scope_hi
        if removed:
            before = min(max(lo - pos, 0), removed)               # 범위 앞에서 지워진 글자
            a, b = max(pos, lo), min(pos + removed, hi)
            lo -= before
            hi -= before + max(0, b - a)                          # 범위 안에서 지워진 글자
        if added:
            if pos < lo:
                lo += added; hi += added
            elif pos <= hi:                                       # 범위 안(양 끝 포함)에서 넣은 글자
                hi += added
        self._scope_lo, self._scope_hi = lo, max(lo, hi)
        self.editor.set_scope_range((self._scope_lo, self._scope_hi))

    def _regex(self) -> QRegularExpression | None:
        """정규식 모드면 컴파일한 것을, 아니면 None 을 준다."""
        if not self.find_bar.use_regex():
            return None
        rx = QRegularExpression(self.find_bar.text())
        # ^ $ 는 (예전처럼) 줄머리·줄끝이다. `.` 은 줄바꿈에 맞지 않는다 —
        # 줄을 넘어 찾으려면 \n 이나 (?s) 를 쓴다.
        opts = QRegularExpression.MultilineOption
        if not self.find_bar.case_sensitive():
            opts |= QRegularExpression.CaseInsensitiveOption
        rx.setPatternOptions(opts)
        return rx if rx.isValid() else None

    #: 바꾸기 칸의 $1, ${1}, \1 을 캡처 그룹으로 인식한다 — 세 가지
    #: 표기 다 흔히 쓰이므로(다른 에디터·정규식 관례가 갈린다) 셋
    #: 다 받는다.
    _REPL_GROUP_RE = re.compile(r"\$\{(\d+)\}|\$(\d+)|\\(\d+)")

    #: 정규식 바꾸기 칸의 한 토막: \\ \n \t, ${1} $1 \1
    _REPL_TOKEN_RE = re.compile(
        r"\\\\|\\n|\\t|\$\{(\d+)\}|\$(\d+)|\\(\d+)")

    def _expand_at(self, rx, full: str, start: int, template: str) -> str:
        """전체 글 `full` 의 `start` 에서 시작하는 일치에 대해 바꿀 글을 만든다.
        일치한 글만 따로 다시 맞추지 않고 원래 자리에서(앞뒤 문맥 그대로)
        맞추므로 lookbehind·\\b·^ 가 어긋나지 않는다. 바꾸기 칸에서
        \\n 은 줄바꿈, \\t 는 탭, \\\\ 는 역슬래시 하나, $1 ${1} \\1 은
        캡처 그룹이다."""
        m = rx.match(full, start, QRegularExpression.NormalMatch,
                     QRegularExpression.AnchoredMatchOption)
        last = m.lastCapturedIndex() if m.hasMatch() else -1

        def repl(mo):
            t = mo.group(0)
            if t == "\\\\":
                return "\\"
            if t == "\\n":
                return "\n"
            if t == "\\t":
                return "\t"
            n = int(mo.group(1) or mo.group(2) or mo.group(3))
            if n > last:
                return t     # 없는 그룹 참조 — 그대로 둔다(오타 방지)
            return m.captured(n)

        return self._REPL_TOKEN_RE.sub(repl, template)

    def _expand_replacement(self, matched_text: str, template: str) -> str:
        """정규식 바꾸기의 캡처 그룹을 치환 문자열에 채워 넣는다.

        찾은 텍스트에 같은 정규식을 다시 매치해서 그룹을 얻는다 —
        QTextDocument.find() 가 돌려주는 커서에는 그룹 정보가 없어서
        직접 다시 매치하는 수밖에 없다. 정규식이 아니거나(평문 찾기)
        다시 매치가 안 되면(lookaround 때문에 어긋나는 드문 경우 등)
        template 을 안전하게 그대로 쓴다.
        """
        rx = self._regex()
        if rx is None:
            return template
        m = rx.match(matched_text)
        if not m.hasMatch():
            return template

        def repl(mo):
            n = int(mo.group(1) or mo.group(2) or mo.group(3))
            if n > m.lastCapturedIndex():
                return mo.group(0)   # 없는 그룹 참조 — 그대로 둔다(오타 방지)
            return m.captured(n)

        return self._REPL_GROUP_RE.sub(repl, template)

    def _find_flags(self, backward: bool = False):
        flags = QTextDocument.FindFlags()
        if backward:
            flags |= QTextDocument.FindBackward
        if self.find_bar.case_sensitive():
            flags |= QTextDocument.FindCaseSensitively
        return flags

    @Slot()
    def on_query_changed(self):
        if self.find_bar.is_workspace():
            self.search_workspace()
        else:
            self.highlight_matches_in_file()

    # -- 찾기: 현재 파일 ------------------------------------------------------

    def _iter_matches(self):
        """현재 문서의 모든 일치 구간을 커서로 돌려준다."""
        needle = self.find_bar.text()
        if not needle:
            return
        doc = self.editor.document()
        rx = self._regex()
        if self.find_bar.use_regex() and rx is None:
            return
        flags = self._find_flags()
        cursor = QTextCursor(doc)
        bounds = None
        if self.find_bar.is_selection():
            bounds = self._scope_bounds()
            if bounds is None:
                return
            cursor.setPosition(bounds[0])
        count = 0
        if rx is not None:
            # 줄(블록) 하나 안에서만 찾는 QTextDocument.find() 로는 \n 이 든
            # 패턴이 맞지 않는다. 전체 글에서 직접 맞추고 그 자리로 커서를
            # 만든다 — 문서 위치와 글 속 위치는 줄바꿈 한 글자씩으로 같다.
            full = doc.toPlainText()
            pos = bounds[0] if bounds else 0
            while count < self.MAX_HITS and pos <= len(full):
                m = rx.match(full, pos)
                if not m.hasMatch():
                    return
                a, b = m.capturedStart(), m.capturedEnd()
                if b <= a:                   # 빈 일치는 건너뛴다
                    pos = a + 1
                    continue
                if bounds and b > bounds[1]:
                    return
                c = QTextCursor(doc)
                c.setPosition(a)
                c.setPosition(b, QTextCursor.KeepAnchor)
                yield c
                count += 1
                pos = b
            return
        while count < self.MAX_HITS:
            cursor = doc.find(rx, cursor, flags) if rx else doc.find(needle, cursor, flags)
            if cursor.isNull():
                return
            if bounds and (cursor.selectionStart() >= bounds[1] or cursor.selectionEnd() > bounds[1]):
                return                       # 범위를 벗어난 일치는 셈에 넣지 않는다
            yield cursor
            count += 1

    def highlight_matches_in_file(self):
        matches = list(self._iter_matches())
        self.editor.set_search_matches(matches)
        if not self.find_bar.text():
            self.find_bar.set_status("")
        elif self.find_bar.use_regex() and self._regex() is None:
            self.find_bar.set_status("정규식 오류")
        elif self.find_bar.is_selection() and self._scope_bounds() is None:
            self.find_bar.set_status("먼저 글을 선택하세요")
        else:
            self.find_bar.set_status(f"{len(matches)}개" if matches else "없음")

    def find_step(self, backward: bool):
        if self.find_bar.is_workspace():
            self.search_workspace()
            return
        needle = self.find_bar.text()
        if not needle:
            return
        doc = self.editor.document()
        rx = self._regex()
        if self.find_bar.use_regex() and rx is None:
            return
        if self.find_bar.is_selection() or rx is not None:
            self._find_step_in_scope(backward)
            return
        flags = self._find_flags(backward)
        start = self.editor.textCursor()
        found = doc.find(rx, start, flags) if rx else doc.find(needle, start, flags)
        if found.isNull():
            # 문서 끝(또는 처음)에서 반대편으로 한 바퀴 돈다.
            wrap = doc.characterCount() - 1 if backward else 0
            found = doc.find(rx, wrap, flags) if rx else doc.find(needle, wrap, flags)
            if found.isNull():
                self.find_bar.set_status("없음")
                return
            self.statusBar().showMessage("처음부터 다시 찾았습니다", 2000)
        self.push_location()
        self.editor.ensure_visible(found.blockNumber())
        self.editor.setTextCursor(found)
        self.editor.centerCursor()
        self._sync_active_match(found)

    def _find_step_in_scope(self, backward: bool):
        """선택 범위 안에서만 다음/이전 일치로 간다. 끝에 닿으면 범위의 반대편에서 이어진다."""
        matches = list(self._iter_matches())
        if not matches:
            scoped = self.find_bar.is_selection()
            self.find_bar.set_status("먼저 글을 선택하세요" if scoped and self._scope_bounds() is None else "없음")
            return
        cur = self.editor.textCursor()
        if backward:
            pool = [c for c in matches if c.selectionStart() < cur.selectionStart()]
            found = pool[-1] if pool else matches[-1]
            wrapped = not pool
        else:
            pool = [c for c in matches if c.selectionStart() >= cur.selectionEnd()]
            found = pool[0] if pool else matches[0]
            wrapped = not pool
        if wrapped:
            if self.find_bar.is_selection():
                msg = ("범위의 처음부터 다시 찾았습니다" if not backward
                       else "범위의 끝부터 다시 찾았습니다")
            else:
                msg = "처음부터 다시 찾았습니다"
            self.statusBar().showMessage(msg, 2000)
        self.push_location()
        self.editor.ensure_visible(found.blockNumber())
        self.editor.setTextCursor(found)
        self.editor.centerCursor()
        self._sync_active_match(found)

    def _sync_active_match(self, cursor):
        matches = list(self._iter_matches())
        active = next((i for i, c in enumerate(matches)
                       if c.selectionStart() == cursor.selectionStart()), -1)
        self.editor.set_search_matches(matches, active)
        if matches:
            self.find_bar.set_status(f"{active + 1}/{len(matches)}")

    def replace_current(self):
        if self.find_bar.is_workspace():
            self.replace_all()
            return
        cursor = self.editor.textCursor()
        if cursor.hasSelection() and self.find_bar.is_selection():
            b = self._scope_bounds()
            if b is None or cursor.selectionStart() < b[0] or cursor.selectionEnd() > b[1]:
                cursor = QTextCursor(cursor)          # 범위 밖의 선택은 바꾸지 않고 다음 일치로만 간다
                cursor.clearSelection()
        if cursor.hasSelection():
            template = self.find_bar.replace_text()
            rx = self._regex()
            if rx is not None:
                full = self.editor.document().toPlainText()
                out = self._expand_at(rx, full, cursor.selectionStart(), template)
            else:
                matched = cursor.selectedText().replace("\u2029", "\n")
                out = self._expand_replacement(matched, template)
            cursor.insertText(out)
        self.find_step(False)

    def replace_all(self):
        if self.find_bar.is_workspace():
            self._replace_all_workspace()
        else:
            self._replace_all_file()

    def _replace_all_file(self):
        matches = list(self._iter_matches())
        if not matches:
            self.find_bar.set_status("없음")
            return
        template = self.find_bar.replace_text()
        cursor = self.editor.textCursor()
        rx = self._regex()
        full = self.editor.document().toPlainText()
        # 바꿀 글은 고치기 전의 전체 글에서 모두 만들어 둔다.
        outs = []
        for c in matches:
            if rx is not None:
                outs.append(self._expand_at(rx, full, c.selectionStart(), template))
            else:
                matched = c.selectedText().replace("\u2029", "\n")
                outs.append(self._expand_replacement(matched, template))
        cursor.beginEditBlock()
        # 뒤에서부터 바꿔야 앞쪽 위치가 밀리지 않는다.
        for c, out in reversed(list(zip(matches, outs))):
            c.insertText(out)
        cursor.endEditBlock()
        self.highlight_matches_in_file()     # 먼저 다시 칠하고
        self.find_bar.set_status(f"{len(matches)}개 바꿈")   # 그 위에 결과를 쓴다

    # -- 찾기: 작업공간 -------------------------------------------------------

    def _compile_needle(self):
        """작업공간 검색용 파이썬 정규식. 평문이면 escape 해서 쓴다."""
        text = self.find_bar.text()
        if not text:
            return None
        flags = 0 if self.find_bar.case_sensitive() else re.IGNORECASE
        try:
            return re.compile(text if self.find_bar.use_regex()
                              else re.escape(text), flags)
        except re.error:
            return None

    def search_workspace(self):
        if not self.workspace:
            return
        rx = self._compile_needle()
        if rx is None:
            self.results.clear()
            self.find_bar.set_status(
                "정규식 오류" if self.find_bar.text() else "")
            return

        hits, total = [], 0
        for path in self.workspace.source_files():
            try:
                lines = read_manuscript(path).splitlines()
            except (OSError, UnicodeDecodeError):
                continue
            found = [(i + 1, line) for i, line in enumerate(lines) if rx.search(line)]
            if found:
                hits.append((path, found))
                total += len(found)
            if total >= self.MAX_HITS:
                break

        self.results.populate(hits)
        self.results.setVisible(True)
        self.find_bar.set_status(
            f"{total}개 / 파일 {len(hits)}개" if total else "없음")
        # 현재 파일 안의 일치도 같이 칠해 둔다.
        self.editor.set_search_matches(list(self._iter_matches()))

    #: $1, ${1} 을 파이썬 re.sub 이 알아듣는 \g<n> 로 바꾼다. 이미
    #: 파이썬 식(\1)으로 쓴 것은 re.subn() 이 스스로 알아서 처리하므로
    #: 안 건드린다 — $ 로 시작하는 것만 본다.
    _DOLLAR_GROUP_RE = re.compile(r"\$\{(\d+)\}|\$(\d+)")

    def _replace_all_workspace(self):
        rx = self._compile_needle()
        if rx is None:
            return
        new = self.find_bar.replace_text()
        if self.find_bar.use_regex():
            new = self._DOLLAR_GROUP_RE.sub(
                lambda m: f"\\g<{m.group(1) or m.group(2)}>", new)

        # 열려 있는 파일이 더러우면 디스크와 어긋난다. 먼저 저장시킨다.
        if self._dirty and self._path is not None:
            r = QMessageBox.question(
                self, "저장 후 진행",
                "현재 원고에 저장하지 않은 변경이 있습니다.\n"
                "작업공간 전체 바꾸기는 디스크의 파일을 고치므로\n"
                "먼저 저장해야 합니다. 저장할까요?",
                QMessageBox.Save | QMessageBox.Cancel)
            if r != QMessageBox.Save or not self.save_file():
                return

        targets = []
        for path in self.workspace.source_files():
            try:
                text = read_manuscript(path)
            except (OSError, UnicodeDecodeError):
                continue
            try:
                new_text, n = rx.subn(new, text)
            except re.error:
                continue   # 없는 그룹을 \g<n> 으로 참조하는 등 — 이 파일은 건너뛴다
            if n:
                targets.append((path, new_text, n))

        if not targets:
            self.find_bar.set_status("없음")
            return

        total = sum(n for _, _, n in targets)
        r = QMessageBox.question(
            self, "작업공간 전체 바꾸기",
            f"파일 {len(targets)}개에서 {total}곳을 바꿉니다.\n"
            f"실행 취소가 되지 않습니다. 진행할까요?",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if r != QMessageBox.Yes:
            return

        failed = []
        for path, new_text, _ in targets:
            try:
                path.write_text(new_text, encoding="utf-8")
            except OSError as e:
                failed.append(f"{self.workspace.relative(path)}: {e}")

        if self._path is not None and self._path.exists():
            line = self.editor.file_line()
            self.load(self._path)
            self.editor.goto_file_line(line)

        if failed:
            QMessageBox.warning(self, "일부 실패", "\n".join(failed[:10]))
        self.search_workspace()
        self.find_bar.set_status(
            f"{total}곳 바꿈 (파일 {len(targets) - len(failed)}개)")

    # -- 선택 영역 변형 -----------------------------------------------------------

    def _transform(self, fn):
        cursor = self.editor.textCursor()
        cursor.beginEditBlock()
        fn(cursor)
        cursor.endEditBlock()
        self.editor.setFocus()

    def wrap_in_environment(self):
        name, ok = QInputDialog.getText(self, "환경으로 감싸기", "환경 이름:")
        name = name.strip()
        if not ok or not name:
            return
        self._transform(lambda c: SelectionTransform.to_environment(c, name))

    def unwrap_selection(self):
        cursor = self.editor.textCursor()
        cursor.beginEditBlock()
        did = SelectionTransform.unwrap(cursor)
        cursor.endEditBlock()
        self.editor.setFocus()
        if not did:
            self.statusBar().showMessage("풀 수 있는 목록·펜스·환경이 없습니다", 2000)

    def reflow_selection(self):
        """선택 영역을 문단 재배열한다. 사용자가 명시적으로 고른 영역만
        건드린다 — 자동으로 켜져 있는 서식이 아니다."""
        width = self.prefs.reflow_width()
        single = self.prefs.reflow_single_line()
        self._transform(lambda c: SelectionTransform.reflow_paragraphs(c, width, single))

    def add_heading_shift_menus(self, menu, has_selection: bool = True):
        """장/절 표제 수준 증가·감소 — 각각 현재 행 / 선택 범위 / 현재 원고
        세 범위를 하위 메뉴로 둔다. 책 전체에는 적용하지 않는다."""
        for title, delta in (("장/절 표제 수준 증가", -1), ("장/절 표제 수준 감소", 1)):
            sub = menu.addMenu(title)
            for label, scope in (("현재 행", "line"), ("선택 범위", "selection"),
                                 ("현재 원고", "document")):
                a = sub.addAction(
                    label, lambda d=delta, sc=scope: self.shift_heading_level(d, sc))
                if scope == "selection" and not has_selection:
                    a.setEnabled(False)

    def _heading_blocks(self, first: int, last: int):
        """[first, last] 번째 줄 중 진짜 표제인 줄을 (블록, 수준) 으로 돌려준다.
        앞쪽 front matter 와 코드펜스 안의 `#` 줄은 표제가 아니므로 문서
        처음부터 훑으며 그 상태를 따라간다."""
        out = []
        in_front = False
        fence = 0                      # 열려 있는 펜스의 백틱 수(0 = 없음)
        block = self.editor.document().firstBlock()
        while block.isValid() and block.blockNumber() <= last:
            text = block.text()
            n = block.blockNumber()
            if in_front:
                if FRONTMATTER_CLOSE_RE.match(text):
                    in_front = False
            elif n == 0 and FRONTMATTER_OPEN_RE.match(text):
                in_front = True
            elif fence:
                m = FENCE_CLOSE_RE.match(text)
                if m and len(m.group(1)) >= fence:
                    fence = 0
            else:
                m = FENCE_OPEN_LOOSE_RE.match(text)
                if m:
                    fence = len(m.group(1))
                elif n >= first:
                    h = HEADING_RE.match(text)
                    if h:
                        out.append((block, len(h.group(1))))
            block = block.next()
        return out

    def shift_heading_level(self, delta: int, scope: str = "auto"):
        """장/절 표제(#)의 수준을 한 단계 올리거나(delta=-1, ## → #)
        내린다(delta=+1, # → ##).

        scope: "line"(커서가 놓인 표제행) / "selection"(선택 범위 안의
        표제행) / "document"(지금 편집 중인 파일 전체) / "auto"(선택이
        있으면 선택 범위, 없으면 현재 행 — 단축키용). 책 전체에는
        적용하지 않는다.

        한계(최상위 # 를 더 올리거나 6단계를 더 내리는 것)에 닿은 표제는
        그대로 두고, 몇 개를 그렇게 두었는지 알려 준다. 바꾸는 것은 `#`
        한 글자의 추가·삭제뿐이라 커서와 라벨({#...})은 그대로다.
        """
        verb = "올렸습니다" if delta < 0 else "내렸습니다"
        doc = self.editor.document()
        cur = self.editor.textCursor()
        if scope == "auto":
            scope = "selection" if cur.hasSelection() else "line"

        if scope == "line":
            first = last = cur.blockNumber()
        elif scope == "selection":
            if not cur.hasSelection():
                self.statusBar().showMessage("선택 범위가 없습니다", 3000)
                return
            a = doc.findBlock(cur.selectionStart())
            b = doc.findBlock(cur.selectionEnd())
            if cur.selectionEnd() > cur.selectionStart() and cur.selectionEnd() == b.position():
                b = b.previous()          # 다음 줄 맨 앞까지 잡힌 선택은 그 줄을 안 친다
            first, last = a.blockNumber(), b.blockNumber()
        else:
            first, last = 0, doc.blockCount() - 1

        targets = self._heading_blocks(first, last)
        if not targets:
            self.statusBar().showMessage(
                "표제행이 아닙니다" if scope == "line" else "표제행이 없습니다", 3000)
            return

        moved = skipped = 0
        edit = QTextCursor(doc)
        edit.beginEditBlock()
        for block, level in targets:
            if not 1 <= level + delta <= 6:
                skipped += 1
                continue
            c = QTextCursor(block)
            if delta < 0:
                c.movePosition(QTextCursor.MoveOperation.Right, QTextCursor.MoveMode.KeepAnchor, 1)
                c.removeSelectedText()
            else:
                c.insertText("#")
            moved += 1
        edit.endEditBlock()
        self.editor.setFocus()

        if scope == "line":
            if skipped:
                self.statusBar().showMessage(
                    "더 올릴 수 없습니다(최상위 #)" if delta < 0
                    else "더 내릴 수 없습니다(6단계)", 3000)
            return
        msg = f"표제 {moved}개를 {verb}"
        if skipped:
            msg += f" (한계에 닿아 그대로 둔 것 {skipped}개)"
        self.statusBar().showMessage(msg, 4000)

    # -- 악센트 입력 -------------------------------------------------------------

    def open_image_check(self):
        if self._path is None:
            QMessageBox.information(self, "그림 점검", "먼저 원고를 열어 주세요.")
            return
        dlg = ImageCheckDialog(self)
        self.__dict__.setdefault("_check_dialogs", []).append(dlg)
        dlg.show()

    def open_crossref_check(self, focus=None):
        if self._path is None:
            QMessageBox.information(self, "상호참조 점검", "먼저 원고를 열어 주세요.")
            return
        dlg = CrossRefCheckDialog(self, focus)
        self.__dict__.setdefault("_check_dialogs", []).append(dlg)
        dlg.show()

    def open_crossref_check_at_cursor(self, cursor=None):
        """우클릭 메뉴용: 커서(또는 우클릭한 자리)가 참조형 마크업 위면 그 참조 항목을
        고른 채 점검 창을 연다. 아니면 그냥 연다."""
        focus = None
        if self._path is not None:
            cur = cursor or self.editor.textCursor()
            hit = ref_at_position(cur.block().text(), cur.positionInBlock())
            if hit:
                focus = (self._path, cur.blockNumber() + 1, hit[0], hit[1])
        self.open_crossref_check(focus)

    def open_help(self):
        if getattr(self, "_help_dialog", None) is None:
            self._help_dialog = HelpDialog(self)
        self._help_dialog.show()
        self._help_dialog.raise_()

    def open_guide(self, kind: str):
        """도움말 ▸ ndhmarkdown ▸ 사양서/치트시트, 도움말 ▸ Reference Manual.

        `ndhmd4tex --guide[=이름]` 은 뭔가를 새로 만드는 게 아니다. 자기
        resource 폴더에 있는 그 이름의 PDF 를 찾아 ndhmd4tex 자신이 직접
        시스템 뷰어로 연다(컴파일 결과를 열 때처럼 우리가 QDesktopServices
        로 여는 게 아니라, ndhmd4tex 내부에서 이미 열어 버린다). 그러니
        우리는 명령을 실행하고 실패했을 때만 알리면 된다 — 결과 파일을
        찾아다닐 필요가 없다.
        """
        if self._compile_proc is not None:
            return                       # 이미 다른 컴파일/변환이 진행 중
        if not self._ensure_tool():
            return
        names = {"guide": None,
                 "cheatsheet": "ndhmd4tex_cheatsheet.pdf",
                 "manual": "ndhmdWriter-MANUAL.pdf"}
        name = names[kind]
        args = ["--guide"] if name is None else [f"--guide={name}"]
        cmd = self.tool.command(args)
        if cmd is None:
            return

        self.statusBar().showMessage("여는 중…")
        proc = QProcess(self)
        proc.setProcessChannelMode(QProcess.MergedChannels)
        proc.finished.connect(lambda code, st, p=proc: self._guide_finished(p))
        proc.errorOccurred.connect(lambda e, p=proc: self._convert_failed(p))
        self._compile_proc = proc
        proc.start(cmd[0], cmd[1:])

    def _guide_finished(self, proc):
        if proc is not self._compile_proc:
            return
        self._compile_proc = None
        raw = decode_subprocess_output(bytes(proc.readAllStandardOutput()))
        if proc.exitCode() != 0:
            ConsoleOutputDialog(
                self, "문서를 열지 못했습니다", raw or "알 수 없는 오류입니다.").show()
            return
        self.statusBar().showMessage("문서를 열었습니다", 4000)

    @staticmethod
    def _pm_word_cursor(cursor: QTextCursor):
        """커서가 놓인 곳의 pm 입력 "단어" — 공백·한글·한자 등 비ASCII 글자로 끊기는 ASCII 덩어리
        (`han/geul`, `{h:ai}`, `ka@` 처럼 `/` `'` `@` `{}` 도 단어의 일부다). 앞쪽의 여는 괄호·따옴표·`*`와
        뒤쪽의 닫는 괄호·마침표류는 떼어 낸다. 한 줄 안에서만 찾고, 없으면 None."""
        block = cursor.block()
        text = block.text()
        pos = cursor.positionInBlock()

        def tok(ch):
            return ord(ch) < 128 and not ch.isspace()

        start = end = pos
        while start > 0 and tok(text[start - 1]):
            start -= 1
        while end < len(text) and tok(text[end]):
            end += 1
        while start < end and text[start] in "([\"'<*_":
            start += 1
        while end > start and text[end - 1] in ")]\">*_.,;:!?":
            end -= 1
        if start >= end:
            return None
        c = QTextCursor(block)
        c.setPosition(block.position() + start)
        c.setPosition(block.position() + end, QTextCursor.KeepAnchor)
        return c

    def _pm_target(self, cursor: QTextCursor | None = None):
        """pm 변환/보내기 대상: 편집창의 선택이 있으면 그것, 없으면 (cursor 또는 현재 커서 위) 단어.
        대상 커서(선택 상태)를 돌려주고, 없으면 None."""
        cur = self.editor.textCursor()
        if cur.hasSelection():
            return cur
        # 메뉴 액션이 triggered(checked) 로 불러 bool 이 올 수 있다 — 커서가 아니면 현재 커서를 쓴다.
        return self._pm_word_cursor(cursor if isinstance(cursor, QTextCursor) else cur)

    def send_selection_to_pmime(self, cursor: QTextCursor | None = None):
        """선택(없으면 커서 위 단어)을 한중일 pm 입력기의 입력칸으로 보내고 그리로 포커스를 준다. 입력기에서
        Enter 를 한 번 치면 변환 결과가 (그대로 남아 있는) 선택 영역을 대체한다."""
        target = self._pm_target(cursor)
        if target is None:
            self.statusBar().showMessage("pm 입력기로 보낼 글을 선택하거나 단어 위에 커서를 두세요", 3000)
            return
        self.editor.setTextCursor(target)          # 단어였다면 그 단어를 선택해 둔다
        text = target.selectedText().replace("\u2029", "\n")
        self.open_pmime_panel()
        self._pmime_panel.input.setPlainText(text)
        self._pmime_panel.input.moveCursor(QTextCursor.End)

    def convert_selection_pmime(self, cursor: QTextCursor | None = None):
        """선택(없으면 커서 위 단어)을 한중일 pm 입력기의 지금 설정(엔진·한자 필터·NFC·LaTeX 확장)으로
        바로 변환해 그 자리에 되넣는다(실행 취소 한 번, 입력기 창은 열지 않는다)."""
        target = self._pm_target(cursor)
        if target is None:
            self.statusBar().showMessage("pm 변환할 글을 선택하거나 단어 위에 커서를 두세요", 3000)
            return
        if load_pmime_core() is None:
            self.statusBar().showMessage("pmime_core.py 를 찾지 못했습니다", 5000)
            return
        if getattr(self, "_pmime_panel", None) is None:
            self._pmime_panel = PmImePanel(self)
        text = target.selectedText().replace("\u2029", "\n")
        try:
            out = self._pmime_panel.converted(text)
        except Exception as e:
            self.statusBar().showMessage(f"pm 변환 오류: {e}", 5000)
            return
        if out and out != text:
            target.insertText(out)                 # 선택/단어 자리에 한 번의 실행 취소 단위로
            self.editor.setTextCursor(target)
            self.statusBar().showMessage("pm 변환했습니다", 3000)

    # -- 한자 변환 (F9) ---------------------------------------------------------

    def convert_hanja(self, *_, _tries: int = 0):
        """커서 앞의 한글(또는 선택한 글자)을 한자로 바꾸는 후보 창을 연다. 음(`가`)·단어(`국가`)·
        훈음(`노래 가`)을 모두 찾는다. 사전은 처음 쓸 때 한 번 만든다."""
        core = load_hanja_core()
        if core is None:
            self.statusBar().showMessage(
                "hanja_core.py 를 찾지 못했습니다 — ndhmdWriter.py 와 같은 폴더에 두세요.", 6000)
            return
        ed = self.editor
        # 한글 조합 중인 글자는 먼저 확정한다. 이 에디터는 조합 중 글자를 진짜 텍스트로 임시 삽입해 두므로,
        # 확정하지 않은 채 바꾸면 조합 상태가 어긋난다.
        if ed._preedit_length > 0:
            # 입력기의 확정은 비동기로 도착할 수 있다(맥에서 Ctrl+\ 처럼 입력기를 거쳐 온 키는 특히).
            # 한 번 확정을 청하고, 이벤트를 돌려 본 뒤에도 남아 있으면 잠깐씩 기다리며 다시 시도한다.
            if _tries == 0:
                QGuiApplication.inputMethod().commit()
            QCoreApplication.processEvents()
            if ed._preedit_length > 0:
                if _tries < 8:
                    QTimer.singleShot(30, lambda: self.convert_hanja(_tries=_tries + 1))
                else:
                    self.statusBar().showMessage(
                        "조합 중인 글자를 확정(Space 등)한 뒤 다시 눌러 주세요.", 4000)
                return
        db = hanja_data_dir() / "hanja_dict.db"
        if not core.dict_is_ready(str(db), find_mssymbol_txt() is not None):
            self._build_hanja_dict(core, db)
            return
        if getattr(self, "_hanja", None) is None:
            try:
                self._hanja = core.Hanja(str(db), str(hanja_data_dir() / "hanja_user.db"))
            except Exception as e:
                self.statusBar().showMessage(f"한자 사전을 열지 못했습니다: {e}", 6000)
                return
        cur = ed.textCursor()
        selected = cur.selectedText().replace("\u2029", "\n") if cur.hasSelection() else ""
        before = "" if cur.hasSelection() else cur.block().text()[:cur.positionInBlock()]
        # 한자를 선택했거나 한자 바로 뒤에 커서가 있으면 거꾸로 — 그 한자의 훈음을 보이고 음을 고른다.
        cands = core.find_reverse(self._hanja, before, selected)
        if cands is not None:
            if not cands:
                shown = (selected or before[-1:]).strip()
                self.statusBar().showMessage(f"'{shown}' — 데이터가 없습니다.", 4000)
                return
        else:
            cands = core.find_candidates(self._hanja, before, selected, self.prefs.hanja_recent_first())
        if not cands:
            self.statusBar().showMessage("한자 후보가 없습니다.", 2500)
            return
        self._hanja_anchor = QTextCursor(cur)
        pop = HanjaPopup(self, cands)
        pop.chosen.connect(self._apply_hanja)
        self._hanja_popup = pop
        rect = ed.cursorRect(cur)
        pos = ed.viewport().mapToGlobal(rect.bottomLeft())
        screen = QGuiApplication.screenAt(pos) or QGuiApplication.primaryScreen()
        pop.adjustSize()
        g = screen.availableGeometry()
        x = min(pos.x(), g.right() - pop.width())
        y = pos.y() if pos.y() + pop.height() <= g.bottom() else \
            ed.viewport().mapToGlobal(rect.topLeft()).y() - pop.height()
        pop.move(QPoint(max(g.left(), x), max(g.top(), y)))
        pop.show()
        pop.setFocus()

    def reset_hanja_dict(self):
        """개발·시험용 숨은 기능(Ctrl+Shift+Alt+F9): 한자 사전 DB 를 지운다. 다음 F9 에서 다시 만든다.
        최근 입력 기록(hanja_user.db)은 지우지 않는다."""
        if getattr(self, "_hanja_building", False):
            self.statusBar().showMessage("한자 사전을 만드는 중이라 지우지 않았습니다.", 3000)
            return
        h = getattr(self, "_hanja", None)
        if h is not None:
            try:
                h.close()
            except Exception:
                pass
            self._hanja = None
        db = hanja_data_dir() / "hanja_dict.db"
        gone = 0
        for suffix in ("", ".building", "-journal", "-wal", "-shm"):
            f = Path(str(db) + suffix)
            try:
                if f.exists():
                    f.unlink()
                    gone += 1
            except OSError as e:
                self.statusBar().showMessage(f"사전 DB 를 지우지 못했습니다: {e}", 6000)
                return
        self.statusBar().showMessage(
            "한자 사전 DB 를 지웠습니다 — 다음 F9 에서 다시 만듭니다." if gone
            else "지울 한자 사전 DB 가 없습니다.", 4000)

    def _build_hanja_dict(self, core, db: Path):
        txt = find_hanja_txt()
        if txt is None:
            self.statusBar().showMessage(
                "한자 사전 hanja.txt 를 찾지 못했습니다 — ndhmdWriter.py 와 같은 폴더에 두세요.", 8000)
            return
        if getattr(self, "_hanja_building", False):
            return
        self._hanja_building = True
        self.statusBar().showMessage("한자 사전을 처음 만드는 중입니다… 잠시만요.")
        job = _HanjaBuild(core, txt, db, find_mssymbol_txt())
        self._hanja_job = job
        job.signals.done.connect(self._on_hanja_built)
        QThreadPool.globalInstance().start(job)

    def _on_hanja_built(self, err):
        self._hanja_building = False
        if err:
            self.statusBar().showMessage(f"한자 사전을 만들지 못했습니다: {err}", 8000)
            return
        self.statusBar().showMessage("한자 사전을 만들었습니다.", 3000)
        self.convert_hanja()

    def _apply_hanja(self, n: int, hanja: str, reading: str, tail: int = 0, kind: int = 0):
        cur = QTextCursor(self._hanja_anchor)
        if kind == 2:
            # 거꾸로 변환(한자 → 음). 병기 설정을 따른다:
            #   한글 병기 켜짐: 從(종)   한자 병기 켜짐: 종(從)   둘 다 꺼짐: 종 (바꿔치기)
            if not cur.hasSelection():
                end = cur.position() - tail          # 낱말 앞쪽만 바꾸면 뒤 tail 글자는 그대로
                cur.setPosition(end - n)
                cur.setPosition(end, QTextCursor.KeepAnchor)
            if self.prefs.hanja_parenthesize():
                out = f"{hanja}({reading})"
            elif self.prefs.hanja_hangul_first():
                out = f"{reading}({hanja})"
            else:
                out = reading
            cur.beginEditBlock()
            cur.insertText(out)
            cur.endEditBlock()
            if tail:
                cur.movePosition(QTextCursor.Right, QTextCursor.MoveAnchor, tail)
            self.editor.setTextCursor(cur)
            self.editor.setFocus()
            return
        if not cur.hasSelection():
            # 낱말 앞쪽만 바꾸는 경우(`한자입력` 의 `한자`) 뒤의 tail 글자는 그대로 두고 커서도 그 뒤에 둔다.
            end = cur.position() - tail
            cur.setPosition(end - n)
            cur.setPosition(end, QTextCursor.KeepAnchor)
        # 병기는 한자에만 적용한다. 기호(ⅰ, ㎏ …)에는 붙이지 않는다.
        #   한글 병기: 國家(국가)   한자 병기: 국가(國家) — 바꾸는 원문(`노래 가` 포함)을 그대로 둔다.
        orig = cur.selectedText()
        out = hanja
        if kind == 0:
            if self.prefs.hanja_hangul_first():
                out = f"{orig}({hanja})"
            elif self.prefs.hanja_parenthesize():
                out = f"{hanja}({reading})"
        cur.beginEditBlock()          # 실행 취소 한 번에 원래 한글로
        cur.insertText(out)
        cur.endEditBlock()
        if tail:
            cur.movePosition(QTextCursor.Right, QTextCursor.MoveAnchor, tail)
        self.editor.setTextCursor(cur)
        self.editor.setFocus()
        try:
            self._hanja.remember(reading, hanja)
        except Exception:
            pass

    def open_pmime_panel(self):
        if getattr(self, "_pmime_panel", None) is None:
            self._pmime_panel = PmImePanel(self)
        self._pmime_panel.show()
        self._pmime_panel.raise_()
        self._pmime_panel.activateWindow()
        self._pmime_panel.input.setFocus()

    def open_accent_panel(self):
        if getattr(self, "_accent_panel", None) is None:
            self._accent_panel = AccentPanel(self)
            self._accent_panel.apply_theme(self._theme)
        self._accent_panel.show()
        self._accent_panel.raise_()

    def open_math_symbol_panel(self):
        if getattr(self, "_math_symbol_panel", None) is None:
            self._math_symbol_panel = MathSymbolPanel(self)
        self._math_symbol_panel.show()
        self._math_symbol_panel.raise_()

    def open_color_palette(self):
        if getattr(self, "_color_palette", None) is None:
            self._color_palette = ColorPalettePanel(self)
        self._color_palette.show()
        self._color_palette.raise_()

    def open_table_editor(self):
        if getattr(self, "_table_editor", None) is None:
            self._table_editor = TableEditorDialog(self)
        self._table_editor.show()
        self._table_editor.raise_()

    def graphics_dirs(self) -> list:
        """그림이 놓이는 폴더 목록 — graphicspath: 의 순서를 따르고, 없으면
        작업공간 최상위 하나. 그림 들여오기와 같은 규칙이다."""
        if self._path is None or not self.workspace:
            return []
        book_dir = LabelIndex.book_files(self.index, self._path)[0].parent
        dirs = []
        for gp in Preamble.graphicspath(self.index, self._path, self._live_reader):
            d = (book_dir / gp).resolve()
            if d not in dirs:
                dirs.append(d)
        return dirs or [self.workspace.root]

    def jigsaw_search_dirs(self) -> list:
        """조각 그림 코드의 \\includegraphics·\\input 이 찾아볼 폴더들."""
        dirs = list(self.graphics_dirs())
        if self.workspace and self.workspace.root not in dirs:
            dirs.append(self.workspace.root)
        return [d for d in dirs if d.is_dir()]

    def jigsaw_target_at_cursor(self):
        """커서가 놓인 줄의 그림 중 조각 그림(옆에 도구가 만든 .tex 가 있는
        PDF — 여러 쪽 그림의 낱장 foo-2.pdf 포함)이면 그 .tex 경로. 한 줄에
        그림이 여럿이면 커서가 걸친 것."""
        cur = self.editor.textCursor()
        line = cur.block().text()
        col = cur.positionInBlock()
        found = [m for m in FIGURE_RE.finditer(line)]
        hit = [m for m in found if m.start() <= col <= m.end()] or (
            found if len(found) == 1 else [])
        for m in hit:
            path = self._resolve_image(m.group(2))
            tex = JigsawFigure.locate(path) if path is not None else None
            if tex is not None:
                return tex
        return None

    def jigsaw_insert_target(self):
        """열려 있는 조각 그림 창 중 가장 최근에 쓴 것과 그 입력칸. 없으면 None."""
        dlg = getattr(self, "_active_jigsaw", None)
        dialogs = getattr(self, "_jigsaw_dialogs", [])
        if dlg is None or dlg not in dialogs or not dlg.isVisible():
            return None
        return dlg

    def open_jigsaw_dialog(self, tex: Path = None):
        if not self.workspace or self._path is None:
            QMessageBox.information(self, "조각 그림", "작업공간에서 파일을 먼저 열어 주세요.")
            return
        dialogs = self.__dict__.setdefault("_jigsaw_dialogs", [])
        if tex is not None:
            for d in dialogs:
                if d._edit_tex is not None and d._edit_tex == tex:
                    d.show()
                    d.raise_()
                    return
        dlg = JigsawDialog(self, tex)
        dialogs.append(dlg)
        dlg.show()
        dlg.raise_()

    def edit_jigsaw_at_cursor(self):
        tex = self.jigsaw_target_at_cursor()
        if tex is None:
            self.statusBar().showMessage(
                "커서가 조각 그림 줄 위에 있지 않습니다 "
                "(옆에 조각 그림 도구가 만든 .tex 가 있는 PDF 그림이어야 합니다).", 5000)
            return
        self.open_jigsaw_dialog(tex)

    def edit_math_at_cursor(self):
        """수식 편집기를 모달로 연다. 커서가 수식 위에 있으면 그것을 고치고,
        아니면 커서(또는 선택) 자리에 새 수식을 넣는다. 넣기를 누르면 창이
        닫히고 원고가 바뀐다(실행 취소 한 번)."""
        text = self.editor.toPlainText()
        cur = self.editor.textCursor()
        pos = cur.position()
        target = PreviewScanner.find(text, pos)
        orig = None
        if target is not None and target.kind == "math":
            orig = split_math_delims(target.source)
            kind, inner = orig[0], orig[3]
            if kind != "env":
                inner = inner.strip()
            start, end = target.start, target.end
        else:
            if cur.hasSelection():
                start, end = cur.selectionStart(), cur.selectionEnd()
                inner = text[start:end].strip()
            else:
                start = end = pos
                inner = ""
            line = cur.block().text()
            kind = "display" if (not line.strip() and not inner) else "inline"
        preamble = (Preamble.collect(self.index, self._path, self._live_reader)
                    if self._path is not None else "")
        win = MathEditorWindow(None, "", parent=self, embedded=True, preamble=preamble)
        win.set_text(inner)
        win.mode.setCurrentIndex(max(win.mode.findData(kind), 0))
        win._dirty = False
        win._update_title()
        win._request(0)
        got = {}
        win.committed.connect(lambda t, m: got.update(text=t, mode=m))
        if not win.exec_modal() or "text" not in got:
            self.editor.setFocus()
            return
        mode = got["mode"]
        if mode == "auto":
            mode = detect_mode(got["text"])
        new = wrap_math(got["text"], mode, orig)
        c = self.editor.textCursor()
        c.beginEditBlock()
        c.setPosition(start)
        c.setPosition(end, QTextCursor.KeepAnchor)
        c.insertText(new)
        c.endEditBlock()
        self.editor.setTextCursor(c)
        self.editor.setFocus()
        self.statusBar().showMessage("수식을 고쳤습니다" if orig else "수식을 넣었습니다", 3000)

    def open_image_import(self):
        if getattr(self, "_image_import_panel", None) is None:
            self._image_import_panel = ImageImportPanel(self)
        else:
            self._image_import_panel.refresh()
        self._image_import_panel.show()
        self._image_import_panel.raise_()

    def toggle_word_wrap(self, checked: bool):
        self.editor.setLineWrapMode(
            QPlainTextEdit.WidgetWidth if checked else QPlainTextEdit.NoWrap)
        self.prefs.set_word_wrap(checked)

    def set_smart_quotes_style(self, style: str):
        self.prefs.write(smart_quotes=style)
        self.editor.smart_quotes_style = style
        if style == "cjk" and not self.prefs.smart_punctuation():
            # 한국어식 따옴표를 고르면 편의상 문장부호(고리점·모점)도
            # 같이 켠다 — 그 뒤로는 서로 독립적으로 끌 수 있다.
            self._act_smart_punct.setChecked(True)   # toggled 가 실제 반영까지 한다

    def toggle_smart_punctuation(self, on: bool):
        self.prefs.write(smart_punctuation=on)
        self.editor.smart_punctuation = on

    # -- 약어 슬롯 ---------------------------------------------------------------

    @staticmethod
    def slot_key_name(key: str) -> str:
        """슬롯 단축키의 표시 이름. 맥은 Option 이 기호 입력에 쓰이므로 물리 Control 키를 쓴다."""
        return ("Control+" if sys.platform == "darwin" else "Alt+") + key

    def insert_slot(self, key: str, *, from_shortcut: bool = False):
        """슬롯 `key` 의 문자열을 커서 위치에 넣는다. 선택이 있으면 대체하되, 문자열의 `{선택}` 은
        선택했던 글로, `{커서}` 는 넣은 뒤 커서가 놓일 자리로 바뀐다. 실행 취소는 한 번에."""
        if from_shortcut and not self.editor.hasFocus():
            return                               # 찾기 바 같은 다른 칸에서는 편집창에 넣지 않는다
        if not SlotStore.is_global(key) and not self.slots.book_available():
            self.statusBar().showMessage(
                f"{self.slot_key_name(key)}: 책(작업공간)을 연 뒤에 쓸 수 있는 슬롯입니다.", 4000)
            return
        text = self.slots.get(key)
        if not text:
            self.statusBar().showMessage(
                f"{self.slot_key_name(key)} 슬롯이 비어 있습니다 — 도구 ▸ 약어 슬롯…에서 등록하세요.", 4000)
            return
        cur = self.editor.textCursor()
        sel = cur.selectedText().replace("\u2029", "\n") if cur.hasSelection() else ""
        body = text.replace("{선택}", sel)
        back = body.find("{커서}")
        body = body.replace("{커서}", "")
        cur.beginEditBlock()
        start = cur.selectionStart()
        cur.insertText(body)
        cur.endEditBlock()
        if back >= 0:
            cur.setPosition(start + back)
        self.editor.setTextCursor(cur)

    def open_slot_dialog(self):
        SlotDialog(self).exec()

    def open_all_cards(self):
        """모든 카드 보기 — 작업공간 최상위의 모든 원고를 책별로 묶어 보인다."""
        self.open_cards(all_mode=True)

    def open_cards(self, all_mode: bool = False):
        """카드 보기(시놉시스). 처음 한 번 만들고 이후에는 같은 창을 새로 읽어 보인다."""
        if self._path is None:
            self.statusBar().showMessage("원고를 연 뒤에 카드를 볼 수 있습니다.", 3000)
            return
        if getattr(self, "_cards_dialog", None) is None:
            self._cards_dialog = SynopsisCardsDialog(self)
            self._place_cards_beside_drawer(self._cards_dialog)
        else:
            self._cards_dialog.reanchor()
            self._cards_dialog.reload()
        self._cards_dialog.set_all_mode(all_mode)
        self._cards_dialog.show()
        self._cards_dialog.raise_()

    def _place_cards_beside_drawer(self, dlg):
        """앱을 실행하고 처음 카드 보기를 열 때, 창이 서랍을 가리지 않게 서랍 오른쪽에 둔다
        (서랍에서 카드로 끌어다 놓으려면 둘이 함께 보여야 한다). 서랍이 닫혀 있으면 그대로 둔다."""
        try:
            if not self.drawer.isVisible():
                return
            tl = self.drawer.mapToGlobal(QPoint(0, 0))
            left = tl.x() + self.drawer.width() + 8
            scr = (self.screen() or QGuiApplication.primaryScreen()).availableGeometry()
            width = min(dlg.width(), scr.right() - left - 8)
            if width < 480:                       # 오른쪽이 너무 좁으면 건드리지 않는다
                return
            g = self.geometry()
            top = min(max(g.top() + 40, scr.top()), max(scr.top(), scr.bottom() - dlg.height()))
            dlg.resize(width, dlg.height())
            dlg.move(left, top)
        except Exception:
            pass

    def open_note_panel(self):
        """메뉴에서 부른다 — 메모가 없는 파일에도 새로 쓸 수 있어야
        하므로, 있고 없고를 안 가리고 그냥 연다."""
        if getattr(self, "_note_panel", None) is None:
            self._note_panel = NotePanel(self)
        else:
            self._note_panel.load_for_current()
        self._note_panel.show()
        self._note_panel.raise_()

    def focus_note_of(self, path: Path):
        """서랍의 📝 를 눌렀을 때. 그 파일이 지금 파일이 아니면 먼저 연 뒤, 메모 창을 열어(이미
        열려 있으면 그대로) 포커스를 준다."""
        if self._path != path:
            self.open_from_drawer(path)
            if self._path != path:
                return                      # 열지 못했다(저장 취소 등)
        self.open_note_panel()
        panel = self._note_panel

        def focus():
            panel.raise_()
            panel.activateWindow()
            panel.text.setFocus(Qt.OtherFocusReason)
        focus()
        QTimer.singleShot(0, focus)         # 막 show() 한 창은 한 박자 뒤에야 활성화된다

    def _sync_note_panel(self):
        """파일을 전환할 때마다 부른다(0.4.152). 메모 창을 **저절로 열지 않는다** — 메모는 서랍의 📝 를
        누르거나 [도구 ▸ 메모…] 로 연다. 이미 열려 있던 창은 다른 파일로 넘어간 순간 그 메모가
        이 화면과 무관해지므로 내용을 비우고 닫는다(다음에 열릴 때 새 파일 것이 로드된다)."""
        note_panel = getattr(self, "_note_panel", None)
        if note_panel is not None:
            note_panel.load_for_current()
            note_panel.hide()

    def open_citation_panel(self):
        if getattr(self, "_citation_panel", None) is None:
            self._citation_panel = CitationPanel(self)
        else:
            self._citation_panel.refresh()
        self._citation_panel.show()
        self._citation_panel.raise_()

    # -- AI 도우미 (실험) ---------------------------------------------------------------

    def ai_config(self) -> dict:
        st = self._settings
        tool = str(st.value("ai/tool", "claude"))
        cfg = {"tool": tool if tool in AI_TOOLS else "claude",
               "timeout": int(st.value("ai/timeout", 180) or 180)}
        for t in AI_TOOLS:
            cfg[f"{t}_path"] = str(st.value(f"ai/{t}_path", "") or "")
            cfg[f"{t}_args"] = str(st.value(f"ai/{t}_args", "") or "") or AI_DEFAULT_ARGS[t]
        return cfg

    def ai_prompts(self) -> list:
        raw = self._settings.value("ai/prompts", "")
        try:
            items = json.loads(raw) if raw else None
        except (TypeError, ValueError):
            items = None
        if not isinstance(items, list) or not items:
            return [dict(x) for x in AI_DEFAULT_PROMPTS]
        return [{"name": str(x.get("name", "")), "mode": x.get("mode", AI_REPLACE),
                 "prompt": str(x.get("prompt", ""))} for x in items if isinstance(x, dict)]

    def ai_save_config(self, cfg: dict, items: list):
        st = self._settings
        for k, v in cfg.items():
            st.setValue(f"ai/{k}", v)
        st.setValue("ai/prompts", json.dumps(items, ensure_ascii=False))

    def add_ai_menu(self, menu, cursor):
        sub = menu.addMenu("AI 도우미 (실험)")
        has_sel = cursor.hasSelection()
        for n, item in enumerate(self.ai_prompts()):
            tag = "" if item["mode"] == AI_REPLACE else "  [조언]"
            a = sub.addAction(item["name"] + tag)
            a.setEnabled(has_sel)
            a.triggered.connect(lambda _=False, it=item, c=QTextCursor(cursor): self.run_ai(it, c))
        if not has_sel:
            sub.addSeparator()
            sub.addAction("글을 먼저 선택하세요").setEnabled(False)
        sub.addSeparator()
        sub.addAction("설정…", self.open_ai_settings)

    def run_ai(self, item: dict, cursor: QTextCursor):
        if not cursor.hasSelection():
            return
        dlg = AiResultDialog(self, item, cursor)
        dlg.show()

    def open_ai_settings(self):
        AiSettingsDialog(self).exec()

    # -- 외부 도구 ----------------------------------------------------------------------

    def ext_tools(self) -> list:
        raw = self._settings.value(EXT_TOOLS_KEY, "")
        try:
            items = json.loads(raw) if raw else []
        except (TypeError, ValueError):
            items = []
        return [{"name": str(x.get("name", "")), "command": str(x.get("command", "")),
                 "mode": x.get("mode") if x.get("mode") in EXT_MODE_LABELS else EXT_PROPOSE,
                 "confirm": bool(x.get("confirm", True))}
                for x in items if isinstance(x, dict) and x.get("name")]

    def ext_tool_dirs(self) -> str:
        return str(self._settings.value("exttools/dirs", "") or "")

    def ext_tool_timeout(self) -> int:
        try:
            return int(self._settings.value("exttools/timeout", 60) or 60)
        except (TypeError, ValueError):
            return 60

    def open_ext_tool_settings(self):
        ExtToolSettingsDialog(self).exec()

    def fill_ext_tool_menu(self, menu, cursor=None):
        """외부 도구 목록을 메뉴에 채운다. cursor 가 없으면 편집창의 현재 커서."""
        menu.clear()
        c = cursor if cursor is not None else self.editor.textCursor()
        scope = "선택 범위" if c.hasSelection() else "현재 파일 전체"
        items = self.ext_tools()
        for item in items:
            tag = "  [바로 적용]" if item["mode"] == EXT_APPLY else ""
            a = menu.addAction(item["name"].replace("&", "&&") + tag)
            a.setToolTip(item["command"])
            a.triggered.connect(lambda _=False, it=item, cc=QTextCursor(c): self.run_ext_tool(it, cc))
        if items:
            menu.addSeparator()
            menu.addAction(f"대상: {scope}").setEnabled(False)
        else:
            menu.addAction("등록된 도구가 없습니다").setEnabled(False)
        menu.addSeparator()
        menu.addAction("설정…", self.open_ext_tool_settings)

    def add_ext_tool_menu(self, menu, cursor):
        sub = menu.addMenu("외부 도구")
        self.fill_ext_tool_menu(sub, cursor)

    def run_ext_tool(self, item: dict, cursor: QTextCursor = None):
        """선택 범위(없으면 현재 파일 전체)를 외부 도구에 맡긴다."""
        if self.editor.document() is None or self._path is None and not self.editor.toPlainText():
            return
        c = QTextCursor(cursor) if cursor is not None else QTextCursor(self.editor.textCursor())
        if not c.hasSelection():
            c = QTextCursor(self.editor.document())
            c.select(QTextCursor.Document)
        if not c.selectedText().strip():
            self.statusBar().showMessage("보낼 글이 없습니다", 3000)
            return
        if item.get("confirm", True):
            scope = "선택 범위" if (cursor is not None and cursor.hasSelection()) or (
                cursor is None and self.editor.textCursor().hasSelection()) else "현재 파일 전체"
            dlg = ExtToolConfirmDialog(self, item, scope, len(c.selectedText()))
            if dlg.exec() != QDialog.Accepted:
                return
            item = dict(item, command=dlg.command())
            if dlg.save_requested():
                self._save_ext_tool_command(item)
        if item.get("mode") == EXT_APPLY:
            self._run_ext_tool_apply(item, c)
        else:
            ExtToolResultDialog(self, item, c).show()

    def _save_ext_tool_command(self, item: dict):
        items = self.ext_tools()
        for it in items:
            if it["name"] == item["name"]:
                it["command"] = item["command"]
                break
        self._settings.setValue(EXT_TOOLS_KEY, json.dumps(items, ensure_ascii=False))

    def _run_ext_tool_apply(self, item: dict, cursor: QTextCursor):
        orig = cursor.selectedText()
        plain = orig.replace("\u2029", "\n")
        whole = cursor.selectionStart() == 0 and cursor.selectionEnd() >= self.editor.document().characterCount() - 1
        keep = self.editor.textCursor().position()
        doc = self.editor.document()
        try:
            program, args, stdin_text, tmp = ext_tool_build(item["command"], plain, self.ext_tool_dirs())
        except ValueError as e:
            QMessageBox.warning(self, item["name"], str(e))
            return
        sel = QTextCursor(cursor)
        runner = AiRunner(self)
        self._ext_runners = getattr(self, "_ext_runners", [])
        self._ext_runners.append(runner)
        self.statusBar().showMessage(f"{item['name']} 실행 중…")

        def done(ok, out, err):
            if tmp:
                try:
                    os.remove(tmp)
                except OSError:
                    pass
            if runner in self._ext_runners:
                self._ext_runners.remove(runner)
            runner.deleteLater()
            if not ok:
                self.statusBar().clearMessage()
                QMessageBox.warning(self, item["name"], (err or "알 수 없는 오류")[:600])
                return
            if self.editor.document() is not doc or sel.selectedText() != orig:
                self.statusBar().clearMessage()
                QMessageBox.warning(self, item["name"],
                                    "실행하는 사이 원문이 바뀌었거나 다른 파일로 옮겨 적용하지 않았습니다.")
                return
            new = ext_tool_fit_output(plain, out)
            if new == plain:
                self.statusBar().showMessage(f"{item['name']}: 바뀐 곳이 없습니다", 5000)
                return
            c = QTextCursor(sel)
            c.beginEditBlock()
            c.insertText(new)
            c.endEditBlock()
            if whole:
                tc = self.editor.textCursor()
                tc.setPosition(min(keep, max(0, doc.characterCount() - 1)))
                self.editor.setTextCursor(tc)
            self.statusBar().showMessage(
                f"{item['name']}: 적용했습니다 (Ctrl+Z 로 되돌립니다)" + (f" · {err[:120]}" if err else ""), 8000)

        runner.done.connect(done)
        runner.start(program, args, stdin_text, os.path.dirname(program), self.ext_tool_timeout())

    def dict_lookup(self, text: str, template: str):
        """선택한 글을 사전 주소(`{q}` 자리)에 넣어 기본 브라우저로 연다."""
        QDesktopServices.openUrl(QUrl(dictionary_url(template, text)))

    def open_dictionary_settings(self):
        DictionarySettingsDialog(self).exec()

    def web_lookup(self, text: str, engine: str):
        """선택한 단어/구절을 기본 브라우저로 검색한다. 우클릭 메뉴의
        "찾아보기…" 에서 부른다."""
        query = urllib.parse.quote(text)
        if engine == "wikipedia":
            url = f"https://ko.wikipedia.org/w/index.php?search={query}"
        else:
            url = f"https://www.google.com/search?q={query}"
        QDesktopServices.openUrl(QUrl(url))

    def show_codepoint_at_cursor(self):
        """커서 위치 글자 하나의 유니코드 코드포인트를 상태바에 보여준다.

        선택 영역이 있으면 그게 정확히 한 글자일 때만 그 글자를 본다
        (두 글자 이상을 골랐으면 어느 걸 보라는 건지 애매해진다).
        선택이 없으면 커서 바로 뒤 글자를 본다.
        """
        cursor = self.editor.textCursor()
        if cursor.hasSelection():
            text = cursor.selectedText()
            if len(text) != 1:
                self.statusBar().showMessage(
                    "한 글자만 선택했을 때 코드포인트를 보여줄 수 있습니다", 3000)
                return
            ch = text
        else:
            block_text = cursor.block().text()
            pos = cursor.positionInBlock()
            if pos >= len(block_text):
                self.statusBar().showMessage("커서 뒤에 글자가 없습니다", 3000)
                return
            ch = block_text[pos]
        code = ord(ch)
        self.statusBar().showMessage(f"'{ch}'  U+{code:04X}  ({code})", 8000)

    def find_book_bibliographies(self):
        """책 전체(현재 파일이 책의 일부가 아니면 자기 파일만)에서
        :::{thebibliography} 블록이 있는 파일들을 책 순서대로 찾는다.
        (path, (open_n, close_n), lines) 목록을 돌려준다. 지금 열려
        있는 파일은 디스크가 아니라 편집창에서 읽는다 — 저장 전
        변경도 반영돼야 한다(다른 점검들과 같은 원칙)."""
        found = []
        if self._path is None:
            return found
        for path in LabelIndex.book_files(self.index, self._path):
            if path == self._path:
                lines = self.editor.toPlainText().splitlines()
            else:
                try:
                    lines = read_manuscript(path).splitlines()
                except (OSError, UnicodeDecodeError):
                    continue
            rng = find_bibliography_range_in_lines(lines)
            if rng is not None:
                found.append((path, rng, lines))
        return found

    def open_bibliography_editor(self):
        """[도구] ▸ 참고문헌 편집. thebibliography 는 책 전체에 하나
        있는 것으로 본다 — 지금 편집 중인 파일이 아니라 다른 장(예:
        backmatter.md)에 있어도, 책 안이라면 어디서든 열 수 있어야
        citekey 를 그 자리에서 바로 입력할 수 있다.

        책 안에 여러 개가 발견되면 합칠지 물어보고, 합치면 맨 마지막
        것에 전부 모은다. 거절하면 맨 마지막 것만 유효한 것으로 본다.
        """
        if self._path is None:
            QMessageBox.information(self, "참고문헌 편집", "먼저 원고를 열어 주세요.")
            return
        found = self.find_book_bibliographies()
        if not found:
            target_path = self._path        # 없으면 지금 파일에 새로 만든다(기존 동작)
        elif len(found) == 1:
            target_path = found[0][0]
        else:
            r = QMessageBox.question(
                self, "참고문헌 병합",
                f"둘 이상의 참고문헌이 있습니다({len(found)}개). 병합할까요?",
                QMessageBox.Yes | QMessageBox.No)
            if r == QMessageBox.Yes:
                target_path = self._merge_bibliographies(found)
            else:
                target_path = found[-1][0]  # 맨 마지막 것만 유효

        if getattr(self, "_bib_dialog", None) is None:
            self._bib_dialog = BibliographyGridDialog(self, target_path)
        else:
            self._bib_dialog.set_target(target_path)
        self._bib_dialog.show()
        self._bib_dialog.raise_()

    def _merge_bibliographies(self, found) -> Path:
        """found(책 순서대로의 여러 문헌 목록)를 맨 마지막 파일에
        전부 합친다. 앞선 파일들에서는 그 블록 자체를 지운다. 합쳐진
        대상 파일 경로를 돌려준다."""
        delim = self.prefs.bib_delimiter()
        all_rows = []
        for path, (open_n, close_n), lines in found:
            entry_lines = lines[open_n + 1: close_n]
            for option, key, author, others in parse_bibitem_lines(entry_lines, delim):
                all_rows.append((key, option, author, others))

        for path, rng, lines in found[:-1]:
            self._remove_bibliography_block(path, rng, lines)

        target_path = found[-1][0]
        self.write_bibliography(all_rows, target_path, jump=False)
        return target_path

    def _remove_bibliography_block(self, path: Path, rng, lines: list):
        """참고문헌 병합 때, 맨 마지막이 아닌 파일에서 그 블록
        자체를 지운다."""
        open_n, close_n = rng
        new_lines = lines[:open_n] + lines[close_n + 1:]
        tidy = []
        for line in new_lines:
            if not line.strip() and tidy and not tidy[-1].strip():
                continue
            tidy.append(line)
        out = "\n".join(tidy)
        if out and not out.endswith("\n"):
            out += "\n"
        if path == self._path:
            cursor = QTextCursor(self.editor.document())
            cursor.select(QTextCursor.Document)
            cursor.insertText(out)
        else:
            try:
                path.write_text(out, encoding="utf-8")
            except OSError as e:
                QMessageBox.warning(self, "참고문헌 병합", f"{path.name} 을(를) 고치지 못했습니다: {e}")

    def write_bibliography(self, rows: list, target_path: Path = None, jump: bool = True):
        """그리드 내용을 :::{thebibliography widest=N} ~ ::: 블록으로
        target_path 파일에 다시 쓴다(안 주면 지금 파일). target_path
        가 지금 열려 있는 파일이면 편집창에 반영하고, 아니면 디스크에
        직접 쓴다.

        widest 는 손으로 관리하게 두지 않는다 — 지금 목록의 가장 긴
        citekey 길이로 매번 새로 계산한다(원래 이 값의 존재 이유가
        정렬 들여쓰기 폭이니, 목록이 바뀌면 같이 바뀌는 게 맞다).
        항목 사이에는 빈 줄을 넣는다 — thebibliography 환경은
        `lines: keep` 이 아니라서, 빈 줄 없이 붙이면 ndhmd4tex 이 여러
        \\bibitem 을 한 문단으로 이어붙여 버린다.

        author 뒤 구분자(쉼표/마침표)는 스타일 가이드마다 달라서 설정을
        따른다(참고문헌 편집창의 콤보로 고른다).

        jump 가 True(기본)면 — 대상이 지금 파일이 아니었을 때 — 저장
        직후 그 참고문헌 위치로 커서를 옮긴다(이전 위치는 Alt+Left 로
        돌아올 수 있다). 병합 중 앞선 파일들을 처리할 때는 jump=False
        로 불러서 매번 화면이 튀지 않게 한다.
        """
        if target_path is None:
            target_path = self._path
        delim = self.prefs.bib_delimiter()
        widest = max((len(key) for key, *_ in rows), default=0)
        lines_out = [f":::{{thebibliography widest={widest}}}"]
        for i, (key, option, author, others) in enumerate(rows):
            opt = f"[{option}]" if option else ""
            if author and others:
                body = f"{author}{delim} {others}"
            else:
                body = author or others
            entry = f"\\bibitem{opt}{{{key}}}"
            if body:
                entry += f" {body}"
            lines_out.append(entry)
            if i != len(rows) - 1:
                lines_out.append("")
        lines_out.append(":::")
        new_text = "\n".join(lines_out)

        was_current = (target_path == self._path)
        open_n_after = None
        if was_current:
            cursor = QTextCursor(self.editor.document())
            rng = self.editor.bibliography_range()
            if rng is not None:
                open_n, close_n = rng
                doc = self.editor.document()
                start_block = doc.findBlockByNumber(open_n)
                end_block = doc.findBlockByNumber(close_n)
                cursor.setPosition(start_block.position())
                cursor.setPosition(end_block.position() + end_block.length() - 1,
                                   QTextCursor.KeepAnchor)
                cursor.insertText(new_text)
            else:
                cursor = self.editor.textCursor()
                cursor.insertText(new_text + "\n")
            self.editor.set_bibliography_folded(True)
        else:
            try:
                text = read_manuscript(target_path)
            except (OSError, UnicodeDecodeError):
                QMessageBox.warning(self, "참고문헌 편집", f"{target_path.name} 을(를) 읽지 못했습니다.")
                return
            lines = text.splitlines()
            rng = find_bibliography_range_in_lines(lines)
            if rng is not None:
                open_n, close_n = rng
                new_lines = lines[:open_n] + lines_out + lines[close_n + 1:]
                open_n_after = open_n
            else:
                new_lines = list(lines)
                if new_lines and new_lines[-1].strip():
                    new_lines.append("")
                open_n_after = len(new_lines)
                new_lines.extend(lines_out)
            out = "\n".join(new_lines)
            if text.endswith("\n") or not out.endswith("\n"):
                out += "\n"
            try:
                target_path.write_text(out, encoding="utf-8")
            except OSError as e:
                QMessageBox.warning(self, "참고문헌 편집", f"쓰지 못했습니다: {e}")
                return

        if jump and not was_current and open_n_after is not None:
            self.open_at(target_path, open_n_after + 1)

    def convert_table_cells(self, rows: list):
        """표 편집기용: 셀의 마크다운을 ndhmd4tex 로 LaTeX 로 바꾼다.
        (변환된 행들, "") 또는 (None, 오류 메시지)."""
        if not self._ensure_tool():
            return None, "ndhmd4tex 위치가 지정되지 않았습니다."
        m = FRONTMATTER_RE.match(self.editor.toPlainText())
        front = m.group(1) if m else ""
        path = getattr(self, "_path", None)
        workdir = Path(path).parent if path else self.workspace.root
        return markdown_cells_to_tex(self.tool, rows, workdir, front)

    def open_table_editor_with_text(self, text: str):
        fmt, aligns, data_or_err = TableEditorDialog.parse_table_text(text)
        if fmt is None:
            QMessageBox.information(self, "안내", "더 복잡한 표는 전용 표 편집 프로그램을 이용하셔요")
            return

        if getattr(self, "_table_editor", None) is None:
            self._table_editor = TableEditorDialog(self)
        
        self._table_editor.load_data(fmt, aligns, data_or_err)
        self._table_editor.show()
        self._table_editor.raise_()

    # -- 설정 -----------------------------------------------------------------

    def open_preferences(self):
        dlg = PreferencesDialog(self)
        dlg.exec()

    def apply_preferences(self):
        self.editor._apply_font(self.prefs.font_family(), self.prefs.font_size())
        self.editor._update_gutter_width()
        self.editor.apply_tab_spaces(self.prefs.tab_spaces())
        self.editor.tab_to_spaces_enabled = self.prefs.tab_to_spaces()
        self.editor.smart_quotes_style = self.prefs.smart_quotes_style()
        self.editor.smart_punctuation = self.prefs.smart_punctuation()
        self.editor.set_fullscreen_column(self.prefs.fullscreen_column())
        self._apply_theme(self.prefs.resolved_theme())
        self._apply_item_gap(force=True)

    def _apply_item_gap(self, force: bool = False):
        """목록 항목 간격 설정을 하이라이터에 건다. 시작할 때와 문서를 갈아 끼운 뒤에는
        (글꼴이 막 적용된 상태에서) force 로 서식을 새로 만들고 다시 칠한다."""
        self.editor.highlighter.set_item_gap(
            self.prefs.item_gap_scale() if self.prefs.item_gap() else 0.0,
            self.prefs.item_gap_bullets(), force)

    # -- 전체화면 ---------------------------------------------------------------
    #
    # macOS 의 진짜 전체화면(showFullScreen)은 별도의 "스페이스"로 전환되는
    # 네이티브 전체화면인데, 이 전환 이후 트랙패드의 두 손가락 스크롤 제스처가
    # 자식 위젯까지 내려오지 않는 Qt/Cocoa 쪽의 알려진 문제가 있다. 방향키나
    # 스크롤바 드래그는 전혀 다른 이벤트 경로라 멀쩡한데 트랙패드만 먹통이
    # 되는 증상이 정확히 이 문제의 특징이다.
    #
    # 우회법은 단순하다 — 스페이스를 만들지 않는 "가짜 전체화면"을 쓴다.
    # 창틀을 없애고 화면 크기로 늘리기만 하면 일반 창인 채로 화면을 채우므로
    # 이 버그 자체가 발생할 자리가 없다. 다른 OS 는 이런 문제가 보고된 바
    # 없으니 굳이 흉내 낼 필요 없이 진짜 전체화면을 그대로 쓴다.

    def toggle_fullscreen(self):
        if sys.platform == "darwin":
            self._toggle_fake_fullscreen()
        else:
            self.showNormal() if self.isFullScreen() else self.showFullScreen()

    def _toggle_fake_fullscreen(self):
        if self._fake_fullscreen:
            self.setWindowFlag(Qt.FramelessWindowHint, False)
            self.show()
            if self._pre_fullscreen_geometry is not None:
                self.setGeometry(self._pre_fullscreen_geometry)
            self._fake_fullscreen = False
        else:
            self._pre_fullscreen_geometry = self.geometry()
            screen = self.screen() or QGuiApplication.primaryScreen()
            self.setWindowFlag(Qt.FramelessWindowHint, True)
            self.show()
            if screen is not None:
                self.setGeometry(screen.geometry())
            self._fake_fullscreen = True
        self.editor.set_fullscreen(self._fake_fullscreen)
        self._act_fullscreen.setChecked(self._fake_fullscreen)
        self.editor.setFocus()

    def changeEvent(self, event):
        super().changeEvent(event)
        if event.type() == QEvent.WindowStateChange and sys.platform != "darwin":
            # F11 뿐 아니라 창 관리자의 전체화면 조작도 여기서 같이 잡힌다 —
            # 토글 액션 하나에만 기대면 놓친다. macOS 는 가짜 전체화면을
            # 쓰므로 windowState 가 애초에 바뀌지 않아 이 경로를 안 탄다.
            is_full = self.isFullScreen()
            self.editor.set_fullscreen(is_full)
            self._act_fullscreen.setChecked(is_full)

    # -- 표시 ---------------------------------------------------------------

    def _zoom(self, delta: float):
        font = self.editor.font()
        font.setPointSizeF(max(7.0, font.pointSizeF() + delta))
        self.editor.setFont(font)
        self.editor._update_gutter_width()
        self.prefs.write(font_size=font.pointSizeF())

    def toggle_fence_here(self):
        if not self.editor.toggle_fence_at_cursor():
            self.statusBar().showMessage("커서가 닫힌 코드 펜스나 :::{환경} 안에 있지 않습니다.", 3000)

    def fold_all_fences(self, folded: bool):
        n = self.editor.set_all_fences_folded(folded)
        self.statusBar().showMessage(
            (f"펜스·환경 {n}개를 {'접었습니다' if folded else '폈습니다'}." if n
             else "바꿀 펜스·환경이 없습니다."), 3000)

    def toggle_frontmatter_fold(self, checked: bool | None = None):
        if checked is None:
            checked = not self.editor.frontmatter_folded
        ok = self.editor.set_frontmatter_folded(checked)
        self._act_fold.setChecked(self.editor.frontmatter_folded)
        self._settings.setValue("view/fold_frontmatter", checked)
        if not ok and checked:
            self.statusBar().showMessage("이 원고에는 프론트매터가 없습니다", 2500)
        self.editor.setFocus()

    def _sync_fold_action(self):
        """열린 원고에 설정값을 적용하고 메뉴 체크 상태를 맞춘다."""
        want = self._act_fold.isChecked()
        self.editor.set_frontmatter_folded(want)
        self._act_fold.setEnabled(self.editor.frontmatter_range() is not None)

    def toggle_theme(self):
        self._apply_theme(DARK if self._theme is LIGHT else LIGHT)

    def _apply_theme(self, theme: Theme):
        self._theme = theme
        self.editor.apply_theme(theme)
        self.find_bar.apply_theme(theme)
        self.results.apply_theme(theme)
        self.issues.apply_theme(theme)
        self.drawer.apply_theme(theme)
        self.wing.apply_theme(theme)
        self.toc.apply_theme(theme)
        self.preview.apply_theme(theme)
        self.tag_bar.apply_theme(theme)
        if getattr(self, "_accent_panel", None) is not None:
            self._accent_panel.apply_theme(theme)
        if getattr(self, "_note_panel", None) is not None:
            self._note_panel.apply_theme(theme)
        if getattr(self, "_cards_dialog", None) is not None:
            self._cards_dialog.apply_theme(theme)
        if getattr(self, "_pmime_panel", None) is not None:
            self._pmime_panel.apply_theme(theme)
        self.splitter.setStyleSheet(
            f"QSplitter::handle {{ background: {theme.current_line}; width: 1px; }}")
        self.setStyleSheet(f"""
            QMainWindow {{ background: {theme.bg}; }}
            QMenuBar {{
                background: {theme.bg}; color: {theme.fg};
                border: none; padding: 2px 6px;
            }}
            QMenuBar::item:selected {{ background: {theme.current_line}; }}
            QMenu {{
                background: {theme.bg}; color: {theme.fg};
                border: 1px solid {theme.marker}; padding: 4px;
            }}
            QMenu::item {{ padding: 4px 22px 4px 14px; }}
            QMenu::item:selected {{ background: {theme.current_line}; }}
            QStatusBar {{
                background: {theme.bg}; color: {theme.gutter_fg_active};
                border-top: 1px solid {theme.current_line};
            }}
            QStatusBar QLabel {{ color: {theme.gutter_fg_active}; padding: 0 8px; }}
            QScrollBar:vertical {{ background: transparent; width: 10px; margin: 0; }}
            QScrollBar::handle:vertical {{
                background: {theme.gutter_fg}; border-radius: 5px; min-height: 30px;
            }}
            QScrollBar::add-line, QScrollBar::sub-line {{ height: 0; }}
            QScrollBar::add-page, QScrollBar::sub-page {{ background: transparent; }}
        """)

    def _mark_dirty(self):
        if self._switching_document:
            return                      # 우리가 문서를 갈아 끼우는 중일 뿐, 사용자 편집이 아니다
        if self.editor.toPlainText() == getattr(self, "_baseline_text", None):
            return                      # 포맷팅만 바뀐 신호(여백 재계산 등) — 실제 글자는 그대로다
        was_shown = self._title_dirty
        if not self._dirty and self.prefs.auto_close_drawer() and self.drawer.isVisible():
            # 저장된 상태에서 처음 고치는 순간 — 글쓰기가 시작되었으니 서랍을 닫는다.
            self._act_drawer.setChecked(False)
            self.toggle_drawer(False)
        self._dirty = True
        if self._path is not None:
            if self._has_unsaved():
                self._dirty_docs[self._path] = self.editor.document()
            else:
                self._dirty_docs.pop(self._path, None)
        if was_shown != self._has_unsaved():
            # 비었다가 채워지거나 그 반대일 때만 제목을 다시 그린다.
            self._update_title()
        if self.find_bar.isVisible() and not self.find_bar.is_workspace():
            self.highlight_matches_in_file()
        if self._act_wing.isChecked():
            self._label_timer.start()
        self._schedule_preview()

    def _update_title(self):
        self._title_dirty = self._has_unsaved()
        if self._path and self.workspace:
            name = self.workspace.relative(self._path)
        elif self._path:
            name = self._path.name
        else:
            name = "새 원고"
        enc = self._src_enc.get(self._path) if self._path else None
        mark = f" [{enc}→UTF-8]" if enc in NON_UTF8_ENCODINGS else ""
        self.setWindowTitle(
            f"{'● ' if self._title_dirty else ''}{name}{mark} — {self.workspace.name}")

    def _update_status(self):
        cursor = self.editor.textCursor()
        self._pos_label.setText(
            f"{self.editor.file_line()}행 {cursor.positionInBlock() + 1}열")
        self._ws_label.setText(self.workspace.name)
        block = cursor.block()
        prev = block.previous().userState() if block.previous().isValid() else 0
        depth = max(env_depth(prev), env_depth(block.userState()))
        frame = max(frame_depth(prev), frame_depth(block.userState()))
        parts = []
        if depth:
            parts.append(f"::: {depth}")
        if frame:
            parts.append(f"==== {frame}")
        self._env_label.setText("  ".join(parts))


def _qt_alive(obj) -> bool:
    """C++ 쪽이 이미 지워진 Qt 객체인지(파이썬 참조만 남은 경우)."""
    try:
        obj.isVisible()
        return True
    except RuntimeError:
        return False


def _app_icon() -> QIcon:
    """번들된 아이콘을 스크립트 자신의 위치 기준으로 찾는다.

    없어도 앱이 죽으면 안 되므로(배포 방식에 따라 아이콘 파일 없이 스크립트만
    돌아다닐 수 있다) 못 찾으면 빈 QIcon 을 준다 — Qt 는 그걸 조용히
    기본 아이콘으로 대체한다.
    """
    here = Path(__file__).resolve().parent
    for name in ("ndhmdwriter_icon.png", "icon.png"):
        candidate = here / name
        if candidate.is_file():
            return QIcon(str(candidate))
    return QIcon()


#: Windows 에서 GUI 앱(콘솔 없음)이 콘솔 프로그램(latexmk, xelatex,
#: dvisvgm, ndhmd4tex 등)을 띄우면 그때마다 새 검은 콘솔 창이 잠깐
#: 나타났다 사라진다. subprocess.run() 에 이 플래그를 얹으면 창 없이
#: 조용히 돈다 — 표준 출력/오류 캡처는 그대로 된다. 다른 OS 에는 이
#: 상수 자체가 없으므로 getattr 로 안전하게 0(무시)을 받는다.
_NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)


def _suppress_console(proc: "QProcess"):
    """QProcess 의 자식 콘솔 창을 Windows 에서 숨긴다 — *였다*.

    지금은 어디서도 안 쓰인다. QProcess.setCreateProcessArgumentsModifier()
    로 CREATE_NO_WINDOW 를 걸고, 표준입력을 널 디바이스로 이어 EOF 가
    바로 나오게 하는 것까지 시도했는데도(그 이유는 아래 남겨 둔다),
    Windows 에서 ndhmd4tex 호출이 "…중" 상태로 멈추는 증상이 여전했다.
    Windows 환경 없이 원격으로 두 번 고쳐봤지만 재현·검증이 안 되니,
    깜빡이는 검은 창을 감수하고 확실히 동작하는 예전 방식(콘솔을 그대로
    두는 것)으로 되돌렸다. 아래는 처음 이 함수를 만들 때의 추정이다 —
    맞았을 수도, 틀렸을 수도 있다. 나중에 실제 Windows 에서 하나씩
    다시 검증하기 전까지는 부르지 않는다.

    (원래 추정) 콘솔을 억제하면 자식의 표준입력이 애매한 상태로 남는다.
    콘솔이 있었다면(억제하기 전에는 Windows 가 새 콘솔을 임시로 띄워
    줬다) stdin 이 진짜 터미널이라 `isatty()` 가 참이었을 자리인데,
    콘솔 자체를 없애면 그 판단이 뒤집힌다. "터미널이 아니면 표준입력을
    읽는다"는 흔한 분기가 있는 도구라면, 아무도 채워주지 않는 입력을
    기다리며 자식이 영원히 멈춘다 — 명령행에서 직접 실행하면 멀쩡한
    것과는 맞아떨어졌지만, 표준입력을 널로 이어도 증상이 그대로였던
    걸 보면 이 추정 자체가 틀렸거나 다른 원인이 더 있는 것으로 보인다.

    참고로 subprocess.run() 쪽의 _NO_WINDOW(수식 미리보기의 xelatex 등)는
    이것과 메커니즘이 달라(Qt 의 커스텀 후크가 아니라 파이썬 표준
    subprocess 의 평범한 creationflags 인자다) 그대로 남겨 뒀다 — 지금까지
    이쪽에서 멈춘다는 보고는 없었다.
    """
    if sys.platform != "win32":
        return
    def modifier(args):
        args.flags |= 0x08000000   # CREATE_NO_WINDOW
    proc.setCreateProcessArgumentsModifier(modifier)
    proc.setStandardInputFile(QProcess.nullDevice())


# ---------------------------------------------------------------------------
# 원고 읽기: 인코딩 감지
# ---------------------------------------------------------------------------
#: UTF-8 이 아닌 채로 열린 원고. 저장하면 UTF-8 로 바뀌므로 처음 저장할 때 묻는다.
NON_UTF8_ENCODINGS = ("cp949", "utf-16")


def read_manuscript_ex(path) -> tuple:
    """원고(또는 부속 파일)를 읽어 (글, 원래 인코딩)을 준다.

    UTF-8 BOM 은 떼고("utf-8-sig"), UTF-16 은 BOM 으로 알아보고, 그 밖에는
    UTF-8 을 엄격하게 시도한 뒤 안 되면 cp949 로 읽는다. 줄 끝은
    Path.read_text 처럼 \\n 으로 통일한다. 어느 것으로도 못 읽으면
    UnicodeDecodeError — 부르는 쪽이 이미 잡고 있는 예외다.
    저장은 어디서나 BOM 없는 UTF-8 이다(cp949 로 내보내는 기능은 없다)."""
    data = Path(path).read_bytes()
    if data.startswith(b"\xef\xbb\xbf"):
        text, enc = data[3:].decode("utf-8"), "utf-8-sig"
    elif data.startswith((b"\xff\xfe", b"\xfe\xff")):
        text, enc = data.decode("utf-16"), "utf-16"
    else:
        try:
            text, enc = data.decode("utf-8"), "utf-8"
        except UnicodeDecodeError:
            text, enc = data.decode("cp949"), "cp949"
    if "\r" in text:
        text = text.replace("\r\n", "\n").replace("\r", "\n")
    return text, enc


def read_manuscript(path) -> str:
    return read_manuscript_ex(path)[0]


def decode_subprocess_output(data: bytes) -> str:
    r"""자식 프로세스 출력을 디코딩한다.

    한글 Windows 콘솔은 기본이 cp949 다. ndhmd4tex 처럼 우리가 직접 만든
    파이썬 도구는 PYTHONIOENCODING 으로 UTF-8 을 강제할 수 있지만,
    latexmk/xelatex 같은 외부 TeX 도구는 그럴 수 없어 로캘을 그대로
    따른다. UTF-8 로 무조건 디코딩하면(대체 문자로) 한글 메시지가
    뭉개지므로, UTF-8 을 먼저 엄격하게 시도하고 실패하면 cp949 로,
    그래도 안 되면 마지막에만 UTF-8 대체 디코딩으로 물러난다.
    """
    for enc in ("utf-8", "cp949"):
        try:
            return data.decode(enc)
        except UnicodeDecodeError:
            continue
    return data.decode("utf-8", "replace")


def _pythonic_process_env() -> "QProcessEnvironment":
    """ndhmd4tex 처럼 파이썬으로 만든 자식 프로세스에게 UTF-8 로 말하라고
    시킨다 — *의도는* 그랬다.

    지금은 어디서도 안 쓰인다. QProcess.setProcessEnvironment() 를 걸었더니
    Windows 에서만 ndhmd4tex 호출이 시작은 하고 끝나지 않는 증상이 나왔다
    (같은 코드가 macOS 에서는 멀쩡했다). setProcessEnvironment() 와
    _suppress_console() 의 CreateProcessArgumentsModifier 가 Windows 에서
    서로 간섭하는 것으로 보이는데, 정확한 내부 원인은 Windows 환경 없이
    여기서 못 밝혔다. decode_subprocess_output() 의 cp949 대비만으로도
    원래 문제(한글이 깨지는 것)는 충분히 해결되므로, 위험을 감수하고
    이 함수를 다시 연결할 이유가 없다. 나중에 Windows 에서 정확한 원인을
    밝히기 전까지는 이대로 죽은 코드로 남겨 둔다.
    """
    env = QProcessEnvironment.systemEnvironment()
    env.insert("PYTHONIOENCODING", "utf-8")
    return env


def ndhmdsync_config_path() -> Path | None:
    """ndhmdsync.py 가 세 후보 폴더를 순서대로 뒤지는 것 그대로다.

        ~/Library/ndhmd4tex/config/ndhmdsync.ini   (macOS)
        ~/ndhmd4tex/config/ndhmdsync.ini            (Windows — %USERPROFILE%)
        ~/.config/ndhmd4tex/config/ndhmdsync.ini    (그 외)

    셋 다 뒤지긴 하지만 실제로 쓸 파일은 하나만 있으면 되므로, 이 OS
    몫의 자리에만 쓴다 — 다른 후보에 이미 뭔가 있어도 그건 그대로 두고,
    이 자리가 우선순위상 먼저 읽히니 그걸로 충분하다(macOS 후보가
    최우선이라, macOS 에서는 그 자리에 쓰는 것으로 항상 이긴다).
    """
    home = Path.home()
    if sys.platform == "darwin":
        return home / "Library" / "ndhmd4tex" / "config" / "ndhmdsync.ini"
    if sys.platform == "win32":
        return home / "ndhmd4tex" / "config" / "ndhmdsync.ini"
    return home / ".config" / "ndhmd4tex" / "config" / "ndhmdsync.ini"


def macos_app_bundle():
    """macOS 에서 .app 번들 안에서 돌고 있으면 그 번들 경로, 아니면 None.
    py2app(별칭 모드 포함)은 실행기가 EXECUTABLEPATH·RESOURCEPATH 환경변수를
    정해 준다. 둘 다 없고 얼린 실행 파일이면 sys.executable 의 상위 .app."""
    if sys.platform != "darwin":
        return None
    for var, ups in (("EXECUTABLEPATH", 3), ("RESOURCEPATH", 2)):
        v = os.environ.get(var)
        if v:
            p = Path(v)
            for _ in range(ups):
                p = p.parent
            if p.suffix == ".app":
                return p
    # 얼린 실행 파일(PyInstaller 등)일 때만 실행 파일의 상위 .app 을 인정한다.
    # 얼리지 않은 파이썬은 python.org 판처럼 sys.executable 이 Python.app
    # 안을 가리킬 수 있는데, 그걸 번들로 오인하면 안 된다.
    if getattr(sys, "frozen", False):
        for par in Path(sys.executable).parents:
            if par.suffix == ".app":
                return par
    return None


def self_invoke_template() -> str:
    """지금 실행 중인 나 자신을 --goto %l %f 로 다시 부르는 명령줄.

    PyInstaller 로 얼린 실행 파일이면 그 실행 파일 자체를, 아니면 지금
    돌고 있는 파이썬으로 이 스크립트를 다시 부른다. ndhmdsync.py 는 이
    문자열을 공백 기준으로 토큰화한 뒤 %l/%f 를 채우므로(먼저 쪼개고
    나중에 채운다 — 경로에 공백이 있어도 안전하다), 경로마다 큰따옴표로
    감싸 둔다.
    """
    bundle = macos_app_bundle()
    if bundle is not None:
        # .app 으로 돌 때 sys.executable 은 번들의 실행기가 아니라 파이썬
        # 해석기다(py2app -A 별칭 모드는 홈브루 파이썬 그 자체). 그것에
        # --goto 를 주면 앱이 아니라 빈 파이썬이 뜬다. `open -n -a` 로
        # 번들을 새 프로세스로 띄우면, 이미 실행 중인 창에는 단일 인스턴스
        # 전달(IPC)로 --goto 가 건네지고 새 프로세스는 곧 끝난다.
        return f'/usr/bin/open -n -a "{bundle}" --args --goto %l %f'
    if getattr(sys, "frozen", False):
        return f'"{sys.executable}" --goto %l %f'
    script = str(Path(__file__).resolve())
    return f'"{sys.executable}" "{script}" --goto %l %f'


def locate_pdf_viewer():
    """OS 별로 정해진 자리에서 PDF 뷰어를 찾아 (실행파일 경로,
    ndhmdsync.ini [PDFVIEW] command 템플릿) 을 준다. 못 찾으면
    (None, None).

    ndhmdsync.py 자신의 하드코딩된 폴백이 실제로 무엇을 실행하는지
    그대로 따른다 — 짐작이 아니라 그 소스를 직접 읽고 옮긴 것이다:

    - Skim 은 앱 번들(.app) 자체가 아니라 그 안의 displayline 헬퍼를
      불러야 정방향 검색 인자(줄, PDF, 소스 파일 순서)를 받는다.
    - Okular 는 `--unique` 뒤에 "PDF경로#src:줄 소스경로" 형태로 묶인
      인자 하나를 받는다 — 셋으로 나뉜 인자가 아니다.
    - SumatraPDF 는 `-reuse-instance -forward-search 소스 줄 PDF` 순서다.

    Windows 후보 경로는 ndhmdsync.py 자신이 보는 것(Program Files 둘,
    %LOCALAPPDATA%\\SumatraPDF)보다 한 자리 더 본다 —
    %LOCALAPPDATA%\\Programs\\SumatraPDF 는 최근 설치 관례라 따로
    추가했다.
    """
    if sys.platform == "win32":
        candidates = [
            r"C:\Program Files\SumatraPDF\SumatraPDF.exe",
            r"C:\Program Files (x86)\SumatraPDF\SumatraPDF.exe",
        ]
        localappdata = os.environ.get("LOCALAPPDATA")
        if localappdata:
            base = Path(localappdata)
            candidates.append(str(base / "SumatraPDF" / "SumatraPDF.exe"))
            candidates.append(str(base / "Programs" / "SumatraPDF" / "SumatraPDF.exe"))
        for c in candidates:
            if Path(c).is_file():
                return c, f'"{c}" -reuse-instance -forward-search %f %l %p'
        return None, None

    if sys.platform == "darwin":
        exe = Path("/Applications/Skim.app/Contents/SharedSupport/displayline")
        if exe.is_file():
            return str(exe), f'"{exe}" %l %p %f'
        return None, None

    found = shutil.which("okular")
    if found:
        return found, f'{found} --unique "%p#src:%l %f"'
    return None, None


def locate_tblrdoumi() -> str | None:
    """Windows 에서 tblrDoumi.exe 가 흔히 설치되는 두 자리를 본다 —
    사용자가 직접 지목한 곳이다. macOS 는 여기서 경로를 찾지 않는다 —
    `open -a`가 이름만으로 LaunchServices 를 통해 찾아 주므로, 파일
    경로를 직접 뒤질 필요가 없다(오히려 어느 볼륨의 어느 자리에
    설치했는지 짐작하는 쪽이 더 깨지기 쉽다).
    """
    if sys.platform != "win32":
        return None
    candidates = [r"C:\Program Files\tblrDoumi\tblrDoumi.exe"]
    localappdata = os.environ.get("LOCALAPPDATA")
    if localappdata:
        candidates.append(str(Path(localappdata) / "Programs" / "tblrDoumi" / "tblrDoumi.exe"))
    for c in candidates:
        if Path(c).is_file():
            return c
    return None


_IPC_KEY = "ndhmdWriter-singleinstance"


def _try_send_to_running_instance(argv: list) -> bool:
    """이미 떠 있는 인스턴스가 있으면 인자를 그리로 넘기고 True.

    없으면(또는 응답이 없으면) False — 이 프로세스가 직접 창을 띄워야
    한다. 짧은 시간제한만 두므로, 평소(아무도 안 떠 있을 때) 시작이
    느려지지 않는다.
    """
    socket = QLocalSocket()
    socket.connectToServer(_IPC_KEY)
    if not socket.waitForConnected(500):
        return False
    payload = "\x00".join(argv).encode("utf-8")
    socket.write(payload)
    socket.waitForBytesWritten(1000)
    socket.disconnectFromServer()
    return True


def process_argv(win: "MainWindow", argv: list):
    """`--goto 줄 파일` 또는 파일 경로 하나. 시작할 때와 IPC 로 다른
    인스턴스의 요청을 받았을 때 둘 다 이 함수를 거친다."""
    if not argv:
        return
    if argv[0] == "--goto" and len(argv) >= 3:
        try:
            line = int(argv[1])
        except ValueError:
            return
        target = Path(argv[2]).resolve()
        if not target.is_file():
            win.statusBar().showMessage(f"파일을 찾지 못했습니다: {target}", 6000)
            return
        _ensure_workspace_for(win, target)
        win.open_path(target, line)
        return
    target = Path(argv[0]).resolve()
    if target.is_file():
        _ensure_workspace_for(win, target)
        win.open_path(target)


def _ensure_workspace_for(win: "MainWindow", target: Path):
    """인자로 받은 파일이 지금 작업공간 밖이면, 그 파일의 폴더를
    작업공간으로 삼는다. main() 이 원래 하던 것과 같은 판단이다."""
    if not win.workspace.contains(target):
        win.workspace = Workspace(target.parent)
        win._settings.setValue("workspace/root", str(win.workspace.root))
        win.index = BookIndex(win.workspace)
        win.tags = TagStore(win.workspace)


def _fix_macos_path():
    """Finder 로 더블클릭해 켠 앱은 로그인 셸의 PATH 를 물려받지 않는다.

    launchd 가 주는 기본 PATH 는 `/usr/bin:/bin:/usr/sbin:/sbin` 정도뿐이라,
    터미널에서 이 스크립트를 돌릴 때는 안 보이던 문제가 .app 으로 묶어
    더블클릭하는 순간 나타난다 — latexmk 도 ksruncltex 도 kpsewhich 도
    "PATH 에 없다"는 정직하지만 헷갈리는 오류로 이어진다.

    MacTeX 은 항상 /Library/TeX/texbin 에 xelatex·latexmk·kpsewhich·texlua
    를 심볼릭 링크로 모아 두고, ndhmd4tex/ndhmdsync 는 보통 /usr/local/bin
    (Homebrew 인텔이나 수동 설치)이나 /opt/homebrew/bin(Homebrew 애플
    실리콘)에 놓인다. 이 세 곳을 시작할 때 보충해 둔다.
    """
    if sys.platform != "darwin":
        return
    extra = ("/Library/TeX/texbin", "/usr/local/bin", "/opt/homebrew/bin")
    parts = os.environ.get("PATH", "").split(os.pathsep)
    # 뒤에 붙이면 기존 PATH 어딘가에 이름만 같은 깨진/구식 실행 파일이 먼저
    # 걸릴 수 있다. 앞에 둬서 이 세 곳이 항상 우선하게 한다.
    prepend = [p for p in extra if p not in parts and Path(p).is_dir()]
    os.environ["PATH"] = os.pathsep.join(prepend + parts)


# =============================================================================
# 다국어(i18n) — 한국어 / English
# =============================================================================
# 설계: 화면에 보이는 글을 모두 한국어로 쓰되, 영어를 고르면 Qt 경계(위젯에
# 글을 넘기는 자리)에서만 번역한다. 한국어 모드에서는 아무것도 가로채지
# 않는다 — 이 절 전체가 한국어 경로에는 영향이 없다.
#
#   _EN        {한국어: 영어} 정확 일치. 값에 {0} {1}… 이 있고 키에 {} 가
#              있으면 "f-문자열 서식"으로 보고 정규식으로 맞춘다(자리 채움은
#              다시 번역한다).
#   _T(s)      정확 일치 → 서식 일치 → (모두 안 되면) 긴 구절 부분 치환.
#              한글이 없는 글은 그대로 돌려준다(멱등).
#   install_i18n("en")  QAction·QLabel·버튼·메뉴·메시지 상자·입력 대화상자·
#              파일 대화상자·표/목록 항목·상태 표시줄 등의 글 받는 자리를 감싼다.
#
# 번역하지 않는 것: 사용자 원고·파일 이름, AI 도우미에 보내는 지시문,
# 한국어 매뉴얼(MANUAL.md), 단축키 이름.

_UI_LANG = "ko"
_HANGUL_RE = re.compile("[가-힣ㄱ-ㅎㅏ-ㅣ]")

_EN = {
    '외부 도구(&Z)': 'External tools(&Z)',
    '외부 도구': 'External tools',
    '등록된 도구가 없습니다': 'No tools registered',
    '  [바로 적용]': '  [apply directly]',
    '대상: {}': 'Target: {0}',
    '현재 파일 전체': 'Whole current file',
    '보낼 글이 없습니다': 'There is no text to send',
    '{} 실행 중…': '{0} running…',
    '실행 중…': 'Running…',
    '{}: 바뀐 곳이 없습니다': '{0}: nothing changed',
    '{}: 적용했습니다 (Ctrl+Z 로 되돌립니다)': '{0}: applied (undo with Ctrl+Z)',
    '실행하는 사이 원문이 바뀌었거나 다른 파일로 옮겨 적용하지 않았습니다.': 'The original text changed while the tool ran, or you moved to another file, so nothing was applied.',
    '외부 도구 — {}': 'External tool — {0}',
    '변경점 보기 (글자 단위)': 'Show changes (character level)',
    '완료. 변경점을 보고 반영하세요.': 'Done. Review the changes and apply them.',
    '<b>{}</b> · {} · 입력 {}자': '<b>{0}</b> · {1} · input: {2} chars',
    '외부 도구 설정': 'External tool settings',
    '실행 전 확인': 'Confirm before run',
    '외부 도구 실행 — {}': 'Run external tool — {0}',
    '대상: {} · {}자': 'Target: {0} · {1} chars',
    '이 명령을 도구에 저장': 'Save this command to the tool',
    '옵션 도움말 (--help)': 'Option help (--help)',
    '실행 파일: {}': 'Executable: {0}',
    '불러오는 중…': 'Loading…',
    '도움말을 얻지 못했습니다.': 'Could not get the help text.',
    '명령': 'Command',
    '교체 제안': 'Replacement proposal',
    '바로 적용': 'Apply directly',
    '추가 검색 폴더': 'Extra search folders',
    '비워 두면 PATH 와 흔한 설치 위치에서 찾습니다 (여러 폴더는 ; 로 구분)': 'If empty, PATH and common install locations are searched (separate several folders with ;)',
    '{}번째 줄: 이름과 명령을 모두 적어 주세요.': 'Row {0}: enter both a name and a command.',
    '명령이 비어 있습니다.': 'The command is empty.',
    '명령을 읽을 수 없습니다: {}': 'Could not parse the command: {0}',
    '실행 파일이 없습니다: {}': 'Executable not found: {0}',
    "{} 을(를) 찾지 못했습니다. PATH 나 '추가 검색 폴더'에 두세요.": "Could not find {0}. Put it on PATH or in 'Extra search folders'.",
    '선택한 글(없으면 현재 파일 전체)을 명령의 표준 입력으로 보내고, 표준 출력으로 글을 바꿉니다.\n인자에 {입력} 이 있으면 글을 임시 파일(UTF-8)에 쓰고 그 경로를 넣습니다(표준 입력은 쓰지 않음).\n예: hgwordstitcher   ·   aspell --lang=en pipe   ·   "C:\\tools\\fix.exe" {입력}': 'Sends the selected text (or the whole current file if nothing is selected) to the command\'s standard input, and replaces the text with its standard output.\nIf the arguments contain {입력}, the text is written to a temporary file (UTF-8) and its path is substituted (standard input is not used).\nExamples: hgwordstitcher   ·   aspell --lang=en pipe   ·   "C:\\tools\\fix.exe" {입력}',
    '절': 'Section',
    '삽입 대상: {}': 'Insert into: {0}',
    '{} 자': '{0} chars',
    '📚 참고문헌': '📚 Bibliography',
    '스타일·정의': 'Styles & definitions',
    '  {}   ·   {}줄 접힘': '  {0}   ·   {1} lines folded',
    '원고 ({});;부속 파일 ({});;모든 파일 (*)': 'Manuscripts ({0});;Auxiliary files ({1});;All files (*)',
    '번호': 'Number',
    '이름+번호': 'Name + number',
    '수식 (1)': 'Equation (1)',
    '그림 N': 'Figure N',
    '표 N': 'Table N',
    '제목(직접 정의 매크로)': 'Title (custom macro)',
    '제목(hyperref 표준)': 'Title (hyperref standard)',
    '쪽수': 'Page number',
    '컴파일 실패': 'Compile failed',
    '다른 프로그램이 등록되어 있습니다:\n{}': 'Another program is registered:\n{0}',
    '미리볼 수 없는 파일 형식입니다.': 'This file type cannot be previewed.',
    '조각 그림 ‘{}’ — {}': 'Snippet figure ‘{0}’ — {1}',
    '분수': 'Fraction',
    '분수(디스플레이 크기)': 'Fraction (display size)',
    '분수(인라인 크기)': 'Fraction (inline size)',
    '연분수': 'Continued fraction',
    '이항계수': 'Binomial coefficient',
    '제곱근': 'Square root',
    '극한': 'Limit',
    '상극한': 'Limit superior',
    '하극한': 'Limit inferior',
    '최댓값': 'Maximum',
    '최솟값': 'Minimum',
    '상한': 'Supremum',
    '하한': 'Infimum',
    '위줄': 'Overline',
    '밑줄': 'Underline',
    '위 중괄호': 'Overbrace',
    '아래 중괄호': 'Underbrace',
    '위에 얹기': 'Stack above',
    '아래에 달기': 'Stack below',
    '긴 화살표(위 글)': 'Long arrow (text above)',
    '여러 줄 첨자': 'Multi-line subscript',
    '글자(본문 글꼴)': 'Text (body font)',
    '굵은 글자': 'Bold text',
    '로만체': 'Roman',
    '굵은체': 'Bold',
    '굵은 기호': 'Bold symbol',
    '칠판체 ℝ': 'Blackboard bold ℝ',
    '필기체 𝒜': 'Calligraphic 𝒜',
    '프락투어 𝔄': 'Fraktur 𝔄',
    '스크립트체': 'Script',
    '이탤릭': 'Italic',
    '산세리프': 'Sans-serif',
    '타자체': 'Typewriter',
    '함수 이름': 'Function name',
    '모자': 'Hat',
    '긴 모자': 'Wide hat',
    '물결': 'Tilde',
    '긴 물결': 'Wide tilde',
    '줄': 'Bar',
    '벡터': 'Vector',
    '점': 'Dot',
    '두 점': 'Double dot',
    '( … ) 크기 맞춤': '( … ) auto-sized',
    '[ … ] 크기 맞춤': '[ … ] auto-sized',
    '{ … } 크기 맞춤': '{ … } auto-sized',
    '| … | 크기 맞춤': '| … | auto-sized',
    '‖ … ‖ 크기 맞춤': '‖ … ‖ auto-sized',
    '⟨ … ⟩ 크기 맞춤': '⟨ … ⟩ auto-sized',
    '⌊ … ⌋ 크기 맞춤': '⌊ … ⌋ auto-sized',
    '⌈ … ⌉ 크기 맞춤': '⌈ … ⌉ auto-sized',
    '한쪽만 있는 구분자': 'One-sided delimiter',
    '식 번호 직접 지정': 'Set equation number manually',
    '라벨': 'Label',
    '정렬 사이 글': 'Text between alignments',
    '넓은 공백': 'Wide space',
    '공백': 'Space',
    '얇은 공백': 'Thin space',
    '중간 공백': 'Medium space',
    '음의 공백': 'Negative space',
    '그리스 문자': 'Greek letters',
    '관계': 'Relations',
    '연산·논리': 'Operators & logic',
    '화살표': 'Arrows',
    '기타 기호': 'Other symbols',
    '점·괄호': 'Dots & brackets',
    '분수·근호·첨자': 'Fractions, roots, scripts',
    '큰 연산자': 'Large operators',
    '괄호(크기 맞춤)': 'Brackets (auto-sized)',
    '글꼴·장식': 'Fonts & decorations',
    '위 첨자': 'Superscript',
    '아래 첨자': 'Subscript',
    '수식모드의 액센트': 'Math-mode accents',
    '이항 관계 연산자': 'Binary relations',
    '이항 연산자': 'Binary operators',
    '여닫는 부호': 'Delimiters',
    '기타 부호': 'Miscellaneous',
    '수학 기호가 아닌 것': 'Non-mathematical symbols',
    'AmS: 기호 모음': 'AmS: symbol sets',
    '그밖에': 'Others',
    '{}   {}   ({}곳)': '{0}   {1}   ({2} places)',
    '? 확인 필요   {}   [{}]   ({}곳)': '? Needs checking   {0}   [{1}]   ({2} places)',
    '파일': 'File',
    '편집': 'Edit',
    '보기': 'View',
    '도구': 'Tools',
    '컴파일': 'Compile',
    '설정': 'Settings',
    '도움말': 'Help',
    '윤문 (뜻은 그대로)': 'Polish (keep meaning)',
    '문어체로': 'To written style',
    '구어체로': 'To spoken style',
    '더 간결하게': 'More concise',
    '묘사 보강': 'Enrich description',
    '조언 (문제점과 개선 제안)': 'Advice (problems & suggestions)',
    '자료 보충 (확인할 사실)': 'Research notes (facts to check)',
    '네이버 국어사전': 'Naver Korean Dictionary',
    '네이버 영한사전': 'Naver English-Korean Dictionary',
    '네이버 한자사전': 'Naver Hanja Dictionary',
    '내보냈습니다: {}': 'Exported: {0}',
    '그림 · {}': 'Figure · {0}',
    '라벨 날개': 'Label flags',
    '각주': 'Footnote',
    '상호참조 라벨': 'Cross-reference label',
    '문헌': 'Reference',
    '참조 표지': 'Reference marker',
    '{} 사본{}': '{0} copy{1}',
    '\n\n하위 파일에 붙인 태그·메모·시놉시스도 함께 사라집니다. 되돌릴 수 없습니다.': '\n\nTags, memos and synopses attached to the sub-files will also be lost. This cannot be undone.',
    '   ·   ⚠ 서랍 ▸ 컴파일 참고: {}': '   ·   ⚠ Drawer ▸ Compile notes: {0}',
    '작업공간 청소 완료 — 원고 {}개, 파일 {}개 삭제': 'Workspace cleaned — {0} manuscripts, {1} files deleted',
    '표제 {}개를 {}': '{0} headings {1}',
    '첫 줄이 `+` 로 시작하지 않습니다': 'The first line does not start with `+`',
    '닫힌 셀을 찾지 못했습니다': 'Could not find a closed cell',
    '표의 첫 줄과 끝 줄이 가로 테두리가 아닙니다': 'The first and last lines of the table are not horizontal borders',
    '바닥글(두 번째 `=` 줄)이 있는 grid 표는 편집기에서 다룰 수 없습니다': 'Grid tables with a footer (a second `=` line) cannot be handled in the editor',
    '머리글이 정확히 한 줄인 grid 표만 편집기에서 다룰 수 있습니다 (첫 행 아래에 `+===+` 줄이 하나 있어야 합니다)': 'Only grid tables with exactly one header row can be handled in the editor (there must be a single `+===+` line below the first row)',
    '프론트매터': 'Front matter',
    '줄 접힘': 'lines folded',
    '(작업공간 없음)': '(no workspace)',
    '찾을 내용': 'Find',
    '바꿀 내용': 'Replace with',
    '대소문자': 'Match case',
    '정규식': 'Regex',
    '바꾸기': 'Replace',
    '모두 바꾸기': 'Replace all',
    '바꾸기 줄 열기/닫기': 'Show/hide replace row',
    '찾기·바꾸기 이력 (입력칸에서 ↑/↓)': 'Find/replace history (↑/↓ in the field)',
    '파인더에서 보기': 'Reveal in Finder',
    '탐색기에서 보기': 'Show in Explorer',
    '삭제(&X)': 'Delete(&X)',
    '훑어보기(&P)…': 'Preview(&P)…',
    '시스템 편집기로 열기(&E)': 'Open in system editor(&E)',
    '파일명 복사(&C)': 'Copy file name(&C)',
    '열기': 'Open',
    '작업공간으로 이동(&W)': 'Move to workspace(&W)',
    '자료 창고로 이동(&A)': 'Move to archive(&A)',
    '이름 또는 #태그로 거르기': 'Filter by name or #tag',
    '태그로 거르기 — 고르면 입력창에 이어 붙는다': 'Filter by tag — your choice is appended to the field',
    '태그': 'Tags',
    '#초고  #1장  — 원고에는 들어가지 않습니다': '#draft  #ch1  — not included in the manuscript',
    '떼어내기 — 따로 떠다니는 창으로': 'Detach — into a floating window',
    '닫기': 'Close',
    '라벨 거르기': 'Filter labels',
    '더블클릭 → 참조 삽입 · 우클릭 → 형식 선택': 'Double-click → insert reference · Right-click → choose format',
    '정의 위치로 가기': 'Go to definition',
    '라벨 이름 복사': 'Copy label name',
    '모두 접기': 'Collapse all',
    '다시 읽기 — 타이핑만으로는 자동 갱신되지 않는다(파일 전환·저장 때 새로 짠다)': 'Reload — typing alone does not refresh it (rebuilt on file switch or save)',
    '{}: 프론트매터가 목록/사전 형태가 아닙니다.': '{0}: the front matter is not a list/dictionary.',
    '미리보기': 'Preview',
    '지금 가져오기': 'Fetch now',
    '받는 중…': 'Downloading…',
    '정방향 검색으로 열기 (커서 위치)': 'Open with forward search (cursor position)',
    '시스템 PDF 뷰어로 열기': 'Open with system PDF viewer',
    '열지 않음': "Don't open",
    '고정폭 글꼴만': 'Monospaced fonts only',
    '끄면 모든 글꼴을 고르는 목록에 나열합니다. 옛한글처럼 고정폭 글꼴에 없는 글자를\n쓸 때 필요합니다. 고정폭이 아니면 표·코드의 열이 어긋나 보일 수 있고, 본문 폭 계산\n("0" 글자 폭 기준)도 글꼴에 따라 달라집니다.': 'When off, all fonts are listed. Needed for characters (such as Old Hangul) that monospaced fonts lack. With a non-monospaced font, table and code columns may look misaligned, and the body-width calculation (based on the width of "0") varies by font.',
    '편집창 글꼴': 'Editor font',
    '탭 너비(칸)': 'Tab width (columns)',
    '탭 문자(\\t)를 스페이스로': 'Convert tab (\\t) to spaces',
    'YAML 프론트매터에 탭 문자가 섞이면 파서가 바로 오류를 냅니다. 끄면 Tab 키가 탭 문자를 그대로 넣습니다 — 탭 문자를 선호하는 분들을 위해 꺼 둘 수 있게 했습니다.': 'A tab character in YAML front matter makes the parser fail immediately. When off, the Tab key inserts a literal tab — provided for those who prefer tab characters.',
    '설명 목록 항목 사이 간격 (화면 표시만)': 'Spacing between description-list items (display only)',
    'ndhmd4tex 는 목록 항목 사이의 빈 줄을 허용하지 않습니다. 대신 `항목 :: 설명` 줄의\n`::` 앞 공백 한 글자를 크게 그려 그 줄을 높입니다. 원고 내용·줄 번호·실행 취소에는\n영향이 없고 화면에서만 항목이 벌어져 보입니다. 기본은 꺼져 있습니다.': 'ndhmd4tex does not allow blank lines between list items. Instead, the single space before `::` in an `item :: description` line is drawn larger to make that line taller. The manuscript text, line numbers and undo are unaffected; items only look more spread out on screen. Off by default.',
    ' 배': '×',
    '글머리표·번호 목록에도 적용': 'Also apply to bulleted/numbered lists',
    '`- `, `1. ` 뒤의 공백을 키웁니다. 위 항목이 꺼져 있으면 무시됩니다.': 'Enlarges the space after `- ` and `1. `. Ignored if the option above is off.',
    '한자 변환: 최근 입력한 한자 우선': 'Hanja conversion: prefer recently used hanja',
    'F9 후보 창에서 한 번 고른 한자를 같은 읽기의 후보 맨 앞으로 올립니다.\n예: `가` 에서 歌 를 골랐으면 다음부터 歌 가 먼저 나옵니다.': 'A hanja picked once in the F9 candidate window moves to the front of the candidates for the same reading.\nExample: if you chose 歌 for `가`, 歌 comes first from then on.',
    '한자 변환: 한글 병기 — 國家(국가)': 'Hanja conversion: add hangul reading — 國家(국가)',
    '한자를 넣을 때 읽기를 괄호로 덧붙입니다.': 'Appends the reading in parentheses when inserting hanja.',
    '한자 변환: 한자 병기 — 국가(國家)': 'Hanja conversion: add hanja — 국가(國家)',
    '원래 한글을 그대로 두고 한자를 괄호로 덧붙입니다. 한글 병기와는 둘 중 하나만 켜집니다.': 'Keeps the original hangul and appends the hanja in parentheses. Only one of this and the hangul-reading option can be on.',
    '창 크기·위치 기억': 'Remember window size & position',
    '켜 두면 다음에 실행할 때 지난번 창 크기와 위치를 그대로 되살립니다.': 'When on, the window size and position from last time are restored at the next launch.',
    '마지막 원고 다시 열기': 'Reopen last manuscript',
    '켜면 앱을 시작할 때 직전에 열어 두었던 원고를 그 줄 위치까지 다시 엽니다.\n작업공간은 원래 저장되어 있으므로, 그 작업공간 안의 파일일 때만 열립니다.\nPDF 뷰어의 역방향 검색이나 파일 인자로 시작할 때는 그쪽이 우선합니다.\n기본은 꺼져 있습니다.': "When on, the manuscript that was open last is reopened at startup, at the same line. The workspace is saved anyway, so this only applies to files inside that workspace. When launched via the PDF viewer's reverse search or with a file argument, that takes priority. Off by default.",
    '글쓰기가 시작되면 서랍을 자동으로 닫기': 'Auto-close the drawer when writing starts',
    '저장된 상태의 원고를 처음 고치는 순간 서랍을 닫아 글쓰기에 집중하게 합니다.\n서랍은 Ctrl+B 로 다시 열 수 있고, 다시 열어 두면 계속 고치는 동안에는 닫히지 않습니다\n(저장한 뒤 다시 고치기 시작할 때 또 닫힙니다).': 'Closes the drawer the moment you first edit a saved manuscript, so you can focus on writing. Reopen it with Ctrl+B; if you reopen it, it stays open while you keep editing (it closes again the next time you start editing after a save).',
    '책을 컴파일하면 하위 파일의 단독 산출물 지우기': 'Delete stand-alone outputs of sub-files when compiling the book',
    "책 전체 컴파일이 성공하면, 그 책에 포함된 하위 파일의 .tex·.nmdsync·.synctex 를\n지웁니다(이전에 '이 파일만' 컴파일해서 생긴 낡은 것). PDF 는 지우지 않습니다.\n정방향 검색은 하위 파일 자신의 .nmdsync 와 PDF 가 있으면 그쪽으로,\n없으면 책의 PDF 로 갑니다.": "When the whole book compiles successfully, the .tex, .nmdsync and .synctex files of the sub-files in that book are deleted (stale leftovers from compiling 'this file only'). PDFs are not deleted. Forward search uses the sub-file's own .nmdsync and PDF if present, otherwise the book's PDF.",
    ' 자': ' chars',
    '전체화면 편집 폭': 'Full-screen editor width',
    '전체화면일 때만 적용됩니다. 창 모드에서는 창 크기를 따릅니다.': 'Applies only in full-screen mode. In windowed mode the window size is used.',
    '문단 재배열 너비': 'Paragraph reflow width',
    '한 줄로 합치기(끄면 위 너비에서 줄바꿈)': 'Join into one line (when off, wrap at the width above)',
    '미리보기에서 원격 그림 자동으로 가져오기': 'Auto-fetch remote images in preview',
    "꺼두면 URL 그림은 '지금 가져오기'를 눌러야 내려받습니다.\n남이 준 원고를 열 때 의도치 않게 외부로 요청이 나가지 않도록 기본은 꺼져 있습니다.": "When off, URL images are downloaded only when you press 'Fetch now'. Off by default so that opening someone else's manuscript does not send unintended outside requests.",
    '커서가 수식·그림·표 위에 머물면 미리보기 자동으로 열기': 'Auto-open preview when the cursor rests on a formula, image or table',
    '기본은 꺼져 있습니다 — 미리보기 패널은 원래 "읽는 중에 튀어나오지\n않는다"는 게 설계 의도라, 이건 그 반대로 쓰고 싶을 때만 켜는 것입니다.\n켜 두면, 벗어났을 때도 자동으로 연 경우에만 스스로 닫힙니다 —\nCtrl+Shift+P 로 직접 열어 둔 것은 그대로 둡니다.': 'Off by default — the preview panel is designed not to pop up while you read, so turn this on only if you want the opposite. When on, it closes itself on leaving only if it was opened automatically; a panel you opened with Ctrl+Shift+P is left alone.',
    ' 초': ' s',
    '시스템을 따름': 'Follow system',
    '밝게': 'Light',
    '어둡게': 'Dark',
    '고대비(순백)': 'High contrast (pure white)',
    '빨강': 'Red',
    '노랑': 'Yellow',
    '초록': 'Green',
    '파랑': 'Blue',
    '테마': 'Theme',
    '지금 등록': 'Register now',
    'SumatraPDF(Windows)·Skim(macOS)에서 Ctrl+클릭으로 이 앱을 열 수 있게 합니다. 누르면 ndhmdsync.ini 에 지금 바로 등록합니다.': 'Lets SumatraPDF (Windows) and Skim (macOS) open this app with Ctrl+click. Pressing it registers the app in ndhmdsync.ini right now.',
    'PDF 뷰어 역방향 검색': 'PDF viewer reverse search',
    '감지된 뷰어로 등록': 'Register detected viewer',
    'Windows 는 SumatraPDF, macOS 는 Skim, Linux 는 Okular 을 정해진 설치 위치에서 찾아 ndhmdsync.ini 의 [PDFVIEW] 에 등록합니다.': 'Looks for SumatraPDF (Windows), Skim (macOS) or Okular (Linux) at their standard install locations and registers it under [PDFVIEW] in ndhmdsync.ini.',
    'PDF 뷰어 기본 앱': 'Default PDF viewer',
    'latexmk: 여러 번 컴파일이 필요한 참고문헌·색인을 알아서 반복합니다.\nksruncltex: 실패 시 콘솔 출력을 그대로 보여줍니다(줄별 되짚기 없음).': 'latexmk: repeats compilation automatically for bibliographies and indexes that need several passes.\nksruncltex: on failure, shows the raw console output (no per-line tracing).',
    '컴파일러': 'Compiler',
    '정방향 검색: 컴파일이 끝나면 지금 커서 줄에 해당하는 PDF 자리를, 등록된 PDF 뷰어로\n엽니다. 시스템 뷰어와 등록한 뷰어가 다를 때 둘이 함께 뜨는 일이 없습니다.\n정방향 검색이 안 되는 경우(예: 하위 원고만 컴파일)에는 PDF만 연다.': 'Forward search: after compiling, opens the PDF position matching the current cursor line in the registered PDF viewer. If the system viewer and the registered viewer differ, they are not both opened. When forward search is unavailable (e.g. compiling a sub-manuscript only), just the PDF is opened.',
    '컴파일 뒤': 'After compile',
    '애니메이션 gif/webp 를 움직이게 넣기 (--animation)': 'Embed animated gif/webp as animation (--animation)',
    '꺼져 있으면 애니메이션 그림도 첫 프레임만 쓴다.\n켜면 프레임을 PNG 로 쪼개 \\animategraphics 로 넣는다 — 움직임은 PDF 뷰어가\n지원할 때(Acrobat 계열)만 보이고, 그 밖의 뷰어는 첫 장만 보인다.\n프레임별 지연은 살지 않고 단일 속도로 재생한다. 프레임이 많으면\n컴파일이 느려지고 PDF 가 커진다. 적용은 다음 컴파일부터.\n※ ndhmd4tex 은 animate 패키지를 불러 주지 않는다 — 원고의 preamble 에\n\\usepackage{animate} 가 있어야 컴파일된다.': "When off, animated images use only their first frame. When on, frames are split into PNGs and inserted with \\animategraphics — the motion is visible only in PDF viewers that support it (Acrobat family); other viewers show only the first frame. Per-frame delays are not preserved; playback uses a single speed. Many frames slow compilation and enlarge the PDF. Takes effect from the next compile.\n※ ndhmd4tex does not load the animate package — the manuscript's preamble must contain \\usepackage{animate} to compile.",
    '전부': 'All',
    ' 장까지': ' pages max',
    '등록되어 있지 않습니다.': 'Not registered.',
    '이 앱이 등록되어 있습니다.': 'This app is registered.',
    '다른 프로그램이 등록되어 있습니다:\n': 'Another program is registered:\n',
    '설정 안 됨(ndhmdsync 자체 기본값 사용)': "Not set (ndhmdsync's own default is used)",
    '설정됨: {}': 'Set: {0}',
    '1~0 선택 · Space/→ 다음 쪽 · ← 이전 쪽 · Esc 닫기': '1–0 select · Space/→ next page · ← previous page · Esc close',
    '훈음(음을 고르세요)': 'Meanings (choose a reading)',
    '한자 후보': 'Hanja candidates',
    '{} {}개 — {}/{} 쪽': '{0} {1} items — page {2}/{3}',
    '두벌식 (%du)': '2-set (%du)',
    '한글자판→영문 (%ed)': 'Hangul keyboard→English (%ed)',
    '변환 없음 (%clean)': 'No conversion (%clean)',
    '한자 필터 없음': 'No hanja filter',
    '한자 (han)': 'Hanja (han)',
    '한중일 pm 입력기': 'CJK pm input',
    '끄면 NFD(첫가끝 자모)로 내보냅니다. 옛한글을 조합해 쓸 때만 끄세요.\nNFD 글자는 문단 재배열 너비·글자 수 계산에서 3글자로 셉니다.': 'When off, output is NFD (conjoining jamo). Turn off only when composing Old Hangul.\nNFD characters count as 3 characters in paragraph reflow width and character counts.',
    'LaTeX 확장': 'LaTeX expansion',
    "\\'e → é, \\x{AC00} → 가 같은 LaTeX 표기를 실제 문자로 바꿉니다.": "Converts LaTeX notation such as \\'e → é and \\x{AC00} → 가 into real characters.",
    '삽입 후 비우기': 'Clear after insert',
    '로마자로 입력 — Enter 삽입 · Shift+Enter 줄바꿈 · Esc 닫기 · Alt+Z 되살리기': 'Type in romanization — Enter insert · Shift+Enter new line · Esc close · Alt+Z restore',
    '변환 결과': 'Result',
    '일어사용자한자': 'Japanese user kanji',
    '일본어 사용자 한자 사전(customkanji.json)을 찾아 입력하고, 등록·수정·삭제합니다.': 'Finds and enters entries from the Japanese user-kanji dictionary (customkanji.json), and adds, edits or deletes them.',
    '삽입': 'Insert',
    '복사': 'Copy',
    '비우기': 'Clear',
    '삽입했습니다': 'Inserted',
    '클립보드로 복사했습니다': 'Copied to clipboard',
    '일본어 사용자 한자': 'Japanese user kanji',
    '검색 (키·한자·신자체로도)': 'Search (also by key, kanji, shinjitai)',
    '새 단어': 'New entry',
    '수정': 'Edit',
    '삭제': 'Delete',
    '다시 읽기': 'Reload',
    '파일을 다시 읽습니다(다른 곳에서 고쳤을 때)': 'Reloads the file (when it was edited elsewhere)',
    '{} / {} 단어 — {}': '{0} / {1} entries — {2}',
    '로마자 키 — 예: ai, ai2 (소문자)': 'Romanized key — e.g. ai, ai2 (lowercase)',
    '예: 愛': 'e.g. 愛',
    '키 ({h:…}):': 'Key ({h:…}):',
    '한자:': 'Kanji:',
    '새 단어 등록': 'Add new entry',
    '단어 수정': 'Edit entry',
    '악상 시르콩플렉스 ^': 'Circumflex ^',
    '악상 그라브 `': 'Grave `',
    '악상 테귀 ´': 'Acute ´',
    '트레마 ¨': 'Diaeresis ¨',
    '틸드 ~': 'Tilde ~',
    '카론 ˇ': 'Caron ˇ',
    '마크롱 ¯': 'Macron ¯',
    '브레베 ˘': 'Breve ˘',
    '세디유 ¸': 'Cedilla ¸',
    '링 ˚': 'Ring ˚',
    '점(위) ˙': 'Dot above ˙',
    '오고넥 ˛': 'Ogonek ˛',
    '괄호': 'Brackets',
    '문장부호': 'Punctuation',
    '기호': 'Symbols',
    '통화': 'Currency',
    '그림문자': 'Pictographs',
    '표정': 'Emoticons',
    '글머리': 'Bullets',
    '보조 입력': 'Helper input',
    '라틴 확장': 'Latin extended',
    '문장부호·괄호': 'Punctuation & brackets',
    'IPA 확장': 'IPA extensions',
    '사용자': 'User',
    '눌러서 커서 위치에 삽입 · 창은 열어 둔 채로 계속 쓸 수 있습니다': 'Click to insert at the cursor · the window can stay open for repeated use',
    '예: AC00, U+1F600, 0x2603': 'e.g. AC00, U+1F600, 0x2603',
    '대문자': 'Uppercase',
    '추가할 문자(코드포인트 입력칸도 같이 쓸 수 있습니다)': 'Character to add (the code point field can be used too)',
    '추가': 'Add',
    '우클릭 — 목록에서 삭제': 'Right-click — remove from list',
    '그림의 형식을 알 수 없습니다: {}\nContent-Type: {} — URL에도 확장자가 없습니다.': 'Unknown image format: {0}\nContent-Type: {1} — the URL has no extension either.',
    '그림이 아니라 문서가 돌아왔습니다: {}\nContent-Type: {}': 'A document came back instead of an image: {0}\nContent-Type: {1}',
    '훑어보기 — {}': 'Preview — {0}',
    '시스템 프로그램으로 열기': 'Open with system program',
    'PDF 미리보기를 쓰려면 QtPdf 가 있어야 합니다.': 'QtPdf is required for PDF preview.',
    '\\bibitem {}개': '{0} \\bibitem entries',
    '.bib {}개 파일': '{0} .bib files',
    '그림 들여오기': 'Import images',
    '클릭 — 선택 · 더블클릭 — 삽입 · 우클릭 — 정보/열기/이름만 삽입': 'Click — select · Double-click — insert · Right-click — info/open/insert name only',
    'figure로 삽입': 'Insert as figure',
    '예: .6\\linewidth, 5cm': 'e.g. .6\\linewidth, 5cm',
    '새로고침': 'Refresh',
    '가져오기…': 'Import…',
    '그림 ({})': 'Figures ({0})',
    '{} 을(를) {} 로 들여왔습니다.': 'Imported {0} as {1}.',
    '그림 정보': 'Image info',
    '그림 이름만 삽입': 'Insert image name only',
    '파일 이름 (확장자 없이)': 'File name (without extension)',
    'standalone: 한 덩어리 그림(TikZ 등).\narticle / oblivoir: 문단·여러 줄 수식처럼 폭이 정해져야 하는 것.\n여러 쪽이 나오면 쪽마다 따로 잘라 낱장 그림으로 만든다.': 'standalone: a single-block figure (TikZ etc.).\narticle / oblivoir: things that need a defined width, such as paragraphs or multi-line equations.\nIf several pages result, each page is cropped separately into its own figure.',
    'xelatex 가 기본. luamplib(MetaPost 그림) 등 LuaTeX 에서만 되는 것은 lualatex.': 'xelatex is the default. Use lualatex for things that only work in LuaTeX, such as luamplib (MetaPost figures).',
    '예) \\usepackage{tikz}\n\\usepackage{xcolor}': 'e.g. \\usepackage{tikz}\n\\usepackage{xcolor}',
    '미리보기를 누르면 여기에 그림이 나옵니다.': 'Press Preview and the figure appears here.',
    '임시 폴더에 컴파일해 보기만 합니다 (Ctrl+Enter)': 'Only test-compiles in a temporary folder (Ctrl+Enter)',
    '조각 그림 편집 — {}': 'Edit snippet figure — {0}',
    '컴파일 중…': 'Compiling…',
    '{} 을(를) 다시 만들었습니다.': 'Rebuilt {0}.',
    '프리앰블': 'Preamble',
    '그림 코드': 'Figure code',
    '조각 그림 ‘': 'Snippet figure ‘',
    '색상 이름 복사': 'Copy color name',
    'RGB 값 복사': 'Copy RGB value',
    '색상 팔레트': 'Color palette',
    'xcolor 기본': 'xcolor basic',
    'SVG 색상': 'SVG colors',
    '클릭 — 색 이름 삽입 · 우클릭 — 이름/RGB/CMYK 복사': 'Click — insert color name · Right-click — copy name/RGB/CMYK',
    '항상 편집창에 삽입': 'Always insert into the editor',
    '조각 그림 창이 열려 있어도 색 이름을 본문 편집창에 넣습니다.': 'Inserts the color name into the main editor even when a snippet-figure window is open.',
    '색 이름 검색(예: Aqua, DarkGreen)…': 'Search color names (e.g. Aqua, DarkGreen)…',
    '식': 'Equation',
    '번호 없는 식': 'Unnumbered equation',
    '수식을 입력하면 여기에 TeX 로 구운 그림이 나옵니다.': 'Type a formula and its TeX-rendered image appears here.',
    '격자 편집 — {}': 'Grid edit — {0}',
    '행렬·환경 삽입': 'Insert matrix / environment',
    '환경': 'Environment',
    '행': 'Rows',
    '열 (& 로 나뉘는 칸 수)': 'Columns (cells separated by &)',
    '검색: 명령 이름 (예: arrow, le)': 'Search: command name (e.g. arrow, le)',
    '전체': 'All',
    '구조 (분수·근호 …)': 'Structures (fractions, roots …)',
    '기호 그림을 처음 한 번 만드는 중…': 'Building the symbol images for the first time…',
    '기호 {}개 — 누르면 커서 위치에 들어갑니다': '{0} symbols — click to insert at the cursor',
    '\\newcommand{\\R}{\\mathbb{R}} 처럼 쓰는 정의나 \\usepackage': 'Definitions such as \\newcommand{\\R}{\\mathbb{R}}, or \\usepackage',
    '기호 일람표': 'Symbol table',
    '보기(&V)': 'View(&V)',
    '편집(&E)': 'Edit(&E)',
    '격자로 편집(&G)…': 'Edit as grid(&G)…',
    '미리보기 바로 갱신': 'Refresh preview immediately',
    '자동 괄호 짝 (\\left…\\right)': 'Auto bracket pairs (\\left…\\right)',
    '( [ | 를 치면 \\left( \\right) 를 채우고 커서를 가운데에 둔다': 'Typing ( [ | fills in \\left( \\right) and puts the cursor in the middle',
    '삽입(&I)': 'Insert(&I)',
    '행렬·환경 삽입…': 'Insert matrix / environment…',
    '   ⚠ 짝이 안 맞는 괄호 {}곳': '   ⚠ {0} unmatched brackets',
    '(이름 없음)': '(untitled)',
    '{}{} — ndhmdMath {}': '{0}{1} — ndhmdMath {2}',
    '클립보드에 복사했습니다': 'Copied to clipboard',
    '수식 파일 (*.tex *.txt *.md);;모든 파일 (*)': 'Math files (*.tex *.txt *.md);;All files (*)',
    '저장했습니다': 'Saved',
    '다른 이름으로 저장': 'Save as',
    '수식 파일 (*.tex *.txt)': 'Math files (*.tex *.txt)',
    '저장하지 않은 변경이 있습니다. 저장할까요?': 'There are unsaved changes. Save them?',
    '수식 기호': 'Math symbols',
    '전체 보기': 'Show all',
    '검색(예: alpha, sum, ≤)…': 'Search (e.g. alpha, sum, ≤)…',
    '기호 열을 클릭하면 유니코드가, 명령어 열을 클릭하면 LaTeX 코드가 커서 위치에 들어갑니다.': 'Click the symbol column to insert the Unicode character, or the command column to insert the LaTeX code, at the cursor.',
    '이 문서에 대한 메모 — inline 표기 규칙, 마감일 같은 것들': 'Notes on this document — inline notation rules, deadlines, and the like',
    '이 메모 삭제': 'Delete this memo',
    '메모 삭제': 'Delete memo',
    '이 문서의 메모를 지울까요?': "Delete this document's memo?",
    'bib 인용 삽입': 'Insert bib citation',
    '저자·제목·citekey 로 걸러 보기': 'Filter by author, title or citekey',
    '{}개 파일': '{0} files',
    '참고문헌 편집': 'Edit bibliography',
    '행 추가': 'Add row',
    '선택 행 삭제': 'Delete selected rows',
    'author 구분자:': 'Author separator:',
    ', (쉼표)': ', (comma)',
    '. (마침표)': '. (period)',
    '적용': 'Apply',
    '우클릭 — 본문 커서 위치에 그 citekey 삽입': 'Right-click — insert that citekey at the cursor',
    '본문에 citekey 삽입': 'Insert citekey in text',
    '상호참조 점검': 'Cross-reference check',
    '다시 읽기 — 원고를 고친 뒤 목록을 새로 만든다(자동으로 갱신되지는 않는다)': 'Reload — rebuilds the list after you edit the manuscript (it does not refresh automatically)',
    '참조 위치로': 'Go to reference',
    '이 참조가 쓰인 자리로 간다 (더블클릭과 같다)': 'Jump to where this reference is used (same as double-click)',
    '정의 위치로': 'Go to definition',
    '이 라벨이 선언된 자리로 간다 (죽은 참조는 정의가 없다)': 'Jump to where this label is declared (a dead reference has no definition)',
    'Enter: 참조 위치로 · Alt+↓/↑: 같은 라벨의 다음/이전 참조': 'Enter: go to reference · Alt+↓/↑: next/previous reference to the same label',
    "'{}' 참조 {}/{}": "'{0}' reference {1}/{2}",
    '참조 위치로 가기': 'Go to reference',
    '그림 점검': 'Image check',
    '받지 않은 원격 그림 모두 가져오기': 'Fetch all remote images not yet downloaded',
    '변환 필요한 그림 모두 변환하기': 'Convert all images that need conversion',
    '✓ 캐시됨': '✓ Cached',
    '○ 받지 않음': '○ Not downloaded',
    '곳)': ' places)',
    '✓ 준비됨   {}   [{}]   ({}곳)': '✓ Ready   {0}   [{1}]   ({2} places)',
    '△ 변환 필요   {}   [{}]   →  {}{}.png   ({}곳)': '△ Needs conversion   {0}   [{1}]   →  {2}{3}.png   ({4} places)',
    '✗ LaTeX이 못 받는 형식   {}   [{}]   ({}곳)': '✗ Format LaTeX cannot accept   {0}   [{1}]   ({2} places)',
    '? 확인 필요   ': '? Needs checking   ',
    '그림 {}개 중 컴파일 준비됨 {}개{}{}': '{0} images, {1} ready to compile{2}{3}',
    '받는 중… (0/{})': 'Downloading… (0/{0})',
    'ndhmdWriter 도움말': 'ndhmdWriter Help',
    'ndhmd4tex 를 찾지 못했습니다.': 'Could not find ndhmd4tex.',
    '변환 결과에서 표(tblr)를 찾지 못했습니다. ndhmd4tex 의 출력 형식이 달라졌을 수 있습니다.': 'Could not find a table (tblr) in the conversion result. The ndhmd4tex output format may have changed.',
    '변환 결과의 행·열 수가 원래 표와 맞지 않습니다. 셀 안에 표를 깨뜨리는 내용이 있는지 확인해 주세요.': 'The number of rows/columns in the conversion result does not match the original table. Check whether any cell contains something that breaks the table.',
    '간단 표 편집기': 'Simple table editor',
    '마크다운 표 (파이프)': 'Markdown table (pipe)',
    '마크다운 표 (grid)': 'Markdown table (grid)',
    'pandoc 식 grid 표: +---+ 테두리와 | 로 그린 표. 머리글은 첫 행(아래에 +===+).\n칸 너비는 전각 글자를 2칸으로 세어 맞춥니다. 병합 셀·바닥글은 이 편집기로 못 만듭니다.': 'Pandoc-style grid table: drawn with +---+ borders and |. The header is the first row (with +===+ below it).\nColumn widths count full-width characters as 2 columns. Merged cells and footers cannot be created in this editor.',
    '셀의 마크다운을 LaTeX로 변환': 'Convert cell Markdown to LaTeX',
    'LaTeX(tabular/tabularx)로 낼 때, 셀 안의 `코드`·**굵게**·*기울임*·[#라벨] 같은 마크다운과 _ % $ 같은 특수문자를 ndhmd4tex 가 변환하는 그대로 LaTeX 로 바꿉니다. 이미 LaTeX 로 쓴 셀이면 끄십시오.': 'When outputting LaTeX (tabular/tabularx), Markdown in cells such as `code`, **bold**, *italic*, [#label] and special characters like _ % $ are converted to LaTeX exactly as ndhmd4tex does. Turn this off if the cells are already written in LaTeX.',
    '행: ': 'Rows: ',
    '열: ': 'Columns: ',
    '클립보드의 표 붙이기': 'Paste table from clipboard',
    '엑셀·스프레드시트·TSV(탭으로 나뉜 글)를 복사해 둔 것을 표 전체로 가져옵니다.\n지금 표의 내용은 대체됩니다. 칸 안에서 Ctrl+V 를 누르면 그 칸부터 채웁니다.': 'Imports copied Excel / spreadsheet / TSV (tab-separated text) data as the whole table.\nThe current table contents are replaced. Pressing Ctrl+V inside a cell fills from that cell onward.',
    '본문에 삽입': 'Insert into text',
    '취소': 'Cancel',
    '표 형식을 인식할 수 없습니다.': 'The table format could not be recognized.',
    'TAGS 주석': 'TAGS comments',
    '장별로 자르기': 'Split by chapter',
    '하위 파일 접두어:': 'Sub-file prefix:',
    '셸 명령 실행': 'Run shell command',
    '지금 파일: {}': 'Current file: {0}',
    '지금 열린 파일 없음': 'No file open',
    '{filename} 또는 %f → 파일 이름(확장자 제외)으로 바뀝니다. {}': '{filename} or %f → replaced by the file name (without extension). {0}',
    '예: pdflatex {filename}.tex': 'e.g. pdflatex {filename}.tex',
    '실행': 'Run',
    '[종료 코드 {}]': '[exit code {0}]',
    '[실행 실패]': '[failed to run]',
    'tex {}행 → {}:{}  {}': 'tex line {0} → {1}:{2}  {3}',
    '눌러서 이 원고를 연다': 'Click to open this manuscript',
    '{} · {}자': '{0} · {1} chars',
    '작게': 'Small',
    '기본': 'Default',
    '크게': 'Large',
    '카드 보기': 'Card view',
    '＋ 파일 추가': '＋ Add file',
    '서랍의 파일을 이 책의 마지막에 넣는다(서랍에서 끌어다 놓아도 된다)': "Append the drawer's file to the end of this book (you can also drag it from the drawer)",
    '새로 고침': 'Refresh',
    '모든 카드 보기': 'All cards view',
    '작업공간 최상위의 모든 원고를 책별로 묶어 보인다. 이 상태에서는 카드를 옮기거나 책에서 빼지 못한다(시놉시스는 고칠 수 있다).': 'Shows every manuscript at the top level of the workspace, grouped by book. In this state cards cannot be moved or removed from a book (synopses can still be edited).',
    '열기(&O)': 'Open(&O)',
    '인자에 {프롬프트} 가 있어야 합니다.': 'The arguments must contain {프롬프트}.',
    'AI 도우미(실험) — {}': 'AI assistant (experimental) — {0}',
    '답을 기다리는 중…': 'Waiting for a reply…',
    '선택 범위를 이 결과로 교체': 'Replace selection with this result',
    '선택 범위 아래에 삽입': 'Insert below the selection',
    '다시 시도': 'Retry',
    '중단': 'Stop',
    '<b>{}</b> · {} · 선택 {}자': '<b>{0}</b> · {1} · {2} chars selected',
    '답을 기다리는 중… (몇 초 걸립니다)': 'Waiting for a reply… (takes a few seconds)',
    'AI 결과로 교체했습니다(Ctrl+Z 로 되돌립니다).': 'Replaced with the AI result (undo with Ctrl+Z).',
    'AI 결과를 선택 범위 아래에 넣었습니다(Ctrl+Z 로 되돌립니다).': 'Inserted the AI result below the selection (undo with Ctrl+Z).',
    '사전 설정': 'Presets',
    'AI 도우미 설정 (실험)': 'AI assistant settings (experimental)',
    '실험 기능입니다. 선택한 글이 <b>설치된 명령행 도구를 통해 외부 AI 서비스로 전송</b>됩니다. 공개 전 원고라면 서비스의 약관과 데이터 사용 방식을 확인하고 쓰세요. 도구는 원고와 무관한 빈 임시 폴더에서 실행됩니다.': "This is an experimental feature. The selected text is <b>sent to an external AI service through the installed command-line tool</b>. For unpublished manuscripts, check the service's terms and data-use policy first. The tool runs in an empty temporary folder unrelated to the manuscript.",
    '사용할 도구': 'Tool to use',
    '인자에서 {프롬프트} 는 지시문으로 바뀌고, 선택한 글은 표준 입력으로 갑니다. 모델을 고르려면 인자에 --model(claude·agy) 또는 -m(codex) 을 덧붙이세요. 인자에 {선택} 이 있으면 선택한 글을 표준 입력 대신 그 자리에 넣습니다(agy 기본). agy 의 읽기 전용 옵션은 확인하지 못했습니다.': "In the arguments, {프롬프트} is replaced by the instruction and the selected text goes to standard input. To choose a model, append --model (claude, agy) or -m (codex) to the arguments. If the arguments contain {선택}, the selected text is placed there instead of on standard input (agy default). agy's read-only option could not be confirmed.",
    '기다리는 한도': 'Time limit',
    '교체 제안 (결과가 글을 대신함)': 'Replacement (result replaces the text)',
    '조언 (참고용 답)': 'Advice (reference answer)',
    "지시문. 선택한 글은 따로 붙으므로 '표준 입력의 글을 …' 처럼 쓰세요.": "Instruction. The selected text is attached separately, so write it like 'Take the text on standard input and …'.",
    '이름': 'Name',
    '방식': 'Mode',
    '지시문': 'Instruction',
    '약어 슬롯': 'Abbreviation slots',
    '편집창에서 슬롯 단축키를 누르면 등록한 문자열이 커서 자리에 들어갑니다.\n1~5번은 모든 책에서 같고, 6~9·0번은 지금 연 책에만 적용됩니다.\n`{선택}` = 선택했던 글, `{커서}` = 넣은 뒤 커서가 놓일 자리  (예: 「{선택}」{커서})': 'Pressing a slot shortcut in the editor inserts the registered string at the cursor.\nSlots 1–5 are shared by all books; slots 6–9 and 0 apply only to the book currently open.\n`{선택}` = the previously selected text, `{커서}` = where the cursor lands after insertion  (e.g. 「{선택}」{커서})',
    '파일(&F)': 'File(&F)',
    '작업공간 열기(&W)…': 'Open workspace(&W)…',
    '작업공간 이력': 'Workspace history',
    '작업공간 폴더 보기': 'Show workspace folder',
    '새 원고(&N)…': 'New manuscript(&N)…',
    '열기(&O)…': 'Open(&O)…',
    '들여오기(&I)…': 'Import(&I)…',
    '저장(&S)': 'Save(&S)',
    '다른 이름으로 저장(&A)…': 'Save as(&A)…',
    '이 파일 다시 읽기(&R)': 'Reload this file(&R)',
    '서랍 다시 읽기': 'Reload drawer',
    '장별로 자르기(&C)…': 'Split by chapter(&C)…',
    '하위 파일 합치기(&M)…': 'Merge sub-files(&M)…',
    '내보내기': 'Export',
    '닫기(&Q)': 'Quit(&Q)',
    '실행 취소': 'Undo',
    '다시 실행': 'Redo',
    '잘라내기': 'Cut',
    '붙여넣기': 'Paste',
    '찾기(&F)…': 'Find(&F)…',
    '바꾸기(&R)…': 'Replace(&R)…',
    '작업공간에서 찾기(&W)…': 'Find in workspace(&W)…',
    '다음 찾기': 'Find next',
    '이전 찾기': 'Find previous',
    '워드랩(&P)': 'Word wrap(&P)',
    '스마트 문장부호': 'Smart punctuation',
    '마침표·쉼표를 고리점·모점으로(。、)': 'Periods and commas as ideographic marks (。、)',
    "곧은 따옴표: Alt+' / Alt+Shift+'   곧은 마침표·쉼표: Alt+. / Alt+,": "Straight quotes: Alt+' / Alt+Shift+'   Straight period/comma: Alt+. / Alt+,",
    '글머리 기호 목록으로': 'To bulleted list',
    '번호 매긴 목록으로': 'To numbered list',
    '코드펜스로 감싸기': 'Wrap in code fence',
    '인용문으로 감싸기': 'Wrap in blockquote',
    '환경으로 감싸기(&V)…': 'Wrap in environment(&V)…',
    '감싼 것 풀기': 'Unwrap',
    '문단 재배열': 'Reflow paragraph',
    '이전 위치로': 'Back',
    '다음 위치로': 'Forward',
    '참조 ↔ 정의로 가기': 'Go to reference ↔ definition',
    '같은 키의 다음 참조로': 'Next reference with the same key',
    '도구(&T)': 'Tools(&T)',
    '보조 입력(&X)…': 'Helper input(&X)…',
    '수식 기호(&S)…': 'Math symbols(&S)…',
    '수식 편집·삽입(&Y)…': 'Edit/insert math(&Y)…',
    '색상 팔레트(&D)…': 'Color palette(&D)…',
    '커서 위치 코드포인트 보기': 'Show code point at cursor',
    '메모(&M)…': 'Memo(&M)…',
    '약어 슬롯(&Y)…': 'Abbreviation slots(&Y)…',
    'AI 도우미 설정(실험)…': 'AI assistant settings (experimental)…',
    '카드 보기(시놉시스)(&V)…': 'Card view (synopsis)(&V)…',
    '모든 카드 보기(작업공간 전체)…': 'All cards view (whole workspace)…',
    '한중일 pm 입력기…': 'CJK pm input…',
    '선택을 pm 변환 (현재 설정으로 바로)': 'Convert selection with pm (current settings)',
    '한자 변환(&K)': 'Hanja conversion(&K)',
    '그림 들여오기(&I)…': 'Import images(&I)…',
    '간단 표 편집기(&T)…': 'Simple table editor(&T)…',
    '조각 그림 만들기(&J)…': 'Create snippet figure(&J)…',
    '조각 그림 편집(&E)…': 'Edit snippet figure(&E)…',
    'bib 인용 삽입(&C)…': 'Insert bib citation(&C)…',
    '참고문헌 편집(&G)…': 'Edit bibliography(&G)…',
    '셸 명령 실행(&H)…': 'Run shell command(&H)…',
    'tblrDoumi 실행(&Y)': 'Launch tblrDoumi(&Y)',
    '서랍 보이기(&D)': 'Show drawer(&D)',
    '서랍을 최신 수정순으로 정렬(&M)': 'Sort drawer by last modified(&M)',
    '주변 창 모두 닫기(&W)': 'Close all side panels(&W)',
    '라벨 날개(&L)': 'Label flags(&L)',
    'TOC 보기(&C)': 'Show TOC(&C)',
    '미리보기 패널(&P)': 'Preview panel(&P)',
    '프론트매터 접기(&Y)': 'Fold front matter(&Y)',
    '펜스·환경 접기/펴기(커서 위치)': 'Fold/unfold fence or environment (at cursor)',
    '펜스·환경 모두 접기': 'Fold all fences and environments',
    '펜스·환경 모두 펴기': 'Unfold all fences and environments',
    '전체화면(&F)': 'Full screen(&F)',
    '컴파일(&C)': 'Compile(&C)',
    '마크업 점검(&K)': 'Markup check(&K)',
    '그림 점검(&U)…': 'Image check(&U)…',
    '상호참조 점검(&X)…': 'Cross-reference check(&X)…',
    '프론트매터 덤프': 'Dump front matter',
    '책 컴파일(&B)': 'Compile book(&B)',
    '이 파일만 컴파일(&F)': 'Compile this file only(&F)',
    '변환후 tex 열기(&V)': 'Convert and open tex(&V)',
    '결과 tex 열기(&X)': 'Open result tex(&X)',
    'PDF에서 이 위치 보기(&V)': 'Show this position in PDF(&V)',
    '작업공간 청소(&C)…': 'Clean workspace(&C)…',
    '설정(&S)': 'Settings(&S)',
    '환경설정(&P)…': 'Preferences(&P)…',
    '테마 전환(&T)': 'Toggle theme(&T)',
    '글자 크게': 'Larger text',
    '글자 작게': 'Smaller text',
    '도움말(&H)': 'Help(&H)',
    'ndhmdWriter 정보 / 단축키(&H)': 'About ndhmdWriter / Shortcuts(&H)',
    '사양서(&S)': 'Specification(&S)',
    '치트시트(&C)': 'Cheat sheet(&C)',
    '작업공간 폴더 선택': 'Select workspace folder',
    '작업공간: {}  (원고 {}개)': 'Workspace: {0}  ({1} manuscripts)',
    '{} → 작업공간 최상위': '{0} → workspace top level',
    '한 개 파일로 내보내기': 'Export as a single file',
    '마크다운 (*.md)': 'Markdown (*.md)',
    '내보냈습니다: ': 'Exported: ',
    '장별 파일로 내보낼 폴더': 'Folder for per-chapter files',
    '{} 에 {}개 파일을 내보냈습니다:\n': 'Exported {1} files to {0}:\n',
    '원고 {}개': '{0} manuscripts',
    '저장하지 않은 편집 {}개': '{0} unsaved edits',
    '작업공간': 'Workspace',
    '작업공간이 필요합니다': 'A workspace is required',
    '열기·저장·찾기는 작업공간 안에서만 이루어집니다.\n먼저 작업공간 폴더를 지정해 주세요.': 'Opening, saving and searching work only inside a workspace.\nPlease specify a workspace folder first.',
    '작업공간 밖입니다': 'Outside the workspace',
    '원고는 작업공간 안에만 둘 수 있습니다.\n\n작업공간: {}\n선택한 경로: {}': 'Manuscripts can be placed only inside the workspace.\n\nWorkspace: {0}\nSelected path: {1}',
    '새 원고': 'New manuscript',
    '파일 이름:': 'File name:',
    '들여오기': 'Import',
    '원고 ({})': 'Manuscripts ({0})',
    '{} 을(를) 작업공간으로 들여왔습니다.': 'Imported {0} into the workspace.',
    '저장하지 않은 원고': 'Unsaved manuscript',
    '지금 쓰신 내용에 아직 이름이 없습니다. 다른 파일을 열기 전에 저장할까요?': 'What you are writing has no name yet. Save it before opening another file?',
    '{} — .nmd (스타일·템플릿 원고)': '{0} — .nmd (style/template manuscript)',
    '파일을 찾지 못했습니다: {}': 'File not found: {0}',
    '책 최상위로 인식한 파일: {}': "File recognized as the book's top level: {0}",
    '시도한 경로:': 'Paths tried:',
    '그림 · ': 'Figure · ',
    '미리보기를 지원하지 않는 형식입니다 ({}).': 'This format cannot be previewed ({0}).',
    '원격 그림입니다. 아직 내려받지 않았습니다.\n{}\n\n눌러서 받으면 {}/ 에 저장되고, 다음부터는 네트워크 없이 이 파일을 씁니다.': 'This is a remote image and has not been downloaded yet.\n{0}\n\nClick to download it to {1}/; from then on this file is used without the network.',
    '표   (근사 미리보기 — 실제 조판은 컴파일해야 보입니다)': 'Table   (approximate preview — the real typesetting appears only after compiling)',
    '수식': 'Formula',
    '조판하는 중…': 'Typesetting…',
    '붙이기 — 원래 자리로': 'Dock — back to its original place',
    '[{}{}] 삽입': 'Insert [{0}{1}]',
    "라벨 '{}' 의 정의를 찾지 못했습니다.": "Could not find the definition of label '{0}'.",
    '참조': 'Reference',
    '더 돌아갈 위치가 없습니다': 'No earlier position',
    '더 나아갈 위치가 없습니다': 'No later position',
    ' 사본': ' copy',
    '{} 사본 {}{}': '{0} copy {1}{2}',
    '이름 변경': 'Rename',
    '새 이름:': 'New name:',
    '\n하위 장 {}개는 최상위로 남습니다.': '\n{0} sub-chapters will remain at the top level.',
    '{} 을(를) 삭제하시겠습니까?{}\n되돌릴 수 없습니다.': 'Delete {0}?{1}\nThis cannot be undone.',
    '{} 을(를) {}개 하위 파일로 잘랐습니다 ({} … {}).': 'Split {0} into {1} sub-files ({2} … {3}).',
    '{} 에 포함된 하위 파일 {}개의 내용을 이 문서에 그대로 넣고, 그 파일들을 삭제합니다.\n\n': 'The contents of the {1} sub-files included in {0} will be put into this document as they are, and those files will be deleted.\n\n',
    '\n\n하위 파일 안의 {{포함}} 줄 {}개는 그대로 남아, 그 파일들이 이 문서의 하위 파일이 됩니다.': '\n\n{0} {{include}} lines inside the sub-files remain as they are, and those files become sub-files of this document.',
    '하위 파일 {}개를 합쳤습니다.': 'Merged {0} sub-files.',
    '{} 검사 중…': 'Checking {0}…',
    'ndhmd4tex 를 찾지 못했습니다': 'ndhmd4tex not found',
    'PATH 에 ndhmd4tex 가 없습니다. 위치를 지정해 주세요.': 'ndhmd4tex is not on PATH. Please specify its location.',
    'ndhmd4tex 위치': 'ndhmd4tex location',
    'ndhmd4tex (ndhmd4tex ndhmd4tex.py);;모든 파일 (*)': 'ndhmd4tex (ndhmd4tex ndhmd4tex.py);;All files (*)',
    '실행 실패': 'Failed to run',
    'ndhmd4tex 를 실행하지 못했습니다.\n컴파일 ▸ 마크업 점검를 다시 눌러 위치를 지정할 수 있습니다.': 'Could not run ndhmd4tex.\nChoose Compile ▸ Markup check again to specify its location.',
    '마크업 점검 — {}   오류 {} · 경고 {}   (누르면 그 줄로 갑니다)': 'Markup check — {0}   Errors {1} · Warnings {2}   (click to jump to that line)',
    'tblrDoumi 로 보냈습니다 — 거기서 LaTeX 를 복사해 이 창에 붙여넣으세요. ({})': 'Sent to tblrDoumi — copy the LaTeX there and paste it into this window. ({0})',
    'tblrDoumi를 정해진 자리에서 찾지 못했습니다. 실행 파일을 직접 지정할까요?': 'tblrDoumi was not found at its standard locations. Specify the executable manually?',
    'tblrDoumi 실행 파일 선택': 'Select the tblrDoumi executable',
    '{} 메타데이터 덤프 중…': 'Dumping metadata of {0}…',
    '프론트매터 덤프 완료': 'Front matter dump finished',
    '{} 변환 중…': 'Converting {0}…',
    'ndhmd4tex 를 실행하지 못했습니다.': 'Could not run ndhmd4tex.',
    '{} 컴파일 중… ({})': 'Compiling {0}… ({1})',
    '   ·   ⚠ {} 생김': '   ·   ⚠ {0} appeared',
    '   ·   ⚠ 서랍 ▸ 컴파일 참고: ': '   ·   ⚠ Drawer ▸ Compile notes: ',
    '{} 를 실행하지 못했습니다.': 'Could not run {0}.',
    '열었습니다 — {}': 'Opened — {0}',
    '작업공간 청소': 'Clean workspace',
    '{}개 원고의 .tex 와 그 산출물(pdf, log, aux 등)을 모두 지웁니다.\nmd 원고는 건드리지 않습니다. 되돌릴 수 없습니다.\n계속할까요?': 'This deletes the .tex files of {0} manuscripts and all their outputs (pdf, log, aux, etc.).\nMd manuscripts are not touched. This cannot be undone.\nContinue?',
    '작업공간 청소 완료 — 원고 ': 'Workspace cleaned — manuscripts: ',
    '개, 파일 ': ', files: ',
    '개 삭제': ' deleted',
    'PDF 파일이 없습니다': 'No PDF file',
    '동기화 정보를 찾을 수 없습니다': 'Sync information not found',
    '등록됨 — {}': 'Registered — {0}',
    '{}개 바꿈': '{0} replaced',
    '작업공간 전체 바꾸기': 'Replace in whole workspace',
    '파일 {}개에서 {}곳을 바꿉니다.\n실행 취소가 되지 않습니다. 진행할까요?': 'This replaces {1} occurrences in {0} files.\nIt cannot be undone. Proceed?',
    '{}곳 바꿈 (파일 {}개)': '{0} replaced ({1} files)',
    '환경으로 감싸기': 'Wrap in environment',
    '환경 이름:': 'Environment name:',
    '올렸습니다': 'raised',
    '내렸습니다': 'lowered',
    '표제 ': 'Headings: ',
    '개를 ': ' ',
    ' (한계에 닿아 그대로 둔 것 {}개)': ' ({0} left unchanged at the limit)',
    '여는 중…': 'Opening…',
    '문서를 열었습니다': 'Document opened',
    '한자 사전을 처음 만드는 중입니다… 잠시만요.': 'Building the hanja dictionary for the first time… one moment.',
    '한자 사전을 만들었습니다.': 'Hanja dictionary built.',
    'AI 도우미 (실험)': 'AI assistant (experimental)',
    '설정…': 'Settings…',
    "'{}'  U+{}  ({})": "'{0}'  U+{1}  ({2})",
    '병합된 셀이 있는 grid 표는 편집기에서 다룰 수 없습니다': 'Grid tables with merged cells cannot be handled in the editor',
    '한 셀에 문단이 여럿인 grid 표는 편집기에서 다룰 수 없습니다': 'Grid tables with several paragraphs in one cell cannot be handled in the editor',
    '간단 표 편집기에서 편집…': 'Edit in simple table editor…',
    '환경으로 감싸기…': 'Wrap in environment…',
    '한자 변환': 'Hanja conversion',
    '찾아보기…': 'Look up…',
    'Google에서 찾기': 'Search on Google',
    '위키백과에서 찾기': 'Search on Wikipedia',
    '사전에서 찾기': 'Look up in dictionary',
    '사전 설정…': 'Dictionary settings…',
    '이 위치로 PDF 열기': 'Open PDF at this position',
    '현재 파일': 'Current file',
    '선택 범위': 'Selection',
    '(이력 없음)': '(no history)',
    '이력 지우기': 'Clear history',
    '자기 자신에는 넣을 수 없습니다.': 'Cannot be inserted into itself.',
    '작업공간 밖의 파일입니다.': 'This file is outside the workspace.',
    '{} 이(가) 이미 다른 원고를 포함하고 있습니다.\n포함은 2단계까지만 지원됩니다.': '{0} already includes another manuscript.\nIncludes are supported only up to two levels.',
    '{{이름}} 은 최상위 파일과 같은 폴더에서 찾습니다.\n같은 폴더 안에서만 묶을 수 있습니다.': '{{name}} is looked up in the same folder as the top-level file.\nFiles can be grouped only within the same folder.',
    '구조': 'Structure',
    '하위 파일 합치기…': 'Merge sub-files…',
    '삭제(&X)…': 'Delete(&X)…',
    '책 전체': 'Whole book',
    'PyYAML이 설치되어 있지 않습니다 — pip install pyyaml': 'PyYAML is not installed — pip install pyyaml',
    ': 프론트매터가 목록/사전 형태가 아닙니다.': ': the front matter is not a list/dictionary.',
    '기본 + kotex': 'Default + kotex',
    '기본만': 'Default only',
    '렌더 도구를 찾지 못했습니다 — dvisvgm, pdftocairo, pdftoppm 중 하나가 필요합니다.': 'No rendering tool found — one of dvisvgm, pdftocairo or pdftoppm is required.',
    '{} 변환에 실패했습니다.': 'Conversion of {0} failed.',
    '그릴 수 없는 파일입니다.': 'This file cannot be drawn.',
    '{}        ✕ 닫기': '{0}        ✕ Close',
    '머무는 시간': 'Dwell time',
    '설정 파일을 읽는 중 오류가 있습니다.': 'There was an error reading the settings file.',
    '설정됨: ': 'Set: ',
    '개 — ': ' items — ',
    ' 쪽': ' pages',
    'pmime_core.py 를 찾지 못했습니다 — ndhmdWriter.py 와 같은 폴더에 두세요.': 'pmime_core.py not found — put it in the same folder as ndhmdWriter.py.',
    '입력을 되살렸습니다': 'Input restored',
    '단어 삭제': 'Delete entry',
    '{}   {}\n\n이 단어를 사전에서 지울까요?': '{0}   {1}\n\nRemove this entry from the dictionary?',
    '코드포인트:': 'Code point:',
    '특수': 'Special',
    '{}  (U+{})': '{0}  (U+{1})',
    '{}  (우클릭: 삭제)': '{0}  (right-click: delete)',
    '그림을 내려받지 못했습니다: {}\n{}: {}': 'Could not download the image: {0}\n{1}: {2}',
    '캐시에 쓰지 못했습니다: {}\n{}': 'Could not write to the cache: {0}\n{1}',
    '\n아래 "시스템 프로그램으로 열기"를 눌러 보세요.': '\nTry "Open with system program" below.',
    '작업공간에서 파일을 먼저 열어 주세요.': 'Please open a file in the workspace first.',
    '이미 작업공간 안에 있는 파일입니다.': 'This file is already inside the workspace.',
    "'{}' 폴더에 이미 '{}' 이(가) 있습니다.\n다른 이름으로 들여올 이름:": "The folder '{0}' already contains '{1}'.\nName to import it under:",
    'graphicspath: 에 지정된 폴더를 훑습니다.': 'Scans the folders specified in graphicspath:.',
    'graphicspath: 가 없어 작업공간 전체를 훑습니다.': 'There is no graphicspath:, so the whole workspace is scanned.',
    '크기: {} KB': 'Size: {0} KB',
    'PDF 그림 — 해상도 정보 없음': 'PDF figure — no resolution info',
    ' — 조각 그림 도구가 만든 파일. 도구에서 편집·재생성한다.': ' — a file made by the snippet-figure tool. Edit and regenerate it in the tool.',
    '알 수 없는 엔진: {}': 'Unknown engine: {0}',
    '알 수 없는 문서 클래스: {}': 'Unknown document class: {0}',
    '{} 을(를) 찾지 못했습니다.': 'Could not find {0}.',
    '그림이 비어 있습니다(찍힌 것이 없는 쪽뿐입니다).': 'The figure is empty (only blank pages resulted).',
    '재생성': 'Regenerate',
    '저장하고 삽입': 'Save and insert',
    '이름:': 'Name:',
    '클래스:': 'Class:',
    '엔진:': 'Engine:',
    '프리앰블 (패키지·색 정의 등)': 'Preamble (packages, color definitions, etc.)',
    '조각 그림 만들기': 'Create snippet figure',
    '{} 을(를) 읽지 못했습니다.': 'Could not read {0}.',
    '저장 폴더: {}': 'Save folder: {0}',
    '그림 코드를 적어 주세요.': 'Please enter the figure code.',
    '컴파일 실패: {}': 'Compile failed: {0}',
    '컴파일했습니다.': 'Compiled.',
    '컴파일했습니다 — {}쪽, 쪽마다 따로 저장됩니다.': 'Compiled — {0} pages, each saved separately.',
    '미리보기를 그릴 수 없습니다(PDF 는 만들어졌습니다).': 'The preview could not be drawn (the PDF was created).',
    '조각 그림': 'Snippet figure',
    '파일 이름에는 글자·숫자·점·밑줄·붙임표만 쓸 수 있습니다.': 'File names may contain only letters, digits, dots, underscores and hyphens.',
    ' 쪽 수가 바뀌어 파일이 {} 이(가) 되었습니다(지운 것: {}) — 원고의 그림 줄을 확인하세요.': ' The page count changed, so the files are now {0} (deleted: {1}) — check the figure lines in the manuscript.',
    ' 원고 쪽 미리보기는 파일을 다시 열거나 F5 로 새로 고치세요.': ' To refresh the preview on the manuscript side, reopen the file or press F5.',
    '조각 그림 {} 을(를) 재생성했습니다.': 'Regenerated snippet figure {0}.',
    'CMYK 값 복사': 'Copy CMYK value',
    'HSB 값 복사': 'Copy HSB value',
    '삽입 대상: ': 'Insert into: ',
    '행렬/환경 (탭으로 칸 이동)': 'Matrix / environment (Tab moves between cells)',
    '여러 줄 수식 환경': 'Multi-line equation environment',
    ' (소스 {}번째 줄 근처)': ' (near source line {0})',
    'TeX 오류: {}{}': 'TeX error: {0}{1}',
    '오류: {}{}': 'Error: {0}{1}',
    '미리보기 갱신': 'Refresh preview',
    '그림을 그릴 수 없습니다(QtPdf 또는 pdftoppm 이 필요합니다).': 'Cannot draw the image (QtPdf or pdftoppm is required).',
    '격자 편집 — ': 'Grid edit — ',
    '행 삭제': 'Delete row',
    '열 추가': 'Add column',
    '열 삭제': 'Delete column',
    '. 소스의 % 주석도 그대로 보존됩니다.': '. % comments in the source are preserved as they are.',
    '\nTab/Shift+Tab 칸 이동 · Ctrl+Enter 아래에 행 추가 · Ctrl+Tab 오른쪽에 열 추가': '\nTab/Shift+Tab move between cells · Ctrl+Enter add row below · Ctrl+Tab add column to the right',
    '글자로 표시합니다 (xelatex 또는 QtPdf 없음)': 'Shown as text (xelatex or QtPdf not available)',
    '글자로 표시합니다 (일람표 쪽 수가 맞지 않음)': 'Shown as text (symbol table page count mismatch)',
    '기호 ': 'Symbols: ',
    '자동 판별': 'Auto-detect',
    '인라인  $…$': 'Inline  $…$',
    '디스플레이  \\[…\\]': 'Display  \\[…\\]',
    '환경 그대로': 'Environment as is',
    '원고 프리앰블': 'Manuscript preamble',
    '모양:': 'Style:',
    '확대:': 'Zoom:',
    'Ctrl+Enter 본문에 넣기 · Esc 취소': 'Ctrl+Enter insert into text · Esc cancel',
    '수식(&M)': 'Math(&M)',
    '본문에 넣기 (Ctrl+Enter)': 'Insert into text (Ctrl+Enter)',
    '취소 (Esc)': 'Cancel (Esc)',
    '열기…': 'Open…',
    '저장': 'Save',
    '다른 이름으로 저장…': 'Save as…',
    '클립보드에서 불러오기': 'Load from clipboard',
    '종료': 'Quit',
    '소스 그대로': 'Source as is',
    '$ … $ 로 감싸서': 'Wrapped in $ … $',
    '\\[ … \\] 로 감싸서': 'Wrapped in \\[ … \\]',
    '   ⚠ 짝이 안 맞는 괄호 ': '   ⚠ Unmatched brackets: ',
    '커서가 행렬·cases·align 류 환경 안에 있어야 합니다': 'The cursor must be inside a matrix, cases or align-type environment',
    '비어 있는 수식은 넣을 수 없습니다': 'An empty formula cannot be inserted',
    '기호(클릭=삽입)': 'Symbol (click = insert)',
    '명령어(클릭=삽입)': 'Command (click = insert)',
    '카테고리': 'Category',
    '메모 — {}': 'Memo — {0}',
    '메모': 'Memo',
    '작업공간에 .bib 파일이 없습니다.': 'There is no .bib file in the workspace.',
    '\n저자: {}': '\nAuthor: {0}',
    '\n제목: {}': '\nTitle: {0}',
    '{}에서 문헌 {}개 중 {}개 표시': 'Showing {2} of {1} references in {0}',
    '{}에서 문헌 {}개': '{1} references in {0}',
    '참고문헌 편집 — {}': 'Edit bibliography — {0}',
    '중복된 citekey': 'Duplicate citekey',
    '책에서 [프리픽스라벨]·[@키] 형태의 참조를 찾지 못했습니다.': 'No references of the form [prefixlabel] or [@key] were found in the book.',
    "라벨 '{}' 은 선언된 곳이 없습니다(죽은 참조).": "Label '{0}' is not declared anywhere (dead reference).",
    '이 .bib 를 선언한 줄(\\addbibresource·\\bibliography)이 원고에 없습니다.': 'The manuscript has no line declaring this .bib (\\addbibresource or \\bibliography).',
    "'{}' 의 참조는 이 하나뿐입니다.": "This is the only reference to '{0}'.",
    '문헌 항목으로 가기': 'Go to reference entry',
    '.bib 선언 줄로 가기': 'Go to .bib declaration line',
    '인용 키 복사': 'Copy citation key',
    '원격 그림 없음': 'No remote images',
    '변환 필요한 그림 없음': 'No images need conversion',
    '받는 중… ({}/{})': 'Downloading… ({0}/{1})',
    '일부 변환 실패': 'Some conversions failed',
    '작업공간 열기': 'Open workspace',
    '저장 / 다른 이름으로 저장': 'Save / Save as',
    '이 파일 다시 읽기 / 서랍 다시 읽기': 'Reload this file / Reload drawer',
    '실행 취소 / 다시 실행': 'Undo / Redo',
    '찾기 / 바꾸기': 'Find / Replace',
    'Ctrl+F / Ctrl+H (macOS는 메뉴로만)': 'Ctrl+F / Ctrl+H (macOS: menu only)',
    '작업공간에서 찾기': 'Find in workspace',
    '목록 · 코드펜스 · 인용문 · 환경으로 감싸기 / 풀기': 'Wrap / unwrap as list, code fence, blockquote, environment',
    '선택한 줄 통째로 들여쓰기 / 내어쓰기(리스트 안 가림)': 'Indent / outdent whole selected lines (regardless of lists)',
    '장/절 표제 수준 증가 / 감소(선택이 있으면 선택 범위, 없으면 현재 행)': 'Raise / lower heading level (selection if any, otherwise the current line)',
    '인터넷 주소 열기 — [글자](URL)·[글자][표지]·맨 주소(그림은 제외)': 'Open web address — [text](URL), [text][marker], bare URL (images excluded)',
    'Ctrl+클릭': 'Ctrl+click',
    '이전 위치로 / 다음 위치로': 'Back / Forward',
    '서랍 / 라벨 날개 / TOC / 미리보기': 'Drawer / Label flags / TOC / Preview',
    '프론트매터 접기': 'Fold front matter',
    '코드 펜스·`:::{환경}` 접기/펴기(커서 위치)': 'Fold/unfold code fence or `:::{env}` (at cursor)',
    '전체화면': 'Full screen',
    '보조 입력(라틴 확장·문장부호·IPA)': 'Helper input (Latin extended, punctuation, IPA)',
    '수식 기호(lshort 기호 모음)': 'Math symbols (lshort symbol collection)',
    '수식 편집기(커서가 수식 위면 고치고, 아니면 새로 넣는다)': 'Math editor (edits the formula under the cursor, otherwise inserts a new one)',
    '색상 팔레트(xcolor 기본·SVG·Nine Colors)': 'Color palette (xcolor basic, SVG, Nine Colors)',
    '메모(문서에 딸린 것 — 서랍의 📝 를 눌러도 열린다)': 'Memo (attached to the document — also opens via 📝 in the drawer)',
    '약어 슬롯 편집 / 슬롯 입력(1~5 전역, 6~0 현재 책)': 'Edit abbreviation slots / insert a slot (1–5 global, 6–0 current book)',
    'Ctrl+Alt+Y / Alt+1~0 (맥: Control+1~0)': 'Ctrl+Alt+Y / Alt+1–0 (Mac: Control+1–0)',
    '카드 보기(원고별 시놉시스 카드)': 'Card view (per-manuscript synopsis cards)',
    '모든 카드 보기(작업공간 전체)': 'All cards view (whole workspace)',
    '참조 ↔ 정의로 가기 (각주·[#라벨]·[@키]·그림 이름; Ctrl+클릭도 같다) / 같은 키의 다음 참조': 'Go to reference ↔ definition (footnotes, [#label], [@key], image names; Ctrl+click works too) / next reference with the same key',
    '주변 창 모두 닫기 (메인 창은 닫히지 않는다)': 'Close all side panels (the main window stays open)',
    '조각 그림 만들기 / 커서 줄의 조각 그림 편집': 'Create snippet figure / edit the snippet figure on the cursor line',
    '참고문헌 편집(버튼 클릭도 가능)': 'Edit bibliography (the button works too)',
    '마크업 점검': 'Markup check',
    '상호참조 점검(죽은 \\ref 찾기)': 'Cross-reference check (find dead \\ref)',
    '책 컴파일 / 이 파일만 컴파일': 'Compile book / Compile this file only',
    '변환후 tex 열기 / 결과 tex 열기': 'Convert and open tex / Open result tex',
    'PDF에서 이 위치 보기': 'Show this position in PDF',
    '(메뉴에서)': '(from the menu)',
    '환경설정': 'Preferences',
    '테마 전환': 'Toggle theme',
    'ndhmdWriter 정보 / 단축키': 'About ndhmdWriter / Shortcuts',
    'ndhmarkdown 사양서 / 치트시트': 'ndhmarkdown specification / cheat sheet',
    'ndhmd4tex 를 실행하지 못했습니다: {}': 'Could not run ndhmd4tex: {0}',
    '첫 번째 행은 열의 정렬(l, c, r)을 지정합니다. 두 번째 행부터 제목과 내용을 입력하세요.': 'The first row sets column alignment (l, c, r). Enter headings and contents from the second row.',
    '정렬': 'Alignment',
    '열 {}': 'Column {0}',
    '행 {}개': '{0} rows',
    '열 {}개': '{0} columns',
    '{}행 × {}열을 붙였습니다.': 'Pasted {0} rows × {1} columns.',
    '클립보드에 붙일 표 데이터가 없습니다.': 'There is no table data on the clipboard to paste.',
    'X(비례 너비) 정렬은 마크다운 표로 표현할 수 없어 LaTeX tabularx로 대신 냈습니다.': 'X (proportional width) alignment cannot be expressed as a Markdown table, so LaTeX tabularx was output instead.',
    '선택된 내용이 없습니다.': 'Nothing is selected.',
    '{} 을(를) 최상위 제목({})마다 잘라 {{포함}} 줄로 바꿉니다 — 한 단계만.': 'Splits {0} at each top-level heading ({1}) and replaces them with {{include}} lines — one level only.',
    ' · 포함 {}개 딸려 감': ' · {0} includes go along',
    '{}  ←  {}  ({}줄{})': '{0}  ←  {1}  ({2} lines{3})',
    '접두어에 쓸 수 없는 글자가 있거나 비어 있습니다.': 'The prefix is empty or contains characters that are not allowed.',
    '지금 파일: ': 'Current file: ',
    '{filename} 또는 %f → 파일 이름(확장자 제외)으로 바뀝니다. ': '{filename} or %f → replaced by the file name (without extension). ',
    '(이미 실행 중인 명령이 끝나기를 기다리는 중)\n': '(waiting for the command already running to finish)\n',
    '[종료 코드 ': '[exit code ',
    '오류 위치로': 'Go to error',
    '오류 위치로 ({}/{})': 'Go to error ({0}/{1})',
    'tex {}행 → {}:{}\n{}': 'tex line {0} → {1}:{2}\n{3}',
    '행 → ': ' line → ',
    '끌어서 순서를 바꾸거나, 서랍으로 끌어 책에서 뺀다': 'Drag to reorder, or drag to the drawer to remove from the book',
    '자': ' chars',
    '시놉시스 — 이 원고를 한두 줄로': 'Synopsis — this manuscript in a line or two',
    '원고를 연 뒤에 카드를 볼 수 있습니다.': 'Cards can be viewed after opening a manuscript.',
    '책에서 빼기(&X)': 'Remove from book(&X)',
    '파일은 지우지 않고 책의 {{}} 줄에서만 뺀다': "Does not delete the file; only removes it from the book's {{}} line",
    '취소했습니다.': 'Cancelled.',
    '실행하지 못했습니다. 경로와 설치를 확인하세요.': 'Could not run. Check the path and installation.',
    '시간이 너무 오래 걸려 중단했습니다.': 'Stopped because it took too long.',
    'AI 도우미(실험) — ': 'AI assistant (experimental) — ',
    '원문': 'Original',
    '결과 (고칠 수 있습니다)': 'Result (editable)',
    '{} 실행 파일을 찾지 못했습니다. 도구 ▶ AI 도우미 설정에서 경로를 지정하세요.': 'Could not find the {0} executable. Specify the path in Tools ▶ AI assistant settings.',
    ' · 선택 ': ' · selected ',
    "원문이 바뀌었거나 다른 파일로 옮겨 교체하지 않았습니다. '선택 범위 아래에 삽입'이나 복사를 쓰세요.": "The original text changed or you moved to another file, so nothing was replaced. Use 'Insert below the selection' or copy.",
    '다른 파일로 옮겨 삽입하지 않았습니다. 복사를 쓰세요.': 'You moved to another file, so nothing was inserted. Use copy.',
    '주소의 {q} 자리에 선택한 글이 들어갑니다. 예: https://ko.dict.naver.com/#/search?query={q}': 'The selected text is put in place of {q} in the address. Example: https://ko.dict.naver.com/#/search?query={q}',
    '주소': 'Address',
    '위로': 'Up',
    '아래로': 'Down',
    '기본값으로': 'Reset to defaults',
    '비워 두면 PATH 와 흔한 설치 위치에서 찾습니다': 'If left empty, PATH and common install locations are searched',
    '{} 경로': '{0} path',
    '{} 인자': '{0} arguments',
    '기본 목록으로': 'Reset list',
    '지시문 목록 (편집창 우클릭 ▶ AI 도우미에 나타납니다)': 'Instruction list (shown under right-click ▶ AI assistant in the editor)',
    '새 지시문': 'New instruction',
    '기본 목록': 'Default list',
    '지시문 목록을 기본값으로 되돌립니다. 지금 목록은 사라집니다.': 'Resets the instruction list to the defaults. The current list will be lost.',
    '전역': 'Global',
    '이 책': 'This book',
    '{}  ({})': '{0}  ({1})',
    '저장하지 못한 슬롯: {}': 'Slots that could not be saved: {0}',
    '끄기(곧은 따옴표 " \')': 'Off (straight quotes " \')',
    '유니코드 따옴표(“” ‘’)': 'Unicode quotes (“” ‘’)',
    'CJK 낫표(『』 「」)': 'CJK corner brackets (『』 「」)',
    '프랑스식 기메(«» ‹›)': 'French guillemets («» ‹›)',
    '작업공간 전환': 'Switch workspace',
    '작업공간: ': 'Workspace: ',
    '  (원고 ': '  (manuscripts: ',
    '개)': ')',
    '(최근 연 작업공간 없음)': '(no recent workspaces)',
    '{} (없음)': '{0} (none)',
    '작업공간으로 이동': 'Move to workspace',
    "작업공간에 이미 '{}' 이(가) 있습니다. 덮어쓸까요?": "The workspace already contains '{0}'. Overwrite?",
    ' → 작업공간 최상위': ' → workspace top level',
    '자료 창고로 이동': 'Move to archive',
    "자료 창고에 이미 '{}' 이(가) 있습니다. 덮어쓸까요?": "The archive already contains '{0}'. Overwrite?",
    '먼저 원고를 열어 주세요.': 'Please open a manuscript first.',
    '\n\n못 찾았거나 순환 포함이라 그대로 남은 것: ': '\n\nLeft as is because not found or circular include: ',
    '정리함 — 죽은 캐시 {}개, 죽은 태그 {}개, 죽은 메모 {}개': 'Cleaned up — {0} dead caches, {1} dead tags, {2} dead memos',
    '새 원고.md': 'new-manuscript.md',
    '이미 있습니다': 'Already exists',
    '{} 이(가) 이미 있습니다.': '{0} already exists.',
    "작업공간에 이미 '{}' 이(가) 있습니다.\n다른 이름으로 들여올 이름:": "The workspace already contains '{0}'.\nName to import it under:",
    '{} 전에, 아직 이름이 없는 지금 편집 내용을 저장할까요?': 'Before {0}, save the current unnamed content?',
    '{} 전에 다음 원고를 저장할까요?\n\n{}\n\n': 'Before {0}, save the following manuscripts?\n\n{1}\n\n',
    '일부 저장 실패': 'Some saves failed',
    '⚠ 2단계 포함': '⚠ Two-level include',
    '{}장': '{0} chapters',
    '없는 포함 {}': 'Missing include {0}',
    '일부 항목을 옮기지 못했습니다': 'Some items could not be moved',
    '저장 후 진행': 'Save and proceed',
    '{} 에 저장하지 않은 변경이 있습니다.\n구조를 바꾸려면 먼저 저장해야 합니다. 저장할까요?': '{0} has unsaved changes.\nYou must save before changing the structure. Save now?',
    '쓰기 실패': 'Write failed',
    '{} 을(를) 고치지 못했습니다.': 'Could not modify {0}.',
    '커서를 수식·그림·표(파이프·grid) 위에 두면 여기에 나옵니다.': 'Place the cursor on a formula, image or table (pipe or grid) and it appears here.',
    '파일을 찾지 못했습니다: ': 'File not found: ',
    '책 최상위로 인식한 파일: ': "File recognized as the book's top level: ",
    '프론트매터 해석 오류 — {}': 'Front matter parse error — {0}',
    '{}   (캐시됨 · {})': '{0}   (cached · {1})',
    '그림 · {}   (방금 받음)': 'Figure · {0}   (just downloaded)',
    '{} 을(를) 그리지 못했습니다.': 'Could not draw {0}.',
    '표': 'Table',
    '표를 읽을 수 없습니다.': 'The table could not be read.',
    '수식   ({})   ·   Ctrl+M 으로 편집': 'Formula   ({0})   ·   edit with Ctrl+M',
    '수식 — 조판 실패': 'Formula — typesetting failed',
    '주변 창 {}개를 닫았습니다.': 'Closed {0} side panels.',
    '닫을 주변 창이 없습니다.': 'There are no side panels to close.',
    '참조점 {}개 · 더블클릭 → [#라벨] 삽입 · 우클릭 → 형식': '{0} reference points · double-click → insert [#label] · right-click → format',
    '참조점이 없습니다': 'No reference points',
    '{} [{}] 의 정의를 찾지 못했습니다.': 'Could not find the definition of {0} [{1}].',
    '{} [{}] 의 정의가 {}곳입니다(첫 곳으로 이동).': '{0} [{1}] is defined in {2} places (jumping to the first).',
    '이름 변경 실패': 'Rename failed',
    '하위 장은 복제되지 않았습니다 — 원본과 자식을 나눠 가지면 구조가 애매해지기 때문입니다.': 'Sub-chapters were not duplicated — sharing children between the original and the copy would make the structure ambiguous.',
    '작업공간 최상위의 원고만 자를 수 있습니다.': 'Only manuscripts at the top level of the workspace can be split.',
    '{} 은(는) 이미 2단계(하위 파일)라 더 자를 수 없습니다.\n포함은 2단계까지만 지원됩니다.': '{0} is already at level 2 (a sub-file) and cannot be split further.\nIncludes are supported only up to two levels.',
    '가장 높은 수준의 제목이 하나뿐이라 그 수준으로는 자를 수 없습니다.\n한 단계 아래({}) 제목이 {}개 있습니다 — 그 수준으로 자를까요?\n(더 높은 제목과 그 앞의 글은 이 문서에 남습니다.)': 'There is only one top-level heading, so splitting at that level is not possible.\nThere are {1} headings one level below ({0}) — split at that level?\n(The higher heading and the text before it stay in this document.)',
    '{}수준({})으로 자르기': 'Split at level {0} ({1})',
    '하위 파일 합치기': 'Merge sub-files',
    '{} 은(는) 포함한 하위 파일이 없습니다.': '{0} has no included sub-files.',
    '\n\n다음은 합치면서 사라집니다(프론트매터 키·태그 주석):\n': '\n\nThe following will be lost in merging (front matter keys and tag comments):\n',
    '하위 파일을 지우지 못했습니다': 'Could not delete the sub-files',
    '표를 TSV로 복사했습니다 — tblrDoumi 에서 붙여넣으세요': 'Table copied as TSV — paste it in tblrDoumi',
    '실행하지 못했습니다.': 'Could not run.',
    '--animation={}': '--animation={0}',
    '{} 이(가) 생성되지 않았습니다.': '{0} was not created.',
    'latexmk 를 찾지 못했습니다': 'latexmk not found',
    'PATH 에 latexmk 가 없습니다. TeX Live/MiKTeX 설치를 확인하십시오.': 'latexmk is not on PATH. Check your TeX Live / MiKTeX installation.',
    'ksruncltex 를 찾지 못했습니다': 'ksruncltex not found',
    'texlua/kpsewhich 를 PATH 에서 찾지 못했거나 ksruncltex 이 설치돼 있지 않은 것 같습니다.': 'texlua/kpsewhich was not found on PATH, or ksruncltex does not appear to be installed.',
    '컴파일 참고 삭제': 'Delete compile notes',
    '{} 을(를) 삭제할까요? 다음 컴파일에서 필요하면 다시 만들어집니다.': 'Delete {0}? It will be recreated at the next compile if needed.',
    '   ·   하위 파일 낡은 산출물 {}개 정리': '   ·   {0} stale sub-file outputs cleaned',
    '컴파일 성공 — {}{}': 'Compile succeeded — {0}{1}',
    '정방향 검색이 되지 않아 PDF 만 열었습니다 (하위 원고만 컴파일했을 수 있습니다)': 'Forward search was not possible, so only the PDF was opened (you may have compiled only a sub-manuscript)',
    '변환후 tex 열기': 'Convert and open tex',
    '변환 실패': 'Conversion failed',
    '열기 실패': 'Failed to open',
    '시스템에 .tex 를 여는 기본 프로그램이 연결되어 있지 않은 것 같습니다.\n\n{}': 'No default program seems to be associated with .tex files on this system.\n\n{0}',
    '먼저 작업공간을 열어 주세요.': 'Please open a workspace first.',
    '컴파일이 진행 중입니다. 끝난 뒤 다시 시도해 주세요.': 'A compile is in progress. Please try again after it finishes.',
    '지울 산출물이 없습니다 — 원고(.md)에서 만들어진 .tex 가 없습니다.': 'Nothing to delete — there are no .tex files generated from manuscripts (.md).',
    '작업공간 청소 — 일부 실패': 'Clean workspace — some failed',
    '결과 tex': 'Result tex',
    '결과 tex 없음': 'No result tex',
    '{} 이(가) 아직 없습니다.\n원고를 컴파일하면 원고와 같은 폴더에 생깁니다.': '{0} does not exist yet.\nCompiling the manuscript creates it in the same folder as the manuscript.',
    'ndhmdsync 를 찾지 못했습니다': 'ndhmdsync not found',
    'PATH 에 ndhmdsync 가 없습니다. 설정에서 위치를 지정하십시오.': 'ndhmdsync is not on PATH. Specify its location in Settings.',
    'PDF 없음': 'No PDF',
    '아직 컴파일한 적이 없어 PDF가 없습니다. 지금 컴파일할까요?': 'There is no PDF because it has never been compiled. Compile now?',
    '등록됨 — ': 'Registered — ',
    '다음 위치만 확인합니다(포터블 설치는 지원하지 않습니다):\n  C:\\Program Files\\SumatraPDF\\SumatraPDF.exe\n  C:\\Program Files (x86)\\SumatraPDF\\SumatraPDF.exe\n  %LOCALAPPDATA%\\SumatraPDF\\SumatraPDF.exe\n  %LOCALAPPDATA%\\Programs\\SumatraPDF\\SumatraPDF.exe': 'Only the following locations are checked (portable installs are not supported):\n  C:\\Program Files\\SumatraPDF\\SumatraPDF.exe\n  C:\\Program Files (x86)\\SumatraPDF\\SumatraPDF.exe\n  %LOCALAPPDATA%\\SumatraPDF\\SumatraPDF.exe\n  %LOCALAPPDATA%\\Programs\\SumatraPDF\\SumatraPDF.exe',
    'PDF 뷰어를 찾지 못했습니다': 'PDF viewer not found',
    '저장하지 않은 편집이 있습니다. 저장하고 다시 읽을까요?\n버리면 지금 화면의 편집 내용은 사라지고 디스크의 것으로 돌아갑니다.': 'There are unsaved edits. Save and reload?\nIf you discard them, the edits on screen are lost and the version on disk is restored.',
    '마지막 원고를 찾지 못했습니다: {}': 'Could not find the last manuscript: {0}',
    '앱 종료': 'Quit app',
    '처음부터 다시 찾았습니다': 'Wrapped around to the start',
    '없음': 'None',
    '{}개 / 파일 {}개': '{0} / {1} files',
    '현재 원고에 저장하지 않은 변경이 있습니다.\n작업공간 전체 바꾸기는 디스크의 파일을 고치므로\n먼저 저장해야 합니다. 저장할까요?': 'The current manuscript has unsaved changes.\nReplacing in the whole workspace modifies files on disk,\nso you must save first. Save now?',
    '일부 실패': 'Some failed',
    '풀 수 있는 목록·펜스·환경이 없습니다': 'No list, fence or environment to unwrap',
    '장/절 표제 수준 증가': 'Raise heading level',
    '장/절 표제 수준 감소': 'Lower heading level',
    '--guide={}': '--guide={0}',
    'pm 입력기로 보낼 글을 선택하거나 단어 위에 커서를 두세요': 'Select text to send to the pm input, or place the cursor on a word',
    'pm 변환할 글을 선택하거나 단어 위에 커서를 두세요': 'Select text to convert with pm, or place the cursor on a word',
    'pmime_core.py 를 찾지 못했습니다': 'pmime_core.py not found',
    'pm 변환했습니다': 'Converted with pm',
    'hanja_core.py 를 찾지 못했습니다 — ndhmdWriter.py 와 같은 폴더에 두세요.': 'hanja_core.py not found — put it in the same folder as ndhmdWriter.py.',
    '한자 후보가 없습니다.': 'No hanja candidates.',
    '한자 사전을 만드는 중이라 지우지 않았습니다.': 'The hanja dictionary is being built, so it was not deleted.',
    '한자 사전 DB 를 지웠습니다 — 다음 F9 에서 다시 만듭니다.': 'Hanja dictionary DB deleted — it will be rebuilt at the next F9.',
    '지울 한자 사전 DB 가 없습니다.': 'There is no hanja dictionary DB to delete.',
    '한자 사전 hanja.txt 를 찾지 못했습니다 — ndhmdWriter.py 와 같은 폴더에 두세요.': 'Hanja dictionary hanja.txt not found — put it in the same folder as ndhmdWriter.py.',
    '한자 사전을 만들지 못했습니다: {}': 'Could not build the hanja dictionary: {0}',
    '커서가 조각 그림 줄 위에 있지 않습니다 (옆에 조각 그림 도구가 만든 .tex 가 있는 PDF 그림이어야 합니다).': 'The cursor is not on a snippet-figure line (it must be a PDF figure with a .tex made by the snippet-figure tool beside it).',
    '수식을 고쳤습니다': 'Formula updated',
    '수식을 넣었습니다': 'Formula inserted',
    '{}: 책(작업공간)을 연 뒤에 쓸 수 있는 슬롯입니다.': '{0}: this slot is available after opening a book (workspace).',
    '{} 슬롯이 비어 있습니다 — 도구 ▸ 약어 슬롯…에서 등록하세요.': 'Slot {0} is empty — register it under Tools ▸ Abbreviation slots….',
    '  [조언]': '  [Advice]',
    'ndhmd4tex 위치가 지정되지 않았습니다.': 'The ndhmd4tex location is not specified.',
    '안내': 'Notice',
    '더 복잡한 표는 전용 표 편집 프로그램을 이용하셔요': 'For more complex tables, please use a dedicated table-editing program',
    '커서가 닫힌 코드 펜스나 :::{환경} 안에 있지 않습니다.': 'The cursor is not inside a closed code fence or :::{env}.',
    '펜스·환경 {}개를 {}.': '{0} fences/environments {1}.',
    '바꿀 펜스·환경이 없습니다.': 'There are no fences or environments to change.',
    '이 원고에는 프론트매터가 없습니다': 'This manuscript has no front matter',
    '행 ': 'Row ',
    '열': 'Column',
    '{}째 줄에서 셀이 겹칩니다': 'Cells overlap at line {0}',
    '표의 {}째 줄 {}칸 `{}` 이(가) 어느 셀의 테두리와도 이어지지 않습니다 — 모서리 `+` 나 세로선 `|` 가 어긋났거나 줄이 모자란지 확인하십시오': 'In the table, line {0} column {1} `{2}` does not connect to any cell border — check whether a corner `+` or vertical bar `|` is misaligned or a line is missing',
    'tblrDoumi로 보내기 (병합·정렬 유지)': 'Send to tblrDoumi (keeps merges and alignment)',
    'grid 표를 TSV로 복사하고 tblrDoumi 열기': 'Copy grid table as TSV and open tblrDoumi',
    '조각 그림 편집…': 'Edit snippet figure…',
    '상호참조 점검… (이 참조로)': 'Cross-reference check… (at this reference)',
    '상호참조 점검…': 'Cross-reference check…',
    '포함은 2단계까지만 지원됩니다.\n{} 은(는) 이미 2단계(하위 파일)입니다.': 'Includes are supported only up to two levels.\n{0} is already at level 2 (a sub-file).',
    '제목': 'Title',
    '프레임': 'Frame',
    '그림': 'Image',
    '인라인': 'Inline',
    '렌더가 너무 오래 걸려 중단했습니다.': 'Stopped because rendering took too long.',
    '원고 프리앰블 (kotex 없이)': 'Manuscript preamble (without kotex)',
    '{}   (오류 {} · 경고 {})': '{0}   (Errors {1} · Warnings {2})',
    '변환 오류: {}': 'Conversion error: {0}',
    '저장하지 못했습니다: {}': 'Could not save: {0}',
    '읽지 못했습니다: {}': 'Could not read: {0}',
    '복사하지 못했습니다: {}': 'Could not copy: {0}',
    ' (그림 없음)': ' (no image)',
    '해상도: {} × {} px': 'Resolution: {0} × {1} px',
    '{}초 안에 끝나지 않아 중단했습니다.': 'Stopped because it did not finish within {0} seconds.',
    '{} 을(를) 실행하지 못했습니다: {}': 'Could not run {0}: {1}',
    '쪽을 자르지 못했습니다: {}': 'Could not crop the page: {0}',
    '{}쪽을 자르지 못했습니다: {}': 'Could not crop page {0}: {1}',
    'PDF 를 읽지 못했습니다': 'Could not read the PDF',
    'QtPdf 또는 pdftoppm 이 필요합니다': 'QtPdf or pdftoppm is required',
    '예기치 못한 오류: {}': 'Unexpected error: {0}',
    "'{}' 이(가) 이미 있습니다. 덮어쓸까요?": "'{0}' already exists. Overwrite?",
    '조각 그림 {} 을(를) 만들어 넣었습니다.': 'Created and inserted snippet figure {0}.',
    '조각 그림 {} 을(를) {}쪽으로 만들어 넣었습니다.': 'Created and inserted snippet figure {0} as {1} pages.',
    '이름 없음': 'Untitled',
    '복사됨: {}': 'Copied: {0}',
    '편집창': 'Editor',
    'xelatex 를 찾지 못했습니다.': 'xelatex not found.',
    '40초 안에 끝나지 않아 중단했습니다.': 'Stopped because it did not finish within 40 seconds.',
    ' (프리앰블 오류로 프리앰블 없이 그렸습니다)': ' (drawn without the preamble because of a preamble error)',
    'xelatex 없음': 'xelatex missing',
    '기호 일람표 닫기 (F4)': 'Close symbol table (F4)',
    '기호 일람표 열기 (F4)': 'Open symbol table (F4)',
    '수식 편집': 'Edit math',
    '고친 내용을 버리고 닫을까요?': 'Discard changes and close?',
    '메모 — ': 'Memo — ',
    '훑을 파일:': 'Files to scan:',
    '\n\n그래도 저장할까요?': '\n\nSave anyway?',
    '참조 {}개 중 죽은 것 {}개(붉은 글씨) — \\label이 없는 [프리픽스라벨]입니다.': '{1} of {0} references are dead (in red) — [prefixlabel] with no \\label.',
    '참조 {}개 — 전부 대응하는 라벨이 있습니다.': '{0} references — all have a matching label.',
    '인용 {}개 — 참고문헌 원본(:::{thebibliography}·.bib)을 찾지 못해 존재 여부는 확인하지 못했습니다.': '{0} citations — the bibliography source (:::{thebibliography} or .bib) was not found, so their existence could not be checked.',
    '────────  인용 (cite)  ────────': '────────  Citations (cite)  ────────',
    "인용 '{}' 의 문헌 항목을 찾을 수 없습니다.": "Could not find the reference entry for citation '{0}'.",
    "문헌 항목 '{}' — 참고문헌 블록입니다(접혀 있으면 📚 참고문헌 줄, Ctrl+Alt+G 로 편집).": "Reference entry '{0}' — it is in the bibliography block (the 📚 Bibliography line if folded; edit with Ctrl+Alt+G).",
    '✗ 찾지 못함   {}': '✗ Not found   {0}',
    '모두 받아 두었습니다': 'All downloaded',
    '받지 않은 원격 그림 모두 가져오기 ({}개)': 'Fetch all remote images not yet downloaded ({0})',
    'Pillow 없음 — pip install Pillow': 'Pillow missing — pip install Pillow',
    'webp/tiff/gif 를 png 로 바꾸려면 Pillow 가 필요합니다.\nndhmd4tex 컴파일도 같은 이유로 Pillow 를 요구합니다.': 'Pillow is required to convert webp/tiff/gif to png.\nndhmd4tex compilation requires Pillow for the same reason.',
    '변환 필요한 그림 모두 변환하기 ({}개)': 'Convert all images that need conversion ({0})',
    '✗ 실패   {}   — {}': '✗ Failed   {0}   — {1}',
    'ndhmd4tex 가 표를 변환하지 못했습니다.\n': 'ndhmd4tex could not convert the table.\n',
    '새 파일 {}개를 같은 폴더에 만들고, 이 문서에는 제목 앞의 글과 {{포함}} 줄만 남습니다.': '{0} new files will be created in the same folder; this document keeps only the text before the first heading and the {{include}} lines.',
    '카드 ': 'Card ',
    '책': 'Book',
    '{} — 모든 원고 {}개': '{0} — all {1} manuscripts',
    '{} — 원고 {}개': '{0} — {1} manuscripts',
    '{} — 단일 파일': '{0} — single file',
    '맨 앞으로(&F)': 'Bring to front(&F)',
    '앞으로 한 칸(&P)': 'Move forward(&P)',
    '뒤로 한 칸(&N)': 'Move backward(&N)',
    '맨 뒤로(&L)': 'Send to back(&L)',
    '완료. 결과를 확인하고 반영하세요.': 'Done. Check the result and apply it.',
    '실패: ': 'Failed: ',
    '이름이 비어 있습니다': 'The name is empty',
    '주소는 http:// 또는 https:// 로 시작해야 합니다': 'The address must start with http:// or https://',
    '주소에 {q} 가 없습니다': 'The address has no {q}',
    '{}번째 줄: {}.': 'Line {0}: {1}.',
    ' 경로': ' path',
    ' 인자': ' arguments',
    '찾음: {}': 'Found: {0}',
    '찾지 못했습니다(설치되어 있지 않거나 경로가 다릅니다).': 'Not found (not installed, or the path differs).',
    '인자': 'Arguments',
    '{} 인자에 {프롬프트} 가 있어야 합니다.': 'The {0} arguments must contain {프롬프트}.',
    '책(작업공간)을 연 뒤에 쓸 수 있습니다': 'Available after opening a book (workspace)',
    '저장하지 못한 슬롯: ': 'Slots that could not be saved: ',
    ' (없음)': ' (none)',
    '옮기지 못했습니다: {}': 'Could not move: {0}',
    '{} 을(를) 읽지 못했습니다: {}': 'Could not read {0}: {1}',
    '쓰지 못했습니다: {}': 'Could not write: {0}',
    '만들기 실패': 'Creation failed',
    '저장하지 않고 종료하면 그 편집은 사라집니다.': 'If you quit without saving, those edits will be lost.',
    '저장하지 않으면 그 편집은 앱을 여는 동안에는 남아 있지만,\n이 작업에는 반영되지 않습니다.': 'If you do not save, those edits stay while the app is open,\nbut are not reflected in this operation.',
    '{}컴파일 참고 ({})': '{0}Compile notes ({1})',
    '컴파일 참고 파일 — 클릭하면 내용을 훑어봅니다': 'Compile note files — click to preview their contents',
    '부속 파일 ({})': 'Auxiliary files ({0})',
    '자료 창고 ({})': 'Archive ({0})',
    '{}/ ({})': '{0}/ ({1})',
    '장': 'Chapter',
    '묶을 수 없습니다': 'Cannot be grouped',
    '{}:{}\n{}': '{0}:{1}\n{2}',
    '{} [{}] 의 참조를 찾지 못했습니다.': 'Could not find a reference to {0} [{1}].',
    '{} [{}] 참조 {}/{} (Ctrl+Alt+Shift+O: 다음 참조)': '{0} [{1}] reference {2}/{3} (Ctrl+Alt+Shift+O: next reference)',
    '복제 실패': 'Duplication failed',
    '삭제 실패': 'Deletion failed',
    '자를 곳이 없습니다 — 같은 수준의 제목이 둘 이상 있어야 합니다\n(코드 펜스·환경 안의 # 줄은 세지 않습니다).': 'Nowhere to split — there must be two or more headings at the same level\n(# lines inside code fences or environments are not counted).',
    '장별로 자르기 실패': 'Splitting by chapter failed',
    '{}\n만든 파일은 되돌렸습니다.': '{0}\nThe files created were rolled back.',
    '  · {}: {}': '  · {0}: {1}',
    '{}: 마크업 문제 없음': '{0}: no markup problems',
    '이 표는 읽을 수 없습니다.': 'This table cannot be read.',
    '셀을 LaTeX 로 바꾸지 못했습니다.\n\n{}': 'Could not convert the cells to LaTeX.\n\n{0}',
    'grid 표': 'Grid table',
    '표를 읽지 못했습니다: {}': 'Could not read the table: {0}',
    ' (병합 셀은 풀려서 왼쪽 위 칸에만 글이 있습니다)': ' (merged cells are unmerged, and only the top-left cell has the text)',
    'tblrDoumi 실행 중…': 'Launching tblrDoumi…',
    '프론트매터 덤프 결과 — {}': 'Front matter dump result — {0}',
    '변환 실패 — {}   오류 {} · 경고 {}': 'Conversion failed — {0}   Errors {1} · Warnings {2}',
    '삭제하지 못했습니다: {}': 'Could not delete: {0}',
    '컴파일 실패 — {}   오류 {}개   (누르면 그 줄로 갑니다)': 'Compile failed — {0}   Errors: {1}   (click to jump to that line)',
    '컴파일 실패 ({})': 'Compile failed ({0})',
    'PDF에서 열지 못했습니다': 'Could not open in PDF',
    '등록 실패': 'Registration failed',
    '{} 에 쓰지 못했습니다:\n{}': 'Could not write to {0}:\n{1}',
    '/Applications/Skim.app 위치만 확인합니다.': 'Only /Applications/Skim.app is checked.',
    'PATH 에서 okular 를 찾지 못했습니다.': 'okular was not found on PATH.',
    '저장 실패': 'Save failed',
    '정규식 오류': 'Regex error',
    '먼저 글을 선택하세요': 'Select some text first',
    '범위의 처음부터 다시 찾았습니다': 'Wrapped around to the start of the range',
    '범위의 끝부터 다시 찾았습니다': 'Wrapped around to the end of the range',
    '현재 행': 'Current line',
    '현재 원고': 'Current manuscript',
    '표제행이 아닙니다': 'Not a heading line',
    '표제행이 없습니다': 'No heading line',
    'pm 변환 오류: {}': 'pm conversion error: {0}',
    "'{}' — 데이터가 없습니다.": "'{0}' — no data.",
    '한 글자만 선택했을 때 코드포인트를 보여줄 수 있습니다': 'The code point can be shown only when a single character is selected',
    '커서 뒤에 글자가 없습니다': 'There is no character after the cursor',
    '참고문헌 병합': 'Merge bibliographies',
    '둘 이상의 참고문헌이 있습니다({}개). 병합할까요?': 'There are {0} bibliographies. Merge them?',
    '▸ {} · {}줄 접힘': '▸ {0} · {1} lines folded',
    '표를 선택해 주세요.': 'Please select a table.',
    '접기 풀기(펴기)': 'Unfold',
    '이 펜스·환경 접기': 'Fold this fence/environment',
    'pm 입력기로 보내기': 'Send to pm input',
    'pm 변환 (현재 설정으로 바로)': 'Convert with pm (current settings)',
    '{}  (하위 폴더 — 서랍 미지원)': '{0}  (sub-folder — not supported in the drawer)',
    '이름 변경(&R)…': 'Rename(&R)…',
    '복제(&D)': 'Duplicate(&D)',
    '오류': 'Error',
    'hanja_core 를 불러오지 못했습니다: {}': 'Could not load hanja_core: {0}',
    'pmime_core 를 불러오지 못했습니다: {}': 'Could not load pmime_core: {0}',
    '{}  (조합 문자)': '{0}  (combining character)',
    '(없음)': '(none)',
    'RGB 복사됨: {}': 'RGB copied: {0}',
    ' (빨간 줄이 정렬 &)': ' (the red line is the alignment &)',
    '다음 citekey가 중복됩니다:\n': 'The following citekeys are duplicated:\n',
    '인용 {}개 중 문헌 항목이 없는 것 {}개(붉은 글씨) — {}에서 찾지 못했습니다.': '{1} of {0} citations have no reference entry (in red) — not found in {2}.',
    '인용 {}개 — 전부 문헌 항목이 있습니다({}).': '{0} citations — all have reference entries ({1}).',
    'c (가운데)': 'c (center)',
    'l (왼쪽)': 'l (left)',
    'r (오른쪽)': 'r (right)',
    'X (비례)': 'X (proportional)',
    '{}. 더 복잡한 표는 전용 표 편집 프로그램을 이용하셔요': '{0}. For more complex tables, please use a dedicated table-editing program',
    '유효한 마크다운 표가 아닙니다.': 'This is not a valid Markdown table.',
    '마크다운 표 파싱 중 오류가 발생했습니다.': 'An error occurred while parsing the Markdown table.',
    '{} 열 지시자를 찾을 수 없습니다.': 'Could not find the {0} column specifier.',
    '{} 본문을 찾을 수 없습니다.': 'Could not find the {0} body.',
    '{} 데이터 행이 없습니다.': '{0} has no data rows.',
    ' — 접두어를 바꿔 주세요.': ' — please change the prefix.',
    '{} 을(를) 책에서 뺐습니다(파일은 그대로 있습니다).': 'Removed {0} from the book (the file is untouched).',
    '넣을 수 있는 파일이 없습니다': 'There are no files that can be added',
    '종료 코드 {}, 출력이 없습니다.': 'Exit code {0}, no output.',
    '  (도구 메시지: {})': '  (tool message: {0})',
    '알 수 없는 오류': 'Unknown error',
    '한 개 파일로 내보내기…': 'Export as a single file…',
    '장별 파일로 내보내기…': 'Export as per-chapter files…',
    '스타일·클래스 파일 — 클릭하면 내용을 훑어보고, 우클릭으로 시스템 편집기로 열 수 있습니다': 'Style/class files — click to preview, right-click to open in the system editor',
    '컴파일되지 않은 .tex (같은 이름의 원고도 .pdf 도 없음) — 클릭하면 훑어보고, 우클릭으로 시스템 편집기로 열 수 있습니다': 'Uncompiled .tex (no same-named manuscript or .pdf) — click to preview, right-click to open in the system editor',
    '(감지되지 않음)': '(not detected)',
    "'{}' 구간에 {{{}}} 이(가) 들어 있어 자르면 포함이 3단계가 됩니다.\n포함은 2단계까지만 지원되므로 자르지 않습니다. 그 {{포함}} 줄을 제목 앞쪽으로 옮기거나 먼저 빼 주세요.": "The section '{0}' contains {{{1}}}, so splitting would make the include three levels deep.\nIncludes are supported only up to two levels, so it was not split. Move that {{include}} line before the heading, or remove it first.",
    '{} 를 읽는 중 오류:\n{}': 'Error while reading {0}:\n{1}',
    '선택 범위가 없습니다': 'There is no selection',
    '더 올릴 수 없습니다(최상위 #)': 'Cannot raise further (top-level #)',
    '더 내릴 수 없습니다(6단계)': 'Cannot lower further (level 6)',
    '문서를 열지 못했습니다': 'Could not open the document',
    '조합 중인 글자를 확정(Space 등)한 뒤 다시 눌러 주세요.': 'Commit the character being composed (e.g. with Space) and press again.',
    '한자 사전을 열지 못했습니다: {}': 'Could not open the hanja dictionary: {0}',
    '사전 DB 를 지우지 못했습니다: {}': 'Could not delete the dictionary DB: {0}',
    '글을 먼저 선택하세요': 'Select some text first',
    '{} 을(를) 고치지 못했습니다: {}': 'Could not modify {0}: {1}',
    '표의 {}째 줄 {}칸 근처가 어느 셀에도 속하지 않습니다 — 이 줄의 `|` 위치가 위아래 줄과 맞는지 확인하십시오': 'Near line {0}, column {1} of the table belongs to no cell — check that the `|` positions on this line match the lines above and below',
    '코드': 'Code',
    ' (커서 위 단어)': ' (word under cursor)',
    '  (하위 폴더 — 서랍 미지원)': '  (sub-folder — not supported in the drawer)',
    '장별로 자르기…': 'Split by chapter…',
    '[{}]: {}': '[{0}]: {1}',
    'pdftoppm 이 쪽을 그리지 못했습니다': 'pdftoppm could not render the page',
    'CMYK 복사됨: {}': 'CMYK copied: {0}',
    '표 변환 실패': 'Table conversion failed',
    '셀 안의 각주는 tabular 안에서 동작하지 않습니다.': 'Footnotes inside cells do not work within tabular.',
    '이미 있는 파일: ': 'Files that already exist: ',
    '알 수 없는 오류입니다.': 'An unknown error occurred.',
    '{}개': '{0}',
    '접었습니다': 'folded',
    '폈습니다': 'unfolded',
    'HSB 복사됨: {}': 'HSB copied: {0}',
    "\n\n표를 넣지 않았습니다. 셀을 이미 LaTeX 로 썼다면 '셀의 마크다운을 LaTeX로 변환'을 끄고 다시 넣으십시오.": "\n\nThe table was not inserted. If the cells are already written in LaTeX, turn off 'Convert cell Markdown to LaTeX' and insert again.",
    '{}: latexmk -C 실패 ({})': '{0}: latexmk -C failed ({1})',
    '(전체 {}쪽 중 1쪽만 미리봅니다)': '(previewing only page 1 of {0})',
    '{}행 {}열': '{0} rows × {1} columns',
    ' · 원격 미수신 {}개': ' · {0} remote not downloaded',
    ' · 변환 필요 {}개': ' · {0} need conversion',
    ' (책 {}권)': ' ({0} books)',
    '표 크기 한도(행 50·열 20)를 넘어 ': 'Exceeding the table size limit (50 rows, 20 columns): ',
    '를 가져오지 못했습니다.': ' could not be imported.',
    '{} → {}/': '{0} → {1}/',
    '한국어': '한국어',
    'English': 'English',
    '언어 / Language': 'Language',
    '언어 / Language(&L)': 'Language(&L)',
    '\n        <h2 style="margin-bottom:2px">ndhmdWriter</h2>\n        <div style="color:#7a7368">버전 {}</div>\n        <div style="color:#7a7368; font-size:11px">Powered by ndhmd4tex 0.20.0, ndhmdsync 0.5.6, ksruncltex and TeXLive 2026</div>\n        <p>\n        지은이: {}<br>\n        라이선스: {}\n        </p>\n        <p style="color:#7a7368; font-size:11px">\n        MIT 라이선스로 배포하기 위해 PySide6를 사용했습니다.\n        </p>\n        <p style="color:#7a7368; font-size:11px">\n        한자 변환 사전은 <b>libhangul</b>의 <code>hanja.txt</code>(Copyright (c) 2005, 2006 Choe Hwanjin)와\n        기호 사전 <code>mssymbol.txt</code>(Copyright (c) 2005-2014 Choe Hwanjin)입니다.\n        All rights reserved. (BSD 라이선스)\n        </p>\n        <div style="color:#7a7368; font-size:10px">\n        {}\n        </div>\n        <p style="font-size:11px">\n        PDF 뷰어와 오가는 동기화(정방향·역방향 검색)를 쓰려면, 환경설정의\n        "PDF 뷰어 역방향 검색" 행에서 <b>지금 등록</b> 버튼을 한 번 눌러\n        두십시오. 정방향 검색은 컴파일 메뉴나 편집창 우클릭 메뉴의\n        "PDF에서 이 위치 보기"(<code>Ctrl+Alt+F</code>)로 부릅니다.\n        </p>\n        <h3>단축키 요약</h3>\n        <table cellspacing="0">{}</table>\n        ': '\n        <h2 style="margin-bottom:2px">ndhmdWriter</h2>\n        <div style="color:#7a7368">Version {0}</div>\n        <div style="color:#7a7368; font-size:11px">Powered by ndhmd4tex 0.20.0, ndhmdsync 0.5.6, ksruncltex and TeXLive 2026</div>\n        <p>\n        Author: {1}<br>\n        License: {2}\n        </p>\n        <p style="color:#7a7368; font-size:11px">\n        PySide6 is used so that the app can be distributed under the MIT license.\n        </p>\n        <p style="color:#7a7368; font-size:11px">\n        The hanja conversion dictionary is <code>hanja.txt</code> from <b>libhangul</b> (Copyright (c) 2005, 2006 Choe Hwanjin) and\n        the symbol dictionary <code>mssymbol.txt</code> (Copyright (c) 2005-2014 Choe Hwanjin).\n        All rights reserved. (BSD license)\n        </p>\n        <div style="color:#7a7368; font-size:10px">\n        {3}\n        </div>\n        <p style="font-size:11px">\n        To use synchronization with the PDF viewer (forward and reverse search), press the\n        <b>Register now</b> button once in the "PDF viewer reverse search" row of Preferences.\n        Forward search is invoked from the Compile menu or the editor\'s right-click menu with\n        "Show this position in PDF" (<code>Ctrl+Alt+F</code>).\n        </p>\n        <h3>Shortcut summary</h3>\n        <table cellspacing="0">{4}</table>\n        ',
}

_EN_EXACT = {}
_EN_PATTERNS = []   # (정규식, 영어 서식, 와일드카드 수)
_EN_FRAG = None
_EN_CACHE = {}


def _i18n_build():
    global _EN_FRAG
    _EN_EXACT.clear()
    _EN_PATTERNS.clear()
    frag = {}
    for ko, en in _EN.items():
        if "{}" in ko or "{{" in ko or "}}" in ko:
            n = ko.count("{}")
            # 고정 글이 짧은 서식("{}장" 등)은 아무 글에나 맞아 버리므로
            # 빈칸을 숫자로만 채울 수 있게 좁힌다.
            rx = _i18n_pattern(ko, numeric=(len(ko) - 2 * n) <= 2)
            _EN_PATTERNS.append((rx, en, n, len(ko) - 2 * n))
        else:
            _EN_EXACT[ko] = en
            if len(ko.strip()) >= 6 and _HANGUL_RE.search(ko):
                frag[ko] = en
    # 구체적인 서식(고정 글이 긴 것)을 먼저
    _EN_PATTERNS.sort(key=lambda p: -p[3])
    keys = sorted(frag, key=len, reverse=True)
    _EN_FRAG = (re.compile("|".join(re.escape(k) for k in keys)), frag) if keys else None


def _i18n_pattern(ko: str, numeric: bool = False):
    s = ko
    s = s.replace("{{{}}}", "\x01\x00\x02").replace("{{}}", "\x01\x00\x02")
    s = s.replace("{}", "\x00")
    parts = re.split("(\x00|\x01|\x02)", s)
    rx = []
    for p in parts:
        if p == "\x00":
            rx.append(r"(\d+)" if numeric else "(.*?)")
        elif p == "\x01":
            rx.append(r"\{")
        elif p == "\x02":
            rx.append(r"\}")
        else:
            q = re.escape(p)
            q = q.replace(r"\{\{", r"\{{1,2}").replace(r"\}\}", r"\}{1,2}")
            rx.append(q)
    return re.compile("^" + "".join(rx) + "$", re.S)


def ui_language() -> str:
    """저장된 화면 언어("ko"|"en"). 환경변수 NDHMD_LANG 이 있으면 그것이 우선."""
    v = os.environ.get("NDHMD_LANG", "").strip().lower()
    if v not in ("ko", "en"):
        try:
            v = str(QSettings("ktug.org", "ndhmdWriter").value("ui/language", "ko"))
        except Exception:
            v = "ko"
    return "en" if v == "en" else "ko"


def _T(s):
    """영어 모드에서 한국어 글을 영어로. 그 밖에는 그대로."""
    if _UI_LANG != "en" or not isinstance(s, str) or not s:
        return s
    if not _HANGUL_RE.search(s):
        return s
    hit = _EN_CACHE.get(s)
    if hit is not None:
        return hit
    r = _i18n_translate(s)
    if "(&" in r:
        r = _i18n_accel(r)
    if "1 " in r:
        r = _PLURAL1_RE.sub(lambda m: m.group(1) + _PLURAL1[m.group(2)], r)
    if len(_EN_CACHE) < 6000:
        _EN_CACHE[s] = r
    return r


_PLURAL1 = {"manuscripts": "manuscript", "files": "file", "images": "image",
            "headings": "heading", "references": "reference", "columns": "column",
            "rows": "row", "sub-files": "sub-file", "places": "place", "edits": "edit",
            "sub-chapters": "sub-chapter", "chars": "char", "citations": "citation",
            "symbols": "symbol", "entries": "entry", "items": "item", "books": "book",
            "pages": "page", "chapters": "chapter", "fences/environments": "fence/environment",
            "includes": "include", "dead caches": "dead cache", "dead tags": "dead tag",
            "dead memos": "dead memo", "references": "reference"}
_PLURAL1_RE = re.compile(r"(?<![\d.,])(?<!\d )\b(1 )(" + "|".join(
    sorted((re.escape(k) for k in _PLURAL1), key=len, reverse=True)) + r")\b")
_HTML_TEXT_RE = re.compile(r">([^<>]*[가-힣][^<>]*)<")
_ACCEL_RE = re.compile(r"\(&(\w)\)")


def _i18n_accel(text: str) -> str:
    """한국어식 "열기(&O)" 의 가속 글쇠 표기를 영어식 "&Open" 으로 옮긴다.
    글쇠 글자를 영어 낱말에서 찾지 못하면 괄호 표기를 그대로 둔다."""
    m = _ACCEL_RE.search(text)
    if not m:
        return text
    key = m.group(1)
    rest = text[:m.start()] + text[m.end():]
    # 낱말 첫 글자를 먼저, 없으면 아무 데나
    for rx in (r"(?<![A-Za-z&])" + re.escape(key), re.escape(key)):
        mm = re.search(rx, rest, re.I)
        if mm:
            i = mm.start()
            return rest[:i] + "&" + rest[i:]
    return text


def _i18n_translate(s: str) -> str:
    en = _EN_EXACT.get(s)
    if en is not None:
        return en
    for rx, tmpl, n, _w in _EN_PATTERNS:
        m = rx.match(s)
        if m:
            groups = [_T(g) for g in m.groups()]
            out = tmpl
            for i, g in enumerate(groups):
                out = out.replace("{%d}" % i, g)
            return out.replace("{{", "{").replace("}}", "}")
    # 앞뒤 공백만 다른 경우
    st = s.strip()
    if st != s and st:
        en = _EN_EXACT.get(st)
        if en is not None:
            lead = s[:len(s) - len(s.lstrip())]
            trail = s[len(s.rstrip()):]
            return lead + en + trail
    if _EN_FRAG:
        rx, frag = _EN_FRAG
        if "<" in s:
            # HTML 이면 태그 사이 글 토막을 하나씩 번역한 뒤 남은 구절을 치환
            s = _HTML_TEXT_RE.sub(lambda m: ">" + _T(m.group(1)) + "<", s)
        return rx.sub(lambda m: frag[m.group(0)], s)
    if "<" in s:
        return _HTML_TEXT_RE.sub(lambda m: ">" + _T(m.group(1)) + "<", s)
    return s


def _T_any(x):
    if isinstance(x, str):
        return _T(x)
    if isinstance(x, list):
        return [_T_any(i) for i in x]
    if isinstance(x, tuple):
        return tuple(_T_any(i) for i in x)
    return x


def _i18n_wrap_method(cls, name, mode="all", idxs=None, kws=None):
    """cls.name 의 글 인자를 번역하는 껍데기로 바꾼다.
    mode: all(문자열 인자 전부) · first(첫 문자열 인자만) · idx(idxs 위치만)."""
    try:
        orig = getattr(cls, name)
    except AttributeError:
        return
    is_static = isinstance(cls.__dict__.get(name), staticmethod)

    def conv(a, k):
        a = list(a)
        if mode == "all":
            a = [_T_any(x) for x in a]
        elif mode == "first":
            for i, x in enumerate(a):
                if isinstance(x, str):
                    a[i] = _T(x)
                    break
        elif mode == "idx":
            for i in (idxs or ()):
                if i < len(a):
                    a[i] = _T_any(a[i])
        if kws:
            for kw in kws:
                if kw in k:
                    k[kw] = _T_any(k[kw])
        return a, k

    if is_static:
        def f(*a, **k):
            a, k = conv(a, dict(k))
            return orig(*a, **k)
        setattr(cls, name, staticmethod(f))
    else:
        def f(self, *a, **k):
            a, k = conv(a, dict(k))
            return orig(self, *a, **k)
        setattr(cls, name, f)


def _i18n_wrap_init(cls):
    try:
        orig = cls.__init__
    except AttributeError:
        return

    def __init__(self, *a, **k):
        a = [_T_any(x) for x in a]
        for kw in ("text", "title", "labelText"):
            if kw in k:
                k[kw] = _T_any(k[kw])
        orig(self, *a, **k)
    cls.__init__ = __init__


def install_i18n(lang: str):
    """언어를 정하고(영어면) Qt 경계를 감싼다. QApplication 이 생긴 뒤,
    창을 만들기 전에 한 번만 부른다."""
    global _UI_LANG
    _UI_LANG = "en" if lang == "en" else "ko"
    if _UI_LANG != "en":
        return
    from PySide6.QtWidgets import (QAbstractButton, QMenuBar, QProgressDialog, QToolBar,
                                   QToolTip)
    _i18n_build()
    W = _i18n_wrap_method
    for c in (QAction, QLabel, QPushButton, QCheckBox, QRadioButton, QToolButton,
              QGroupBox, QMenu, QTreeWidgetItem, QListWidgetItem, QTableWidgetItem,
              QStandardItem):
        _i18n_wrap_init(c)
    for n in ("setText", "setToolTip", "setStatusTip", "setIconText", "setWhatsThis"):
        W(QAction, n)
    for n in ("setText", "setToolTip"):
        W(QAbstractButton, n)
    W(QLabel, "setText")
    W(QGroupBox, "setTitle")
    for n in ("addAction", "addMenu", "setTitle", "addSection"):
        W(QMenu, n, "first")
    W(QMenuBar, "addMenu", "first")
    W(QToolBar, "addAction", "first")
    for n in ("setWindowTitle", "setToolTip", "setStatusTip", "setWhatsThis"):
        W(QWidget, n)
    W(QLineEdit, "setPlaceholderText")
    W(QPlainTextEdit, "setPlaceholderText")
    W(QTextEdit, "setPlaceholderText")
    W(QTextEdit, "setHtml")
    for n in ("addItem", "insertItem", "setItemText"):
        W(QComboBox, n, "first")
    W(QComboBox, "addItems")
    W(QComboBox, "setPlaceholderText")
    for n in ("addTab", "insertTab", "setTabText", "setTabToolTip"):
        W(QTabWidget, n, "first")
    W(QStatusBar, "showMessage", "idx", (0,))
    W(QToolTip, "showText", "idx", (1,))
    W(QTreeWidget, "setHeaderLabels")
    W(QTableWidget, "setHorizontalHeaderLabels")
    W(QTableWidget, "setVerticalHeaderLabels")
    for c in (QTreeWidgetItem,):
        W(c, "setText", "idx", (1,))
        W(c, "setToolTip", "idx", (1,))
    for c in (QListWidgetItem, QTableWidgetItem, QStandardItem):
        W(c, "setText")
        W(c, "setToolTip")
    W(QFormLayout, "addRow", "first")
    for c in (QSpinBox, QDoubleSpinBox):
        W(c, "setSuffix")
        W(c, "setPrefix")
    # 메시지 상자 · 입력 · 파일 대화상자
    for n in ("information", "warning", "critical", "question"):
        W(QMessageBox, n, "idx", (1, 2))
    W(QMessageBox, "about", "idx", (1, 2))
    for n in ("setText", "setInformativeText", "setDetailedText"):
        W(QMessageBox, n)
    W(QMessageBox, "addButton", "first")
    W(QInputDialog, "getText", "idx", (1, 2))
    W(QInputDialog, "getMultiLineText", "idx", (1, 2))
    W(QInputDialog, "getInt", "idx", (1, 2))
    W(QInputDialog, "getDouble", "idx", (1, 2))
    W(QInputDialog, "getItem", "idx", (1, 2, 3))
    for n in ("getOpenFileName", "getOpenFileNames", "getSaveFileName"):
        W(QFileDialog, n, "idx", (1, 3), ("caption", "filter"))
    W(QFileDialog, "getExistingDirectory", "idx", (1,), ("caption",))
    W(QProgressDialog, "setLabelText")
    W(QProgressDialog, "setCancelButtonText")




def main():
    _fix_macos_path()
    app = QApplication(sys.argv)
    install_i18n(ui_language())

    # 단일 인스턴스. 이미 떠 있는 인스턴스가 있으면 인자를 그리로 넘기고
    # 이 프로세스는 그냥 끝난다 — SumatraPDF/Skim 이 역방향 검색으로
    # --goto 를 들고 부를 때마다 새 창이 뜨면 안 된다.
    if _try_send_to_running_instance(sys.argv[1:]):
        return

    app.setApplicationName("ndhmdWriter")
    icon = _app_icon()
    app.setWindowIcon(icon)
    win = MainWindow()
    win.setWindowIcon(icon)
    if sys.argv[1:]:
        process_argv(win, sys.argv[1:])
    else:
        win.restore_last_file()
    win.show()
    if not win.workspace:
        # 최초 실행 등으로 QSettings 에 저장된 작업공간이 아예 없고,
        # 인자로 받은 파일도 없어 위 분기에서도 정해지지 않았다 — 여기서
        # 한 번 고르게 한다. 창을 먼저 보여준 뒤에 물어서, 빈 화면에
        # 대화상자만 뜨는 것보다 앱이 이미 켜져 있다는 맥락이 보이게 한다.
        # 취소하면 choose_workspace() 가 조용히 아무 일도 안 하고
        # 돌아오므로, 작업공간 없는 상태로 계속 쓰는 것도 그대로 허용된다.
        win.choose_workspace()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
