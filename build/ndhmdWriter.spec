# -*- mode: python ; coding: utf-8 -*-
#
# ndhmdWriter — Windows 용 PyInstaller spec
#
# 빌드 (이 파일이 있는 폴더, 즉 ndhmdWriter.py 와 같은 폴더에서):
#
#     pip install pyinstaller PySide6 PyYAML Pillow
#     pyinstaller --noconfirm --clean ndhmdWriter.spec
#
# 결과: dist\ndhmdWriter.exe (ONEFILE = True) 또는 dist\ndhmdWriter\ndhmdWriter.exe (False)
#
# 같은 폴더에 있어야 하는 파일
#   ndhmdWriter.py, pmime_core.py, hanja_core.py, hanja.txt, mssymbol.txt                      (필수 — 한중일 pm 입력기의 변환 코어)
#   shinjitai.json kyujitai.json simplified.json customkanji.json   (pm 입력기 사전)
#   ndhmdwriter_icon.png, ndhmdwriter_icon.ico         (아이콘; 없으면 아이콘 없이 빌드)
#
# 번들하지 않는 것: ndhmd4tex / ndhmdsync / ksruncltex / TeXLive 는 외부 프로그램이므로 PATH 에서 찾는다.
# customkanji.json 은 앱의 "일어사용자한자" 창에서 고친다. 번들 안은 읽기 전용이라 고친 사본은 %APPDATA%\pmimegui 에 저장되고 번들본보다 먼저 쓰인다(exe 곁에 직접 둔 사본도 같은 원리).

import os

# True  = 파일 하나짜리 exe (배포는 편하지만 시작이 느리고, 백신이 의심하는 일이 더 잦다)
# False = 폴더로 배포 (시작이 빠르고 오탐이 적다 — 백신 문제가 있으면 이쪽을 권한다)
ONEFILE = True

HERE = os.path.abspath(SPECPATH)


def have(name):
    return os.path.isfile(os.path.join(HERE, name))


# (원본 경로, 번들 안의 폴더) — "." 은 실행 시 앱의 기본 폴더(_MEIPASS)이다.
datas = []
for name in ("ndhmdwriter_icon.png",
             "shinjitai.json", "kyujitai.json", "simplified.json", "customkanji.json",
             "hanja.txt", "mssymbol.txt"):   # 한자 변환(F9) 사전 원본 — libhangul, BSD 라이선스. 머리말의 저작권 표시를 지우지 말 것
    if have(name):
        datas.append((os.path.join(HERE, name), "."))

# 실행 중에 늦게(함수 안에서) 불러오거나 선택적으로 쓰는 모듈들. 분석이 놓치기 쉬우므로 명시한다.
hiddenimports = [
    "hanja_core",      # 한자 변환(F9) 코어 — 사전 DB 를 만들고 후보를 찾는다 (Qt 없음)
    "sqlite3",
    "pmime_core",      # 한중일 pm 입력기 변환 코어 (ndhmdWriter 가 try-import 한다)
    "unicodedata",     # pmime_core 가 쓴다
    "yaml",            # PyYAML — front matter 읽기 (함수 안에서 import)
]
try:
    import PIL  # noqa: F401
    hiddenimports.append("PIL")   # 선택 — 그림 점검의 webp/gif/tiff 변환
except ImportError:
    pass

# 쓰지 않는 큰 Qt 모듈은 빼서 크기를 줄인다. (Svg, Network, Widgets, Gui, Core 는 남겨 둔다)
excludes = [
    "PySide6.QtWebEngineCore", "PySide6.QtWebEngineWidgets", "PySide6.QtWebEngineQuick",
    "PySide6.QtQml", "PySide6.QtQuick", "PySide6.QtQuick3D", "PySide6.QtQuickWidgets",
    "PySide6.Qt3DCore", "PySide6.Qt3DRender", "PySide6.QtCharts", "PySide6.QtDataVisualization",
    "PySide6.QtMultimedia", "PySide6.QtMultimediaWidgets", "PySide6.QtBluetooth",
    "PySide6.QtSensors", "PySide6.QtSerialPort", "PySide6.QtPdf", "PySide6.QtPdfWidgets",
    "PySide6.QtDesigner", "PySide6.QtHelp", "PySide6.QtTest", "PySide6.QtSql",
    "tkinter",
]

a = Analysis(
    [os.path.join(HERE, "ndhmdWriter.py")],
    pathex=[HERE],            # pmime_core.py 를 찾게 한다
    binaries=[],
    datas=datas,
    hiddenimports=hiddenimports,
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=excludes,
    noarchive=False,
)
pyz = PYZ(a.pure)

icon = os.path.join(HERE, "ndhmdwriter_icon.ico") if have("ndhmdwriter_icon.ico") else None

if ONEFILE:
    exe = EXE(
        pyz,
        a.scripts,
        a.binaries,
        a.datas,
        [],
        name="ndhmdWriter",
        debug=False,
        bootloader_ignore_signals=False,
        strip=False,
        upx=False,            # UPX 로 압축하면 백신 오탐이 크게 늘어난다
        runtime_tmpdir=None,
        console=False,        # 콘솔 창 없음 (GUI 앱)
        disable_windowed_traceback=False,
        icon=icon,
    )
else:
    exe = EXE(
        pyz,
        a.scripts,
        [],
        exclude_binaries=True,
        name="ndhmdWriter",
        debug=False,
        bootloader_ignore_signals=False,
        strip=False,
        upx=False,
        console=False,
        disable_windowed_traceback=False,
        icon=icon,
    )
    coll = COLLECT(
        exe,
        a.binaries,
        a.datas,
        strip=False,
        upx=False,
        name="ndhmdWriter",
    )
