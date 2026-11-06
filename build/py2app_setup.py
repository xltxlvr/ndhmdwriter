import sys
from setuptools import setup

# macOS 환경 체크
if sys.platform != 'darwin':
    print("이 setup.py 스크립트는 macOS 환경에서 py2app을 구동하기 위한 파일입니다.")
    sys.exit(1)

# 번들 메인 스크립트 지정
APP = ['ndhmdWriter.py']

# 번들 내에 포함시킬 추가 데이터 파일 (내장 PNG 아이콘 포함)
DATA_FILES = [
    ('', ['ndhmdwriter_icon.png']),
]

# py2app 세부 빌드 옵션
OPTIONS = {
    'argv_emulation': False,  # PySide6/Qt 앱에서는 드래그 앤 드롭/파일 연결 지원을 위해 False 권장
    'iconfile': 'ndhmdwriter_icon.icns',  # macOS 앱 번들용 아이콘 (.icns)
    'includes': [
        'PySide6',
        'PySide6.QtCore',
        'PySide6.QtGui',
        'PySide6.QtWidgets',
        'yaml',        # pyyaml
        'fontTools',   # fonttools
    ],
    'excludes': [
        'tkinter',
        'matplotlib',
        'scipy',
        'numpy',
        'PyQt5',
        'PyQt6',
    ],
    # Qt6에서 사용하는 필수 플러그인 지정
    'qt_plugins': [
        'platforms',        # Cocoa 등 GUI 렌더링 필수
        'styles',           # 시스템 스타일링
        'iconengines',      # SVG/Qt 아이콘엔진
        'imageformats',     # PNG, JPG 등 이미지 읽기 지원
    ],
    'plist': {
        'CFBundleName': 'ndhmdWriter',
        'CFBundleDisplayName': 'ndhmdWriter',
        'CFBundleIdentifier': 'com.ndhmd.writer',
        'CFBundleVersion': '1.0.0',
        'CFBundleShortVersionString': '1.0.0',
        'NSHumanReadableCopyright': 'Copyright © 2026 ndhmd. All rights reserved.',
        'HighResolutionCapable': True,  # 레티나 디스플레이 고해상도 지원
    },
}

setup(
    name='ndhmdWriter',
    app=APP,
    data_files=DATA_FILES,
    options={'py2app': OPTIONS},
    setup_requires=['py2app'],
)