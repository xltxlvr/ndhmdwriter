# -*- mode: python ; coding: utf-8 -*-


a = Analysis(
    ['ndhmdWriter.py'],
    pathex=[],
    binaries=[],
    datas=[('font.py', '.'), ('ndhmdwriter_icon.png', '.'), ('pmimegui.py', '.'), ('pmime_core.py', '.'), ('hanja_core.py', '.'), ('hanja.txt', '.'), ('mssymbol.txt', '.'), ('kyujitai.json', '.'), ('shinjitai.json', '.'), ('simplified.json', '.'), ('customkanji.json', '.')],
    hiddenimports=[],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    [],
    exclude_binaries=True,
    name='ndhmdWriter',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    icon=['ndhmdwriter_icon.icns'],
)
coll = COLLECT(
    exe,
    a.binaries,
    a.datas,
    strip=False,
    upx=True,
    upx_exclude=[],
    name='ndhmdWriter',
)
app = BUNDLE(
    coll,
    name='ndhmdWriter.app',
    icon='ndhmdwriter_icon.icns',
    bundle_identifier=None,
    info_plist={
        'CFBundleDevelopmentRegion': 'ko_KR',  # 기본 지역 설정
        'CFBundleLocalizations': ['ko', 'en'], # 앱이 지원하는 언어 목록
        'NSHighResolutionCapable': True,       # 레티나 디스플레이 지원
    },
)
