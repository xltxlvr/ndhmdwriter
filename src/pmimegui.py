# pmIME-Multilingual Engine
#
# (C) 2026 Nova de Hi
# GPLv3
#
# version 0.13.2 (2026-10-22), 사전 저장을 pmime_core.add_custom_word 로 일원화
# version 0.13.1 (2026-10-21), 변환 코어를 pmime_core.py 로 분리
# version 0.13.0 (2026-08-14), global LaTeX Latin-char & \x{...} codepoint input
# version 0.12.4 (2026-07-03), LaTeX Commands/Envs 
# version 0.12.3 (2026-07-02), add RRK methhod
# version 0.12.1 (2026-06-30), clear after send
# version 0.12.0 (2026-06-24), send_to_editor & clipboard
# version 0.11.1 (2026-06-24), reversed shinjitai = han
# version 0.10.7 (2026-06-23), find_file 
# version 0.10.6 (2026-06-21), save_new_word in kanja_assistant
# version 0.10.5 (2026-06-21), improve kanja_assistant actions
# version 0.10.4 (2026-06-20), bug fix in kana-map
# version 0.10.3 (2026-06-20), hanja assistant
#
import sys
import os
import platform
import unicodedata
import re
import json

__version__ = "0.13.2"

GUI_AVAILABLE = False
try:
    from PyQt6.QtWidgets import (QApplication, QWidget, QVBoxLayout, QHBoxLayout,
                                 QTextEdit, QLabel, QSplitter, QPushButton, QComboBox,
                                 QDialog, QTextBrowser, QStatusBar, QLineEdit, QListWidget, 
                                 QListWidgetItem,
                                 QFormLayout, QDialogButtonBox, QCheckBox)
    from PyQt6.QtGui import QFont, QIcon, QShortcut, QKeySequence, QKeyEvent
    from PyQt6.QtCore import Qt, QSettings, pyqtSignal, QEvent
    import time 
    import subprocess
    GUI_AVAILABLE = True
except ImportError:
    pass


from pmime_core import *   # noqa: F401,F403 — 변환 코어 (pmime_core.py)
from pmime_core import (kanji_tables, reverse_hanja_map, find_file, load_kanji_tables,
                        convert_text, convert_input, normalize_output, filter_kanji, romaji_to_kana_convert,
                        expand_latex_input, set_latex_expand, process_tags_mixed,
                        process_latex_text, resource_path, add_custom_word)

def copy_to_clipboard(text):
    if not text:
        return False
        
    current_os = platform.system()
    
    # -----------------------------------------------------------------
    # 1. macOS (Darwin) 및 Linux: PyQt6 QClipboard 활용
    # -----------------------------------------------------------------
    if current_os in ["Darwin", "Linux"]:
        try:
            # 현재 실행 중인 QApplication 인스턴스 획득
            app = QApplication.instance()
            if not app:
                # GUI가 아직 뜨지 않았거나 CLI 테스트 환경일 경우 임시 생성
                app = QApplication(sys.argv)
                
            clipboard = QApplication.clipboard()
            clipboard.setText(text)
            
            # [핵심] macOS 시스템(NSPasteboard)이 데이터를 완전히 긁어갈 때까지 
            # Qt의 이벤트 루프를 강제로 구동하여 프로세스 처리를 완료합니다.
            QApplication.processEvents()
            
            # 시스템 클립보드에 데이터가 비어있지 않고 잘 안착했는지 최종 검증
            if clipboard.text() == text:
                return True
                
        except Exception as e:
            sys.stderr.write(f"PyQt6 클립보드 복사 실패 ({current_os}): {e}\n")
            # 실패 시 아래의 subprocess 폴백 로직으로 진입
            pass

    # -----------------------------------------------------------------
    # 2. Windows: ctypes를 통한 Win32 API 유니코드(CF_UNICODETEXT) 직주입
    # -----------------------------------------------------------------
    try:
        if current_os == "Windows":
            import ctypes
            from ctypes import wintypes
            
            GMEM_MOVEABLE = 0x0002
            CF_UNICODETEXT = 13
            
            # Win32 API 함수 포인터 정의
            OpenClipboard = ctypes.windll.user32.OpenClipboard
            OpenClipboard.argtypes = [wintypes.HWND]
            OpenClipboard.restype = wintypes.BOOL
            
            EmptyClipboard = ctypes.windll.user32.EmptyClipboard
            EmptyClipboard.argtypes = []
            EmptyClipboard.restype = wintypes.BOOL
            
            SetClipboardData = ctypes.windll.user32.SetClipboardData
            SetClipboardData.argtypes = [wintypes.UINT, wintypes.HANDLE]
            SetClipboardData.restype = wintypes.HANDLE
            
            CloseClipboard = ctypes.windll.user32.CloseClipboard
            CloseClipboard.argtypes = []
            CloseClipboard.restype = wintypes.BOOL
            
            GlobalAlloc = ctypes.windll.kernel32.GlobalAlloc
            GlobalAlloc.argtypes = [wintypes.UINT, ctypes.c_size_t]
            GlobalAlloc.restype = wintypes.HGLOBAL
            
            GlobalLock = ctypes.windll.kernel32.GlobalLock
            GlobalLock.argtypes = [wintypes.HGLOBAL]
            GlobalLock.restype = wintypes.LPVOID
            
            GlobalUnlock = ctypes.windll.kernel32.GlobalUnlock
            GlobalUnlock.argtypes = [wintypes.HGLOBAL]
            GlobalUnlock.restype = wintypes.BOOL
            
            # UTF-16 LE 인코딩 및 널 문자(\x00\x00) 추가
            unicode_bytes = text.encode('utf-16le') + b'\x00\x00'
            
            if not OpenClipboard(None):
                return False
                
            try:
                EmptyClipboard()
                h_global = GlobalAlloc(GMEM_MOVEABLE, len(unicode_bytes))
                if not h_global:
                    return False
                    
                ptr = GlobalLock(h_global)
                if ptr:
                    ctypes.memmove(ptr, unicode_bytes, len(unicode_bytes))
                    GlobalUnlock(h_global)
                    SetClipboardData(CF_UNICODETEXT, h_global)
            finally:
                CloseClipboard()
            return True

        # -----------------------------------------------------------------
        # 3. macOS 폴백 (PyQt6 호출 실패 시 Subprocess 사용)
        # -----------------------------------------------------------------
        elif current_os == "Darwin":
            import subprocess
            # 외부 환경 유실 방지를 위해 pbcopy의 절대 경로 지정
            process = subprocess.Popen(
                ['/usr/bin/pbcopy'], 
                stdin=subprocess.PIPE, 
                text=True, 
                encoding='utf-8', 
                errors='replace'
            )
            process.stdin.write(text)
            process.stdin.close()  # EOF 명시적 전달
            process.wait()         # pbcopy 데몬이 완전히 가져갈 때까지 대기
            return process.returncode == 0

        # -----------------------------------------------------------------
        # 4. Linux 폴백 (PyQt6 호출 실패 시 xclip/xsel 사용)
        # -----------------------------------------------------------------
        elif current_os == "Linux":
            import subprocess
            try:
                process = subprocess.Popen(
                    ['xclip', '-selection', 'clipboard', '-t', 'UTF8_STRING'], 
                    stdin=subprocess.PIPE, text=True, encoding='utf-8', errors='replace'
                )
                process.communicate(input=text)
                return True
            except FileNotFoundError:
                try:
                    process = subprocess.Popen(
                        ['xsel', '--clipboard', '--input'], 
                        stdin=subprocess.PIPE, text=True, encoding='utf-8', errors='replace'
                    )
                    process.communicate(input=text)
                    return True
                except FileNotFoundError:
                    return False
                    
    except Exception as e:
        sys.stderr.write(f"클립보드 전체 복사 프로세스 중 예외 발생: {e}\n")
        return False
        
    return False


if GUI_AVAILABLE:
    class KanjiAssistant(QWidget):
        kanji_selected = pyqtSignal(str)

        def __init__(self, parent=None):
            super().__init__(parent, Qt.WindowType.Tool | Qt.WindowType.WindowStaysOnTopHint)
            self.setWindowTitle("일본어 한자 입력")
            
            self.resize(300, 310)

            kanji_font = QFont("Noto Sans CJK KR", 11)
            self.setFont(kanji_font)
            
            layout = QVBoxLayout(self)
            layout.setContentsMargins(5, 5, 5, 5)
            
            self.search_input = QLineEdit()
            self.search_input.setPlaceholderText("검색어 입력 (Ctrl+F로 포커스)")
            self.search_input.textChanged.connect(self.filter_items)
            layout.addWidget(self.search_input)
            
            self.result_list = QListWidget()
            self.result_list.itemDoubleClicked.connect(self.on_item_double_clicked)
            layout.addWidget(self.result_list)
            
            # -----------------------------------------------------------------
            # "새 단어 등록" 버튼 배치
            # -----------------------------------------------------------------
            self.register_btn = QPushButton("새 단어 등록")
            self.register_btn.clicked.connect(self.show_registration_dialog)
            layout.addWidget(self.register_btn)
            
            self.full_data = kanji_tables.get("custom_kana", {})
            self.shinjitai_data = kanji_tables.get("shinjitai", {})
            
            self.populate_list(self.full_data)

            # 엔터키 연결 유지 (검색창용)
            self.search_input.returnPressed.connect(self.on_enter_pressed)

            # 키보드 이벤트를 직접 통제하기 위해 이벤트 필터 설치
            self.search_input.installEventFilter(self)
            self.result_list.installEventFilter(self)

        # 창이 표시될 때마다 메인 윈도우 우측 하단으로 위치 고정
        def showEvent(self, event):
            super().showEvent(event)
            if self.parent():
                parent_rect = self.parent().geometry()
                margin = 20
                x = parent_rect.right() - self.width() - margin
                y = parent_rect.bottom() - self.height() - margin
                self.move(x, y)

        # 방향키 및 엔터키 흐름
        def eventFilter(self, source, event):
            if event.type() == QEvent.Type.ShortcutOverride:
                if event.key() == Qt.Key.Key_Escape:
                    event.accept()
                    return True

            if event.type() == QEvent.Type.KeyPress:
                if event.key() == Qt.Key.Key_Escape:
                    if self.search_input.text():
                        self.search_input.clear()
                        self.search_input.setFocus()
                    else:
                        self.hide()
                    return True

                if Qt.Key.Key_0 <= event.key() <= Qt.Key.Key_9:
                    index = event.key() - Qt.Key.Key_0
                    if index < self.result_list.count():
                        item = self.result_list.item(index)
                        self._send_item_data(item)
                    return True

                if source == self.search_input and event.key() == Qt.Key.Key_Down:
                    self.result_list.setFocus()
                    if self.result_list.currentRow() < 0 and self.result_list.count() > 0:
                        self.result_list.setCurrentRow(0)
                    return True

                elif source == self.result_list and event.key() in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
                    self.on_enter_pressed()
                    return True

            return super().eventFilter(source, event)

        def populate_list(self, data):
            self.result_list.clear()
            sorted_items = sorted(data.items(), key=lambda item: len(item[0]), reverse=False)
            
            for index, (key, val) in enumerate(sorted_items):
                if index <= 9:
                    display_text = f"[{index}] {val} - {key}"
                else:
                    display_text = f"    {val} - {key}"
                
                list_item = QListWidgetItem(display_text)
                list_item.setData(Qt.ItemDataRole.UserRole, key)
                self.result_list.addItem(list_item)
                
            if self.result_list.count() > 0:
                self.result_list.setCurrentRow(0)

        def filter_items(self, text):
            if not text:
                self.populate_list(self.full_data)
                return
            
            converted_text = "".join([self.shinjitai_data.get(char, char) for char in text])
            text_lower = text.lower()
            converted_lower = converted_text.lower()

            filtered = {}
            for key, val in self.full_data.items():
                if (text_lower in key.lower() or text_lower in val.lower() or
                    converted_lower in key.lower() or converted_lower in val.lower()):
                    filtered[key] = val
                    
            self.populate_list(filtered)

        def _send_item_data(self, item):
            if item:
                kanji_key = item.data(Qt.ItemDataRole.UserRole)
                self.kanji_selected.emit(kanji_key)

        def on_item_double_clicked(self, item):
            self._send_item_data(item)

        def on_enter_pressed(self):
            self._send_item_data(self.result_list.currentItem())
                
        def closeEvent(self, event):
            self.hide()
            event.ignore()

        # -----------------------------------------------------------------
        # 새 단어 등록 다이알로그 및 저장/메모리 동기화
        # -----------------------------------------------------------------
        def show_registration_dialog(self):
            """간단한 입력 폼 다이알로그를 띄워 Key와 Value를 입력받음"""
            dialog = QDialog(self)
            dialog.setWindowTitle("새 단어 등록")
            dialog.setWindowModality(Qt.WindowModality.WindowModal) # 부모 창을 블록함
            
            dial_layout = QFormLayout(dialog)
            
            key_edit = QLineEdit()
            key_edit.setPlaceholderText("예: 단어 뒤 숫자가 붙은 형태 등")
            val_edit = QLineEdit()
            val_edit.setPlaceholderText("예: 漢字")
            
            dial_layout.addRow("검색키 (Key):", key_edit)
            dial_layout.addRow("변환값 (Value):", val_edit)
            
            btn_box = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
            btn_box.accepted.connect(dialog.accept)
            btn_box.rejected.connect(dialog.reject)
            dial_layout.addRow(btn_box)
            
            # 확인(Ok)을 누른 경우에만 파일 저장 로직 실행
            if dialog.exec() == QDialog.DialogCode.Accepted:
                key = key_edit.text().strip()
                val = val_edit.text().strip()
                
                if key and val:
                    self.save_new_word(key, val)

        def save_new_word(self, key, val):
            """customkanji.json 에 단어를 등록한다. 저장 위치·중복 키 처리·메모리 반영은 pmime_core 가 한다."""
            try:
                add_custom_word(key, val)
            except (OSError, ValueError) as e:
                print(f"사전 저장 실패: {e}")
                return
            self.full_data = kanji_tables["custom_kana"]
            self.filter_items(self.search_input.text())
            self.search_input.setFocus()

    class MainWindow(QWidget):
        def __init__(self):
            super().__init__()
            self.settings = QSettings("ktug.org", "pmIMEgui")

            icon_path = resource_path("pmimegui.png")
            if os.path.exists(icon_path):
                self.setWindowIcon(QIcon(icon_path))
            else:
                print(f"로그: 아이콘 파일을 찾을 수 없습니다 -> {icon_path}")

            self._last_sent_input = ""
            self._is_sending = False
            
            load_kanji_tables()
            self.init_ui()
            
        def init_ui(self):
            self.setWindowTitle(f"pm IME GUI v{__version__}")
            self.resize(400, 580)
            main_layout = QVBoxLayout(self)
            
            # 상단 설정 레이아웃 (콤보박스 라인)
            top_layout = QHBoxLayout()
            self.mode_combo = QComboBox()
            self.mode_combo.addItems(["pm (pm)", "frkim (frk)", "mix (mix)", "rrk-ex (rrk)", "두벌식 (du)", "Kana (jp)", "transparent", "한글자판→영문 (ed)"])
            self.mode_combo.setCurrentIndex(self.settings.value("engine_mode_index", 0, type=int))
            self.mode_combo.currentIndexChanged.connect(self.update_translation)
            self.mode_combo.currentIndexChanged.connect(self.save_settings)
            top_layout.addWidget(QLabel("입력 메서드:"))
            top_layout.addWidget(self.mode_combo)
            
            self.hanja_combo = QComboBox()
            self.hanja_combo.addItems(["없음(none)", "新字体(shin)", "舊字體(kyu)", "简体(sim)"])
            self.hanja_combo.setCurrentIndex(self.settings.value("hanja_mode_index", 0, type=int))
            self.hanja_combo.currentIndexChanged.connect(self.update_translation)
            self.hanja_combo.currentIndexChanged.connect(self.save_settings)
            top_layout.addWidget(QLabel("한자 필터:"))
            top_layout.addWidget(self.hanja_combo)
            
            self.norm_combo = QComboBox()
            self.norm_combo.addItems(["NFD", "NFC"])
            self.norm_combo.setCurrentIndex(self.settings.value("norm_mode_index", 0, type=int))
            self.norm_combo.currentIndexChanged.connect(self.update_translation)
            self.norm_combo.currentIndexChanged.connect(self.save_settings)
            top_layout.addWidget(QLabel("정규화:"))
            top_layout.addWidget(self.norm_combo)
            
            top_layout.addStretch()
            main_layout.addLayout(top_layout)
            
            # 중앙 텍스트 에디터 영역
            splitter = QSplitter(Qt.Orientation.Vertical)
            self.input_edit = QTextEdit()
            self.input_edit.setPlaceholderText("줄머리 %pm, %frk, %mix, %rrk, %du, %ed, %jp, %clean. Shift+Enter 개행")
            self.input_edit.textChanged.connect(self.update_translation)
            
            # 운영체제별 입력창 폰트 설정
            current_os = platform.system()
            if current_os == "Windows":
                font = QFont("Consolas", 12)
            elif current_os == "Darwin":
                font = QFont("Menlo", 14)
            else:
                font = QFont("Free Sans", 13)
            self.input_edit.setFont(font)
            splitter.addWidget(self.input_edit)
            
            self.output_edit = QTextEdit()
            self.output_edit.setReadOnly(True)
            
            # ----------------------------------------------------
            # 출력창 폰트 변경
            # ----------------------------------------------------
            # Mac의 Hiragino와 Win의 MS Gothic을 크로스플랫폼 대응용 튜플로 묶음
            self.font_mapping = {
                0: ("Noto Sans CJK KR", "Source Han Sans KR"),
                1: ("Noto Serif CJK KR", "Source Han Serif KR"),
                2: ("HCR Batang LVT", "HCRBatangLVT", "HCR Batang", "HCRBatang"), 
                3: ("Malgun Gothic", "맑은 고딕"),
                4: ("KoPubWorldDotum Medium", "KoPubWorldDotumMedium"),
                5: ("Hiragino Mincho ProN", "MS Mincho", "TakaoMincho", "Harano Aji Mincho")
            }
            
            splitter.addWidget(self.output_edit)
            main_layout.addWidget(splitter)
            
            # 하단 버튼 바로 위에 배치할 폰트 선택 레이아웃
            font_layout = QHBoxLayout()
            font_layout.addWidget(QLabel("출력 폰트:"))
            
            self.font_combo = QComboBox()
            self.font_combo.addItems([
                "Noto Sans CJK KR",
                "Noto Serif CJK KR",
                "함초롬바탕 LVT / 함초롬바탕",
                "Malgun Gothic",
                "KoPubWorldDotum",
                "Hiragino / MS Mincho"
            ])
            self.font_combo.setCurrentIndex(self.settings.value("output_font_index", 0, type=int))
            self.font_combo.currentIndexChanged.connect(self.apply_output_font)
            self.font_combo.currentIndexChanged.connect(self.save_settings)
            
            font_layout.addWidget(self.font_combo)
            
            # 여백을 추가하여 폰트 콤보는 왼쪽에, 체크박스는 오른쪽에 밀착시킴
            font_layout.addStretch()

            # LaTeX 확장 입력 토글 (모든 입력 메서드에 전역 적용)
            self.latex_cb = QCheckBox("LaTeX 확장 입력")
            self.latex_cb.setToolTip(
                "확장 라틴문자와 유니코드 코드포인트를 실제 문자로 렌더링합니다.\n"
                "예) \\'e → é   \\v{s} → š   \\ss → ß   \\xAC00 → 가   \\x{1F600} → 😀"
            )
            self.latex_cb.setChecked(self.settings.value("latex_expand", True, type=bool))
            set_latex_expand(self.latex_cb.isChecked())
            self.latex_cb.stateChanged.connect(self.on_latex_toggle)
            font_layout.addWidget(self.latex_cb)

            self.clear_after_send_cb = QCheckBox("전송 후 초기화")
            # 설정값 복원 (기본값은 True로 설정하여 기존 동작 유지)
            self.clear_after_send_cb.setChecked(self.settings.value("clear_after_send", True, type=bool))
            self.clear_after_send_cb.stateChanged.connect(self.save_settings)
            font_layout.addWidget(self.clear_after_send_cb)
            
            self.send_prev_cb = QCheckBox("직전 창 전송")
            # 설정값 복원 (기본값은 False)
            self.send_prev_cb.setChecked(self.settings.value("send_prev_window", False, type=bool))
            self.send_prev_cb.stateChanged.connect(self.save_settings)
            
            font_layout.addWidget(self.send_prev_cb)
            # -----------------------------------
            
            main_layout.addLayout(font_layout)
            
            # 하단 버튼 컨트롤 타워
            btn_layout = QHBoxLayout()
            
            self.send_btn = QPushButton("클립보드로 전송 (Enter)")
            self.send_btn.clicked.connect(self.send_to_editor)
            btn_layout.addWidget(self.send_btn)
            
            self.undo_btn = QPushButton("직전 전송 복구 (Alt+Z)")
            self.undo_btn.clicked.connect(self.undo_send)
            btn_layout.addWidget(self.undo_btn)
            
            self.clear_btn = QPushButton("지우기 (ESC)")
            self.clear_btn.clicked.connect(self.clear_text)
            btn_layout.addWidget(self.clear_btn)
            
            main_layout.addLayout(btn_layout)
            
            # 상태 표시줄 및 전역 단축키 맵
            self.status_bar = QStatusBar()
            main_layout.addWidget(self.status_bar)
            
            QShortcut(QKeySequence("Escape"), self, self.clear_text)
            QShortcut(QKeySequence("Alt+Z"), self, self.undo_send)
            QShortcut(QKeySequence("F1"), self, self.show_help)
            
            self.input_edit.installEventFilter(self)
            self.input_edit.setFocus()
            
            # 초기 폰트 적용
            self.apply_output_font(self.font_combo.currentIndex())

            # 한자 검색 보조창 초기화
            self.kanji_assistant = KanjiAssistant(self)
            self.kanji_assistant.kanji_selected.connect(self.insert_kanji_to_editor)
            
            # F10: 보조창 토글
            self.shortcut_f10 = QShortcut(QKeySequence("F10"), self)
            self.shortcut_f10.activated.connect(self.toggle_kanji_assistant)
            
            # Ctrl+F: 보조창 검색 필드로 포커스 이동
            self.shortcut_alt_f = QShortcut(QKeySequence("Ctrl+F"), self)
            # QApplication 차원에서 이 단축키를 잡아야 보조창이 활성화되어 있을 때도 먹힙니다.
            self.shortcut_alt_f.setContext(Qt.ShortcutContext.ApplicationShortcut)
            self.shortcut_alt_f.activated.connect(self.focus_kanji_search)

        def apply_output_font(self, index):
            font_families = self.font_mapping.get(index, ("Noto Sans CJK KR",))
            
            font = QFont()
            font.setFamilies(font_families)
            font.setPointSize(20)
            
            self.output_edit.setFont(font)

        def get_hanja_mode_str(self):
            return ["none", "shinjitai", "kyujitai", "simplified"][self.hanja_combo.currentIndex()]

        def update_translation(self):
            if getattr(self, '_is_sending', False):
                return  # 전송 중일 때는 시그널이 발생해도 무조건 즉시 탈출!
    
            input_text = self.input_edit.toPlainText()
            global_modes = ["pm", "frkim", "pmfrk", "rrk", "dubeol", "kana", "transparent", "dubeol_rev"]
            norm_mode = "NFC" if self.norm_combo.currentIndex() == 1 else "NFD"
            result = convert_input(input_text,
                                   engine_mode=global_modes[self.mode_combo.currentIndex()],
                                   hanja_mode=self.get_hanja_mode_str(),
                                   norm_mode=norm_mode)
            self.output_edit.setPlainText(result)

        def on_latex_toggle(self):
            set_latex_expand(self.latex_cb.isChecked())
            self.save_settings()
            self.update_translation()

        def save_settings(self):
            self.settings.setValue("latex_expand", self.latex_cb.isChecked())
            self.settings.setValue("engine_mode_index", self.mode_combo.currentIndex())
            self.settings.setValue("hanja_mode_index", self.hanja_combo.currentIndex())
            self.settings.setValue("norm_mode_index", self.norm_combo.currentIndex())
            self.settings.setValue("output_font_index", self.font_combo.currentIndex())
            self.settings.setValue("send_prev_window", self.send_prev_cb.isChecked())
            self.settings.setValue("clear_after_send", self.clear_after_send_cb.isChecked())

        def clear_text(self):
            # 청소 시작 전 현재 원문을 안전하게 백업
            current_input = self.input_edit.toPlainText()
            
            if current_input.strip():  # 비어있지 않을 때만 백업 (의미 있는 데이터 보호)
                self._last_sent_input = current_input
                
                # 가드 가동 (clear 과정에서 실시간 번역 이벤트 트리거 방지)
                self._is_sending = True
                
                self.input_edit.clear()
                self.output_edit.clear()
                
                # 가드 해제
                self._is_sending = False
                
                self.status_bar.showMessage("작업 내역 초기화됨 (ESC) - 복구 가능", 2000)
            else:
                # 이미 비어있는 상태라면 그냥 깔끔하게 청소 처리
                self.input_edit.clear()
                self.output_edit.clear()
                self.status_bar.showMessage("작업 내역 초기화됨 (ESC)", 2000)

        def send_to_editor(self):
            txt = self.output_edit.toPlainText() 
            if txt:
                # 1단계: 청소 시작 전 현재 원문을 완벽하게 변수에 고정
                current_input = self.input_edit.toPlainText()
                
                if copy_to_clipboard(txt):
                    self.status_bar.showMessage("클립보드 복사 완료", 2000)
                    
                    # 2단계: 복사 성공 직후 안전하게 백업 전역 변수에 안착
                    self._last_sent_input = current_input
                    
                    # --- 수정된 부분: 전송 후 초기화 여부 체크 ---
                    if self.clear_after_send_cb.isChecked():
                        # 3단계: 가드 성벽 가동 (update_translation의 접근을 원천 봉쇄)
                        self._is_sending = True
                        
                        # 4단계: 안심하고 양쪽 창 청소 수행
                        self.input_edit.clear()
                        self.output_edit.clear()
                        
                        # 5단계: 청소 작전 종료 후 성벽 해제
                        self._is_sending = False
                    else:
                        # 초기화를 하지 않더라도 백업은 이미 완료되었으므로 알림 상태 유지 및 통과
                        pass
                    # --------------------------------------------
                    
                    # 6단계: '직전 창 전송' 체크박스가 켜져 있다면 포커스 이동 및 붙여넣기 실행
                    if self.send_prev_cb.isChecked():
                        import platform
                        import time
                        current_os = platform.system()
                        
                        if current_os == "Darwin":
                            import subprocess
                            script = '''
                            tell application "System Events"
                                keystroke tab using command down
                                delay 0.3
                                keystroke "v" using command down
                            end tell
                            '''
                            subprocess.run(['osascript', '-e', script])
                            self.status_bar.showMessage("직전 창으로 전송 및 붙여넣기 완료!", 3000)
                            
                        elif current_os == "Windows":
                            try:
                                import pyautogui
                                pyautogui.keyUp('ctrl')
                                pyautogui.hotkey('alt', 'tab')
                                time.sleep(0.3)
                                pyautogui.hotkey('ctrl', 'v')
                                self.status_bar.showMessage("직전 창으로 전송 및 붙여넣기 완료!", 3000)
                            except ImportError:
                                # pyautogui가 설치되어 있지 않은 경우의 안전 장치
                                self.status_bar.showMessage("⚠️ pyautogui 누락: 클립보드 복사만 수행되었습니다.", 3000)
                else:
                    self.status_bar.showMessage("❌ 클립보드 복사 실패! 입력을 유지합니다.", 3000)

        def undo_send(self):
            if self._last_sent_input:
                self.input_edit.setPlainText(self._last_sent_input)
                self._last_sent_input = ""
                self.status_bar.showMessage("이전 입력 복구 완료", 2000)
            else:
                self.status_bar.showMessage("❌ 복구할 내역이 없습니다.", 2000)

        def eventFilter(self, obj, event):
            """입력창 키 필터: Enter는 전송, Shift+Enter는 개행만 순수하게 분리"""
            if obj is self.input_edit and event.type() == event.Type.KeyPress:
                if event.key() in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
                    modifiers = event.modifiers()
                    
                    # 오직 Enter만 단독으로 눌린 경우 -> 클립보드로 전송
                    if not (modifiers & Qt.KeyboardModifier.ShiftModifier):
                        self.send_to_editor()
                        return True
                    
            return super().eventFilter(obj, event)


        def toggle_kanji_assistant(self):
            if self.kanji_assistant.isVisible():
                self.kanji_assistant.hide()
                self.input_edit.setFocus()  # 창을 닫으면 메인 에디터로 포커스 복귀
            else:
                self.kanji_assistant.show()
                self.kanji_assistant.search_input.setFocus()
                self.kanji_assistant.search_input.selectAll()

        def focus_kanji_search(self):
            if self.kanji_assistant.isVisible():
                self.kanji_assistant.activateWindow()
                self.kanji_assistant.search_input.setFocus()
                self.kanji_assistant.search_input.selectAll()

        def insert_kanji_to_editor(self, kanji_text):
            # 1. 텍스트 삽입
            cursor = self.input_edit.textCursor()
            cursor.insertText(kanji_text)
            
            # 2. 보조창 검색창 비우기 (다음 검색을 위해)
            self.kanji_assistant.search_input.clear()
            
            # 3. 메인 윈도우 자체를 활성화한 뒤, 에디터에 포커스 주기
            self.activateWindow()       # OS 레벨에서 메인 창으로 포커스를 가져옴
            self.input_edit.setFocus()  # 그 안의 입력 에디터에 커서를 깜빡이게 함

        def show_help(self):
            help_dialog = QDialog(self)
            help_dialog.setWindowTitle("pmIME 도움말 및 가이드")
            help_dialog.resize(500, 480)
            layout = QVBoxLayout(help_dialog)
            
            browser = QTextBrowser()
            browser.setOpenExternalLinks(True)
            
            help_html = """
            <h3>💡 행별 독립 제어 % 매직 태그 신택스</h3>
            <p>각 행의 <b>맨 첫머리</b>에 아래 태그를 붙이면 해당 줄만 독립 엔진으로 작동합니다.</p>
            <table border="1" cellpadding="5" style="border-collapse:collapse; border-color:#ccc; width:100%;">
                <tr bgcolor="#f2f2f2"><th>매직 태그</th><th>글자 변환 메서드 (엔진 종류)</th></tr>
                <tr><td><b>%pm </b></td><td>pm 방식 (음절 구분자: /)</td></tr>
                <tr><td><b>%frk </b></td><td>frkim 방식 (자동 청크 분리, 음절 구분자: ')</td></tr>
                <tr><td><b>%mix </b></td><td>pmfrk 혼합 방식 (자동 청크 분리)</td></tr>
                <tr><td><b>%jp </b></td><td>일본어 로마자 -> 카나(Kana) 변환 모드</td></tr>
                <tr><td><b>%clean </b></td><td>변환없음 (+ 날짜·시간 자리표시자 <code>{YY-MM-DD}</code> <code>{hh:mm:ss}</code> → 지금 시각. YYYY/YY 연, MM 월, DD 일, hh 12시간제·HH 24시간제 시, mm 분, ss 초. 그 밖의 글자는 그대로)</td></tr>
            </table>
            <br>
            <h4>🎯 대괄호 한자 필터 옵션 (메서드 태그에 밀착 지정)</h4>
            <p>태그 뒤에 스페이스 없이 대괄호로 한자 옵션을 주어 행별 자형 필터를 강제합니다.</p>
            <ul>
                <li><b>%pm[shin] </b> : pm 방식 + 일본어 신자체(新字体) 필터</li>
                <li><b>%frk[kyu] </b> : frkim 방식 + 일본어 구자체(旧字体) 필터</li>
                <li><b>%mix[sim] </b> : pmfrk 방식 + 중국어 간체(简体) 필터</li>
                <li><i>※ 옵션 생략 시(예: %pm) 상단 콤보박스의 글로벌 설정을 그대로 추종합니다.</i></li>
            </ul>
            <hr>
            <h3>🔤 LaTeX 확장 라틴문자 (입력 메서드 무관, 전역 적용)</h3>
            <p>하단 <b>[LaTeX 확장 입력]</b> 체크 시, 어떤 엔진 모드에서도 아래 표기가 실제 문자로 렌더링됩니다.
            결과 문자는 한글 변환 대상에서 제외되므로 로마자 사이에 섞어 써도 안전합니다.</p>
            <table border="1" cellpadding="4" style="border-collapse:collapse; border-color:#ccc; width:100%;">
                <tr bgcolor="#f2f2f2"><th>입력</th><th>결과</th><th>입력</th><th>결과</th></tr>
                <tr><td>\\'e \\`e \\^e \\"o \\~n</td><td>é è ê ö ñ</td><td>\\=a \\.z \\u{g} \\v{s}</td><td>ā ż ğ š</td></tr>
                <tr><td>\\H{o} \\r{a} \\c{c} \\k{a}</td><td>ő å ç ą</td><td>\\d{s} \\b{h} \\t{oo}</td><td>ṣ ẖ o͡o</td></tr>
                <tr><td>\\ss \\ae \\oe \\o \\l</td><td>ß æ œ ø ł</td><td>\\i \\j \\th \\dh \\ng</td><td>ı ȷ þ ð ŋ</td></tr>
                <tr><td>\\'{\\i} \\'{\\v{s}}</td><td>í š́ (중첩 가능)</td><td>\\textemdash \\texteuro \\%</td><td>— € %</td></tr>
            </table>
            <p><i>※ 액센트 이름이 영문자인 명령(\\v \\u \\c \\d \\t 등)은 TeX 규칙대로 <b>{ } 또는 공백</b>이 뒤따를 때만
            동작합니다. 따라서 \\textbf, \\begin 같은 일반 명령과 충돌하지 않습니다.</i></p>
            <hr>
            <h3>#️⃣ 유니코드 코드포인트 직접 입력</h3>
            <ul>
                <li><b>\\xAC00</b> → 가 &nbsp;(16진수 4자리 직접 표기)</li>
                <li><b>\\x{AC00}</b>, <b>\\x{1F600}</b> → 가, 😀 &nbsp;(중괄호형: 1~6자리, BMP 밖도 가능)</li>
                <li><b>\\x{1112 1161 11AB}</b> → 한 &nbsp;(공백·쉼표로 여러 코드포인트 나열, 첫가끝 조합에 유용)</li>
                <li><b>\\x{U+AC00}</b>, <b>\\x{0xAC00}</b> → 가 &nbsp;(U+ / 0x 접두사 허용)</li>
                <li><b>\\uAC00</b>, <b>\\U0001F600</b> → 가, 😀 &nbsp;(각각 4자리·8자리 고정)</li>
                <li><b>\\char"AC00</b>, <b>\\char'101</b>, <b>\\char97</b> → 가, A, a &nbsp;(TeX식 16/8/10진수)</li>
                <li>잘못된 코드포인트(범위 밖·서로게이트·비16진수)는 <b>원문 그대로</b> 남습니다.</li>
                <li>확장을 피하려면 백슬래시를 겹쳐 쓰십시오: <b>\\\\'e</b> 는 변환되지 않습니다.</li>
            </ul>
            <p><i>※ NFD 출력 시에도 라틴 확장문자는 결합형(NFC)으로 유지되며, 한글만 분해됩니다.</i></p>
            <hr>
            <h3>⌨️ 시스템 통합 핵심 핫키 (키보드 동작 규칙)</h3>
            <ul>
                <li><b style="color:#d9534f;">Enter</b> : <b>클립보드로 전송</b> (출력 텍스트 복사 후 입력/출력창 모두 자동 청소)</li>
                <li><b style="color:#f0ad4e;">Shift + Enter</b> : <b>행 나누기 (줄바꿈)</b> (멀티레이어 태그 라인 작성용 개행)</li>
                <li><b style="color:#337ab7;">Alt + Z</b> : <b>전송 취소 (Undo)</b> (방금 전송되어 지워진 로마자 원문 복구)</li>
                <li><b>Escape (ESC)</b> : <b>작업 내역 전체 지우기</b> (입력필드 및 출력필드 즉시 초기화)</li>
                <li><b>F1</b> : <b>본 도움말 가이드 팝업</b></li>
                <li><b>F10</b>: <b>일본어 한자 입력 보조창 토글</b></li>
            </ul>
            <br>
            <p style="color:#666; font-size:11px;">※ 상세한 자모 로마자 매핑 테이블 규칙은 외부 동반 명세 문서를 참조하십시오.</p>
            """
            
            browser.setHtml(help_html)
            layout.addWidget(browser)
            help_dialog.exec()


def main():
    import sys
    import os
    import argparse
    import stat

    parser = argparse.ArgumentParser(description="pmIME Case-Sensitive Converter")
    parser.add_argument('-v', '--version', action='version', version=f'%(prog)s {__version__}')
    parser.add_argument('-i', '--input', type=str, help='입력 파일 경로')
    parser.add_argument('-o', '--output', type=str, help='출력 파일 경로')
    parser.add_argument('--macro', type=str, default='jamoword', help='LaTeX 매크로 변환 타겟')
    # parser.add_argument('--macro', type=str, default=None, help='LaTeX 매크로 변환 타겟 (기본적으로 전체 변환, 지정 시 해당 매크로만 변환)')
    parser.add_argument('--env', type=str, help='LaTeX 환경 변환 타겟')
    parser.add_argument('--keep', action='store_true', help='LaTeX 구조 기호 보존')
    
    parser.add_argument('--mode', choices=['pm', 'frk', 'mix', 'rrk', 'du', 'ed', 'jp', 'clean'], default='pm', help='변환 엔진 모드 선택 (기본값: pm)')
    parser.add_argument('--hanja', choices=['none', 'shin', 'kyu', 'sim', 'han'], default='none', help='한자 변환 필터 (기본값: none)')

    parser.add_argument('--no-latex', action='store_true', help='LaTeX 확장 라틴문자/코드포인트 입력 확장을 끔')
    parser.add_argument('--latex-all', action='store_true', help='--macro/--env 문서 모드에서도 문서 전체에 LaTeX 확장 입력 적용')

    parser.add_argument('-n', '--nfc', action='store_true', help='출력 한글을 NFC로 결합 정규화')
    parser.add_argument('-c', '--clip', action='store_true', help='클립보드 전송')
    
    parser.add_argument('-r', '--raw', action='store_true', help='입력 텍스트 전체 변환 (파일 또는 파이프)')
    
    parser.add_argument('text', nargs='?', help='변환할 로마자 문자열')
    
    args = parser.parse_args()

    mode_map = {
        'pm': 'pm', 'frk': 'frkim', 'mix': 'pmfrk', 'rrk': 'rrk', 'du': 'dubeol', 'ed': 'dubeol_rev',
        'jp': 'kana', 'clean': 'transparent'
    }
    hanja_map = {
        'none': 'none', 'shin': 'shinjitai', 'kyu': 'kyujitai', 
        'sim': 'simplified', 'han': 'hanja'
    }
    
    actual_mode = mode_map[args.mode]
    actual_hanja = hanja_map[args.hanja]

    # LaTeX 확장 입력 전역 스위치
    set_latex_expand(not args.no_latex)
    # --------------------------------------------------------------
    
    has_piped_input = False
    if sys.stdin is not None:
        try: 
            has_piped_input = stat.S_ISFIFO(os.fstat(sys.stdin.fileno()).st_mode) or stat.S_ISREG(os.fstat(sys.stdin.fileno()).st_mode)
        except Exception: 
            pass

    if args.text or args.input or has_piped_input:
        input_text = ""
        if args.text: 
            input_text = args.text
        elif args.input:
            with open(args.input, 'r', encoding='utf-8') as f: 
                input_text = f.read()
        elif has_piped_input:
            input_text = sys.stdin.buffer.read().decode('utf-8', errors='replace') if hasattr(sys.stdin, 'buffer') else sys.stdin.read()
                
        if not input_text.strip(): 
            sys.exit(0)

        if args.raw:
            output_text = convert_text(input_text, engine_mode=actual_mode)
        elif (args.input or has_piped_input) and ("<jp>" in input_text or "<kr>" in input_text):
            output_text = process_tags_mixed(input_text)
        elif args.env or (args.macro and (args.input or has_piped_input)):
            # 환경(env)과 매크로(macro) 둘 다 순차적으로 변환
            output_text = input_text
            
            if args.env:
                output_text = process_latex_text(output_text, target_name=args.env, mode="env", keep_structure=args.keep, engine_mode=actual_mode)
            
            if args.macro and (args.input or has_piped_input):
                output_text = process_latex_text(output_text, target_name=args.macro, mode="macro", keep_structure=args.keep, engine_mode=actual_mode)
        else:
            output_text = convert_text(input_text, engine_mode=actual_mode)
        
        # 문서 모드(--macro/--env)는 기본적으로 변환 대상 구간에서만 확장된다.
        # --latex-all 지정 시 문서 전체에 적용.
        if args.latex_all:
            output_text = expand_latex_input(output_text)

        output_text = filter_kanji(output_text, hanja_mode=actual_hanja)

        if actual_mode not in ["kana", "transparent"]:
            output_text = normalize_output(output_text, norm_mode="NFC" if args.nfc else "NFD")
        
        if args.clip: 
            copy_to_clipboard(output_text)
            
        if args.output:
            with open(args.output, 'w', encoding='utf-8') as f: 
                f.write(output_text)
        else:
            if hasattr(sys.stdout, 'buffer'):
                sys.stdout.buffer.write((output_text + '\n').encode('utf-8'))
            else:
                sys.stdout.write(output_text + '\n')
        sys.exit(0)
    else:
        if not GUI_AVAILABLE:
            print("Error: GUI에 필요한 패키지가 없습니다.", file=sys.stderr)
            sys.exit(1)
        app = QApplication(sys.argv)
        win = MainWindow()
        win.show()
        sys.exit(app.exec())


if __name__ == '__main__':
    main()
