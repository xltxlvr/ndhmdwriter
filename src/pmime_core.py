# pmIME-Multilingual Engine — core (Qt 비의존 변환 엔진)
#
# (C) 2026 Nova de Hi
# GPLv3
#
# pmimegui.py(PyQt6 단독 앱)와 ndhmdWriter.py(PySide6 보조 입력기)가 함께 쓰는 코어.
# 변환 규칙·사전은 오직 여기서만 고친다. GUI/클립보드 코드는 이 파일에 없다.
#
# version 0.19.0 (2026-11-12), 히브리어 엔진 he(`%he`, Michigan–Claremont 방식 → 마소라 히브리어) 추가
# version 0.18.0 (2026-11-12), 고전 그리스어 엔진 grc(`%grc`, Beta Code → 폴리토닉 그리스어 NFC) 추가
# version 0.13.2 (2026-10-22), 사용자 한자 사전 API(add/update/delete_custom_word), 사용자 데이터 폴더, 삭제 반영 버그 수정
# version 0.13.1 (2026-10-21), pmimegui.py 에서 코어를 분리 (동작 변경 없음; 데이터 폴더 지정 추가)
#
import sys
import os
import platform
import unicodedata
import re
import json

__version__ = "0.19.0"

def resource_path(relative_path):
    try:
        base_path = sys._MEIPASS
    except AttributeError:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)


# ==============================================================================
# pm map
# ==============================================================================
pm_map = {
  "cho": {
    "ᄀ": "g", "ᄁ": "gg", "ᄂ": "n", "ᄃ": "d", "ᄄ": "dd", "ᄅ": "r", "ᄆ": "m", "ᄇ": "b", "ᄈ": "bb", "ᄉ": "s",
    "ᄊ": "ss", "ᄋ": "q", "ᄌ": "j", "ᄍ": "jj", "ᄎ": "c", "ᄏ": "k", "ᄐ": "t", "ᄑ": "p", "ᄒ": "h", 
    "ᄓ": "ng", "ᄔ": "nn", "ᄕ": "nd", "ᄖ": "nb", "ᄗ": "dg", "ᄘ": "rn", "ᄙ": "rr", "ᄚ": "rh", "ᄛ": "rq",
    "ᄜ": "mb", "ᄝ": "mq", "ᄞ": "bg", "ᄟ": "bn", "ᄠ": "bd", "ᄡ": "bs", "ᄢ": "bsg", "ᄣ": "bsd", "ᄤ": "bsb",
    "ᄥ": "bss", "ᄦ": "bsj", "ᄧ": "bj", "ᄨ": "bc", "ᄩ": "bt", "ᄪ": "bp", "ᄫ": "bq", "ᄬ": "bbq", "ᄭ": "sg",
    "ᄮ": "sn", "ᄯ": "sd", "ᄰ": "sr", "ᄱ": "sm", "ᄲ": "sb", "ᄳ": "sbg", "ᄴ": "sss", "ᄵ": "sf", "ᄶ": "sj",
    "ᄷ": "sc", "ᄸ": "sk", "ᄹ": "st", "ᄺ": "sp", "ᄻ": "sh", "ᄼ": "sl", "ᄽ": "ssl", "ᄾ": "slr", "ᄿ": "sslr",
    "ᅀ": "z", "ᅁ": "qg", "ᅂ": "qd", "ᅃ": "qm", "ᅄ": "qb", "ᅅ": "qs", "ᅆ": "qz", "ᅇ": "qq", "ᅈ": "qj",
    "ᅉ": "qc", "ᅊ": "qt", "ᅋ": "qp", "ᅌ": "f", "ᅍ": "jq", "ᅎ": "jl", "ᅏ": "jjl", "ᅐ": "jlr", "ᅑ": "jjlr",
    "ᅒ": "ck", "ᅓ": "ch", "ᅔ": "cl", "ᅕ": "clr", "ᅖ": "pb", "ᅗ": "pq", "ᅘ": "hh", "ᅙ": "x",
    "ᅚ": "gd", "ᅛ": "ns", "ᅜ": "nj", "ᅝ": "nh", "ᅞ": "dr",
    "ꥠ": "dm", "ꥡ": "db", "ꥢ": "ds", "ꥣ": "dj", "ꥤ": "rg", "ꥥ": "rgg", "ꥦ": "rd", "ꥧ": "rdd", "ꥨ": "rm",
    "ꥩ": "rb", "ꥪ": "rbb", "ꥫ": "rbq", "ꥬ": "rs", "ꥭ": "rj", "ꥮ": "rk", "ꥯ": "mg", "ꥰ": "md", "ꥱ": "ms",
    "ꥲ": "bst", "ꥳ": "bk", "ꥴ": "bh", "ꥵ": "ssb", "ꥶ": "qr", "ꥷ": "qh", "ꥸ": "jjh", "ꥹ": "tt", "ꥺ": "ph",
    "ꥻ": "hs", "ꥼ": "xx", "\u115F": "w"
  },
  "jung": {
    "ᅡ": "a", "ᅢ": "ay", "ᅣ": "ya", "ᅤ": "yay", "ᅥ": "e", "ᅦ": "ey", "ᅧ": "ye", "ᅨ": "yey",
    "ᅩ": "o", "ᅪ": "oa", "ᅫ": "oay", "ᅬ": "oy", "ᅭ": "yo", "ᅮ": "u", "ᅯ": "ue", "ᅰ": "uey",
    "ᅱ": "uy", "ᅲ": "yu", "ᅳ": "v", "ᅴ": "vy", "ᅵ": "i",
    "ᅶ": "ao", "ᅷ": "au", "ᅸ": "yao", "ᅹ": "yayo", "ᅺ": "eo", "ᅻ": "eu", "ᅼ": "ev", "ᅽ": "yeo",
    "ᅾ": "yeu", "ᅿ": "oe", "ᆀ": "oey", "ᆁ": "oyey", "ᆂ": "oo", "ᆃ": "ou", "ᆄ": "yoya", "ᆅ": "yoyay",
    "ᆆ": "yoye", "ᆇ": "yoo", "ᆈ": "yoi", "ᆉ": "ua", "ᆊ": "uay", "ᆋ": "uev", "ᆌ": "uyey", "ᆍ": "uu",
    "ᆎ": "yua", "ᆏ": "yue", "ᆐ": "yuey", "ᆑ": "yuye", "ᆒ": "yuyey", "ᆓ": "yuu", "ᆔ": "yui", "ᆕ": "vu",
    "ᆖ": "vv", "ᆗ": "viu", "ᆘ": "ia", "ᆙ": "iya", "ᆚ": "io", "ᆛ": "iu", "ᆜ": "iv", "ᆝ": "i@",
    "ᆞ": "@", "ᆟ": "@e", "ᆠ": "@u", "ᆡ": "@i", "ᆢ": "@@", "ᆣ": "av", "ᆤ": "yau", "ᆥ": "yeya",
    "ᆦ": "oya", "ᆧ": "oyay",
    "ힰ": "oye", "ힱ": "ooi", "ힲ": "yoa", "ힳ": "yoay", "ힴ": "yoe", "ힵ": "uye", "ힶ": "uii", "ힷ": "yuay",
    "ힸ": "yuo", "ힹ": "va", "ힺ": "ve", "ힻ": "vey", "ힼ": "vo", "ힽ": "iyao", "ힾ": "iyay", "ힿ": "iye",
    "ퟀ": "iyey", "ퟁ": "ioi", "ퟂ": "iyo", "ퟃ": "iyu", "ퟄ": "ii", "ퟅ": "@a", "ퟆ": "@ey",
    "\u1160": "*"
  },
  "jong": {
    "ᆨ": "g", "ᆩ": "gg", "ᆪ": "gs", "ᆫ": "n", "ᆬ": "nj", "ᆭ": "nh", "ᆮ": "d",
    "ᆯ": "r", "ᆰ": "rg", "ᆱ": "rm", "ᆲ": "rb", "ᆳ": "rs", "ᆴ": "rt", "ᆵ": "rp",
    "ᆶ": "rh", "ᆷ": "m", "ᆸ": "b", "ᆹ": "bs", "ᆺ": "s", "ᆻ": "ss", "ᆼ": "q",
    "ᆽ": "j", "ᆾ": "c", "ᆿ": "k", "ᇀ": "t", "ᇁ": "p", "ᇂ": "h", "ᇃ": "gr",
    "ᇄ": "gsg", "ᇅ": "ng", "ᇆ": "nd", "ᇇ": "ns", "ᇈ": "nz", "ᇉ": "nt", "ᇊ": "dg",
    "ᇋ": "dr", "ᇌ": "rgs", "ᇍ": "rn", "ᇎ": "rd", "ᇏ": "rdh", "ᇐ": "rr", "ᇑ": "rmg",
    "ᇒ": "rms", "ᇓ": "rbs", "ᇔ": "rbh", "ᇕ": "rbq", "ᇖ": "rss", "ᇗ": "rz", "ᇘ": "rk",
    "ᇙ": "rx", "ᇚ": "mg", "ᇛ": "mr", "ᇜ": "mb", "ᇝ": "ms", "ᇞ": "mss", "ᇟ": "mz",
    "ᇠ": "mc", "ᇡ": "mh", "ᇢ": "mq", "ᇣ": "br", "ᇤ": "bp", "ᇥ": "bh", "ᇦ": "bq",
    "ᇧ": "sg", "ᇨ": "sd", "ᇩ": "sr", "ᇪ": "sb", "ᇫ": "z", "ᇬ": "fg", "ᇭ": "fgg",
    "ᇮ": "ff", "ᇯ": "fk", "ᇰ": "f", "ᇱ": "fs", "ᇲ": "fz", "ᇳ": "pb", "ᇴ": "pq",
    "ᇵ": "hn", "ᇶ": "hr", "ᇷ": "hm", "ᇸ": "hb", "ᇹ": "x", "ᇺ": "gn", "ᇻ": "gb",
    "ᇼ": "gc", "ᇽ": "gk", "ᇾ": "gh", "ᇿ": "nn", "ퟋ": "nr", "ퟌ": "nc", "ퟍ": "dd",
    "ퟎ": "ddb", "ퟏ": "db", "ퟐ": "ds", "ퟑ": "dsg", "ퟒ": "dj", "ퟓ": "dc", "ퟔ": "dt",
    "ퟕ": "rgg", "ퟖ": "rgh", "ퟗ": "rrz", "ퟘ": "rmh", "ퟙ": "rbd", "ퟚ": "rbp",
    "ퟛ": "rf", "ퟜ": "rfh", "ퟝ": "rq", "ퟞ": "mn", "ퟟ": "mnn", "ퟠ": "mm", "ퟡ": "mbs",
    "ퟢ": "mj", "ퟣ": "bd", "ퟤ": "brp", "ퟥ": "bm", "ퟦ": "bb", "ퟧ": "bsd", "ퟨ": "bj",
    "ퟩ": "bc", "ퟪ": "sm", "ퟫ": "sbq", "ퟬ": "ssg", "ퟭ": "ssd", "ퟮ": "sz", "ퟯ": "sj",
    "ퟰ": "sc", "ퟱ": "st", "ퟲ": "sh", "ퟳ": "zb", "ퟴ": "zbq", "ퟵ": "fm", "ퟶ": "fh",
    "ퟷ": "jb", "ퟸ": "jbb", "ퟹ": "jj", "ퟺ": "ps", "ퟻ": "pt"
  },
  "generic": {
    "ㄱ": "G", "ㄲ": "GG", "ㄴ": "N", "ㄷ": "D", "ㄸ": "DD", "ㄹ": "R", "ㅁ": "M", "ㅂ": "B", "ㅃ": "BB", "ㅅ": "S", "ㅆ": "SS", "ㅇ": "Q", "ㅈ": "J", "ㅊ": "C", "ㅋ": "K", "ㅌ": "T", "ㅍ": "P", "ㅎ": "H",
    "ㄳ": "GS", "ㄵ": "NJ", "ㄶ": "NH", "ㄺ": "RG", "ㄻ": "RM", "ㄼ": "RB", "ㄽ": "RS", "ㄾ": "RT", "ㄿ": "RP", "ㅀ": "RH", "ㅄ": "BS", 
    "ㆁ": "F", "ㅿ": "Z", "ㆆ": "X", "ㅸ": "BQ",
    "ㅏ": "A", "ㅐ": "AY", "ㅑ": "YA", "ㅒ": "YAY", "ㅓ": "E", "ㅔ": "EY", "ㅕ": "YE", "ㅖ": "YEY", "ㅗ": "O", "ㅘ": "OA", "ㅙ": "OAY", "ㅚ": "OY", "ㅛ": "YO", "ㅜ": "U", "ㅝ": "UE", "ㅞ": "UEY", "ㅟ": "UY", "ㅠ": "YU", "ㅡ": "V", "ㅢ": "VY", "ㅣ": "I", "ㆍ": "AA"
  }
}

frk_map = {
    "cho": {
        "ᄀ": "g", "ᄁ": "G", "ᄂ": "n", "ᄃ": "d", "ᄄ": "D", "ᄅ": "r", "ᄆ": "m", "ᄇ": "b", "ᄈ": "B",
        "ᄉ": "s", "ᄊ": "S", "ᄋ": "x", "ᄌ": "j", "ᄍ": "J", "ᄎ": "c", "ᄏ": "k", "ᄐ": "t", "ᄑ": "p", "ᄒ": "h",
        "ᅀ": "z", "ᅌ": "Q", "ᅙ": "X", "ᄫ": "v",
        "ᄡ": "bs", "ᄠ": "bd", "ᄢ": "bsg", "ᄣ": "bsd", "ᄦ": "bsj",
        "ᄭ": "sg", "ᄯ": "sd", "ᄰ": "sr", "ᄲ": "sb", "ᄶ": "sj", "ᄷ": "sc", "ᄸ": "sk", "ᄹ": "st", "ᄺ": "sp",
        "\u115F": "w"
    },
    "jung": {
        "ᅡ": "a", "ᅢ": "ai", "ᅣ": "ia", "ᅤ": "iai", "ᅥ": "e", "ᅦ": "ei", "ᅧ": "ie", "ᅨ": "iei",
        "ᅩ": "o", "ᅪ": "oa", "ᅫ": "oai", "ᅬ": "oi", "ᅭ": "io", "ᅮ": "u", "ᅯ": "ue", "ᅰ": "uei",
        "ᅱ": "ui", "ᅲ": "iu", "ᅳ": "y", "ᅴ": "yi", "ᅵ": "i", "ᆞ": "@", "ᆡ": "@i", "ᆢ": "@@",
        "\u1160": "*"
    },
    "jong": {
        "ᆨ": "g", "ᆩ": "G", "ᆪ": "gs", "ᆫ": "n", "ᆬ": "nj", "ᆭ": "nh", "ᆮ": "d",
        "ᆯ": "r", "ᆰ": "rg", "ᆱ": "rm", "ᆲ": "rb", "ᆳ": "rs", "ᆴ": "rt", "ᆵ": "rp",
        "ᆶ": "rh", "ᆷ": "m", "ᆸ": "b", "ᆹ": "bs", "ᆺ": "s", "ᆻ": "S", "ᆼ": "q",
        "ᆽ": "j", "ᆾ": "c", "ᆿ": "k", "ᇀ": "t", "ᇁ": "p", "ᇂ": "h",
        "ᇰ": "Q", 
        "ᇦ": "v", 
        "ᇙ": "rX", 
        "ᇹ": "X", 
        "ᇚ": "mg", 
        "ᇧ": "sg", 
        "ᇨ": "sd", 
        "ᇩ": "sr", 
        "ᇪ": "sb"
    }
}

rrk_map = {
    "cho": {
        "ᄀ": "g", "ᄁ": "kk", "ᄂ": "n", "ᄃ": "d", "ᄄ": "tt", "ᄅ": "l", "ᄆ": "m", "ᄇ": "b", "ᄈ": "pp",
        "ᄉ": "s", "ᄊ": "ss", "ᄋ": "", "ᄌ": "j", "ᄍ": "jj", "ᄎ": "ch", "ᄏ": "k", "ᄐ": "t", "ᄑ": "p", "ᄒ": "h",
        "ᄭ": "sg", "ᄯ": "sd", "ᄰ": "sl", "ᄲ": "sb", "ᄶ": "sj", "ᄷ": "sch", "ᄸ": "sk", "ᄹ": "st", "ᄺ": "sp",
    },
    "jung": {
        "ᅡ": "a", "ᅢ": "ae", "ᅣ": "ya", "ᅤ": "yae", "ᅥ": "eo", "ᅦ": "e", "ᅧ": "yeo", "ᅨ": "ye",
        "ᅩ": "o", "ᅪ": "wa", "ᅫ": "wae", "ᅬ": "oe", "ᅭ": "yo", "ᅮ": "u", "ᅯ": "wo", "ᅰ": "we",
        "ᅱ": "wi", "ᅲ": "yu", "ᅳ": "eu", "ᅴ": "ui", "ᅵ": "i", "ᆞ": "@", "ᆡ": "@i"
    },
    "jong": {
        "ᆨ": "g", "ᆩ": "kk", "ᆪ": "gs", "ᆫ": "n", "ᆬ": "nj", "ᆭ": "nh", "ᆮ": "d",
        "ᆯ": "l", "ᆰ": "lg", "ᆱ": "lm", "ᆲ": "lb", "ᆳ": "ls", "ᆴ": "lt", "ᆵ": "lp",
        "ᆶ": "lh", "ᆷ": "m", "ᆸ": "b", "ᆹ": "bs", "ᆺ": "s", "ᆻ": "ss", "ᆼ": "ng",
        "ᆽ": "j", "ᆾ": "ch", "ᆿ": "k", "ᇀ": "t", "ᇁ": "p", "ᇂ": "h",
        "ᇚ": "mg", 
        "ᇧ": "sg", 
        "ᇨ": "sd", 
        "ᇩ": "sl", 
        "ᇪ": "sb"
    }
}

rrk_cho_map = {v: k for k, v in rrk_map["cho"].items()}
rrk_jung_map = {v: k for k, v in rrk_map["jung"].items()}
rrk_jong_map = {v: k for k, v in rrk_map["jong"].items()}
rrk_cho_map["r"] = "ᄅ"
RRK_VOWEL_PATTERN = re.compile(f"({'|'.join(sorted(rrk_jung_map.keys(), key=len, reverse=True))})")

romaji_to_kana = {
    "a":"あ","i":"い","u":"う","e":"え","o":"お",
    "xa":"ぁ","xi":"ぃ","xu":"ぅ","xe":"ぇ","xo":"ぉ",
    "va":"ゔぁ","vi":"ゔぃ","vu":"ゔ","ve":"ゔぇ","vo":"ゔぉ",
    "ka":"か","ki":"き","ku":"く","ke":"け","ko":"こ",
    "kya": "きゃ", "kyu": "きゅ", "kyo": "きょ",
    "ga":"が","gi":"ぎ","gu":"ぐ","ge":"げ","go":"ご",
    "gya": "ぎゃ", "gyu": "ぎゅ", "gyo": "ぎょ",
    "sa":"さ","si":"し","su":"す","se":"せ","so":"そ",
    "sha":"しゃ","shi":"し","shu":"しゅ","sho":"しょ",
    "sya":"しゃ","syu":"しゅ","syo":"しょ",
    "ja":"じゃ","ji":"じ","ju":"じゅ","jo":"じょ",
    "zya":"じゃ","zyu":"じゅ","zyo":"じょ",
    "jya":"じゃ","jyu":"じゅ","jyo":"じょ",
    "za":"ざ","zi":"じ","zu":"ず","ze":"ぜ","zo":"ぞ",
    "ta":"た","ti":"ち","tu":"つ","te":"て","to":"と",
    "da":"だ","di":"ぢ","du":"づ","de":"で","do":"ど",
    "dxi":"でぃ", "txi": "てぃ",
    "cha":"ちゃ","chi":"ち","tsu":"つ","chu":"ちゅ","cho":"ちょ",
    "tya":"ちゃ","tyu":"ちゅ","tyo":"ちょ",
    "na":"な","ni":"に","nu":"ぬ","ne":"ね","no":"の",
    "nya": "にゃ", "nyu": "にゅ", "nyo": "にょ",
    "ha":"は","hi":"ひ","hu":"ふ","he":"へ","ho":"ほ",
    "hya":"ひゃ","hyu":"ひゅ","hyo":"ひょ",
    "fa":"ふぁ","fi":"ふぃ","fu":"ふ","fe":"ふぇ","fo":"ふぉ",
    "ba":"ば","bi":"び","bu":"ぶ","be":"べ","bo":"ぼ",
    "bya":"びゃ","byu":"びゅ","byo":"びょ",
    "pa":"ぱ","pi":"ぴ","pu":"ぷ","pe":"ぺ","po":"ぽ",
    "pya":"ぴゃ","pyu":"ぴゅ","pyo":"ぴょ",
    "ma":"ま","mi":"み","mu":"む","me":"め","mo":"も",
    "mya": "みゃ", "myu": "みゅ", "myo": "みょ",
    "ya":"や","yu":"ゆ","yo":"よ",
    "xya":"ゃ","xyu":"ゅ","xyo":"ょ",
    "~a":"ゃ","~u":"ゅ","~o":"ょ",
    "ra":"ら","ri":"り","ru":"る","re":"れ","ro":"ろ",
    "rya": "りゃ", "ryu": "りゅ", "ryo": "りょ",
    "wa":"わ","wi":"ゐ","we":"ゑ","wo":"を",
    "n'":"ん", "xt":"っ", "xk":"ヶ",
    "{onaji}":"ゝ", "--":"ー", "{noma}":"\u3005",
    "?a": "は", "?e": "へ", "?i": "ひ", "?u": "ふ", "?o": "ほ"
}

kanji_tables = {"none": {}, "shinjitai": {}, "kyujitai": {}, "simplified": {}}

# 전역 변수 초기화
kanji_tables = {}
sorted_kana_keys = []
reverse_hanja_map = {}

def build_reverse_map(original_dict):
    reverse_map = {}
    for trad_hanja, simp_hanja in original_dict.items():
        if simp_hanja not in reverse_map:
            reverse_map[simp_hanja] = []
        reverse_map[simp_hanja].append(trad_hanja)
    return reverse_map

#: 앱이 알려 주는 데이터 폴더(예: 번들 폴더, 사용자 데이터 폴더). 가장 먼저 찾는다.
EXTRA_DATA_DIRS = []


def set_data_dirs(dirs):
    """데이터 JSON 을 찾을 폴더를 지정하고 표를 다시 읽는다."""
    EXTRA_DATA_DIRS[:] = [str(d) for d in dirs if d]
    load_kanji_tables()


def user_data_dir():
    """사용자가 고쳐 쓰는 데이터(customkanji.json)를 두는 폴더. 쓰기 가능한 곳이다."""
    if platform.system() == "Windows":
        base = os.environ.get("APPDATA") or os.path.expanduser("~")
        return os.path.join(base, "pmimegui")
    return os.path.expanduser("~/.config/pmimegui")


def get_possible_base_dirs():
    paths = list(EXTRA_DATA_DIRS)
    
    # 1. Working Directory (OS 공통)
    working_dir = os.getcwd()
    if working_dir not in paths:
        paths.append(working_dir)
    # 사용자 데이터 폴더는 exe 곁·번들보다 먼저 본다(앱이 저장한 사본이 이기게).
    _ud = user_data_dir()
    if _ud not in paths:
        paths.append(_ud)

    system = platform.system()
    is_frozen = getattr(sys, 'frozen', False)

    if system == "Windows":
        # Windows 2. exe가 있는 폴더 (또는 스크립트 경로)
        if is_frozen:
            exe_dir = os.path.dirname(sys.executable)
        else:
            exe_dir = os.path.dirname(os.path.abspath(__file__))
            
        if exe_dir not in paths:
            paths.append(exe_dir)
            
        # Windows 3. PyInstaller 내부 라이브러리 임시 경로 (_MEIPASS)
        if is_frozen and hasattr(sys, '_MEIPASS'):
            meipass_dir = sys._MEIPASS
            if meipass_dir not in paths:
                paths.append(meipass_dir)

    else:
        # MacOS & Linux 2. ~/.config/pmimegui/ 폴더
        config_dir = os.path.expanduser("~/.config/pmimegui")
        if config_dir not in paths:
            paths.append(config_dir)
            
        # MacOS & Linux 3. 실행파일 (py)이 있는 경로
        if is_frozen:
            exe_dir = os.path.dirname(sys.executable)
        else:
            exe_dir = os.path.dirname(os.path.abspath(__file__))
            
        if exe_dir not in paths:
            paths.append(exe_dir)
            
        # MacOS 4. Mac Bundle의 경우만 ../Resources/ 추가
        # (App Bundle 내부 구조: Contents/MacOS 에 실행파일 존재)
        if system == "Darwin" and is_frozen:
            resource_dir = os.path.abspath(os.path.join(exe_dir, "..", "Resources"))
            if resource_dir not in paths:
                paths.append(resource_dir)

    # 이 파일이 있는 폴더(어떻게 실행되든)는 맨 마지막 후보로 둔다 — 사용자가 exe 곁/설정 폴더에 둔
    # 사전이 번들된 사전보다 먼저 쓰이게 하려는 것이다.
    _here = os.path.dirname(os.path.abspath(__file__))
    if _here not in paths:
        paths.append(_here)

    return paths


def find_file(filename):
    for base in get_possible_base_dirs():
        full_path = os.path.join(base, filename)
        if os.path.exists(full_path):
            return full_path
    return None # 파일을 찾지 못한 경우

_CUSTOM_APPLIED = set()      # romaji_to_kana 에 얹혀 있는 사용자 단어 키


def load_kanji_tables():
    global kanji_tables, sorted_kana_keys
    
    filenames = {
        "shinjitai": "shinjitai.json",
        "kyujitai": "kyujitai.json",
        "simplified": "simplified.json",
        "custom_kana": "customkanji.json"
    }
    
    kanji_tables["none"] = {}
    
    for mode, filename in filenames.items():
        file_path = find_file(filename)
        
        if file_path:
            try:
                with open(file_path, "r", encoding="utf-8") as f:
                    kanji_tables[mode] = json.load(f)
            except Exception as e:
                print(f"Error loading {file_path}: {e}")
                kanji_tables[mode] = {}
        else:
            print(f"File not found: {filename}")
            kanji_tables[mode] = {}

    # 예전 파일이 {"custom_kana": {...}} 로 한 겹 싸여 있으면 알맹이만 쓴다.
    _c = kanji_tables.get("custom_kana", {})
    if isinstance(_c, dict) and isinstance(_c.get("custom_kana"), dict):
        kanji_tables["custom_kana"] = _c = _c["custom_kana"]

    if "romaji_to_kana" in globals():
        target_map = globals()["romaji_to_kana"]
        base = globals().get("_ROMAJI_BASE")
        if base is not None:
            # 지난번에 얹었던 사용자 단어를 먼저 걷어 낸다(삭제·이름 변경이 반영되게).
            for k in list(_CUSTOM_APPLIED):
                if k in base:
                    target_map[k] = base[k]
                else:
                    target_map.pop(k, None)
        _CUSTOM_APPLIED.clear()
        if _c:
            target_map.update(_c)
            _CUSTOM_APPLIED.update(_c.keys())
        sorted_kana_keys = sorted(target_map.keys(), key=lambda x: len(x), reverse=True)

    reverse_hanja_map.clear()
    
    for mode in ["shinjitai", "kyujitai"]:
        if mode in kanji_tables:
            temp_map = build_reverse_map(kanji_tables[mode])
            for simp, trad_list in temp_map.items():
                if simp not in reverse_hanja_map:
                    reverse_hanja_map[simp] = []
                
                # 중복 방지 (예: 신자체와 간체자가 동일한 형태일 경우)
                for t in trad_list:
                    if t not in reverse_hanja_map[simp]:
                        reverse_hanja_map[simp].append(t)


# load kanji table
_ROMAJI_BASE = dict(romaji_to_kana)     # customkanji 를 얹기 전의 기본 표(삭제·교체를 되돌리기 위해)
load_kanji_tables()

bracket_map = {
    "0": ("「", "」"), "1": ("『", "』"), "2": ("〈", "〉"), "3": ("《", "》"), "4": ("〔", "〕"),
    "5": ("【", "】"), "6": ("〖", "〗"), "7": ("\u3018", "\u3019"), "8": ("\u301A", "\u301B"), "9": ("｟", "｠"),
    "#0": ("\uFE59","\uFE5A"), "#1": ("\uFE5B","\uFE5C"), "#2": ("\uFF3B","\uFF3D"), "#3": ("\uFF08","\uFF09"),
    "#4": ("\u2018","\u2019"), "#5": ("\u201C","\u201D")
}

hat_map = {
    "^~": "\uFF5E", "^.": "\u3002", "^,": "\u3001", "^>": "\u00B7", "^<": "\u30FB",
    "^-": "\u2015", "^*": "\u2026", "^/": "/", "^\\": "\\",
    "^=": "\u3005", "^:": "\uFF1A", "^;": "\uFF1B", "^^": "\u005E"
}

cho_map = {v: k for k, v in pm_map["cho"].items() if v != "q"}
cho_map["q"] = "ᄋ"
if "" not in cho_map: cho_map[""] = "ᄋ"
cho_map["fg"] = "ᅁ"

jung_map = {v: k for k, v in pm_map["jung"].items()}
jong_map = {v: k for k, v in pm_map["jong"].items()}

jung_aliases = {
    "ai": "ᅢ", "yai": "ᅤ", "ei": "ᅦ", "yei": "ᅨ", "oi": "ᅬ", "oai": "ᅫ", "uei": "ᅰ", "ui": "ᅱ", "vi": "ᅴ",
    "oyei": "ᆁ", "yoy": "ᆈ", "yoyai": "ᆅ", "uai": "ᆊ", "uyei": "ᆌ", "yuei": "ᆐ", "yuyei": "ᆒ", "oyai": "ᆧ",
    "oei": "ᆀ"
}
jung_map.update(jung_aliases)

sorted_pm_vowels = sorted(jung_map.keys(), key=lambda x: (len(x), x), reverse=True)
PM_VOWEL_PATTERN_FIXED = r"(" + "|".join(re.escape(v) for v in sorted_pm_vowels) + r")"

frk_jung_map = {v: k for k, v in frk_map["jung"].items()}
sorted_frk_vowels = sorted(frk_jung_map.keys(), key=lambda x: (len(x), x), reverse=True)
FRK_VOWEL_PATTERN = r"(" + "|".join(re.escape(v) for v in sorted_frk_vowels) + r")"

frk_cho_map = {v: k for k, v in frk_map["cho"].items() if v not in ("q", "x")}
frk_cho_map["x"] = "ᄋ"
if "" not in frk_cho_map: frk_cho_map[""] = "ᄋ"

frk_jong_map = {v: k for k, v in frk_map["jong"].items()}

compat_map = {}
for k, v in pm_map["generic"].items():
    roman = v.replace("/", "")
    if roman.isalpha() and roman.isupper():
        compat_map[roman] = k
compat_map.update({k.upper(): v for k, v in jung_aliases.items()})

PM_PSEUDO_SINGLE_CONSONANTS = ["gg", "dd", "bb", "ss", "jj"]


def hira_to_kata(text):
    return "".join(chr(ord(ch) + 0x60) if 0x3041 <= ord(ch) <= 0x3096 else ch for ch in text)


def kata_to_hira(text):
    return "".join(chr(ord(ch) - 0x60) if 0x30A1 <= ord(ch) <= 0x30F6 else ch for ch in text)


#: 대소문자까지 구분하는 가타카나 전용 규칙(0.17.1).
KATA_ONLY_RULES = {"Ti": "ティ", "Di": "ディ"}


def romaji_to_kana_convert(romaji, force_mode=None):
    kana = ""
    i = 0
    max_len = max(len(k) for k in romaji_to_kana.keys())

    # 기호 쌍(앞/뒤) 상태를 추적하기 위한 플래그 변수
    # True: 열린 상태(다음에는 닫아야 함), False: 닫힌 상태(다음에는 열어야 함)
    single_quote_opened = False
    double_quote_opened = False

    while i < len(romaji):
        # 1. 쌍따옴표형 기호 처리 (`` 또는 '') -> 『 』
        if romaji[i:i+2] in ("``", "''"):
            if not double_quote_opened:
                kana += "『"
                double_quote_opened = True
            else:
                kana += "』"
                double_quote_opened = False
            i += 2
            continue

        # 2. 홑따옴표형 기호 처리 (` 또는 ') -> 「 」
        # 단, n' 처리 로직(ん/ッ)이 아래에 따로 있으므로 n' 상태가 아닐 때만 처리
        if romaji[i] in ("`", "'"):
            # 이전 글자가 'n' 또는 'N'인 경우 아래의 n' 로직으로 토스하기 위해 패스
            if i > 0 and romaji[i-1].lower() == 'n':
                pass 
            else:
                if not single_quote_opened:
                    kana += "「"
                    single_quote_opened = True
                else:
                    kana += "」"
                    single_quote_opened = False
                i += 1
                continue

        # ==========================================
        # 마침표, 쉼표 처리 로직
        # ==========================================
        if romaji[i] in ('.', ','):
            prev_is_digit = (i > 0 and romaji[i-1].isdigit())
            next_is_digit = (i + 1 < len(romaji) and romaji[i+1].isdigit())
            if prev_is_digit and next_is_digit:
                kana += romaji[i]
            else:
                kana += "。" if romaji[i] == '.' else "、"
            i += 1
            continue

        # n 및 n' 처리 로직
        if romaji[i].lower() == "n":
            is_upper_n = romaji[i].isupper()
            if i + 1 < len(romaji) and romaji[i + 1] == "'":
                kana += "ッ" if is_upper_n else "ん"
                i += 2
                continue
            elif i + 1 < len(romaji) and romaji[i + 1].lower() in "aeiouyw":
                pass
            else:
                kana += "ン" if is_upper_n else "ん"
                i += 1
                continue

        # 촉음(っ) 처리 로직
        if i + 1 < len(romaji) and romaji[i].isalpha() and romaji[i].lower() == romaji[i+1].lower():
            if romaji[i].lower() not in "aeioun":
                chunk_matched = False
                for l in range(max_len, 0, -1):
                    if romaji[i:i+l].lower() in romaji_to_kana:
                        chunk_matched = True
                        break
                if not chunk_matched:
                    kana += "ッ" if romaji[i].isupper() else "っ"
                    i += 1
                    continue

        # 가타카나 전용 규칙: 대문자 + 소문자 `Ti` → ティ, `Di` → ディ.
        # (`TI` → チ, `DI` → ヂ 는 아래 일반 규칙 그대로. 히라가나 강제 모드에서는 적용하지 않는다.)
        if force_mode != "hira" and romaji[i:i+2] in KATA_ONLY_RULES:
            kana += KATA_ONLY_RULES[romaji[i:i+2]]
            i += 2
            continue

        # 로마자 -> 카나 매칭 로직
        matched = None
        matched_len = 0
        for length in range(max_len, 0, -1):
            chunk = romaji[i:i + length]
            if chunk.lower() in romaji_to_kana:
                matched = romaji_to_kana[chunk.lower()]
                matched_len = length
                chunk_is_upper = chunk[0].isupper()
                break
                
        if matched:
            if force_mode == "kata" or (force_mode is None and chunk_is_upper):
                kana += hira_to_kata(matched)
            elif force_mode == "hira":
                kana += kata_to_hira(hira_to_kata(matched))
            else:
                kana += matched
            i += matched_len
        else:
            kana += romaji[i]
            i += 1

    return kana

def filter_kanji(text, hanja_mode="none"):
    if hanja_mode == "none":
        return text

    output_text = []
    
    for char in text:
        # 1. 한국식 정자체(hanja)로 역변환
        if hanja_mode == "hanja":
            if char in reverse_hanja_map:
                candidates = reverse_hanja_map[char]
                if len(candidates) > 1:
                    output_text.append(f"{{{'|'.join(candidates)}}}")
                else:
                    output_text.append(candidates[0])
            else:
                output_text.append(char)
                
        # 2. 신자체, 구자체, 간체자로 변환하는 모드
        elif hanja_mode in kanji_tables:
            output_text.append(kanji_tables[hanja_mode].get(char, char))
            
        # 3. 알 수 없는 모드일 경우 원본 유지
        else:
            output_text.append(char)

    return "".join(output_text)

########################## 

def parse_syllable_core(roman_str, engine_mode="pm"):
    if not roman_str: return ""
    if engine_mode == "pm" and "/" in roman_str:
        return "".join([parse_syllable_core(s, "pm") for s in roman_str.split("/")])
    
    remaining = roman_str

    if engine_mode == "rrk":
        c_map, v_map, t_map = rrk_cho_map, rrk_jung_map, rrk_jong_map
    elif engine_mode == "frkim":
        c_map, v_map, t_map = frk_cho_map, frk_jung_map, frk_jong_map
    else:
        c_map, v_map, t_map = cho_map, jung_map, jong_map

    cho_char = c_map.get("")
    for i in range(len(remaining), 0, -1):
        if remaining[:i] in c_map:
            cho_char = c_map[remaining[:i]]
            remaining = remaining[i:]
            break
    jung_char = ""
    for i in range(len(remaining), 0, -1):
        if remaining[:i] in v_map:
            jung_char = v_map[remaining[:i]]
            remaining = remaining[i:]
            break
    jong_char = ""
    for i in range(len(remaining), 0, -1):
        if remaining[:i] in t_map:
            jong_char = t_map[remaining[:i]]
            remaining = remaining[i:]
            break
            
    # [방점 처리 루틴]
    bangjeom = ""
    if remaining.startswith(";"):
        bangjeom = "\u302E"  # 거성 (Single Dot)
        remaining = remaining[1:]
    elif remaining.startswith(":"):
        bangjeom = "\u302F"  # 상성 (Double Dot)
        remaining = remaining[1:]
        
    return cho_char + jung_char + jong_char + bangjeom + remaining


def parse_compat(roman_str):
    result = ""
    remaining = roman_str
    while remaining:
        matched = False
        for i in range(len(remaining), 0, -1):
            if remaining[:i] in compat_map:
                result += compat_map[remaining[:i]]
                remaining = remaining[i:]
                matched = True
                break
        if not matched:
            result += remaining[0]; remaining = remaining[1:]
    return result


def split_consonants_pmfrk(lead_cluster):
    if not lead_cluster: return "", ""
    if lead_cluster in PM_PSEUDO_SINGLE_CONSONANTS or len(lead_cluster) == 1: return "", lead_cluster
    if len(lead_cluster) >= 2 and lead_cluster[-2:] in PM_PSEUDO_SINGLE_CONSONANTS: return lead_cluster[:-2], lead_cluster[-2:]
    return lead_cluster[:-1], lead_cluster[-1]


def parse_auto_chunk(chunk, engine_mode="frkim"):
    prev_jong=""
    this_jong=""
    if not chunk: return ""
    
    # =========================================================================
    # [규칙 4] 대시(-) 강제 음절 분리: 
    # 대시를 기준으로 잘라 재귀 호출하면, 뒤에 모음이 올 경우 자연스럽게 
    # 선행 자음이 없으므로 'ㅇ'이 붙고(규칙 1), 자음이 오면 초성이 됩니다(규칙 2).
    # =========================================================================
    if engine_mode == "rrk" and "-" in chunk:
        return "".join([parse_auto_chunk(c, engine_mode="rrk") for c in chunk.split("-")])
        
    # =========================================================================
    # pm 모드: /, ;, : 
    # =========================================================================
    if engine_mode == "pm":
        tokens = re.split(r"(?<=[/;:])", chunk)
        
        result_chunks = []
        for token in tokens:
            if not token: 
                continue
            
            if token.endswith("/"):
                pure_token = token[:-1]
                if pure_token:
                    result_chunks.append(parse_syllable_core(pure_token, engine_mode="pm"))
            else:
                result_chunks.append(parse_syllable_core(token, engine_mode="pm"))
                
        return "".join(result_chunks)

    # =========================================================================
    # mix(pmfrk), frkim, rrk 모드: 자동 음절 분리
    # =========================================================================
    if engine_mode == "pmfrk": vow_pattern = PM_VOWEL_PATTERN_FIXED
    elif engine_mode == "rrk": vow_pattern = RRK_VOWEL_PATTERN
    else: vow_pattern = FRK_VOWEL_PATTERN
    
    vowel_matches = list(re.finditer(vow_pattern, chunk))
    if not vowel_matches: 
        return chunk
        
    syllables = []
    for idx, match in enumerate(vowel_matches):
        v_start = match.start()
        this_jung = match.group(1)
        
        if idx == 0: lead_cluster = chunk[:v_start]
        else: lead_cluster = chunk[vowel_matches[idx-1].end():v_start]
            
        this_cho, this_jong = "", ""
        
        if idx == 0:
            # [규칙 1 & 2] 첫 모음 앞의 자음 처리
            if not lead_cluster: this_cho = ""  # 자음이 없으면 'ㅇ' (맵에서 ""는 "ㅇ"으로 매칭됨)
            elif engine_mode == "rrk": this_cho = lead_cluster
            elif lead_cluster.startswith("-"): this_cho = lead_cluster[1:]
            elif lead_cluster.startswith("'"): this_cho = ""
            elif lead_cluster.startswith("/"): this_cho = lead_cluster[1:]
            else: this_cho = lead_cluster
        else:
            prev_jong = ""
            if engine_mode == "rrk":
                # [규칙 3] 모음과 모음 사이의 자음 분리
                # 오른쪽 끝에서부터 '유효한 초성'을 먼저 찾고, 남은 앞부분이 '유효한 종성'인지 확인하여 분리
                # (예: "ngg" -> prev_jong="ng", this_cho="g")
                for i in range(len(lead_cluster)):
                    head, tail = lead_cluster[:i], lead_cluster[i:]
                    if (tail == "" or tail in rrk_cho_map) and (head == "" or head in rrk_jong_map):
                        prev_jong, this_cho = head, tail
                        break
                else:
                    # 완벽한 분리점을 찾지 못한 경우의 안전망 (왼쪽부터 종성 최대 매칭)
                    for i in range(len(lead_cluster), -1, -1):
                        head, tail = lead_cluster[:i], lead_cluster[i:]
                        if head == "" or head in rrk_jong_map:
                            prev_jong, this_cho = head, tail
                            break
            elif "'" in lead_cluster:
                parts = lead_cluster.split("'", 1)
                prev_jong, this_cho = parts[0], parts[1]
            elif "-" in lead_cluster:
                parts = lead_cluster.split("-", 1)
                prev_jong, this_cho = parts[0], parts[1]
            else:
                if engine_mode == "pmfrk":
                    prev_jong, this_cho = split_consonants_pmfrk(lead_cluster)
                else:
                    m = re.match(r"^(.*?)([a-zA-Z]*)$", lead_cluster)
                    prefix = m.group(1) if m else lead_cluster
                    alpha = m.group(2) if m else ""
                    if alpha and len(alpha) > 1:
                        prev_jong = prefix + alpha[:-1]
                        this_cho = alpha[-1]
                    else:
                        prev_jong = prefix
                        this_cho = alpha
                        
        if prev_jong and syllables: 
            syllables[-1][2] = (syllables[-1][2] or "") + prev_jong
            
        syllables.append([this_cho, this_jung, this_jong])
        
    last_v_end = vowel_matches[-1].end()
    rem_tail = chunk[last_v_end:]
    if rem_tail and syllables: 
        syllables[-1][2] = (syllables[-1][2] or "") + rem_tail

    result_str = ""
    for syl in syllables:
        if syl[1] == "": 
            result_str += syl[0]
        else:
            c_part = syl[0]
            core_mode = "pm" if engine_mode == "pmfrk" else engine_mode
            result_str += parse_syllable_core(c_part + syl[1] + syl[2], engine_mode=core_mode)
            
    return result_str

# ==============================================================================
# LaTeX 입력 확장 (전역)
#   1) 확장 라틴문자   : \'e -> é , \v{s} -> š , \ss -> ß , \ae -> æ ...
#   2) 유니코드 코드포인트 : \xAC00 -> 가 , \x{1F600} -> 😀 , \x{1112 1161 11AB} -> 한
#  * 입력 메서드(pm/frk/mix/rrk/jp/clean)와 무관하게 변환 파이프라인 최전방에서 동작한다.
# ==============================================================================

LATEX_EXPAND_ENABLED = True          # 전역 스위치 (GUI 체크박스 / CLI --no-latex 로 제어)

def set_latex_expand(flag):
    global LATEX_EXPAND_ENABLED
    LATEX_EXPAND_ENABLED = bool(flag)

# 마커용 사용자 영역(PUA) 문자. 본문에 등장할 일이 없으므로 후속 치환 규칙과 충돌하지 않는다.
_LX_OPEN = "\uE000"
_LX_CLOSE = "\uE001"

# ------------------------------------------------------------------
# 1) 액센트 명령 -> 결합 발음구별기호(combining diacritical mark)
#    결합 후 NFC 정규화하므로 미리 만들어 둔 완성형 표가 필요 없다.
# ------------------------------------------------------------------
LATEX_ACCENT_MAP = {
    "'": "\u0301",   # acute        \'e      -> é
    "`": "\u0300",   # grave        \`e      -> è
    "^": "\u0302",   # circumflex   \^e      -> ê
    '"': "\u0308",   # diaeresis    \"o      -> ö
    "~": "\u0303",   # tilde        \~n      -> ñ
    "=": "\u0304",   # macron       \=a      -> ā
    ".": "\u0307",   # dot above    \.z      -> ż
    "u": "\u0306",   # breve        \u{g}    -> ğ
    "v": "\u030C",   # caron        \v{s}    -> š
    "H": "\u030B",   # double acute \H{o}    -> ő
    "r": "\u030A",   # ring         \r{a}    -> å
    "c": "\u0327",   # cedilla      \c{c}    -> ç
    "k": "\u0328",   # ogonek       \k{a}    -> ą
    "d": "\u0323",   # dot below    \d{s}    -> ṣ
    "b": "\u0331",   # macron below \b{h}    -> ẖ
    "t": "\u0361",   # tie          \t{oo}   -> o͡o
}

# ------------------------------------------------------------------
# 2) 독립 문자/합자 명령 (이름이 영문자인 것)
# ------------------------------------------------------------------
LATEX_SPECIAL_WORD_MAP = {
    # 라틴 확장 문자
    "ss": "ß", "SS": "ẞ", "ae": "æ", "AE": "Æ", "oe": "œ", "OE": "Œ",
    "aa": "å", "AA": "Å", "o": "ø", "O": "Ø", "l": "ł", "L": "Ł",
    "i": "ı", "j": "ȷ", "dh": "ð", "DH": "Ð", "th": "þ", "TH": "Þ",
    "ng": "ŋ", "NG": "Ŋ", "dj": "đ", "DJ": "Đ",
    # 인용/구두점
    "guillemotleft": "«", "guillemotright": "»",
    "guilsinglleft": "‹", "guilsinglright": "›",
    "quotedblbase": "„", "quotesinglbase": "‚",
    "textquotedblleft": "“", "textquotedblright": "”",
    "textquoteleft": "‘", "textquoteright": "’",
    "textendash": "–", "textemdash": "—",
    "textellipsis": "…", "ldots": "…", "dots": "…",
    "textbullet": "•", "textperiodcentered": "·",
    "dag": "†", "ddag": "‡", "S": "§", "P": "¶",
    # 기호
    "pounds": "£", "texteuro": "€", "textyen": "¥", "textcent": "¢",
    "copyright": "©", "textregistered": "®", "texttrademark": "™",
    "textdegree": "°", "textmu": "µ", "textpm": "±",
    "texttimes": "×", "textdiv": "÷",
    "textasciitilde": "~", "textasciicircum": "^",
    "textbackslash": "\\", "textunderscore": "_",
    "textbraceleft": "{", "textbraceright": "}",
    # 자주 쓰는 IPA
    "textschwa": "ə", "textopeno": "ɔ", "textesh": "ʃ", "textyogh": "ʒ",
    "textturnv": "ʌ", "textscripta": "ɑ", "textglotstop": "ʔ", "textbari": "ɨ",
}

# ------------------------------------------------------------------
# 3) 이름이 기호인 명령 (뒤에 오는 공백을 먹지 않는다)
# ------------------------------------------------------------------
LATEX_SPECIAL_SYM_MAP = {
    "%": "%", "&": "&", "#": "#", "$": "$", "_": "_",
}

def _lx_alt(keys):
    return "|".join(re.escape(k) for k in sorted(keys, key=len, reverse=True))

_LX_ACC_ALPHA = _lx_alt([k for k in LATEX_ACCENT_MAP if k.isalpha()])
_LX_ACC_SYM = _lx_alt([k for k in LATEX_ACCENT_MAP if not k.isalpha()])
_LX_SPEC_WORD = _lx_alt(LATEX_SPECIAL_WORD_MAP.keys())
_LX_SPEC_SYM = _lx_alt(LATEX_SPECIAL_SYM_MAP.keys())

# 액센트 인자: {...}(1단계 중첩 허용) / \i \j / 단일 문자
_LX_ARG = r"(?:\{(?:[^{}]|\{[^{}]*\})*\}|\\[ij](?![A-Za-z])|[A-Za-z])"

LATEX_INPUT_RE = re.compile(
    rf"""
      (?P<esc>\\\\)                                     # \\ 는 확장하지 않고 그대로 통과(탈출 문자)
    | \\x\{{(?P<cpbrace>[^{{}}]{{0,80}})\}}             # \x{{AC00}} , \x{{1112 1161 11AB}}
    | \\x(?P<cp4>[0-9A-Fa-f]{{4}})                      # \xAC00
    | \\u(?P<cpu4>[0-9A-Fa-f]{{4}})                     # \uAC00
    | \\U(?P<cpU8>[0-9A-Fa-f]{{8}})                     # \U0001F600
    | \\char"(?P<chex>[0-9A-Fa-f]{{1,6}})               # TeX: \char"AC00
    | \\char'(?P<coct>[0-7]{{1,8}})                     # TeX: \char'101
    | \\char(?P<cdec>[0-9]{{1,7}})                      # TeX: \char97
    | \\(?P<specw>{_LX_SPEC_WORD})(?![A-Za-z])(?P<specw_tail>\{{\}}|[ \t])?
    | \\(?P<specs>{_LX_SPEC_SYM})
    | \\(?P<acca>{_LX_ACC_ALPHA})(?![A-Za-z])[ \t]*(?P<arga>{_LX_ARG})
    | \\(?P<accs>{_LX_ACC_SYM})[ \t]*(?P<args>{_LX_ARG})
    """,
    re.VERBOSE,
)


def _lx_codepoint(token):
    """단일 코드포인트 토큰(16진)을 문자로. 실패하면 None."""
    t = token.strip()
    if not t:
        return None
    low = t.lower()
    if low.startswith("u+"):
        t = t[2:]
    elif low.startswith("0x"):
        t = t[2:]
    try:
        cp = int(t, 16)
    except ValueError:
        return None
    if cp < 0 or cp > 0x10FFFF or 0xD800 <= cp <= 0xDFFF:
        return None
    return chr(cp)


def _lx_codepoint_list(body):
    """\\x{...} 내부: 공백/쉼표/+ 로 구분된 여러 코드포인트를 허용."""
    tokens = [t for t in re.split(r"[\s,+]+", body.strip()) if t]
    if not tokens:
        return None
    out = []
    for tok in tokens:
        ch = _lx_codepoint(tok)
        if ch is None:
            return None
        out.append(ch)
    return "".join(out)


def _lx_accent_base(arg):
    """액센트 인자를 실제 밑글자 문자열로 정규화."""
    if arg.startswith("{") and arg.endswith("}"):
        arg = arg[1:-1]
    arg = arg.strip()
    # 액센트 밑글자로 쓰인 \i \j 는 점 없는 i/j 가 아니라 보통의 i/j 로 취급 (\'\i -> í)
    arg = re.sub(r"\\([ij])(?![A-Za-z])", r"\1", arg)
    # 중첩 액센트 지원: \'{\v{s}}
    return expand_latex_input(arg)


def _lx_apply_accent(mark, base):
    if not base:
        return None
    return unicodedata.normalize("NFC", base[0] + mark + base[1:])


def expand_latex_input(text, protect=None):
    """
    LaTeX식 확장 라틴문자/코드포인트 입력을 실제 문자로 렌더링한다.

    protect 가 리스트이면, 확장 결과를 그 리스트에 적재하고 본문에는 PUA 마커만 남긴다.
    (이후 로마자->한글 치환 단계에서 확장 결과가 다시 건드려지는 것을 막기 위한 장치)
    """
    if not text or not LATEX_EXPAND_ENABLED or "\\" not in text:
        return text

    def _repl(m):
        g = m.group
        if g("esc") is not None:
            return m.group(0)

        value = None
        if g("cpbrace") is not None:
            value = _lx_codepoint_list(g("cpbrace"))
        elif g("cp4") is not None:
            value = _lx_codepoint(g("cp4"))
        elif g("cpu4") is not None:
            value = _lx_codepoint(g("cpu4"))
        elif g("cpU8") is not None:
            value = _lx_codepoint(g("cpU8"))
        elif g("chex") is not None:
            value = _lx_codepoint(g("chex"))
        elif g("coct") is not None:
            try:
                value = chr(int(g("coct"), 8))
            except (ValueError, OverflowError):
                value = None
        elif g("cdec") is not None:
            try:
                cp = int(g("cdec"), 10)
                value = chr(cp) if 0 <= cp <= 0x10FFFF and not (0xD800 <= cp <= 0xDFFF) else None
            except (ValueError, OverflowError):
                value = None
        elif g("specw") is not None:
            value = LATEX_SPECIAL_WORD_MAP.get(g("specw"))
            # 제어어 뒤의 {} 나 공백 한 칸은 TeX 규칙대로 흡수, 그 외 공백류는 보존
            tail = g("specw_tail")
            if value is not None and tail and tail not in ("{}", " ", "\t"):
                value = value + tail
        elif g("specs") is not None:
            value = LATEX_SPECIAL_SYM_MAP.get(g("specs"))
        elif g("acca") is not None:
            value = _lx_apply_accent(LATEX_ACCENT_MAP[g("acca")], _lx_accent_base(g("arga")))
        elif g("accs") is not None:
            value = _lx_apply_accent(LATEX_ACCENT_MAP[g("accs")], _lx_accent_base(g("args")))

        if value is None:
            return m.group(0)          # 해석 실패 시 원문 보존
        if protect is None:
            return value
        protect.append(value)
        return f"{_LX_OPEN}{len(protect) - 1}{_LX_CLOSE}"

    return LATEX_INPUT_RE.sub(_repl, text)


def restore_latex_input(text, saved):
    for idx, ch in enumerate(saved):
        text = text.replace(f"{_LX_OPEN}{idx}{_LX_CLOSE}", ch)
    return text


# --------------------------------------------------------------------------
# 두벌식 (%du) — 영문 자판 키를 한글로. `-` 한 개는 강제 분절 부호(음절 경계, 출력되지 않음),
# `--` 는 글자 그대로의 `-`. 대문자는 Shift 입력(ㅃㅉㄸㄲㅆㅒㅖ), 그 밖의 대문자는 소문자와 같다.
# --------------------------------------------------------------------------
_DU_CONS = dict(zip("qwertasdfgzxcvQWERT", "ㅂㅈㄷㄱㅅㅁㄴㅇㄹㅎㅋㅌㅊㅍㅃㅉㄸㄲㅆ"))
_DU_VOW = dict(zip("yuiopjkhlbnmOP", "ㅛㅕㅑㅐㅔㅓㅏㅗㅣㅠㅜㅡㅒㅖ"))
# 옛한글(다소 지원): K 아래아, KK 쌍아래아, A ㅿ, D ㆁ, G ㆆ, QD ㅸ. 이 글자가 든 음절은 조합 자모열로 낸다.
_DU_CONS.update({"A": "ㅿ", "D": "ㆁ", "G": "ㆆ", "\1": "ㅸ"})
_DU_VOW["K"] = "ㆍ"
_DU_OLD_CONS = "ㅿㆁㆆㅸ"
# 어두(또는 `-` 뒤)의 ㅅ계 합용병서 초성: tr ㅺ, te ㅼ, tq ㅽ, tw ㅾ (tt 는 ㅆ). 모음이 바로 이어질 때만.
_DU_SCLUSTER = {"r": "ㅺ", "e": "ㅼ", "q": "ㅽ", "w": "ㅾ", "t": "ㅆ"}
_DU_OLD_LEAD = {"ㅺ": "\u112d", "ㅼ": "\u112f", "ㅽ": "\u1132", "ㅾ": "\u1136", "ㅿ": "\u1140", "ㆁ": "\u114c", "ㆆ": "\u1159", "ㅸ": "\u112b"}
_DU_OLD_TAIL = {"ㅿ": "\u11eb", "ㆁ": "\u11f0", "ㆆ": "\u11f9", "ㅸ": "\u11e6"}
_DU_OLD_VOW = {"ㆎ": "\u11a1", "ㆍ": "\u119e", "\u11a2": "\u11a2"}
_DU_OLD_LONE = {"ㆍ": "ㆍ"}
_DU_LEAD = "ㄱㄲㄴㄷㄸㄹㅁㅂㅃㅅㅆㅇㅈㅉㅊㅋㅌㅍㅎ"
_DU_VOWELS = "ㅏㅐㅑㅒㅓㅔㅕㅖㅗㅘㅙㅚㅛㅜㅝㅞㅟㅠㅡㅢㅣ"
_DU_TAIL = " ㄱㄲㄳㄴㄵㄶㄷㄹㄺㄻㄼㄽㄾㄿㅀㅁㅂㅄㅅㅆㅇㅈㅊㅋㅌㅍㅎ"
_DU_VV = {("ㅗ", "ㅏ"): "ㅘ", ("ㅗ", "ㅐ"): "ㅙ", ("ㅗ", "ㅣ"): "ㅚ", ("ㅜ", "ㅓ"): "ㅝ",
          ("ㅜ", "ㅔ"): "ㅞ", ("ㅜ", "ㅣ"): "ㅟ", ("ㅡ", "ㅣ"): "ㅢ", ("ㆍ", "ㆍ"): "\u11a2", ("ㆍ", "ㅣ"): "ㆎ"}
_DU_TT = {("ㄱ", "ㅅ"): "ㄳ", ("ㄴ", "ㅈ"): "ㄵ", ("ㄴ", "ㅎ"): "ㄶ", ("ㄹ", "ㄱ"): "ㄺ",
          ("ㄹ", "ㅁ"): "ㄻ", ("ㄹ", "ㅂ"): "ㄼ", ("ㄹ", "ㅅ"): "ㄽ", ("ㄹ", "ㅌ"): "ㄾ",
          ("ㄹ", "ㅍ"): "ㄿ", ("ㄹ", "ㅎ"): "ㅀ", ("ㅂ", "ㅅ"): "ㅄ"}
_DU_TT_SPLIT = {v: k for k, v in _DU_TT.items()}


def dubeolsik_to_hangul(keys):
    """영문 자판 키열(`-` = 강제 분절)을 한글로. 두벌식 조합 규칙: 겹받침, 받침의 다음 모음 이동
    (겹받침은 뒤쪽만 이동), ㅗㅜㅡ 복합 모음. 자모를 알 수 없는 글자는 그대로 둔다."""
    out = []
    st = {"L": None, "V": None, "T": None}

    def flush():
        L, V, T = st["L"], st["V"], st["T"]
        if L and V and (L in _DU_OLD_LEAD or V in _DU_OLD_VOW or T in _DU_OLD_TAIL):
            lead = _DU_OLD_LEAD.get(L) or chr(0x1100 + _DU_LEAD.index(L))
            vow = _DU_OLD_VOW.get(V) or chr(0x1161 + _DU_VOWELS.index(V))
            tail = (_DU_OLD_TAIL.get(T) or chr(0x11A7 + _DU_TAIL.index(T))) if T else ""
            out.append(lead + vow + tail)
        elif L and V:
            out.append(chr(0xAC00 + (_DU_LEAD.index(L) * 21 + _DU_VOWELS.index(V)) * 28
                           + (_DU_TAIL.index(T) if T else 0)))
        else:
            out.append((L or "") + (V or ""))
        st["L"] = st["V"] = st["T"] = None

    fresh = True                             # 어두 또는 강제 분절 직후
    skip = 0
    for i, ch in enumerate(keys):
        if skip:
            skip -= 1; continue
        was_fresh, fresh = fresh, False
        if ch == "\0":                      # 내부 분절 표지
            flush(); fresh = True; continue
        if (was_fresh and ch == "t" and i + 2 < len(keys) and keys[i + 1] in _DU_SCLUSTER
                and keys[i + 2] in _DU_VOW):
            st["L"] = _DU_SCLUSTER[keys[i + 1]]; skip = 1
            continue
        if ch in _DU_CONS:
            j = _DU_CONS[ch]
            if st["L"] is None and st["V"] is None:
                st["L"] = j
            elif st["V"] is None:            # 모음 없이 자음이 이어짐
                flush(); st["L"] = j
            elif st["L"] is None:            # 홀로 모음 뒤의 자음
                flush(); st["L"] = j
            elif st["T"] is None:
                if j in _DU_TAIL or j in _DU_OLD_CONS:
                    st["T"] = j
                else:
                    flush(); st["L"] = j
            elif (st["T"], j) in _DU_TT:
                st["T"] = _DU_TT[(st["T"], j)]
            else:
                flush(); st["L"] = j
        else:
            j = _DU_VOW[ch]
            if st["L"] is None:
                if st["V"] is not None and (st["V"], j) in _DU_VV:
                    st["V"] = _DU_VV[(st["V"], j)]
                else:
                    if st["V"] is not None: flush()
                    st["V"] = j
            elif st["V"] is None:
                st["V"] = j
            elif st["T"] is None:
                if (st["V"], j) in _DU_VV:
                    st["V"] = _DU_VV[(st["V"], j)]
                else:
                    flush(); st["V"] = j
            else:
                T = st["T"]
                if T in _DU_TT_SPLIT:
                    a, b = _DU_TT_SPLIT[T]
                    st["T"] = a; flush(); st["L"] = b
                else:
                    st["T"] = None; flush(); st["L"] = T
                st["V"] = j
    flush()
    return "".join(out)


def _du_chunk(m):
    """영문자 덩어리 하나(하이픈 포함)를 변환한다."""
    parts = re.split(r"(-+)", m.group(0).replace("QD", "\1"))
    keys = []
    for part in parts:
        if part.startswith("-"):
            n = len(part)
            keys.extend(["\0"] if n == 1 else ["\0"] + ["-"] * (n - 1) + ["\0"])
        else:
            keys.extend(c if (c in _DU_CONS or c in _DU_VOW) else c.lower() for c in part)
    # 자판에 없는 글자(하이픈 리터럴 포함)는 분절로 취급해 그대로 내보낸다.
    res, buf = [], []
    for k in keys:
        if k == "\0" or k in _DU_CONS or k in _DU_VOW:
            buf.append(k)
        else:
            res.append(dubeolsik_to_hangul("".join(buf))); buf = []; res.append(k)
    res.append(dubeolsik_to_hangul("".join(buf)))
    return "".join(res)


# --- 두벌식 역변환: 한/영을 잊고 한글 모드로 쳐 버린 글(`ㅣㅐㅐㅏ`)을 영문 자판 글(`look`)로 되돌린다.
_DU_REV = {v: k for k, v in _DU_CONS.items() if k.isascii() and k.isalpha() and k not in "ADG"}
_DU_REV.update({v: k for k, v in _DU_VOW.items() if k.isascii() and k.isalpha() and k != "K"})
_DU_REV.update({"ㅿ": "A", "ㆁ": "D", "ㆆ": "G", "ㆍ": "K", "ㅸ": "QD"})
_DU_VV_REV = {v: "".join(_DU_REV[c] for c in k) for k, v in _DU_VV.items()}
_DU_TT_REV = {v: "".join(_DU_REV[c] for c in k) for k, v in _DU_TT.items()}


def _du_rev_jamo(j):
    """호환 자모 하나 → 영문 자판 키(여러 글자일 수 있음). 모르면 None."""
    return _DU_REV.get(j) or _DU_VV_REV.get(j) or _DU_TT_REV.get(j)


def hangul_to_dubeolsik(text):
    """한글(완성형 음절·호환 자모)을 두벌식 자판 위치의 영문자로 되돌린다. 한글이 아닌 글자는 그대로.
    된소리·ㅒㅖ 는 Shift 글쇠이므로 대문자가 된다(ㄲ → R)."""
    out = []
    for ch in text:
        o = ord(ch)
        if 0xAC00 <= o <= 0xD7A3:
            i = o - 0xAC00
            lead, vow, tail = i // 588, (i % 588) // 28, i % 28
            out.append(_du_rev_jamo(_DU_LEAD[lead]))
            out.append(_du_rev_jamo(_DU_VOWELS[vow]))
            if tail:
                out.append(_du_rev_jamo(_DU_TAIL[tail]))
        else:
            out.append(_du_rev_jamo(ch) or ch)
    return "".join(out)


_DU_CHUNK_RE = re.compile(r"[A-Za-z](?:[A-Za-z]|-+(?=[A-Za-z]))*")

# ------------------------------------------------------------------
# 날짜·시간 자리표시자 (%clean 전용): {YY-MM-DD} {hh:mm:ss} -> 시스템 시계의 지금
#   YYYY 4자리 연도 / YY 2자리 연도 / MM 월 / DD 일 / hh 12시간제 시 / HH 24시간제 시 / mm 분 / ss 초 (모두 0 채움)
#   토큰이 아닌 문자(- : / . 공백 한글 등)는 평범한 글자로 그대로 둔다. am/pm 은 넣지 않는다(쓰고 싶으면 직접 쓴다).
#   중괄호 안에 토큰 말고 영문자·숫자가 남으면 변환하지 않는다. 바로 앞이 글자·`}`·`]` 이면 LaTeX 인자(\SI{5}{mm})로 보고 건드리지 않는다.
# ------------------------------------------------------------------
_DT_TOKEN_RE = re.compile(r"YYYY|YY|MM|DD|hh|HH|mm|ss")
_DT_BRACE_RE = re.compile(r"(?<![\w}\]])\{([^{}\n]+)\}")


def expand_datetime_tokens(text, now=None):
    import datetime as _dt
    now = now or _dt.datetime.now()
    vals = {
        "YYYY": f"{now.year:04d}", "YY": f"{now.year % 100:02d}", "MM": f"{now.month:02d}", "DD": f"{now.day:02d}",
        "hh": f"{(now.hour % 12) or 12:02d}", "HH": f"{now.hour:02d}", "mm": f"{now.minute:02d}", "ss": f"{now.second:02d}",
    }

    def repl(m):
        body = m.group(1)
        if not _DT_TOKEN_RE.search(body) or re.search(r"[A-Za-z0-9]", _DT_TOKEN_RE.sub("", body)):
            return m.group(0)
        return _DT_TOKEN_RE.sub(lambda t: vals[t.group(0)], body)

    return _DT_BRACE_RE.sub(repl, text)


# --------------------------------------------------------------------------
# 고전 그리스어(Beta Code → 폴리토닉 그리스어)
# --------------------------------------------------------------------------
# TLG·Perseus 의 Beta Code 를 쓴다. 글자 뒤에 기호를 붙인다: `a)/nqrwpos` → ἄνθρωπος.
#   글자  a b g d e z h q i k l m n c o p r s t u f x y w v(ϝ)
#   기호  )부드러운 숨  (거센 숨  /예음  \억음  =곡절  +분음  |아래 iota
#   대문자  `*` 를 글자 앞에(`*a`, 기호는 `*` 와 글자 사이 `*)/a` 이거나 글자 뒤 `*a)/`) 두거나, 영문 대문자(`A`)
#   시그마  `s` 는 낱말 끝에서 ς, 그 밖에서 σ. `s1`=σ  `s2`=ς  `s3`=ϲ(달 모양) 로 강제
#   문장부호  `:` → · (ano teleia)   `'` → ’ (생략)   `;` 는 그대로(그리스어 물음표와 정규화로 같다)
# 결합 기호는 정해진 차례(분음 → 숨 → 악센트 → 아래 iota)로 세운 뒤 NFC 로 완성형(U+1F00대)으로 합친다.
_GRC_LETTERS = {
    "a": "α", "b": "β", "g": "γ", "d": "δ", "e": "ε", "z": "ζ", "h": "η", "q": "θ", "i": "ι",
    "k": "κ", "l": "λ", "m": "μ", "n": "ν", "c": "ξ", "o": "ο", "p": "π", "r": "ρ", "t": "τ",
    "u": "υ", "f": "φ", "x": "χ", "y": "ψ", "w": "ω", "v": "ϝ",
}
_GRC_CAPITALS = {k: unicodedata.normalize("NFC", v.upper()) for k, v in _GRC_LETTERS.items()}
_GRC_CAPITALS["v"] = "Ϝ"
_GRC_MARKS = {")": "\u0313", "(": "\u0314", "/": "\u0301", "\\": "\u0300", "=": "\u0342",
              "+": "\u0308", "|": "\u0345"}
_GRC_RANK = {"\u0308": 0, "\u0313": 1, "\u0314": 1, "\u0300": 2, "\u0301": 2, "\u0342": 2, "\u0345": 3}
_GRC_RE = re.compile(
    r"(?:(?P<star>\*)(?P<pre>[)(/\\=+|]*))?"
    r"(?:(?P<sig>[sS])(?P<sv>[123])|(?P<l>[A-Za-z]))"
    r"(?P<post>[)(/\\=+|]*)")


def betacode_to_greek(text):
    """Beta Code 를 폴리토닉 그리스어(NFC)로. 변환표에 없는 글자(j 등)와 숫자·공백은 그대로 둔다."""
    def repl(m):
        letter = (m.group("sig") or m.group("l")).lower()
        capital = bool(m.group("star")) or (m.group("sig") or m.group("l")).isupper()
        marks = (m.group("pre") or "") + (m.group("post") or "")
        if letter == "s":
            sv = m.group("sv")
            if sv == "3":
                base = "Ϲ" if capital else "ϲ"
            elif sv == "2":
                base = "Σ" if capital else "ς"
            elif sv == "1":
                base = "Σ" if capital else "σ"
            else:
                src, a, b = m.string, m.start(), m.end()
                prev_letter = a > 0 and (src[a - 1].isascii() and src[a - 1].isalpha() or src[a - 1] in ")(/\\=+|")
                next_letter = b < len(src) and ((src[b].isascii() and src[b].isalpha()) or src[b] == "*")
                final = prev_letter and not next_letter
                base = "Σ" if capital else ("ς" if final else "σ")
        elif letter in _GRC_LETTERS:
            base = _GRC_CAPITALS[letter] if capital else _GRC_LETTERS[letter]
        else:
            return m.group(0)
        seq = sorted((_GRC_MARKS[c] for c in marks), key=_GRC_RANK.get)
        return base + "".join(seq)
    out = _GRC_RE.sub(repl, text)
    out = out.replace(":", "\u00b7").replace("'", "\u2019")
    return unicodedata.normalize("NFC", out)


# ── 마소라 히브리어 (Michigan–Claremont 방식) ──────────────────────────────
# 자음 대문자, 모음·부호는 자음 뒤에 쓴다. 어말형(ך ם ן ף ץ)은 자동. 결과는 NFC(결합 부호는 정준 순서로 정렬).
_HE_CONS = {")": "\u05D0", "B": "\u05D1", "G": "\u05D2", "D": "\u05D3", "H": "\u05D4",
            "W": "\u05D5", "Z": "\u05D6", "X": "\u05D7", "+": "\u05D8", "Y": "\u05D9", "K": "\u05DB",
            "L": "\u05DC", "M": "\u05DE", "N": "\u05E0", "S": "\u05E1", "(": "\u05E2", "P": "\u05E4",
            "C": "\u05E6", "Q": "\u05E7", "R": "\u05E8", "T": "\u05EA"}
_HE_FINAL = {"\u05DB": "\u05DA", "\u05DE": "\u05DD", "\u05E0": "\u05DF", "\u05E4": "\u05E3", "\u05E6": "\u05E5"}
_HE_SIN = {"$": "\u05E9\u05C1", "#": "\u05E9\u05C2"}
_HE_MARKS = {"A": "\u05B7", "F": "\u05B8", "E": "\u05B6", ",": "\u05B5", "I": "\u05B4",
             "O": "\u05B9", "U": "\u05BB", ":": "\u05B0", ".": "\u05BC"}
_HE_HATAF = {"A": "\u05B2", "E": "\u05B1", "F": "\u05B3"}


def betacode_to_hebrew(text):
    """Michigan–Claremont 식 로마자 → 마소라 히브리어(유니코드, NFC).
    ) ב… 자음 + 모음 A F E , I O U : . ;  `$` `#` 은 쉰·씬, `-` 막케프, `;` 소프 파숙."""
    out = []
    n = len(text)
    i = 0
    last_cons = -1            # 자음 뒤인지(부호를 읽을 수 있는지)
    while i < n:
        ch = text[i]
        u = ch.upper()
        base = None
        if u in _HE_CONS:
            base = _HE_CONS[u]
        elif ch in _HE_SIN:
            base = _HE_SIN[ch]
        if base is not None:
            out.append(base)
            last_cons = len(out) - 1
            i += 1
            continue
        if last_cons >= 0:    # 자음 바로 뒤(또는 앞선 부호 뒤)의 부호
            if ch == ":" and i + 1 < n and text[i + 1].upper() in _HE_HATAF:
                out.append(_HE_HATAF[text[i + 1].upper()]); i += 2; continue
            if ch in ".,:" or u in "AEIOUF":
                out.append(_HE_MARKS[u]); i += 1; continue
        if ch == "-":
            out.append("\u05BE")
        elif ch == ";":
            out.append("\u05C3")
        else:
            out.append(ch)
        # 자음이 아닌 글자(공백·구두점)는 낱말을 끊는다
        last_cons = -1
        i += 1
    # 어말형: 낱말 안 마지막 자음 위치 찾기
    res = "".join(out)
    chars = list(res)
    j = 0
    L = len(chars)
    while j < L:
        c = chars[j]
        if c in _HE_FINAL:
            m = j + 1
            while m < L and (0x0591 <= ord(chars[m]) <= 0x05C7) and chars[m] != "\u05BE" and chars[m] != "\u05C3":
                m += 1
            if m >= L or not ("\u05D0" <= chars[m] <= "\u05EA"):
                chars[j] = _HE_FINAL[c]
        j += 1
    return unicodedata.normalize("NFC", "".join(chars))


def convert_text(text, engine_mode="pm"):
    if not text: return ""

    # 고전 그리스어 — Beta Code 의 `\` `/` `(` `)` 등이 LaTeX 확장·명령어 보호와 겹치므로 그 앞에서 끝낸다.
    if engine_mode == "grc":
        return betacode_to_greek(text)
    if engine_mode == "he":
        return betacode_to_hebrew(text)

    # 한글 자판으로 잘못 친 영문 되돌리기 — 입력이 이미 한글이므로 LaTeX 확장·로마자 보호를 거치지 않는다.
    if engine_mode == "dubeol_rev":
        return hangul_to_dubeolsik(text)

    # ==========================================
    # 0. LaTeX 입력 확장 (모든 입력 메서드 공통, 최우선 처리)
    #    확장 결과는 PUA 마커로 봉인해 두었다가 마지막에 복원한다.
    # ==========================================
    latex_saved = []
    text = expand_latex_input(text, protect=latex_saved)

    if engine_mode == "transparent":
        return expand_datetime_tokens(restore_latex_input(text, latex_saved))

    # ==========================================
    # 1. 라틴 문자 보호 구문 및 LaTeX 명령어 보호
    # ==========================================
    # 1) (\\[^\s\\].*?\\[ \t]) : 시작은 '\' + 공백아님, 끝은 '\' + 공백/탭 (\Apple\ )
    # 2) (\\[a-zA-Z]+(?:\[[^\]]*\])?(?:\s*\{?)?) : 일반 LaTeX 명령어 (\Apple 등)
    cmd_pattern = (
        r"(\\[^\s\\].*?\\[ \t])"              # 기존: \Word ... \[space] 리터럴 보호
        r"|(\\(?:begin|end)\{[^}]*\})"        # 신규: \begin{...} / \end{...} 환경 이름 통째 보호
        r"|(\\[a-zA-Z]+(?:\[[^\]]*\])?(?:\s*\{?)?)"  # 기존: 일반 명령어(인자는 변환 대상으로 남김)
    )
    saved_commands = []

    def replacer(match):
        cmd = match.group(0)
        saved_commands.append(cmd)
        return f"999{len(saved_commands)-1:03d}"

    protected_text = re.sub(cmd_pattern, replacer, text)

    # ==========================================
    # 2. 치환
    # ==========================================
    # 호환자모 처리
    if engine_mode in ("pm", "pmfrk"):
        sorted_generic = sorted(pm_map["generic"].items(), key=lambda x: len(x[1]), reverse=True)
        for kor_char, rom_upper in sorted_generic:
            protected_text = protected_text.replace(rom_upper, kor_char)

    # 숫자+대괄호 치환
    sorted_brackets = sorted(bracket_map.items(), key=lambda x: len(x[0]), reverse=True)
    for key, (open_bracket, close_bracket) in sorted_brackets:
        protected_text = protected_text.replace(f"{key}[", open_bracket)
        protected_text = protected_text.replace(f"{key}]", close_bracket)

    # 방점 보호
    hat_markers = {}
    for i, (k, v) in enumerate(hat_map.items()):
        marker = f"888{i:02d}" 
        hat_markers[marker] = v
        protected_text = protected_text.replace(k, marker)

    # 자음 분리 (rrk, pmfrk)
    if engine_mode in ("pmfrk", "rrk"):        
        # 1. 'ss'로 시작하는 그룹 처리
        protected_text = re.sub(r"ss([sgdbj])", r"ss-\1", protected_text)
        
        # 2. 'ggg' 처리
        protected_text = protected_text.replace("ggg", "g-gg")
        
        # 3. 모음 사이의 sg, sd, sb, sch, sj 분리 
        # 어두나 기분리된 하이픈(-sg)에서는 무시하고 오직 모음(a,e,i,o,u,w,y) 사이에서만 동작
        protected_text = re.sub(r"(?<=[aeiouwyAEIOUWY])s(g|d|b|ch|j)(?=[aeiouwyAEIOUWY])", r"s-\1", protected_text)
        
        # 4. (기존 pmfrk 전용) sss 패턴 추가 처리
        if engine_mode == "pmfrk":
            vowels = "aeiouAEIOU"
            sss_pattern = rf"([{vowels}])sss([{vowels}])"
            protected_text = re.sub(sss_pattern, r"\1ss-s\2", protected_text)

    # 단어 단위 분리 및 변환
    if engine_mode in ("pm", "frkim", "pmfrk", "rrk"):  # "rrk" 추가
        def replacer_chunk(m):
            return parse_auto_chunk(m.group(1), engine_mode)
        
        chunk_pattern = r"([a-zA-Z\@\*\-\/\'\:\;]+)"
        intermediate = re.sub(chunk_pattern, replacer_chunk, protected_text)
    elif engine_mode == "dubeol":
        intermediate = _DU_CHUNK_RE.sub(_du_chunk, protected_text)
    elif engine_mode == "kana":
        intermediate = romaji_to_kana_convert(protected_text) 
    else:
        intermediate = protected_text

    # ==========================================
    # 3. 복원 로직
    # ==========================================
    for idx, orig_cmd in enumerate(saved_commands):
        marker = f"999{idx:03d}"
        
        # 라틴 문자 보호 구문 (끝이 백슬래시+공백)
        if orig_cmd.endswith('\\ ') or orig_cmd.endswith('\\\t'):
            # 맨 앞의 '\'(1글자)와 맨 뒤의 '\ '(2글자) 완벽 제거
            pure_latex_cmd = orig_cmd[1:-2]
        else:
            # 일반 LaTeX 명령어 복원
            if orig_cmd.startswith("\\\\"):
                pure_latex_cmd = "\\" + orig_cmd[2:]
            else:
                pure_latex_cmd = orig_cmd.replace("\\\\", "\\")
                
        intermediate = intermediate.replace(marker, pure_latex_cmd)

    # 방점 기호 복원
    for marker, char in hat_markers.items():
        intermediate = intermediate.replace(marker, char)

    # LaTeX 확장 문자 복원
    intermediate = restore_latex_input(intermediate, latex_saved)

    return intermediate


# NFD 출력 시 한글만 분해하고 라틴 확장문자는 결합형으로 유지할지 여부
NFD_HANGUL_ONLY = True

def _is_hangul_char(ch):
    code = ord(ch)
    return (0xAC00 <= code <= 0xD7A3 or   # 한글 음절
            0x1100 <= code <= 0x11FF or   # 한글 자모
            0xA960 <= code <= 0xA97F or   # 한글 자모 확장 A
            0xD7B0 <= code <= 0xD7FF)     # 한글 자모 확장 B

def normalize_output(text, norm_mode="NFD", hangul_only=None):
    if not text: return ""
    if hangul_only is None:
        hangul_only = NFD_HANGUL_ONLY
    # NFD를 문자열 전체에 걸면 \'e -> e+U+0301 처럼 라틴 확장문자까지 분해된다.
    # 옛한글 조합에 필요한 것은 한글 분해뿐이므로 한글 문자에만 선택 적용한다.
    if norm_mode == "NFD" and hangul_only:
        return "".join(unicodedata.normalize("NFD", ch) if _is_hangul_char(ch) else ch
                       for ch in text)
    return unicodedata.normalize(norm_mode, text)


# --------------------------------------------------------------------------
# 사용자 한자 사전(customkanji.json) 관리 — {h:키} -> 한자
# --------------------------------------------------------------------------

def custom_kanji_write_path():
    """사용자 사전을 저장할 경로. 지금 쓰는 파일이 쓰기 가능한 일반 위치면 그 파일, 아니면(읽기 전용 폴더·
    PyInstaller 번들 안쪽) 사용자 데이터 폴더."""
    found = find_file("customkanji.json")
    meipass = getattr(sys, "_MEIPASS", None)
    if found:
        inside_bundle = bool(meipass) and os.path.abspath(found).startswith(os.path.abspath(meipass))
        if not inside_bundle and os.access(found, os.W_OK) and os.access(os.path.dirname(found), os.W_OK):
            return found
    return os.path.join(user_data_dir(), "customkanji.json")


def load_custom_kanji():
    """지금 적용 중인 사용자 사전({키: 값})의 사본."""
    return dict(kanji_tables.get("custom_kana", {}))


def save_custom_kanji(data):
    """사전을 파일에 쓰고 메모리 표를 다시 읽는다. 쓴 경로를 돌려준다(실패하면 OSError)."""
    path = custom_kanji_write_path()
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=4)
    os.replace(tmp, path)
    load_kanji_tables()
    return path


def _bare_key(key):
    key = key.strip()
    if key.startswith("{h:") and key.endswith("}"):
        key = key[3:-1]
    return key


def add_custom_word(key, val):
    """새 단어를 등록한다. 키는 `{h:키}` 꼴로 저장하고, 이미 있으면 키 뒤에 01, 02… 를 붙인다.
    저장된 최종 키를 돌려준다."""
    base_key, val = _bare_key(key), val.strip()
    if not base_key or not val:
        raise ValueError("키와 값이 모두 있어야 합니다")
    data = load_custom_kanji()
    final_key = "{h:%s}" % base_key
    if final_key in data:
        for i in range(1, 100):
            cand = "{h:%s%02d}" % (base_key, i)
            if cand not in data:
                final_key = cand
                break
    data[final_key] = val
    save_custom_kanji(data)
    return final_key


def update_custom_word(old_key, new_key, new_val):
    """단어의 키·값을 고친다. 바뀐 키가 다른 단어와 겹치면 ValueError. 최종 키를 돌려준다."""
    base_key, new_val = _bare_key(new_key), new_val.strip()
    if not base_key or not new_val:
        raise ValueError("키와 값이 모두 있어야 합니다")
    final_key = "{h:%s}" % base_key
    data = load_custom_kanji()
    if final_key != old_key and final_key in data:
        raise ValueError("이미 있는 키입니다: " + final_key)
    # 순서를 유지한 채 교체
    data = {(final_key if k == old_key else k): (new_val if k == old_key else v)
            for k, v in data.items()}
    save_custom_kanji(data)
    return final_key


def delete_custom_word(key):
    data = load_custom_kanji()
    if key in data:
        del data[key]
        save_custom_kanji(data)
        return True
    return False


# --------------------------------------------------------------------------
# 입력 전체(여러 줄, 행별 % 태그 포함) 변환 — GUI/Writer 공통
# --------------------------------------------------------------------------
ENGINE_MODES = ["pm", "frkim", "pmfrk", "rrk", "dubeol", "dubeol_rev", "kana", "grc", "he", "transparent"]
HANJA_MODES = ["none", "shinjitai", "kyujitai", "simplified", "hanja"]

_LINE_TAG_RE = re.compile(r"^%(pm|frk|mix|rrk|du|ed|jp|grc|he|clean|uc|lc|tc)(?:\[(shin|kyu|sim|none|han)\])?")
_TAG_MODE = {"pm": "pm", "frk": "frkim", "mix": "pmfrk", "rrk": "rrk", "du": "dubeol", "ed": "dubeol_rev", "jp": "kana", "grc": "grc", "he": "he", "clean": "transparent"}
#: 대소문자 태그 — `%uc` 대문자, `%lc` 소문자, `%tc` 낱말마다 첫 글자만 대문자(나머지는 그대로).
#: 변환 방식은 언제나 `clean`(transparent)이다: LaTeX 입력 확장만 하고, 그 결과에 대소문자를 적용한다.
#: 태그를 쓰지 않는 한 켜지지 않으며 입력기 콤보에도 없다.
_TAG_CASE = {"uc": "upper", "lc": "lower", "tc": "title"}
_CASE_SKIP_RE = re.compile(
    r"(\\(?:[A-Za-z@]+\*?|.)"          # \명령 이름(과 \% 같은 이스케이프) — 건드리지 않는다
    r"|\$[^$\n]*\$|\\\([^\n]*?\\\))")   # $수식$ , \(수식\)


def apply_case(text, how):
    """how = upper / lower / title. LaTeX 명령 이름과 수식은 그대로 두고 나머지에만 적용한다.
    title 은 공백으로 갈린 낱말마다 첫 글자(앞의 괄호·따옴표 같은 문장부호는 건너뜀)만 대문자로
    바꾸고 낱말의 나머지는 건드리지 않는다."""
    def conv(seg):
        if how == "upper":
            return seg.upper()
        if how == "lower":
            return seg.lower()
        def word(m):
            w = m.group(0)
            for i, ch in enumerate(w):
                if ch.isalpha():
                    return w[:i] + ch.title() + w[i + 1:]
            return w
        return re.sub(r"\S+", word, seg)
    out, pos = [], 0
    for m in _CASE_SKIP_RE.finditer(text):
        out.append(conv(text[pos:m.start()]))
        out.append(m.group(0))
        pos = m.end()
    out.append(conv(text[pos:]))
    return "".join(out)


_TAG_HANJA = {"shin": "shinjitai", "kyu": "kyujitai", "sim": "simplified", "none": "none", "han": "hanja"}


def convert_input(text, engine_mode="pm", hanja_mode="none", norm_mode="NFD"):
    """여러 줄 입력을 줄마다 변환한다. 줄 첫머리의 `%pm` `%frk[shin]` 같은 태그는 그 줄만
    엔진/한자 필터를 바꾼다. kana 엔진 줄은 정규화하지 않는다."""
    out = []
    for line in text.split("\n"):
        mode, hmode, clean, case = engine_mode, hanja_mode, line, None
        m = _LINE_TAG_RE.match(line)
        if m:
            case = _TAG_CASE.get(m.group(1))
            mode = "transparent" if case else _TAG_MODE[m.group(1)]
            if m.group(2):
                hmode = _TAG_HANJA[m.group(2)]
            clean = re.sub(r"^\s+", "", line[m.end():])
        conv = convert_text(clean, engine_mode=mode)
        if case:
            conv = apply_case(conv, case)
        conv = filter_kanji(conv, hanja_mode=hmode)
        if mode not in ("kana", "grc", "he"):       # 가나·그리스어는 한글 자모 정규화를 거치지 않는다
            conv = normalize_output(conv, norm_mode=norm_mode)
        out.append(conv)
    return "\n".join(out)


def process_tags_mixed(text):
    def repl_kr_pm(m): return convert_text(m.group(1), engine_mode="pm")
    def repl_kr_frk(m): return convert_text(m.group(1), engine_mode="frkim")
    def repl_jp_mixed(m): return romaji_to_kana_convert(m.group(1))

    text = re.sub(r"<kr>(.*?)</kr>", repl_kr_pm, text, flags=re.DOTALL)
    text = re.sub(r"<kr:frk>(.*?)</kr:frk>", repl_kr_frk, text, flags=re.DOTALL)
    text = re.sub(r"<jp>(.*?)</jp>", repl_jp_mixed, text, flags=re.DOTALL)
    return text


def process_latex_text(text, target_name="jamoword", mode="macro", keep_structure=False, engine_mode="pm"):
    clean_name = target_name.lstrip('\\').replace('begin{', '').replace('}', '')
    result = []
    i = 0
    if mode == "env":
        start_tag = f"\\begin{{{clean_name}}}"
        end_tag = f"\\end{{{clean_name}}}"
        while i < len(text):
            idx = text.find(start_tag, i)
            if idx == -1: result.append(text[i:]); break
            result.append(text[i:idx])
            start_content = idx + len(start_tag)
            end_idx = text.find(end_tag, start_content)
            if end_idx != -1:
                inner_text = text[start_content:end_idx]
                converted = convert_text(inner_text, engine_mode=engine_mode)
                result.append(f"{start_tag}{converted}{end_tag}" if keep_structure else converted)
                i = end_idx + len(end_tag)
            else: result.append(text[idx:start_content]); i = start_content
    else:
        target = f"\\{clean_name}{{"
        while i < len(text):
            idx = text.find(target, i)
            if idx == -1: result.append(text[i:]); break
            result.append(text[i:idx])
            start_content = idx + len(target)
            brace_count = 1
            j = start_content
            while j < len(text) and brace_count > 0:
                if text[j] == '{': brace_count += 1
                elif text[j] == '}': brace_count -= 1
                j += 1
            if brace_count == 0:
                roman_text = text[start_content:j-1]
                converted = convert_text(roman_text, engine_mode=engine_mode)
                result.append(f"\\{clean_name}{{{converted}}}" if keep_structure else converted)
                i = j
            else: result.append(text[idx:start_content]); i = start_content
    return "".join(result)

# ==============================================================================
# CLI 및 전체 런타임 제어 엔트리 포인트
# ==============================================================================
