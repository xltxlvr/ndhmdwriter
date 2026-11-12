# ndhmdWriter

A desktop authoring editor for **ndhmd** — a Markdown dialect that compiles to
LaTeX (and PDF) through [ndhmd4tex](#related-tools). It is built with Python and
PySide6, ships as a single file, and is designed around writing long, structured,
Korean-language manuscripts: books made of chapters, with cross-references,
bibliographies, math, figures and tables.

The UI is available in **Korean** (default) and **English**
(*Settings ▸ Language*, applied on restart). The user manual (`MANUAL.md`) is
currently Korean only.

## Highlights

**Writing**
- Syntax highlighting for ndhmd, including inline markup, `:::{environment}` blocks,
  code fences, YAML front matter and `.bib`/`.yaml` auxiliary files.
- Smart quotes and punctuation, list-aware Enter and indentation, heading-level
  shifting, paragraph reflow, and wrapping/unwrapping selections as lists,
  blockquotes, fences or environments.
- Folding of front matter, bibliography, fences and environments.
- Navigation history (back/forward), reference ↔ definition jumping, Ctrl+click on
  URLs.
- Find bar with history; replace in the current file, the selection, or the whole
  workspace.

**Books and structure**
- *Workspace* and *drawer*: a book is a top-level file that `{{include}}`s chapter
  files. Drag and drop restructures the book; split a file by chapter or merge
  sub-files back.
- Per-file tags, memos and synopsis *cards* (card view of a whole book).
- Label flags, TOC and cross-reference / image / markup checks.

**Live preview**
- Math (rendered through TeX), pipe and grid tables, and images (local and remote,
  with optional auto-fetch off by default) appear in a side panel when the cursor
  rests on them.

**Tools**
- Math editor and symbol table, with grid editing for matrices and environments.
- Snippet figures (TikZ and friends) compiled to PDF figures and re-editable.
- Simple table editor (pipe and pandoc-style grid tables; merged cells can be sent
  to the standalone *tblrDoumi* app).
- Color palette, accent/IPA helper input, abbreviation slots, bibliography editor
  and citation insertion.
- CJK input helpers: `pm` romanization input (Korean, Japanese, Chinese), hanja
  conversion (F9), Japanese user-kanji dictionary, dictionary lookup from the
  context menu (URLs configurable).
- Optional AI assistant (experimental): sends the selected text to an installed
  command-line AI tool you configure; nothing is sent unless you invoke it.

**Compile and sync**
- Compile the whole book or one file with `latexmk` or `ksruncltex`; errors are
  traced back to source lines.
- Forward and reverse search with PDF viewers (SumatraPDF, Skim, Okular) through
  ndhmdsync.

## Requirements

| Component | Needed for |
|---|---|
| Python 3.9+ and **PySide6 ≥ 6.5** | the app itself (required) |
| **PyYAML ≥ 6.0** | front matter features (strongly recommended) |
| `modulegraph` | listed in `requirements.txt` |
| [ndhmd4tex](#related-tools) | markup check, conversion, compile |
| ndhmdsync | forward/reverse PDF search |
| TeX Live, `ksruncltex` or `latexmk` | compile, math preview, snippet figures |
| `dvisvgm`, `pdftocairo` or `pdftoppm` | math preview images |
| Pillow (optional) | converting webp/tiff/gif images |

Windows, macOS and Linux are supported. Everything except the editor itself
degrades gracefully when its external tool is missing; the app tells you which
tool it could not find and lets you point to it.

## Installation and running

```sh
pip install PySide6 pyyaml modulegraph      # add Pillow if you use webp/tiff/gif
python ndhmdWriter.py [file.md]
```

Keep these files in the same folder as `ndhmdWriter.py`:
`pmime_core.py` (pm input), `hanja_core.py` and its dictionary `hanja.txt`
(hanja conversion), `ndhmdMath.py` (math editor), and optionally `fontselector.py`.

To start in English without changing the saved setting:

```sh
NDHMD_LANG=en python ndhmdWriter.py
```

On first launch choose a **workspace folder**; opening, saving and searching
happen inside it. In the app, **Help ▸ About / Shortcuts** lists the key bindings,
and **Settings ▸ Preferences ▸ PDF viewer reverse search ▸ Register now** sets up
Ctrl+click from the PDF back to the source.

## Language support

Switching to English translates menus, dialogs, messages, tooltips and the status
bar at the point where text reaches Qt, so the Korean code path is untouched. User
text (manuscripts, file names, tags, memos) and the instructions sent to the AI
assistant are never translated. Untranslated strings simply stay in Korean.

## Related tools

- **ndhmd4tex** — the ndhmd → LaTeX converter (0.20.0), including pandoc-style
  grid tables.
- **ndhmdsync** (0.5.6) — source ↔ PDF synchronization.
- **ksruncltex** — a cluttex wrapper used as a compile backend.
- **tblrDoumi** — a standalone table-to-LaTeX helper; the Writer exchanges tables
  with it as `.tblr` JSON.
- **pmime** (core 0.17.1) — the CJK romanization input engine.

## Documentation

- `MANUAL.md` — full reference manual (Korean), itself written in ndhmd.
- `CHANGELOG.md` — release history (Korean).

## Status and limitations

0.5.0 is the first release without the beta label. The test suite is an informal
set of offscreen checks; some features (real mouse interaction, launching the
packaged tblrDoumi, macOS-specific behavior) have been verified less than others.
Bug reports are welcome.



# ndhmdSuite

ndhmdSuite is an all-in-one installer designed to set up the ndhmd environment on Windows. It includes the following components:

- **ndhmd4tex**: A command-line utility that parses the ndhmarkdown language and converts it into TeX.
- **ndhmd2html**: A command-line utility that converts ndhmarkdown into (X)HTML.
- **ndhmdsync**: A utility that enables inverse and forward search between the editor and the PDF viewer.
- **ndhmdWriter**: A dedicated editor for ndhmd.
- **ksruncltex**: A cluttex wrapper used for compilation.

Please refer to the following links:

- Intro (in Korean): https://nonametex.imweb.me/intro/?bmode=view&idx=174387790
- Download: https://drive.google.com/file/d/1sEWJ3L15oYN1hjQyb1cUia1nzbuv5Cuu/view?usp=sharing



# License

MIT. The hanja conversion dictionary is `hanja.txt` from **libhangul**
(Copyright © 2005, 2006 Choe Hwanjin) and the symbol dictionary `mssymbol.txt`
(Copyright © 2005–2014 Choe Hwanjin), distributed under the BSD license; see the
notice in *Help ▸ About*.
