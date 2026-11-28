# -*- coding: utf-8 -*-
"""
PDF / HWPX → MD 변환기  (진행도 표시 + 속도 개선판)
- 창에 파일(또는 폴더)을 끌어다 놓아 추가, 여러 개 가능
- 선택 삭제 / 전체 삭제 / Delete 키로 제거
- [기존 폴더에 저장하기] : 원본 파일이 있는 폴더에 .md 로 저장
- [다른 폴더에 저장하기] : 폴더를 선택해서 .md 로 저장
- 변환 중 진행 팝업: 쪽(페이지) 단위 진행도 + 남은 시간 + [취소]
- 속도: PDF는 여러 쪽 묶음으로 나눠 동시에(최대 4개) 변환
- 프로그램을 켜면 새 버전이 있는지 확인하고, 있으면 업데이트 안내 팝업을 띄움
  (인터넷이 막혀 있거나 확인에 실패하면 아무 팝업 없이 조용히 넘어감)

설치:  pip install pymupdf4llm tkinterdnd2
exe 만들 때:  PyInstaller 옵션에 --collect-all pymupdf --collect-all pymupdf4llm 을 꼭 넣을 것
             (빠지면 PDF 변환에 필요한 파일이 없어 모든 PDF 변환이 실패함)
"""
import os
import sys
import json
import queue
import threading
import time
import zipfile
import re
import multiprocessing
import urllib.request
import webbrowser
from concurrent.futures import ProcessPoolExecutor, wait, FIRST_COMPLETED
import xml.etree.ElementTree as ET
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

# exe(--noconsole)로 만들었을 때 출력 대상이 없어서 생기는 오류 방지
if sys.stdout is None:
    sys.stdout = open(os.devnull, "w")
if sys.stderr is None:
    sys.stderr = open(os.devnull, "w")

# 현재 프로그램의 버전 (exe를 새로 만들 때마다 이 숫자를 올려주세요)
CURRENT_VERSION = "1.0.2"
# 최신 버전 정보(version.json)가 있는 위치
VERSION_INFO_SOURCE = "https://raw.githubusercontent.com/tworemind-cpu/md_converter/main/version.json"
UPDATE_TIMEOUT_SEC = 5      # 정보를 읽을 때 기다리는 최대 시간(초)

SUPPORTED = (".pdf", ".hwpx")
MAX_WORKERS = 4             # 동시에 돌리는 변환 일꾼(프로세스) 수의 상한
CHUNK_PAGES = 8             # PDF를 일꾼에게 나눠 줄 때 한 묶음의 쪽수


class Cancelled(Exception):
    """사용자가 취소했을 때"""


# ──────────────────────────────────────────────
# 0) 변환 일꾼(별도 프로세스)에서 쓰는 공용 변수
# ──────────────────────────────────────────────
_mpq = None        # 일꾼 → 화면: 쪽 진행 상황 전달용
_mpcancel = None   # 화면 → 일꾼: 취소 신호


def _init_worker(q, cancel):
    global _mpq, _mpcancel
    _mpq = q
    _mpcancel = cancel


# ──────────────────────────────────────────────
# 1) PDF → MD  (쪽 묶음 단위로 변환하면서 진행 상황을 알림)
# ──────────────────────────────────────────────
def _limit_ai_threads():
    """배치 분석 AI(onnxruntime)가 CPU를 독차지하지 않게 스레드 수를 제한.
    기본 설정은 대기 중에도 CPU를 계속 돌려(spinning) 변환이 몇 배 느려짐.
    pymupdf4llm 을 불러오기 '전에' 실행해야 함. 변환 결과는 달라지지 않음."""
    import onnxruntime as ort
    if getattr(ort.InferenceSession, "_limited", False):
        return
    threads = 2 if (os.cpu_count() or 2) >= 8 else 1
    base = ort.InferenceSession

    class LimitedSession(base):
        _limited = True

        def __init__(self, path, sess_options=None, *args, **kwargs):
            so = sess_options or ort.SessionOptions()
            so.intra_op_num_threads = threads
            so.inter_op_num_threads = 1
            so.add_session_config_entry("session.intra_op.allow_spinning", "0")
            super().__init__(path, so, *args, **kwargs)

    ort.InferenceSession = LimitedSession


def pdf_page_count(path):
    import pymupdf
    with pymupdf.open(path) as doc:
        if doc.needs_pass:
            raise ValueError("암호가 걸린 PDF입니다")
        if doc.page_count == 0:
            raise ValueError("페이지가 없는 PDF입니다")
        return doc.page_count


def pdf_chunk_to_md(path, first, last, idx=None):
    """first 쪽부터 last 쪽 앞까지(0부터 셈) 변환. (쪽별 글자 목록, 일반 글자로만 된 쪽) 반환"""
    try:
        _limit_ai_threads()
        import pymupdf4llm
    except ImportError:
        raise RuntimeError("pymupdf4llm 이 설치되지 않았습니다 (pip install pymupdf4llm)")
    import pymupdf

    parts = []
    bad_pages = []
    with pymupdf.open(path) as doc:
        for p in range(first, last):
            if _mpcancel is not None and _mpcancel.is_set():
                raise Cancelled()
            try:
                # use_ocr=False : 글자 인식(OCR)은 지원하지 않으므로, 쪽마다 OCR 프로그램을 찾는 시간을 없앰
                md = pymupdf4llm.to_markdown(doc, pages=[p], show_progress=False, use_ocr=False)
            except Exception:
                bad_pages.append(p + 1)
                try:
                    md = doc[p].get_text("text")
                except Exception:
                    md = ""
            parts.append(md)
            if _mpq is not None and idx is not None:
                _mpq.put(("page", idx))
    return parts, bad_pages


def join_pdf_parts(parts, bad_pages):
    """쪽별 결과를 하나의 MD 로 합침"""
    md = "\n\n".join(parts)
    if not md or not md.strip():
        raise ValueError("추출된 텍스트가 없습니다 (스캔본·이미지 PDF일 수 있음)")
    if bad_pages:
        md += "\n\n<!-- 일반 글자로만 변환된 쪽: %s -->\n" % ", ".join(map(str, bad_pages[:50]))
    return md

# ──────────────────────────────────────────────
# 2) HWPX → MD  (hwpx 는 zip 안에 XML 이 들어 있는 형식)
# ──────────────────────────────────────────────
def _local(tag):
    """'{네임스페이스}p' → 'p'"""
    return tag.rsplit("}", 1)[-1]


def _t_text(t):
    """<hp:t> 안의 글자 (탭·줄바꿈 등은 공백으로)"""
    s = t.text or ""
    for c in t:
        if _local(c.tag) in ("lineBreak", "tab", "fwSpace", "nbSpace"):
            s += " "
        else:
            s += c.text or ""
        s += c.tail or ""
    return s


def _para_text(p):
    """문단(<hp:p>) 하나의 글자. 표 안의 글자는 제외."""
    out = []
    for run in p:
        if _local(run.tag) != "run":
            continue
        for child in run:
            name = _local(child.tag)
            if name == "t":
                out.append(_t_text(child))
            elif name == "tab":
                out.append(" ")
    return "".join(out).strip()


def _cell_text(tc):
    parts = []
    for el in tc.iter():
        if _local(el.tag) == "p":
            t = _para_text(el)
            if t:
                parts.append(t)
    return "<br>".join(parts)


def _table_md(tbl):
    rows = []
    for tr in tbl:
        if _local(tr.tag) != "tr":
            continue
        row = []
        for tc in tr:
            if _local(tc.tag) != "tc":
                continue
            text = _cell_text(tc).replace("|", "\\|")
            span = 1
            for e in tc:
                if _local(e.tag) == "cellSpan":
                    try:
                        span = max(1, int(e.get("colSpan", "1")))
                    except ValueError:
                        span = 1
            row.append(text)
            row.extend([""] * (span - 1))
        if row:
            rows.append(row)
    if not rows:
        return ""
    # 칸이 1개뿐인 표(박스)는 그냥 글자로
    if len(rows) == 1 and len(rows[0]) == 1:
        return rows[0][0].replace("<br>", "\n")
    width = max(len(r) for r in rows)
    rows = [r + [""] * (width - len(r)) for r in rows]
    lines = ["| " + " | ".join(rows[0]) + " |", "|" + "---|" * width]
    for r in rows[1:]:
        lines.append("| " + " | ".join(r) + " |")
    return "\n".join(lines)


def hwpx_to_md(path):
    if not zipfile.is_zipfile(path):
        raise ValueError("hwpx 형식이 아닙니다 (옛 .hwp 파일이거나 손상된 파일)")
    blocks = []
    with zipfile.ZipFile(path) as zf:
        sections = []
        for name in zf.namelist():
            m = re.match(r"(?i)^Contents/section(\d+)\.xml$", name)
            if m:
                sections.append((int(m.group(1)), name))
        if not sections:
            raise ValueError("본문을 찾을 수 없습니다 (배포용·암호 문서일 수 있음)")
        for _, name in sorted(sections):
            root = ET.fromstring(zf.read(name))
            for p in root:
                if _local(p.tag) != "p":
                    continue
                text = _para_text(p)
                if text:
                    blocks.append(text)
                for run in p:
                    if _local(run.tag) != "run":
                        continue
                    for child in run:
                        if _local(child.tag) == "tbl":
                            t = _table_md(child)
                            if t:
                                blocks.append(t)
    md = "\n\n".join(blocks).strip()
    if not md:
        raise ValueError("추출된 텍스트가 없습니다")
    return md + "\n"


def plan_tasks(files):
    """파일 목록을 일꾼에게 줄 작업으로 나눔.
    PDF는 CHUNK_PAGES 쪽씩 나누고, HWPX는 파일 하나가 작업 하나.
    반환: (작업 목록 [(파일 번호, 시작 쪽, 끝 쪽)], 파일별 쪽수, 열 수 없는 파일 {번호: 오류})"""
    tasks = []
    pages = {}
    errors = {}
    for i, path in enumerate(files):
        if os.path.splitext(path)[1].lower() != ".pdf":
            tasks.append((i, None, None))
            continue
        try:
            pages[i] = pdf_page_count(path)
        except Exception as e:
            errors[i] = e
            continue
        for first in range(0, pages[i], CHUNK_PAGES):
            tasks.append((i, first, min(first + CHUNK_PAGES, pages[i])))
    return tasks, pages, errors


def convert_task(idx, path, first, last):
    """일꾼 프로세스가 실행하는 함수 : PDF 쪽 묶음 1개 또는 HWPX 파일 1개 변환"""
    if first is None:
        return hwpx_to_md(path)
    return pdf_chunk_to_md(path, first, last, idx)


# ──────────────────────────────────────────────
# 새 버전 확인
# ──────────────────────────────────────────────
def parse_version(text):
    """'1.2.10' → (1, 2, 10)  (글자 그대로 비교하면 '1.10.0'이 '1.9.0'보다 작게 나옴)"""
    parts = []
    for piece in str(text).strip().lstrip("vV").split("."):
        digits = "".join(ch for ch in piece if ch.isdigit())
        parts.append(int(digits) if digits else 0)
    return tuple(parts)


def is_newer(latest, current):
    """latest가 current보다 높은 버전이면 True"""
    a, b = parse_version(latest), parse_version(current)
    length = max(len(a), len(b))
    a += (0,) * (length - len(a))
    b += (0,) * (length - len(b))
    return a > b


def fetch_version_info(source=VERSION_INFO_SOURCE):
    """version.json 내용을 읽어 딕셔너리로 돌려줌. 실패하면 None."""
    try:
        request = urllib.request.Request(source, headers={"User-Agent": "update-checker"})
        with urllib.request.urlopen(request, timeout=UPDATE_TIMEOUT_SEC) as response:
            info = json.loads(response.read().decode("utf-8-sig"))
        if "version" not in info or "download_url" not in info:
            return None
        return info
    except Exception:
        # 네트워크 차단, 파일 없음, 형식 오류 등 모든 경우 조용히 넘어감
        return None


# ──────────────────────────────────────────────
# 3) 저장 경로 (같은 이름이 있으면 번호를 붙여 덮어쓰기 방지)
# ──────────────────────────────────────────────
def unique_path(folder, stem, used):
    cand = os.path.join(folder, stem + ".md")
    n = 1
    while os.path.exists(cand) or cand.lower() in used:
        cand = os.path.join(folder, "%s (%d).md" % (stem, n))
        n += 1
    used.add(cand.lower())
    return cand


def short_name(name, limit=40):
    """팝업에 긴 파일 이름이 넘치지 않게 줄임"""
    return name if len(name) <= limit else name[:limit - 1] + "…"


def fmt_sec(sec):
    sec = int(sec)
    m, s = divmod(sec, 60)
    return "%d분 %02d초" % (m, s) if m else "%d초" % s


# ──────────────────────────────────────────────
# 4) 화면
# ──────────────────────────────────────────────
class App:
    BG = "#F4F6FA"
    CARD = "#FFFFFF"
    PRIMARY = "#2563EB"
    PRIMARY_DARK = "#1D4ED8"
    TEXT = "#1F2937"
    MUTED = "#6B7280"
    LINE = "#D1D5DB"
    SCALE = 1000   # 진행 막대를 부드럽게 움직이기 위한 눈금

    def __init__(self, root, dnd_files):
        self.root = root
        self.dnd_files = dnd_files
        self.files = []
        self.q = queue.Queue()
        self.busy = False
        self.cancel_event = threading.Event()
        self.pop = None
        self.total = 0
        self.start_time = 0.0
        self.part = {}          # 파일 번호 → 진행 비율(0~1)
        self.names = {}         # 파일 번호 → 파일 이름
        self.done_n = 0
        self.frac = 0.0
        self.status_text = ""
        self.mpq = None
        self.mpcancel = None

        root.title("PDF · HWPX → MD 변환기")
        root.geometry("820x660")
        root.minsize(680, 540)
        root.configure(bg=self.BG)

        self._style()
        self._build()
        self._refresh()
        self._start_update_check()

    # ----- 새 버전 확인 -----
    def _start_update_check(self):
        """뒤에서 조용히 확인 (프로그램이 멈추지 않음)"""
        result = queue.Queue()
        threading.Thread(target=lambda: result.put(fetch_version_info()),
                         daemon=True).start()
        self.root.after(500, self._poll_update, result, None)

    def _poll_update(self, result, info):
        # 팝업은 반드시 화면(메인) 쪽에서 띄워야 안전하므로 여기서 결과를 받음
        if info is None:
            try:
                info = result.get_nowait()
            except queue.Empty:
                self.root.after(500, self._poll_update, result, None)
                return
            if not info or not is_newer(info["version"], CURRENT_VERSION):
                return
        if self.busy:       # 변환 중에는 방해하지 않고 끝난 뒤에 안내
            self.root.after(1000, self._poll_update, result, info)
            return
        self._show_update_popup(info)

    def _show_update_popup(self, info):
        message = ("새 버전이 있습니다.\n\n현재 버전: %s\n최신 버전: %s\n"
                   % (CURRENT_VERSION, info["version"]))
        notes = str(info.get("notes", "")).replace("\\n", "\n").strip()
        if notes:
            message += "\n[변경 내용]\n%s\n" % notes
        message += "\n지금 다운로드 페이지를 여시겠습니까?"
        if messagebox.askyesno("업데이트 안내", message, parent=self.root):
            url = str(info["download_url"])
            if url.lower().startswith("https://"):     # 웹 주소만 열기
                webbrowser.open(url)

    # ----- 스타일 -----
    def _style(self):
        font = "맑은 고딕"
        s = ttk.Style()
        try:
            s.theme_use("clam")
        except tk.TclError:
            pass
        s.configure(".", font=(font, 10))
        s.configure("TFrame", background=self.BG)
        s.configure("Card.TFrame", background=self.CARD)
        s.configure("Title.TLabel", background=self.BG, foreground=self.TEXT,
                    font=(font, 16, "bold"))
        s.configure("Sub.TLabel", background=self.BG, foreground=self.MUTED)
        s.configure("PopTitle.TLabel", background=self.BG, foreground=self.TEXT,
                    font=(font, 12, "bold"))
        s.configure("TButton", background="#E5E7EB", foreground=self.TEXT,
                    borderwidth=0, padding=(14, 8))
        s.map("TButton", background=[("active", "#D1D5DB"), ("disabled", "#F3F4F6")],
              foreground=[("disabled", "#9CA3AF")])
        s.configure("Primary.TButton", background=self.PRIMARY, foreground="white",
                    padding=(18, 11), font=(font, 11, "bold"))
        s.map("Primary.TButton",
              background=[("active", self.PRIMARY_DARK), ("disabled", "#93C5FD")],
              foreground=[("disabled", "white")])
        s.configure("Treeview", background=self.CARD, fieldbackground=self.CARD,
                    foreground=self.TEXT, rowheight=30, borderwidth=0)
        s.configure("Treeview.Heading", background="#EEF2F7", foreground=self.TEXT,
                    font=(font, 10, "bold"), relief="flat", padding=(8, 6))
        s.map("Treeview", background=[("selected", "#DBEAFE")],
              foreground=[("selected", self.TEXT)])
        s.configure("Horizontal.TProgressbar", troughcolor="#E5E7EB",
                    background=self.PRIMARY, borderwidth=0, thickness=10)

    # ----- 화면 만들기 -----
    def _build(self):
        font = "맑은 고딕"
        top = ttk.Frame(self.root)
        top.pack(fill="x", padx=24, pady=(20, 8))
        ttk.Label(top, text="PDF · HWPX → MD 변환기", style="Title.TLabel").pack(anchor="w")
        ttk.Label(top, text="파일을 아래 창에 끌어다 놓으세요. 여러 개를 한꺼번에 넣어도 됩니다.",
                  style="Sub.TLabel").pack(anchor="w", pady=(2, 0))

        # 파일 목록(드롭 영역)
        card = tk.Frame(self.root, bg=self.CARD, highlightthickness=2,
                        highlightbackground=self.LINE, highlightcolor=self.PRIMARY)
        card.pack(fill="both", expand=True, padx=24, pady=8)
        self.card = card

        cols = ("name", "type", "folder")
        self.tree = ttk.Treeview(card, columns=cols, show="headings", selectmode="extended")
        self.tree.heading("name", text="파일 이름", anchor="w")
        self.tree.heading("type", text="형식", anchor="w")
        self.tree.heading("folder", text="원본 폴더", anchor="w")
        self.tree.column("name", width=300, anchor="w")
        self.tree.column("type", width=70, anchor="w", stretch=False)
        self.tree.column("folder", width=360, anchor="w")
        sb = ttk.Scrollbar(card, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.tree.pack(side="left", fill="both", expand=True, padx=2, pady=2)
        self.tree.bind("<Delete>", lambda e: self.remove_selected())

        self.placeholder = tk.Label(
            card, text="📄\n\n여기에 PDF / HWPX 파일을\n끌어다 놓으세요",
            bg=self.CARD, fg=self.MUTED, font=(font, 13), justify="center")

        # 끌어다 놓기 등록
        for w in (self.root, card, self.tree, self.placeholder):
            w.drop_target_register(self.dnd_files)
            w.dnd_bind("<<Drop>>", self.on_drop)

        # 목록 편집 버튼
        edit = ttk.Frame(self.root)
        edit.pack(fill="x", padx=24, pady=(4, 0))
        self.btn_add = ttk.Button(edit, text="파일 추가", command=self.add_dialog)
        self.btn_del = ttk.Button(edit, text="선택 삭제", command=self.remove_selected)
        self.btn_clear = ttk.Button(edit, text="전체 삭제", command=self.clear_all)
        for b in (self.btn_add, self.btn_del, self.btn_clear):
            b.pack(side="left", padx=(0, 8))
        self.count_label = ttk.Label(edit, text="", style="Sub.TLabel")
        self.count_label.pack(side="right")

        # 저장 버튼
        act = ttk.Frame(self.root)
        act.pack(fill="x", padx=24, pady=(10, 6))
        self.btn_same = ttk.Button(act, text="기존 폴더에 저장하기", style="Primary.TButton",
                                   command=lambda: self.start("same"))
        self.btn_other = ttk.Button(act, text="다른 폴더에 저장하기", style="Primary.TButton",
                                    command=lambda: self.start("other"))
        self.btn_same.pack(side="left", fill="x", expand=True, padx=(0, 6))
        self.btn_other.pack(side="left", fill="x", expand=True, padx=(6, 0))

        self.progress = ttk.Progressbar(self.root, mode="determinate", maximum=self.SCALE)
        self.progress.pack(fill="x", padx=24, pady=(6, 6))

        # 결과 로그
        logf = ttk.Frame(self.root)
        logf.pack(fill="x", padx=24, pady=(0, 18))
        self.log = tk.Text(logf, height=6, bg=self.CARD, fg=self.TEXT, relief="flat",
                           highlightthickness=1, highlightbackground=self.LINE,
                           font=(font, 9), state="disabled", wrap="word")
        lsb = ttk.Scrollbar(logf, orient="vertical", command=self.log.yview)
        self.log.configure(yscrollcommand=lsb.set)
        lsb.pack(side="right", fill="y")
        self.log.pack(side="left", fill="x", expand=True)

    # ----- 로그 -----
    def write_log(self, text):
        self.log.configure(state="normal")
        self.log.insert("end", text + "\n")
        self.log.see("end")
        self.log.configure(state="disabled")

    # ----- 목록 관리 -----
    def _refresh(self):
        self.tree.delete(*self.tree.get_children())
        for i, p in enumerate(self.files):
            ext = os.path.splitext(p)[1].lower().lstrip(".").upper()
            self.tree.insert("", "end", iid=str(i),
                             values=(os.path.basename(p), ext, os.path.dirname(p)))
        if self.files:
            self.placeholder.place_forget()
        else:
            self.placeholder.place(relx=0.5, rely=0.5, anchor="center")
        self.count_label.configure(text="총 %d개" % len(self.files))

    def add_paths(self, paths):
        collected = []
        for p in paths:
            p = os.path.abspath(p)
            if os.path.isdir(p):
                for dp, _, fns in os.walk(p):
                    for fn in sorted(fns):
                        collected.append(os.path.join(dp, fn))
            else:
                collected.append(p)

        added = dup = bad = old_hwp = 0
        have = {f.lower() for f in self.files}
        for p in collected:
            ext = os.path.splitext(p)[1].lower()
            if ext == ".hwp":
                old_hwp += 1
            elif ext not in SUPPORTED:
                bad += 1
            elif p.lower() in have:
                dup += 1
            else:
                self.files.append(p)
                have.add(p.lower())
                added += 1
        self._refresh()
        msg = "%d개 추가" % added
        if dup:
            msg += " / 이미 있는 파일 %d개 제외" % dup
        if bad:
            msg += " / PDF·HWPX가 아닌 파일 %d개 제외" % bad
        if old_hwp:
            msg += " / 옛 .hwp 파일 %d개 제외 (한글에서 hwpx로 저장 후 사용)" % old_hwp
        self.write_log(msg)

    def on_drop(self, event):
        if self.busy:
            return event.action
        self.add_paths(self.root.tk.splitlist(event.data))
        return event.action

    def add_dialog(self):
        if self.busy:
            return
        paths = filedialog.askopenfilenames(
            title="변환할 파일 선택",
            filetypes=[("PDF / HWPX", "*.pdf *.hwpx"), ("모든 파일", "*.*")])
        if paths:
            self.add_paths(paths)

    def remove_selected(self):
        if self.busy:
            return
        idx = sorted((int(i) for i in self.tree.selection()), reverse=True)
        for i in idx:
            del self.files[i]
        self._refresh()

    def clear_all(self):
        if self.busy:
            return
        self.files.clear()
        self._refresh()

    # ----- 진행 팝업 -----
    def _open_popup(self, total):
        pop = tk.Toplevel(self.root)
        self.pop = pop
        pop.title("변환 진행 중")
        pop.configure(bg=self.BG)
        pop.resizable(False, False)
        pop.transient(self.root)

        # 메인 창 가운데에 띄우기
        w, h = 500, 250
        self.root.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() - w) // 2
        y = self.root.winfo_y() + (self.root.winfo_height() - h) // 2
        pop.geometry("%dx%d+%d+%d" % (w, h, max(x, 0), max(y, 0)))

        # 창의 X 버튼을 눌러도 '취소'로 처리
        pop.protocol("WM_DELETE_WINDOW", self.request_cancel)

        body = ttk.Frame(pop)
        body.pack(fill="both", expand=True, padx=24, pady=20)

        self.pop_title = ttk.Label(body, text="변환하는 중입니다…", style="PopTitle.TLabel")
        self.pop_title.pack(anchor="w")

        self.pop_file = ttk.Label(body, text="파일을 여는 중…", style="Sub.TLabel")
        self.pop_file.pack(anchor="w", pady=(8, 8))

        # 전체 진행률 (쪽 단위로 부드럽게 움직임)
        self.pop_bar = ttk.Progressbar(body, mode="determinate", maximum=self.SCALE, value=0)
        self.pop_bar.pack(fill="x")

        self.pop_count = ttk.Label(body, text="완료 0 / %d 파일  (0%%)" % total,
                                   style="Sub.TLabel")
        self.pop_count.pack(anchor="w", pady=(6, 0))

        self.pop_time = ttk.Label(body, text="경과 시간 0초", style="Sub.TLabel")
        self.pop_time.pack(anchor="w")

        self.pop_cancel = ttk.Button(body, text="취소", command=self.request_cancel)
        self.pop_cancel.pack(side="bottom", anchor="e", pady=(10, 0))

        pop.grab_set()          # 변환 중에는 메인 창을 건드릴 수 없게
        pop.focus_set()
        self._tick_time()

    def _tick_time(self):
        """경과 시간·남은 시간을 1초마다 갱신"""
        if not self.pop:
            return
        elapsed = time.time() - self.start_time
        text = "경과 시간 %s" % fmt_sec(elapsed)
        if self.frac >= 0.03 and elapsed >= 3 and not self.cancel_event.is_set():
            remain = elapsed * (1 - self.frac) / self.frac
            text += "   ·   남은 시간 약 %s" % fmt_sec(remain)
        self.pop_time.configure(text=text)
        self.root.after(1000, self._tick_time)

    def _close_popup(self):
        if self.pop:
            try:
                self.pop.grab_release()
                self.pop.destroy()
            except tk.TclError:
                pass
            self.pop = None

    def request_cancel(self):
        if self.cancel_event.is_set():
            return
        ok = messagebox.askyesno(
            "취소", "변환을 취소할까요?\n\n지금 변환 중인 파일은 중단되고 저장되지 않습니다.\n"
                    "이미 저장된 파일은 그대로 남습니다.",
            parent=self.pop)
        if not ok:
            return
        self.cancel_event.set()
        if self.mpcancel is not None:
            self.mpcancel.set()
        self.pop_title.configure(text="취소하는 중입니다…")
        self.pop_file.configure(text="잠시만 기다려 주세요.")
        self.pop_cancel.configure(state="disabled")

    # ----- 진행도 갱신 -----
    def _update_progress(self):
        if not self.total:
            return
        self.frac = min(1.0, sum(self.part.values()) / self.total)
        value = self.frac * self.SCALE
        self.progress.configure(value=value)
        if self.pop:
            self.pop_bar.configure(value=value)
            self.pop_count.configure(text="완료 %d / %d 파일  (%d%%)"
                                     % (self.done_n, self.total, int(self.frac * 100)))
            if not self.cancel_event.is_set():
                self.pop_file.configure(text=self.status_text)

    # ----- 변환 -----
    def _set_busy(self, busy):
        self.busy = busy
        state = "disabled" if busy else "normal"
        for b in (self.btn_add, self.btn_del, self.btn_clear, self.btn_same,
                  self.btn_other):
            b.configure(state=state)

    def start(self, mode):
        if self.busy:
            return
        if not self.files:
            messagebox.showinfo("안내", "변환할 파일을 먼저 추가해 주세요.")
            return
        folder = None
        if mode == "other":
            folder = filedialog.askdirectory(title="저장할 폴더 선택")
            if not folder:
                return
        files = list(self.files)

        self.total = len(files)
        self.part = {}
        self.names = {i: os.path.basename(p) for i, p in enumerate(files)}
        self.done_n = 0
        self.frac = 0.0
        self.status_text = "파일을 여는 중…"
        self.cancel_event.clear()
        self.mpq = multiprocessing.Queue()
        self.mpcancel = multiprocessing.Event()
        self.start_time = time.time()
        self.progress.configure(maximum=self.SCALE, value=0)
        self._set_busy(True)
        self.write_log("─ 변환 시작 (%d개) ─" % len(files))
        self._open_popup(len(files))
        threading.Thread(target=self._worker, args=(files, folder),
                         daemon=True).start()
        self.root.after(100, self._poll)

    def _drain(self, pages, page_done):
        """일꾼 프로세스가 보낸 쪽 진행 상황을 세어 화면용 큐로 옮김"""
        while True:
            try:
                _, idx = self.mpq.get_nowait()
            except queue.Empty:
                break
            page_done[idx] = page_done.get(idx, 0) + 1
            self.q.put(("page", (idx, page_done[idx], pages[idx])))

    def _worker(self, files, folder):
        used = set()
        ok = fail = 0
        cancelled = False
        pages, page_done = {}, {}

        def report_fail(i, e):
            name = os.path.basename(files[i])
            self.q.put(("log", "✘ %s : %s: %s" % (name, type(e).__name__, e)))
            self.q.put(("filedone", (i, name)))

        try:
            tasks, pages, errors = plan_tasks(files)
            for i, e in errors.items():
                report_fail(i, e)
                fail += 1

            left = {}       # 파일 번호 → 남은 작업 수
            for i, _, _ in tasks:
                left[i] = left.get(i, 0) + 1
            results = {}    # 파일 번호 → {시작 쪽: 결과}
            failed = set()

            workers = max(1, min(MAX_WORKERS, (os.cpu_count() or 2) - 1, len(tasks)))
            with ProcessPoolExecutor(max_workers=workers, initializer=_init_worker,
                                     initargs=(self.mpq, self.mpcancel)) as ex:
                futs = {ex.submit(convert_task, i, files[i], first, last): (i, first)
                        for i, first, last in tasks}
                pending = set(futs)
                while pending:
                    self._drain(pages, page_done)
                    done, pending = wait(pending, timeout=0.2, return_when=FIRST_COMPLETED)

                    if self.cancel_event.is_set() and not cancelled:
                        cancelled = True
                        self.mpcancel.set()
                        for f in list(pending):
                            f.cancel()      # 아직 시작 안 한 작업은 취소

                    for f in done:
                        i, first = futs[f]
                        if f.cancelled() or i in failed:
                            continue
                        path = files[i]
                        name = os.path.basename(path)
                        try:
                            results.setdefault(i, {})[first] = f.result()
                            left[i] -= 1
                            if left[i]:
                                continue    # 이 파일의 다른 묶음이 남음
                            got = results.pop(i)
                            if first is None:
                                md = got[None]
                            else:
                                parts, bad = [], []
                                for key in sorted(got):
                                    parts += got[key][0]
                                    bad += got[key][1]
                                md = join_pdf_parts(parts, bad)
                            outdir = folder if folder else os.path.dirname(path)
                            stem = os.path.splitext(name)[0]
                            out = unique_path(outdir, stem, used)
                            with open(out, "w", encoding="utf-8") as fp:
                                fp.write(md)
                            self.q.put(("log", "✔ %s → %s" % (name, out)))
                            ok += 1
                            self.q.put(("filedone", (i, name)))
                        except Cancelled:
                            continue
                        except Exception as e:
                            failed.add(i)
                            results.pop(i, None)
                            for other in pending:
                                if futs[other][0] == i:
                                    other.cancel()
                            report_fail(i, e)
                            fail += 1
        except Exception as e:
            self.q.put(("log", "✘ 변환 엔진 오류: %s" % e))
        self._drain(pages, page_done)
        self.q.put(("done", (ok, fail, cancelled, len(files) - ok - fail)))

    def _poll(self):
        finished = None
        try:
            while True:
                kind, val = self.q.get_nowait()
                if kind == "log":
                    self.write_log(val)
                elif kind == "page":
                    idx, cur, tot = val
                    if self.part.get(idx, 0) < 1.0:
                        self.part[idx] = cur / tot if tot else 1.0
                        self.status_text = "변환 중: %s   (%d / %d쪽)" % (
                            short_name(self.names.get(idx, "")), cur, tot)
                elif kind == "filedone":
                    idx, name = val
                    self.part[idx] = 1.0
                    self.done_n += 1
                    self.status_text = "방금 끝난 파일: %s" % short_name(name)
                elif kind == "done":
                    finished = val
                    break
        except queue.Empty:
            pass

        self._update_progress()

        if finished is None:
            self.root.after(100, self._poll)
            return

        ok, fail, cancelled, skipped = finished
        self._close_popup()
        self._set_busy(False)
        if cancelled:
            self.write_log("─ 취소됨: 성공 %d개, 실패 %d개, 변환 안 함 %d개 ─"
                           % (ok, fail, skipped))
            messagebox.showinfo(
                "취소됨",
                "변환을 취소했습니다.\n\n성공 %d개 / 실패 %d개 / 변환 안 함 %d개"
                % (ok, fail, skipped), parent=self.root)
        else:
            self.write_log("─ 완료: 성공 %d개, 실패 %d개 (걸린 시간 %s) ─"
                           % (ok, fail, fmt_sec(time.time() - self.start_time)))
            messagebox.showinfo("완료", "성공 %d개 / 실패 %d개" % (ok, fail),
                                parent=self.root)


def main():
    try:
        from tkinterdnd2 import TkinterDnD, DND_FILES
    except ImportError:
        r = tk.Tk()
        r.withdraw()
        messagebox.showerror("설치 필요",
                             "tkinterdnd2 가 설치되지 않았습니다.\n\n"
                             "명령 프롬프트에서 아래를 실행해 주세요.\n"
                             "pip install tkinterdnd2 pymupdf4llm")
        return
    root = TkinterDnD.Tk()
    App(root, DND_FILES)
    root.mainloop()


if __name__ == "__main__":
    multiprocessing.freeze_support()   # exe(PyInstaller)로 만들 때 꼭 필요
    main()
