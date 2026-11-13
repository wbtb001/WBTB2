
# ============================================================
# weDownloader_v11.py
#test
# We Plus Downloader - GUI Version
#
# Requirements:
#   pip install requests
#
# Optional:
#   opera-proxy.windows-amd64.exe
#   Place in the same folder as this script.
#
# ============================================================
# CHANGELOG
# ============================================================
#
# v11
# - Load Token API credentials from wefileuser.txt beside the script.
# - Keep environment variables as a fallback when the file is absent.
#
# v10
# - Use the local listening port to confirm a managed Proxy starts.
# - Check upstream connectivity separately without stopping the Proxy.
#
# v09
# - Probe the local HTTP Proxy without waiting for an external tunnel.
# - Treat standard Proxy error responses as proof the listener is ready.
#
# v08
# - Wait for the full configured startup period before failing
#   HTTP Proxy readiness checks.
#
# v07
# - Restore HTTPS certificate verification.
# - Load Token API credentials from environment variables.
# - Require an active HTTP Proxy before loading or downloading.
# - Validate API list responses and clear stale subjects on reload.
# - Keep the application open while load/download workers are active.
# - Validate output paths and stream downloads through temporary files.
# - Verify that detected listeners behave like an HTTP CONNECT Proxy.
#
# v06
# - Detect Proxy listener when application starts.
# - If Proxy is already running before application startup,
#   classify it as External Proxy.
# - External Proxy cannot be started/stopped by this application.
# - If application starts its own Proxy, start/stop is allowed.
# - Check public IP and country through Proxy at startup.
# - Check public IP and country after starting Proxy.
# - Show IP check results in GUI Log and Console.
# - Never terminate an External Proxy when closing application.
# - Disable Proxy control until startup detection completes.
#
# v05
# - Force ALL API requests to use Proxy.
# - Subject / Content / Teacher / TeacherQA / Video API
#   always use Proxy.
# - Token API always uses Proxy.
# - IP Information always uses Proxy.
# - FileAPI can choose Proxy or Direct connection.
# - Added "Download files through Proxy" checkbox.
# - Checkbox default is CHECKED.
# - Checkbox setting only affects FileAPI downloads.
# - Capture checkbox state when starting download.
# - Keep existing v04 GUI and download workflow.
#
# v04
# - Added Tkinter GUI.
# - Added Student ID input and Subject API.
# - Added multiple subject selection.
# - Added Proxy start/stop control.
# - Added output folder selection.
# - Added download log.
# - Added browser-like HTTP headers.
# - Changed Token/FileAPI host to vdo03.
# - Added TeacherQA API.
#
# v03
# - Original downloader logic.
#
# ============================================================

import os
import re
import time
import json
import queue
import socket
import threading
import subprocess
import webbrowser
from urllib.parse import urlparse

from pathlib import Path

import tkinter as tk
from tkinter import ttk, filedialog, messagebox

import requests


# ============================================================
# CONFIGURATION
# ============================================================

APP_VERSION = "weDownloader_v11"

PROXY_EXE = "opera-proxy.windows-amd64.exe"
PROXY_URL = "http://127.0.0.1:18080"

PROXY_HOST = "127.0.0.1"
PROXY_PORT = 18080

PROXY_START_RETRY = 30
PROXY_START_INTERVAL = 500

TOKEN_EXPIRED_TIME = 5400

REQUEST_TIMEOUT = (20, 90)
DOWNLOAD_TIMEOUT = (20, 180)

TOKEN_USERNAME_ENV = "WEDOWNLOADER_TOKEN_USERNAME"
TOKEN_PASSWORD_ENV = "WEDOWNLOADER_TOKEN_PASSWORD"
TOKEN_CREDENTIALS_FILE = "wefileuser.txt"
TOKEN_USERNAME = None
TOKEN_PASSWORD = None


def load_token_credentials():

    credentials_path = (
        Path(__file__).resolve().parent
        / TOKEN_CREDENTIALS_FILE
    )

    if credentials_path.is_file():

        lines = credentials_path.read_text(
            encoding="utf-8-sig"
        ).splitlines()

        if (
            len(lines) < 2
            or not lines[0].strip()
            or not lines[1].strip()
        ):
            raise ValueError(
                f"{TOKEN_CREDENTIALS_FILE} must contain a username "
                "on line 1 and a password on line 2"
            )

        return lines[0].strip(), lines[1].strip()

    return (
        os.environ.get(TOKEN_USERNAME_ENV),
        os.environ.get(TOKEN_PASSWORD_ENV)
    )


# ============================================================
# API ENDPOINTS
# ============================================================

API_IP_LOCATION = "https://ipinfo.io/json"

API_GET_COURSES = (
    "https://store.webythebrain.com/"
    "wp-json/we/v1/products"
)

COURSE_PAGE_SIZE = 48

COURSE_LEVEL_FILTERS = (
    ("ทุกระดับชั้น", ""),
    ("สอบเข้ามหาวิทยาลัย", "university-admission"),
    ("ม.ปลาย", "senior-high-school"),
    ("สอบเข้า ม.4", "m4-admission"),
    ("ม.ต้น", "junior-high-school"),
    ("ประถม-สอบเข้า ม.1", "high-school-entrance"),
    ("ม.6", "m6"),
    ("ม.5", "m5"),
    ("ม.4", "m4"),
    ("ม.3", "m3"),
    ("ม.2", "m2"),
    ("ม.1", "m1"),
    ("ป.6", "p6"),
    ("ป.5", "p5"),
    ("มหาวิทยาลัย", "university"),
)

API_GET_CONTENT = (
    "https://api2.webythebrain.com/"
    "wecanapi/api/ContentWePlus/Get/"
)

API_POST_TEACHER = (
    "https://api2.webythebrain.com/"
    "wecanapi/api/TeacherWePlus/"
)

API_POST_VIDEO = (
    "https://api2.webythebrain.com/"
    "wecanapi/api/VideoWePlus/"
)

API_POST_TEACHER_QA = (
    "https://api2.webythebrain.com/"
    "wecanapi/api/TeacherQA"
)

API_POST_TOKEN = (
    "https://vdo03.webythebrain.com/"
    "wefileapi/api/token"
)

API_POST_FILE = (
    "https://vdo03.webythebrain.com/"
    "wefileapi/api/FileAPI"
)


# ============================================================
# ============================================================
# HTTP HEADERS
# Based on supplied HTTP Capture
# ============================================================

COMMON_HEADERS = {

    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "weplus-online/2.5.3 "
        "Chrome/126.0.6478.61 "
        "Electron/31.0.2 Safari/537.36"
    ),

    "Sec-Ch-Ua": (
        '"Not/A)Brand";v="8", "Chromium";v="126"'
    ),

    "Sec-Ch-Ua-Mobile": "?0",

    "Sec-Ch-Ua-Platform": '"Windows"',

    "Sec-Fetch-Site": "cross-site",
    "Sec-Fetch-Mode": "cors",
    "Sec-Fetch-Dest": "empty",

    "Accept-Encoding": "gzip, deflate, br",
    "Accept-Language": "en-US,en;q=0.9",

    "Priority": "u=1, i",

    "Connection": "keep-alive",
}


GET_HEADERS = {
    **COMMON_HEADERS,
    "Accept": "application/json, text/plain, */*",
}


POST_HEADERS = {
    **COMMON_HEADERS,
    "Accept": "application/json",
    "Content-Type": "application/json",
}


TOKEN_HEADERS = {
    **COMMON_HEADERS,
    "Accept": "application/json, text/plain, */*",
    "Content-Type": "application/json",
}


POST_HEADERS_FILE = {
    **COMMON_HEADERS,
    "Accept": "application/json",
    "Content-Type": "application/json",
    "Access-Control-Allow-Origin": "*",
}


IP_HEADERS = {
    "User-Agent": COMMON_HEADERS["User-Agent"],
    "Accept": "application/json",
}


# ============================================================
# HELPER FUNCTIONS
# ============================================================

def sanitize_filename(filename):

    allowed_chars = (
        r"ก-ฮะ-์a-zA-Z0-9 _.!@#$%^&()\-+'[\]{}"
    )

    return re.sub(
        f"[^{allowed_chars}]",
        "",
        str(filename)
    ).strip()


def parse_list_response(response, source):

    data = response.json()

    if not isinstance(data, list):
        raise ValueError(f"{source} response is not a list")

    if not all(isinstance(item, dict) for item in data):
        raise ValueError(f"{source} response contains a non-object item")

    return data


def parse_course_page_response(response):

    data = response.json()

    if not isinstance(data, dict):
        raise ValueError("Course API response is not an object")

    items = data.get("items")

    if not isinstance(items, list):
        raise ValueError("Course API response does not contain an item list")

    if not all(isinstance(item, dict) for item in items):
        raise ValueError("Course API response contains a non-object item")

    total_pages = data.get("total_page")

    if not isinstance(total_pages, int) or total_pages < 1:
        raise ValueError("Course API response has an invalid total_page")

    return items, total_pages


def normalize_course(product):

    course_url = str(product.get("url") or "").strip()
    slug = urlparse(course_url).path.rstrip("/").rsplit("/", 1)[-1]
    course_id = str(product.get("course_id") or "").strip()

    if not course_id and re.fullmatch(
        r"[A-Za-z]{2,5}\d{2}[A-Za-z0-9_]*",
        slug
    ):
        course_id = slug.upper()

    if not course_id:
        cart_html = str(product.get("cart_icon_html", ""))
        sku_match = re.search(
            r'data-product_sku=["\']([^"\']+)["\']',
            cart_html,
            re.IGNORECASE
        )

        if sku_match and re.fullmatch(
            r"[A-Za-z]{2,5}\d{2}[A-Za-z0-9_]*",
            sku_match.group(1).strip()
        ):
            course_id = sku_match.group(1).strip().upper()

    detail_parts = []

    course_system = str(product.get("course_system") or "").strip()
    course_hour = str(product.get("course_hour") or "").strip()
    price = product.get("price")

    if course_system:
        detail_parts.append(course_system)

    if course_hour and course_hour != "-":
        detail_parts.append(f"{course_hour} ชม.")

    if price not in (None, ""):
        detail_parts.append(f"฿{price}")

    return {
        "subject_id": course_id,
        "subject_name": str(product.get("title") or "").strip(),
        "subject_year": "",
        "course_detail": " | ".join(detail_parts) or "ไม่มีรายละเอียด",
        "course_url": course_url,
        "store_product_id": str(product.get("id", "")),
    }


def resolve_output_target(output_dir, course_id, relative_path, save_as):

    root = Path(output_dir).resolve()
    target = (
        root
        / str(course_id)
        / relative_path
        / save_as
    ).resolve()

    try:
        target.relative_to(root)
    except ValueError as exc:
        raise ValueError(
            "The requested output path is outside the selected folder"
        ) from exc

    return target


# ============================================================
# MAIN APPLICATION
# ============================================================

class DownloaderApp:

    def __init__(self, root):

        self.root = root

        self.root.title(
            f"{APP_VERSION} - We Plus Downloader"
        )

        self.root.geometry("900x710")
        self.root.minsize(760, 580)

        self.log_queue = queue.Queue()

        # Proxy ownership
        self.proxy_process = None
        self.proxy_enabled = False

        # v06: External Proxy / Program Proxy
        self.proxy_external = False
        self.proxy_starting = False
        self.proxy_detection_complete = False

        self.download_running = False
        self.load_running = False

        self.courses = []

        self.token = None
        self.token_timestamp = 0

        self.output_dir = tk.StringVar(
            value=str(Path.cwd() / "Downloads")
        )

        # FileAPI Proxy option
        # Default = True
        # This checkbox affects FileAPI only.

        self.download_via_proxy = tk.BooleanVar(
            value=True
        )

        self._build_ui()

        self._poll_log_queue()

        self.root.protocol(
            "WM_DELETE_WINDOW",
            self.on_close
        )

        self.log("=" * 55)
        self.log(f"{APP_VERSION} started")
        self.log("CHANGELOG v11:")
        self.log("- Token credentials are loaded from wefileuser.txt")
        self.log("- Environment variables remain supported as fallback")
        self.log("=" * 55)

        # ตรวจสอบ Proxy หลังจากสร้าง GUI แล้ว
        # ระหว่างนี้ปุ่ม Proxy จะยังถูก Disable

        self.root.after(
            100,
            self.check_proxy_on_startup
        )


    # ========================================================
    # GUI
    # ========================================================

    def _build_ui(self):

        main = ttk.Frame(
            self.root,
            padding=12
        )

        main.pack(
            fill="both",
            expand=True
        )


        # ----------------------------------------------------
        # Course List
        # ----------------------------------------------------

        account = ttk.LabelFrame(
            main,
            text="รายการคอร์ส",
            padding=10
        )

        account.pack(fill="x")

        row = ttk.Frame(account)
        row.pack(fill="x")

        self.load_button = ttk.Button(
            row,
            text="โหลดรายการคอร์ส",
            command=self.load_courses
        )

        self.load_button.pack(side="left")

        self.course_level_filter = tk.StringVar(
            value=COURSE_LEVEL_FILTERS[0][0]
        )

        ttk.Label(
            row,
            text="ระดับชั้น:"
        ).pack(
            side="left",
            padx=(12, 4)
        )

        self.course_level_combo = ttk.Combobox(
            row,
            textvariable=self.course_level_filter,
            values=[name for name, _ in COURSE_LEVEL_FILTERS],
            state="readonly",
            width=20
        )

        self.course_level_combo.pack(side="left")

        ttk.Label(
            row,
            text="จาก store.webythebrain.com/course/"
        ).pack(
            side="left",
            padx=10
        )

        self.course_count = ttk.Label(
            row,
            text="ยังไม่ได้โหลดรายการคอร์ส"
        )

        self.course_count.pack(
            side="left",
            padx=12
        )


        # Course Listbox

        list_frame = ttk.Frame(account)

        list_frame.pack(
            fill="both",
            expand=True,
            pady=(10, 0)
        )

        self.course_list = tk.Listbox(
            list_frame,
            selectmode=tk.EXTENDED,
            height=11,
            exportselection=False
        )

        scrollbar = ttk.Scrollbar(
            list_frame,
            orient="vertical",
            command=self.course_list.yview
        )

        self.course_list.configure(
            yscrollcommand=scrollbar.set
        )
        horizontal_scrollbar = ttk.Scrollbar(
            list_frame,
            orient="horizontal",
            command=self.course_list.xview
        )
        self.course_list.configure(
            xscrollcommand=horizontal_scrollbar.set
        )

        self.course_list.pack(
            side="left",
            fill="both",
            expand=True
        )

        scrollbar.pack(
            side="right",
            fill="y"
        )
        horizontal_scrollbar.pack(
            side="bottom",
            fill="x"
        )


        # Select buttons

        select_row = ttk.Frame(account)

        select_row.pack(
            fill="x",
            pady=(6, 0)
        )

        ttk.Button(
            select_row,
            text="เลือกทั้งหมด",
            command=self.select_all
        ).pack(side="left")

        ttk.Button(
            select_row,
            text="ล้างการเลือก",
            command=self.clear_selection
        ).pack(
            side="left",
            padx=6
        )

        ttk.Button(
            select_row,
            text="ดูรายละเอียดคอร์ส",
            command=self.open_course_details
        ).pack(
            side="left"
        )


        # ----------------------------------------------------
        # Connection Settings
        # ----------------------------------------------------

        settings = ttk.LabelFrame(
            main,
            text="การเชื่อมต่อและตำแหน่งบันทึก",
            padding=10
        )

        settings.pack(
            fill="x",
            pady=10
        )


        # Proxy process control

        proxy_row = ttk.Frame(settings)
        proxy_row.pack(fill="x")

        self.proxy_status = ttk.Label(
            proxy_row,
            text="Proxy: กำลังตรวจสอบ...",
            foreground="orange"
        )

        self.proxy_status.pack(side="left")

        self.proxy_button = ttk.Button(
            proxy_row,
            text="กำลังตรวจสอบ...",
            command=self.toggle_proxy,
            state="disabled"
        )

        self.proxy_button.pack(
            side="left",
            padx=12
        )

        ttk.Label(
            proxy_row,
            text=f"Local endpoint: {PROXY_URL}"
        ).pack(
            side="left",
            padx=8
        )


        # ----------------------------------------------------
        # FileAPI Proxy Checkbox
        # ----------------------------------------------------

        download_proxy_row = ttk.Frame(settings)

        download_proxy_row.pack(
            fill="x",
            pady=(10, 0)
        )

        ttk.Checkbutton(
            download_proxy_row,
            text="ดาวน์โหลดไฟล์ผ่าน Proxy",
            variable=self.download_via_proxy
        ).pack(side="left")

        ttk.Label(
            download_proxy_row,
            text="(มีผลเฉพาะ FileAPI เท่านั้น)"
        ).pack(
            side="left",
            padx=8
        )


        # ----------------------------------------------------
        # Output Folder
        # ----------------------------------------------------

        path_row = ttk.Frame(settings)

        path_row.pack(
            fill="x",
            pady=(10, 0)
        )

        ttk.Label(
            path_row,
            text="โฟลเดอร์ปลายทาง:"
        ).pack(side="left")

        ttk.Entry(
            path_row,
            textvariable=self.output_dir
        ).pack(
            side="left",
            fill="x",
            expand=True,
            padx=6
        )

        ttk.Button(
            path_row,
            text="Browse...",
            command=self.choose_folder
        ).pack(side="left")


        # ----------------------------------------------------
        # Download Button
        # ----------------------------------------------------

        action_row = ttk.Frame(main)

        action_row.pack(
            fill="x",
            pady=(0, 8)
        )

        self.download_button = ttk.Button(
            action_row,
            text="ดาวน์โหลดคอร์สที่เลือก",
            command=self.start_download
        )

        self.download_button.pack(side="left")

        ttk.Label(
            action_row,
            text="เลือกได้หลายคอร์ส โดยกด Ctrl หรือ Shift"
        ).pack(
            side="left",
            padx=12
        )


        # ----------------------------------------------------
        # Log
        # ----------------------------------------------------

        log_frame = ttk.LabelFrame(
            main,
            text="สถานะการทำงาน",
            padding=8
        )

        log_frame.pack(
            fill="both",
            expand=True
        )

        self.log_text = tk.Text(
            log_frame,
            height=13,
            wrap="word",
            state="disabled"
        )

        log_scroll = ttk.Scrollbar(
            log_frame,
            orient="vertical",
            command=self.log_text.yview
        )

        self.log_text.configure(
            yscrollcommand=log_scroll.set
        )

        self.log_text.pack(
            side="left",
            fill="both",
            expand=True
        )

        log_scroll.pack(
            side="right",
            fill="y"
        )


        # Version

        ttk.Label(
            main,
            text=f"{APP_VERSION} | Based on weDownloader_v06.py",
            foreground="gray"
        ).pack(
            anchor="e",
            pady=(6, 0)
        )


    # ========================================================
    # LOG SYSTEM
    # v06: GUI Log + Console
    # ========================================================

    def log(self, message):

        message = str(message)

        print(
            message,
            flush=True
        )

        self.log_queue.put(message)


    def _poll_log_queue(self):

        try:

            while True:

                message = self.log_queue.get_nowait()

                self.log_text.configure(
                    state="normal"
                )

                self.log_text.insert(
                    "end",
                    message + "\n"
                )

                self.log_text.see("end")

                self.log_text.configure(
                    state="disabled"
                )

        except queue.Empty:
            pass

        self.root.after(
            100,
            self._poll_log_queue
        )


    # ========================================================
    # HTTP REQUEST
    #
    # v06:
    # use_proxy=True is the default.
    #
    # All API calls use Proxy unless explicitly overridden.
    # Only FileAPI is allowed to use use_proxy=False.
    # ========================================================

    def request(
        self,
        url,
        method="GET",
        params=None,
        use_proxy=True,
        headers=None,
        stream=False
    ):

        proxies = None

        if use_proxy:

            proxies = {
                "http": PROXY_URL,
                "https": PROXY_URL
            }


        if method.upper() == "GET":

            response = requests.get(
                url,
                params=params,
                headers=headers or GET_HEADERS,
                proxies=proxies,
                timeout=DOWNLOAD_TIMEOUT if stream else REQUEST_TIMEOUT,
                stream=stream
            )

        else:

            response = requests.post(
                url,
                json=params,
                headers=headers or POST_HEADERS,
                proxies=proxies,
                timeout=DOWNLOAD_TIMEOUT,
                stream=stream
            )

        try:
            response.raise_for_status()
        except requests.HTTPError:
            response.close()
            raise

        return response


    # ========================================================
    # v06: PROXY DETECTION AND IP CHECK
    # ========================================================

    def is_proxy_listening(self):

        try:
            with socket.create_connection(
                (PROXY_HOST, PROXY_PORT),
                timeout=0.25
            ):
                return True
        except OSError:
            return False


    def check_proxy_on_startup(self):

        """
        ตรวจสอบ Proxy ตอนเปิดโปรแกรม
        """

        self.log(
            "[Proxy Check] ตรวจสอบ Proxy ก่อนเริ่มใช้งาน..."
        )

        if self.is_proxy_listening():

            # มี Proxy อยู่ก่อนเข้าโปรแกรม
            self.proxy_external = True
            self.proxy_enabled = True

            self.proxy_status.configure(
                text="Proxy: External / Locked",
                foreground="blue"
            )

            self.proxy_button.configure(
                text="Proxy ถูกล็อก",
                state="disabled"
            )

            self.proxy_detection_complete = True

            self.log(
                "[Proxy Check] พบ Proxy ที่เปิดอยู่ก่อนเข้าโปรแกรม"
            )

            self.log(
                "[Proxy Check] External Proxy detected."
            )

            self.log(
                "[Proxy Check] ปุ่มเปิด/ปิด Proxy ถูกล็อก"
            )

            # ตรวจสอบ IP ผ่าน Proxy
            threading.Thread(
                target=self.check_proxy_ip,
                args=("Startup External Proxy",),
                daemon=True
            ).start()

        else:

            self.proxy_external = False
            self.proxy_enabled = False

            self.proxy_status.configure(
                text="Proxy: ปิด",
                foreground="gray"
            )

            self.proxy_button.configure(
                text="เปิด Proxy",
                state="normal"
            )

            self.proxy_detection_complete = True

            self.log(
                "[Proxy Check] ไม่พบ Proxy ที่เปิดอยู่"
            )

            self.log(
                "[Proxy Check] สามารถเปิด Proxy จากโปรแกรมได้"
            )


    def check_proxy_ip(self, source="Proxy"):

        """
        ตรวจสอบ Public IP ผ่าน Local Proxy เท่านั้น
        """

        self.log(
            f"[IP Check] เริ่มตรวจสอบ IP ผ่าน Proxy ({source})"
        )

        proxies = {
            "http": PROXY_URL,
            "https": PROXY_URL
        }

        try:

            response = requests.get(
                API_IP_LOCATION,
                headers=IP_HEADERS,
                proxies=proxies,
                timeout=15
            )

            response.raise_for_status()

            data = response.json()

            ip_address = data.get("ip", "Unknown")
            country = data.get("country", "Unknown")
            city = data.get("city", "Unknown")
            region = data.get("region", "Unknown")
            org = data.get("org", "Unknown")

            self.log("=" * 55)

            self.log("[IP Check SUCCESS]")

            self.log(f"Source  : {source}")
            self.log(f"IP      : {ip_address}")
            self.log(f"Country : {country}")
            self.log(f"Region  : {region}")
            self.log(f"City    : {city}")
            self.log(f"ISP     : {org}")

            self.log("=" * 55)

            return True

        except Exception as exc:

            self.log(
                f"[IP Check FAILED] ไม่สามารถตรวจสอบ IP ผ่าน Proxy ได้: {exc}"
            )

            return False


    # ========================================================
    # LOAD COURSES
    # Always use Proxy
    # ========================================================

    def load_courses(self):

        if not self._proxy_ready():
            return

        if self.download_running or self.load_running:
            return

        level_name = self.course_level_filter.get()
        level_slug = dict(COURSE_LEVEL_FILTERS).get(level_name, "")

        self.courses = []
        self.course_list.delete(0, "end")
        self.load_running = True

        self.load_button.configure(
            state="disabled"
        )
        self.course_level_combo.configure(
            state="disabled"
        )

        self.download_button.configure(
            state="disabled"
        )

        self.course_count.configure(
            text="กำลังโหลดรายการคอร์ส..."
        )

        threading.Thread(
            target=self._load_courses_worker,
            args=(level_name, level_slug),
            daemon=True
        ).start()


    def _load_courses_worker(self, level_name, level_slug):

        try:

            courses = []
            page = 1
            total_pages = 1

            while page <= total_pages:
                self.log(
                    f"กำลังโหลดคอร์สระดับ {level_name} "
                    f"หน้า {page}/{total_pages} ..."
                )

                params = {
                    "page": page,
                    "per_page": COURSE_PAGE_SIZE
                }

                if level_slug:
                    params["courses"] = level_slug

                response = self.request(
                    API_GET_COURSES,
                    "GET",
                    params,
                    use_proxy=True,
                    headers=GET_HEADERS
                )

                products, total_pages = parse_course_page_response(response)
                courses.extend(
                    normalize_course(product)
                    for product in products
                )
                page += 1

            self.root.after(
                0,
                self._populate_courses,
                courses,
                level_name
            )

            self.log(
                f"โหลดคอร์สระดับ {level_name} สำเร็จ "
                f"{len(courses)} รายการ"
            )

        except Exception as exc:

            error_message = str(exc)

            self.log(
                f"โหลดรายการคอร์สไม่สำเร็จ: {error_message}"
            )

            self.root.after(
                0,
                lambda: self.course_count.configure(
                    text="โหลดรายการคอร์สไม่สำเร็จ"
                )
            )

            self.root.after(
                0,
                lambda message=error_message: messagebox.showerror(
                    "เกิดข้อผิดพลาด", message
                )
            )

        finally:

            self.root.after(
                0,
                self._load_finished
            )


    def _load_finished(self):

        self.load_running = False
        self.load_button.configure(state="normal")
        self.course_level_combo.configure(state="readonly")
        self.download_button.configure(state="normal")


    def _populate_courses(self, courses, level_name):

        self.courses = courses

        self.course_list.delete(
            0,
            "end"
        )

        for course in courses:
            course_id = course.get("subject_id", "")
            store_product_id = course.get("store_product_id", "")
            display_id = course_id or (
                f"ไม่มีรหัส WE PLUS (สินค้า #{store_product_id})"
            )
            name = course.get("subject_name") or "(ไม่มีชื่อคอร์ส)"
            detail = course.get("course_detail", "ไม่มีรายละเอียด")

            self.course_list.insert(
                "end",
                f"{display_id}  |  {name}  |  {detail}"
            )


        self.course_count.configure(
            text=f"{len(courses)} คอร์ส | ระดับชั้น: {level_name}"
        )


    def select_all(self):

        self.course_list.select_set(
            0,
            "end"
        )


    def clear_selection(self):

        self.course_list.selection_clear(
            0,
            "end"
        )

    def open_course_details(self):

        selected = self.course_list.curselection()

        if len(selected) != 1:
            messagebox.showwarning(
                "เลือกคอร์ส",
                "กรุณาเลือกคอร์สเพียงหนึ่งรายการเพื่อเปิดรายละเอียด"
            )
            return

        course_url = self.courses[selected[0]].get("course_url", "")
        parsed_url = urlparse(course_url)

        if (
            parsed_url.scheme != "https"
            or parsed_url.netloc.lower() != "store.webythebrain.com"
        ):
            messagebox.showerror(
                "เปิดรายละเอียดไม่ได้",
                "URL รายละเอียดคอร์สไม่ถูกต้อง"
            )
            return

        if not webbrowser.open(course_url, new=2):
            messagebox.showerror(
                "เปิดรายละเอียดไม่ได้",
                "ไม่สามารถเปิดหน้าเว็บรายละเอียดคอร์สได้"
            )


    # ========================================================
    # OUTPUT FOLDER
    # ========================================================

    def choose_folder(self):

        folder = filedialog.askdirectory(
            initialdir=self.output_dir.get()
            or str(Path.cwd())
        )

        if folder:
            self.output_dir.set(folder)


    # ========================================================
    # PROXY CONTROL
    # v06
    #
    # External Proxy:
    #   Cannot start or stop.
    #
    # Program Proxy:
    #   Can start and stop normally.
    # ========================================================

    def toggle_proxy(self):

        # ต้องตรวจสอบสถานะตอนเริ่มต้นเสร็จก่อน
        if not self.proxy_detection_complete:
            return

        # External Proxy ห้ามควบคุมเด็ดขาด
        if self.proxy_external:

            self.log(
                "[Proxy Control] ไม่อนุญาตให้ควบคุม External Proxy"
            )

            return

        if self.proxy_starting:
            return

        if self.proxy_enabled:

            self.stop_proxy()

        else:

            self.start_proxy()


    def start_proxy(self):

        if not self.proxy_detection_complete:
            return

        # External Proxy ห้ามเปิดซ้ำหรือควบคุม
        if self.proxy_external:

            self.log(
                "[Proxy Control] External Proxy ถูกล็อกอยู่"
            )

            return

        if self.proxy_starting:
            return

        if self.proxy_process is not None:

            if self.proxy_process.poll() is None:

                self.log(
                    "[Proxy Control] Proxy process ทำงานอยู่แล้ว"
                )

                return


        # ตรวจสอบอีกครั้งก่อนเปิด
        # ป้องกันกรณีมี External Proxy เปิดขึ้นมาหลังเข้าโปรแกรม

        if self.is_proxy_listening():

            self.proxy_external = True
            self.proxy_enabled = True

            self.proxy_status.configure(
                text="Proxy: External / Locked",
                foreground="blue"
            )

            self.proxy_button.configure(
                text="Proxy ถูกล็อก",
                state="disabled"
            )

            self.log(
                "[Proxy Control] พบ Proxy ที่ไม่ได้เปิดโดยโปรแกรม"
            )

            self.log(
                "[Proxy Control] ล็อกการควบคุม Proxy"
            )

            threading.Thread(
                target=self.check_proxy_ip,
                args=("External Proxy Detected",),
                daemon=True
            ).start()

            return


        exe_path = (
            Path(__file__).resolve().parent
            / PROXY_EXE
        )

        if not exe_path.is_file():

            messagebox.showerror(
                "ไม่พบโปรแกรม Proxy",
                f"ไม่พบไฟล์ {PROXY_EXE}\n"
                "กรุณาวางไฟล์ไว้ในโฟลเดอร์เดียวกับโปรแกรม"
            )

            return


        try:

            creationflags = getattr(
                subprocess,
                "CREATE_NO_WINDOW",
                0
            )

            self.proxy_process = subprocess.Popen(
                [str(exe_path)],
                cwd=str(exe_path.parent),
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                creationflags=creationflags
            )

            self.proxy_starting = True

            self.proxy_button.configure(
                text="กำลังเปิด Proxy...",
                state="disabled"
            )

            self.proxy_status.configure(
                text="Proxy: กำลังเริ่มต้น...",
                foreground="orange"
            )

            self.log(
                f"[Proxy Control] กำลังเปิด {PROXY_EXE}"
            )

            # รอให้ Proxy เปิด Port
            self.root.after(
                PROXY_START_INTERVAL,
                self._confirm_proxy_started
            )

        except Exception as exc:

            self.proxy_process = None
            self.proxy_starting = False

            self.proxy_button.configure(
                text="เปิด Proxy",
                state="normal"
            )

            messagebox.showerror(
                "เปิด Proxy ไม่สำเร็จ",
                str(exc)
            )


    def _confirm_proxy_started(self, attempt=0):

        """
        รอจนกว่า HTTP Proxy จะพร้อมใช้งาน
        """

        process_alive = (
            self.proxy_process is not None
            and self.proxy_process.poll() is None
        )
        proxy_ready = False

        if process_alive and self.is_proxy_listening():
            proxy_ready = True

        if process_alive and proxy_ready:

            self.proxy_starting = False
            self.proxy_enabled = True
            self.proxy_external = False

            self.proxy_status.configure(
                text="Proxy: เปิด (Managed)",
                foreground="green"
            )

            self.proxy_button.configure(
                text="ปิด Proxy",
                state="normal"
            )

            self.log(
                "[Proxy Control] เปิด Proxy สำเร็จ"
            )

            self.log(
                f"[Proxy Control] Local endpoint: {PROXY_URL}"
            )

            # ตรวจสอบ IP และประเทศทันที
            threading.Thread(
                target=self.check_proxy_ip,
                args=("Program Proxy Started",),
                daemon=True
            ).start()

            return


        if process_alive and attempt < PROXY_START_RETRY:

            self.root.after(
                PROXY_START_INTERVAL,
                lambda: self._confirm_proxy_started(attempt + 1)
            )

            return


        # เปิดไม่สำเร็จ หรือหมดเวลารอ

        self.log(
            "[Proxy Control] ไม่สามารถเปิด Proxy ได้ภายในเวลาที่กำหนด"
        )

        self.proxy_starting = False

        if self.proxy_process is not None:

            try:

                if self.proxy_process.poll() is None:

                    self.proxy_process.terminate()

                    self.proxy_process.wait(
                        timeout=3
                    )

            except Exception as exc:

                self.log(
                    f"[Proxy Control] ไม่สามารถหยุด Process ได้: {exc}"
                )

        self.proxy_process = None
        self.proxy_enabled = False

        self.proxy_status.configure(
            text="Proxy: ปิด",
            foreground="gray"
        )

        self.proxy_button.configure(
            text="เปิด Proxy",
            state="normal"
        )


    def stop_proxy(self):

        # ป้องกันการปิด External Proxy
        if self.proxy_external:

            self.log(
                "[Proxy Control] ปฏิเสธการปิด External Proxy"
            )

            return

        # ต้องเป็น Process ที่โปรแกรมเปิดเองเท่านั้น
        if self.proxy_process is None:

            self.log(
                "[Proxy Control] ไม่มี Proxy Process ที่โปรแกรมเป็นเจ้าของ"
            )

            return


        try:

            if self.proxy_process.poll() is None:

                self.log(
                    "[Proxy Control] กำลังปิด Proxy ที่เปิดโดยโปรแกรม..."
                )

                self.proxy_process.terminate()

                try:

                    self.proxy_process.wait(
                        timeout=5
                    )

                except subprocess.TimeoutExpired:

                    self.log(
                        "[Proxy Control] Process ไม่ตอบสนอง กำลังบังคับปิด..."
                    )

                    self.proxy_process.kill()

                    self.proxy_process.wait(
                        timeout=3
                    )


        except Exception as exc:

            self.log(
                f"[Proxy Control] ปิด Proxy มีข้อผิดพลาด: {exc}"
            )


        self.proxy_process = None
        self.proxy_enabled = False

        self.proxy_status.configure(
            text="Proxy: ปิด",
            foreground="gray"
        )

        self.proxy_button.configure(
            text="เปิด Proxy",
            state="normal"
        )

        self.log(
            "[Proxy Control] ปิด Proxy ที่เปิดโดยโปรแกรมเรียบร้อย"
        )


    # ========================================================
    # START DOWNLOAD
    # ========================================================

    def _proxy_ready(self):

        if not self.proxy_detection_complete:
            messagebox.showwarning(
                "กำลังตรวจสอบ Proxy",
                "กรุณารอให้การตรวจสอบ Proxy เสร็จสิ้นก่อน"
            )
            return False

        if not self.proxy_enabled or not self.is_proxy_listening():
            messagebox.showwarning(
                "Proxy ยังไม่พร้อม",
                "กรุณาเปิด Proxy ที่ใช้งานได้ก่อนเริ่มทำรายการ"
            )
            return False

        return True


    def start_download(self):

        if self.download_running or self.load_running:
            return

        if not self._proxy_ready():
            return


        selected = self.course_list.curselection()

        if not selected:

            messagebox.showwarning(
                "ยังไม่ได้เลือกคอร์ส",
                "กรุณาเลือกคอร์สที่ต้องการดาวน์โหลด"
            )

            return


        courses = [
            self.courses[i]
            for i in selected
        ]
        downloadable_courses = [
            course
            for course in courses
            if course.get("subject_id")
        ]
        courses_without_id = len(courses) - len(downloadable_courses)

        if not downloadable_courses:
            messagebox.showwarning(
                "ไม่พบรหัสคอร์ส",
                "คอร์สที่เลือกไม่มีรหัส WE PLUS จึงไม่สามารถดาวน์โหลดได้"
            )
            return

        if courses_without_id and not messagebox.askyesno(
            "คอร์สบางรายการไม่มีรหัส",
            f"{courses_without_id} คอร์สไม่มีรหัส WE PLUS "
            "และจะถูกข้าม ต้องการดาวน์โหลดคอร์สที่เหลือต่อหรือไม่?"
        ):
            return

        courses = downloadable_courses

        output_dir = self.output_dir.get().strip()

        if not output_dir:

            messagebox.showwarning(
                "ยังไม่ได้เลือกโฟลเดอร์",
                "กรุณากำหนดโฟลเดอร์ปลายทาง"
            )

            return


        # Capture Checkbox value on GUI thread.
        # This value affects FileAPI only.

        download_via_proxy = (
            self.download_via_proxy.get()
        )

        self.log(
            "FileAPI Proxy setting: "
            + (
                "ON - ผ่าน Proxy"
                if download_via_proxy
                else "OFF - ไม่ผ่าน Proxy"
            )
        )

        self.log(
            "All other APIs: ALWAYS through Proxy"
        )


        self.download_running = True

        self.download_button.configure(
            state="disabled"
        )

        self.load_button.configure(
            state="disabled"
        )

        threading.Thread(
            target=self._download_worker,
            args=(
                courses,
                output_dir,
                download_via_proxy
            ),
            daemon=True
        ).start()


    # ========================================================
    # TOKEN
    # Always use Proxy
    # ========================================================

    def _get_token(self):

        if (
            self.token is None
            or (time.time() - self.token_timestamp)
            > TOKEN_EXPIRED_TIME
        ):

            self.log(
                "Token หมดอายุหรือยังไม่มี "
                "กำลังขอ Token ใหม่..."
            )

            username = TOKEN_USERNAME
            password = TOKEN_PASSWORD

            if not username or not password:
                raise RuntimeError(
                    "Add a username on line 1 and a password on line 2 "
                    f"of {TOKEN_CREDENTIALS_FILE}, or set both "
                    f"{TOKEN_USERNAME_ENV} and {TOKEN_PASSWORD_ENV}"
                )

            response = self.request(
                API_POST_TOKEN,
                "POST",
                {
                    "username": username,
                    "password": password
                },
                use_proxy=True,
                headers=TOKEN_HEADERS
            )

            token = response.json()

            if not isinstance(token, str) or not token:
                raise ValueError(
                    "Token API response must be a non-empty string"
                )

            self.token = token

            self.token_timestamp = time.time()

            self.log(
                "ได้รับ Token ใหม่เรียบร้อย"
            )

        return self.token


    # ========================================================
    # TEACHER QA
    # Always use Proxy
    # ========================================================

    def _get_teacher_qa(
        self,
        qa_id,
        teacher_name
    ):

        qa_payload = {

            "qa_id": qa_id,

            "tutor": teacher_name,

            "qa_image": "N/A",

            "qa_link": "N/A"
        }

        try:

            response = self.request(
                API_POST_TEACHER_QA,
                "POST",
                qa_payload,
                use_proxy=True,
                headers=POST_HEADERS
            )

            qa_data = response.json()

            self.log(
                "TeacherQA Response: "
                + json.dumps(
                    qa_data,
                    ensure_ascii=False
                )
            )

            return qa_data

        except Exception as exc:

            self.log(
                f"TeacherQA เรียกไม่สำเร็จ "
                f"[{teacher_name}]: {exc}"
            )

            return None


    # ========================================================
    # DOWNLOAD FILE
    #
    # Only FileAPI follows Checkbox setting.
    # ========================================================

    def _download_file(
        self,
        course_id,
        relative_path,
        filename,
        save_as,
        output_dir,
        use_proxy
    ):

        token = self._get_token()

        headers = dict(
            POST_HEADERS_FILE
        )

        headers["Authorization"] = (
            "Bearer " + token
        )

        payload = {
            "name": filename,
            "pathname": course_id
        }


        self.log(
            "FileAPI Connection: "
            + (
                "ผ่าน Proxy"
                if use_proxy
                else "ไม่ผ่าน Proxy"
            )
        )


        target = resolve_output_target(
            output_dir,
            course_id,
            relative_path,
            save_as
        )
        target.parent.mkdir(
            parents=True,
            exist_ok=True
        )

        temporary_target = target.with_name(target.name + ".part")

        try:
            with self.request(
                API_POST_FILE,
                "POST",
                payload,
                use_proxy=use_proxy,
                headers=headers,
                stream=True
            ) as response:
                with temporary_target.open("wb") as file:
                    for chunk in response.iter_content(chunk_size=64 * 1024):
                        if chunk:
                            file.write(chunk)

            os.replace(temporary_target, target)
        except Exception:
            if temporary_target.exists():
                temporary_target.unlink()
            raise

        self.log(
            f"ดาวน์โหลดสำเร็จ: {target}"
        )


    # ========================================================
    # DOWNLOAD WORKER
    # ========================================================

    def _download_worker(
        self,
        courses,
        output_dir,
        download_via_proxy
    ):

        try:

            Path(output_dir).mkdir(
                parents=True,
                exist_ok=True
            )


            # ------------------------------------------------
            # IP Information
            # Always use Proxy
            # ------------------------------------------------

            try:

                ip_response = self.request(
                    API_IP_LOCATION,
                    "GET",
                    params={},
                    use_proxy=True,
                    headers=IP_HEADERS
                )

                self.log(
                    "IP information: "
                    + json.dumps(
                        ip_response.json(),
                        ensure_ascii=False
                    )
                )

            except Exception as exc:

                self.log(
                    f"ตรวจสอบ IP ไม่สำเร็จ: {exc}"
                )


            # ------------------------------------------------
            # Loop Courses
            # ------------------------------------------------

            for course in courses:

                subject_id = course.get(
                    "subject_id",
                    ""
                )

                if not subject_id:

                    self.log(
                        "ข้ามรายการที่ไม่มี subject_id"
                    )

                    continue


                self.log(
                    f"\n===== เริ่มคอร์ส "
                    f"{course.get('subject_name', subject_id)} "
                    f"[{subject_id}] ====="
                )


                # ------------------------------------------------
                # Content API
                # Always use Proxy
                # ------------------------------------------------

                try:

                    content_response = self.request(
                        API_GET_CONTENT,
                        "GET",
                        {
                            "id": subject_id
                        },
                        use_proxy=True,
                        headers=GET_HEADERS
                    )

                    content_data = parse_list_response(
                        content_response,
                        "Content API"
                    )

                except Exception as exc:

                    self.log(
                        f"เรียก Content ไม่สำเร็จ "
                        f"[{subject_id}]: {exc}"
                    )

                    continue


                # ------------------------------------------------
                # Loop Content
                # ------------------------------------------------

                for content in content_data:

                    content_name = (
                        str(content.get("$id", ""))
                        + ". "
                        + sanitize_filename(
                            content.get("subject_name", "")
                        )
                    )

                    self.log(
                        f"บทเรียน: {content_name}"
                    )


                    # --------------------------------------------
                    # Teacher API
                    # Always use Proxy
                    # --------------------------------------------

                    teacher_payload = {

                        "subject_id": content.get(
                            "subject_id",
                            ""
                        ),

                        "subject_name": content.get(
                            "subject_name",
                            ""
                        ),

                        "subject_year": content.get(
                            "subject_year",
                            ""
                        )
                    }


                    try:

                        teacher_response = self.request(
                            API_POST_TEACHER,
                            "POST",
                            teacher_payload,
                            use_proxy=True,
                            headers=POST_HEADERS
                        )

                        teachers = parse_list_response(
                            teacher_response,
                            "Teacher API"
                        )

                    except Exception as exc:

                        self.log(
                            f"เรียก Teacher ไม่สำเร็จ "
                            f"[{content_name}]: {exc}"
                        )

                        continue


                    teacher_count = len(teachers)

                    self.log(
                        f"จำนวนผู้สอน = {teacher_count}"
                    )


                    # --------------------------------------------
                    # Loop Teachers
                    # --------------------------------------------

                    for teacher in teachers:

                        teacher_name = teacher.get(
                            "teacher_name",
                            ""
                        )


                        # ----------------------------------------
                        # TeacherQA API
                        # Always use Proxy
                        # ----------------------------------------

                        self._get_teacher_qa(
                            content.get("subject_id", ""),
                            teacher_name
                        )


                        # ----------------------------------------
                        # Video API
                        # Always use Proxy
                        # ----------------------------------------

                        video_payload = {

                            "subject_id": content.get(
                                "subject_id",
                                ""
                            ),

                            "subject_name": content.get(
                                "subject_name",
                                ""
                            ),

                            "subject_year": content.get(
                                "subject_year",
                                ""
                            ),

                            "subject_teacher": teacher_name
                        }


                        try:

                            video_response = self.request(
                                API_POST_VIDEO,
                                "POST",
                                video_payload,
                                use_proxy=True,
                                headers=POST_HEADERS
                            )

                            videos = parse_list_response(
                                video_response,
                                "Video API"
                            )

                        except Exception as exc:

                            self.log(
                                f"เรียก Video ไม่สำเร็จ "
                                f"[{teacher_name}]: {exc}"
                            )

                            continue


                        # ----------------------------------------
                        # Loop Videos
                        # ----------------------------------------

                        for video in videos:

                            docfile = video.get(
                                "document_subject_doc",
                                ""
                            )

                            if not docfile:

                                self.log(
                                    "ข้ามรายการไม่มีชื่อไฟล์: "
                                    + str(
                                        video.get(
                                            "document_name",
                                            ""
                                        )
                                    )
                                )

                                continue


                            ext = sanitize_filename(
                                os.path.splitext(str(docfile))[1]
                            )


                            save_name = (
                                sanitize_filename(video.get("$id", ""))
                                + ". "
                                + sanitize_filename(
                                    video.get(
                                        "document_name",
                                        ""
                                    )
                                )
                                + ext
                            )


                            if teacher_count == 1:

                                relative_path = content_name

                            else:

                                relative_path = str(
                                    Path(content_name)
                                    / sanitize_filename(
                                        teacher_name
                                    )
                                )


                            # ------------------------------------
                            # FileAPI
                            # Proxy controlled by Checkbox
                            # ------------------------------------

                            try:

                                self._download_file(
                                    subject_id,
                                    relative_path,
                                    docfile,
                                    save_name,
                                    output_dir,
                                    download_via_proxy
                                )

                            except Exception as exc:

                                self.log(
                                    f"ดาวน์โหลดไม่สำเร็จ "
                                    f"{docfile}: {exc}"
                                )


            self.log(
                "\n===== เสร็จสิ้นการดาวน์โหลดรายการที่เลือก ====="
            )


        except Exception as exc:

            self.log(
                f"เกิดข้อผิดพลาดระหว่างทำงาน: {exc}"
            )


        finally:

            self.root.after(
                0,
                self._download_finished
            )


    # ========================================================
    # DOWNLOAD FINISHED
    # ========================================================

    def _download_finished(self):

        self.download_running = False

        self.download_button.configure(
            state="normal"
        )

        self.load_button.configure(
            state="normal"
        )


    # ========================================================
    # CLOSE APPLICATION
    # ========================================================

    def on_close(self):

        if self.download_running or self.load_running:
            messagebox.showwarning(
                "กำลังทำงาน",
                "กรุณารอให้การโหลดหรือดาวน์โหลดเสร็จก่อนปิดโปรแกรม"
            )
            return

        # ปิดเฉพาะ Proxy ที่โปรแกรมเป็นผู้เปิดเอง
        # ห้ามปิด External Proxy เด็ดขาด

        if (
            self.proxy_process is not None
            and not self.proxy_external
        ):

            self.stop_proxy()

        else:

            if self.proxy_external:

                self.log(
                    "[Exit] External Proxy จะไม่ถูกปิด"
                )

        self.root.destroy()


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":

    try:
        TOKEN_USERNAME, TOKEN_PASSWORD = load_token_credentials()
    except (OSError, ValueError) as exc:
        root = tk.Tk()
        root.withdraw()
        messagebox.showerror(
            "อ่านข้อมูล Token ไม่สำเร็จ",
            str(exc)
        )
        root.destroy()
        raise SystemExit(1)

    root = tk.Tk()

    app = DownloaderApp(root)

    root.mainloop()
