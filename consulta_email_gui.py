"""
Verificador de Alcanzabilidad de Correos - OSINT Email Reachability
Determina si una direccion de correo puede recibir mensajes sin enviar ninguno.

Metodo de verificacion (3 fases):
  1. Sintaxis   - valida el formato RFC.
  2. DNS MX     - consulta registros MX del dominio.
  3. SMTP       - conecta al servidor y usa RCPT TO para verificar el buzon
                  (tecnica estandar de email verification, sin enviar datos).

Estilo monocromo Macintosh clasico.
"""

import re
import random
import socket
import smtplib
import string
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, datetime
from tkinter import filedialog, messagebox
from typing import Optional
import tkinter as tk

import dns.resolver
import dns.exception
import pandas as pd

# ─── Constantes ──────────────────────────────────────────────────────────────

SMTP_FROM    = "verify@osint-mailcheck.example"
SMTP_TIMEOUT = 10
DNS_TIMEOUT  = 5
MAX_MX_TRIES = 3

ESTADO_OK  = "ALCANZABLE"
ESTADO_NO  = "NO ALCANZABLE"
ESTADO_INC = "INCIERTO"

COLS_EXPORT = [
    "fecha_consulta", "email", "estado", "causa",
    "servidor_mx", "smtp_codigo", "tiempo_ms",
]

CAMPOS_ETIQUETAS = [
    ("fecha_consulta", "Fecha consulta"),
    ("email",          "Correo"),
    ("estado",         "Estado"),
    ("causa",          "Causa"),
    ("servidor_mx",    "Servidor MX"),
    ("smtp_codigo",    "Codigo SMTP"),
    ("tiempo_ms",      "Tiempo (ms)"),
]

FORMATOS = ["xlsx", "csv", "txt"]

BG        = "#FFFFFF"
FG        = "#000000"
SEPARADOR = "#DDDDDD"
LOG_OK    = "#006600"
LOG_ERR   = "#CC0000"
LOG_WARN  = "#996600"

FONT       = ("Courier New", 9)
FONT_BOLD  = ("Courier New", 9, "bold")
FONT_TITLE = ("Courier New", 10, "bold")
FONT_SMALL = ("Courier New", 8)

PLACEHOLDER = (
    "Ingresa uno o mas correos separados por coma o por linea:\n"
    "\n"
    "Ejemplo por coma:\n"
    "usuario@gmail.com, contacto@empresa.pe, info@dominio.com\n"
    "\n"
    "Ejemplo por linea:\n"
    "usuario@gmail.com\n"
    "contacto@empresa.pe\n"
    "info@dominio.com"
)

_TUTORIAL = """\
VERIFICADOR DE ALCANZABILIDAD DE CORREOS - OSINT

Proposito: determinar si al escribir a un correo la comunicacion
llegara sin problemas (incluso si cae en spam).

METODO DE VERIFICACION (3 fases)
  1. Sintaxis   verificacion de formato RFC 5321/5322.
  2. DNS MX     consulta los registros MX del dominio.
  3. SMTP       conecta al servidor de correo y pregunta por el
                buzon usando RCPT TO, sin enviar ningun mensaje.

ESTADOS POSIBLES
  ALCANZABLE     El servidor confirmo que el buzon existe y acepta
                 correos para esa direccion especifica.

  NO ALCANZABLE  El buzon no existe, el dominio no tiene DNS o el
                 servidor rechazo la direccion explicitamente.

  INCIERTO       No fue posible confirmar con certeza:
                 - Catch-all: el servidor acepta CUALQUIER direccion
                   del dominio (Gmail, Outlook, Yahoo, etc.)
                 - Puerto 25 bloqueado en la red actual
                 - Respuesta ambigua o temporal del servidor

CAUSAS FRECUENTES DE "NO ALCANZABLE"
  Sintaxis invalida       el formato del correo es incorrecto
  Dominio no encontrado   el dominio no tiene registros DNS
  Sin registros MX        el dominio no puede recibir correos
  Buzon rechazado (550)   el servidor rechazo la direccion

CAUSAS FRECUENTES DE "INCIERTO"
  Catch-all               el servidor acepta todo el dominio;
                          el correo podria o no existir
  Puerto 25 bloqueado     red corporativa o ISP bloquea salida SMTP
  Greylisting (421/450)   el servidor pospuso la respuesta
  Requiere autenticacion  servidor SMTP privado

NOTA IMPORTANTE
  Proveedores grandes (Gmail, Outlook, Yahoo, Hotmail) siempre
  devuelven INCIERTO porque usan catch-all para proteger la
  privacidad de sus usuarios. Esto es esperado y correcto.

COLUMNAS DE RESULTADO
  email        direccion verificada
  estado       ALCANZABLE / NO ALCANZABLE / INCIERTO
  causa        descripcion del resultado
  servidor_mx  primer servidor MX contactado
  smtp_codigo  codigo SMTP de respuesta (250 = ok, 550 = no existe)
  tiempo_ms    tiempo total de verificacion en milisegundos

CORREOS DE PRUEBA
  usuario@gmail.com         INCIERTO  (catch-all)
  nadie@dominiofake123.pe   NO ALCANZABLE  (dominio no existe)
  test@sinmx.example.com    NO ALCANZABLE  (sin registros MX)
  contacto@empresa_real.pe  ALCANZABLE o INCIERTO
"""


# ─── Logica de verificacion ──────────────────────────────────────────────────

_RE_EMAIL = re.compile(
    r"^[a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}$"
)


def _sintaxis_valida(email: str) -> bool:
    return bool(_RE_EMAIL.match(email.strip()))


def _random_address(domain: str) -> str:
    rnd = "".join(random.choices(string.ascii_lowercase, k=14))
    return f"{rnd}_noexiste@{domain}"


def _get_mx_records(domain: str) -> tuple[Optional[list], str]:
    """
    Retorna (lista_de_(prioridad, host), causa_error).
    None  -> dominio no existe (NXDOMAIN).
    []    -> dominio existe pero sin registros MX.
    """
    resolver = dns.resolver.Resolver()
    resolver.timeout = DNS_TIMEOUT
    resolver.lifetime = DNS_TIMEOUT
    try:
        records = resolver.resolve(domain, "MX")
        mx = sorted(
            [(int(r.preference), str(r.exchange).rstrip(".")) for r in records]
        )
        return mx, ""
    except dns.resolver.NXDOMAIN:
        return None, "Dominio no encontrado"
    except dns.resolver.NoAnswer:
        # Sin MX: intentar registro A como fallback
        try:
            resolver.resolve(domain, "A")
            return [(0, domain)], ""
        except Exception:
            return [], "Sin registros MX"
    except dns.exception.Timeout:
        return [], "Timeout en consulta DNS"
    except Exception as exc:
        return [], f"Error DNS: {str(exc)[:50]}"


def _smtp_verify(email: str, mx_hosts: list, timeout: int) -> dict:
    domain = email.split("@")[1]
    catch_all_probe = _random_address(domain)
    errors: list[str] = []

    for _, host in mx_hosts[:MAX_MX_TRIES]:
        smtp: Optional[smtplib.SMTP] = None
        try:
            smtp = smtplib.SMTP(timeout=timeout)
            smtp.connect(host, 25)
            smtp.ehlo_or_helo_if_needed()

            # STARTTLS si el servidor lo anuncia
            try:
                if smtp.has_extn("STARTTLS"):
                    smtp.starttls()
                    smtp.ehlo()
            except Exception:
                pass

            # --- Fase catch-all: probar direccion inexistente ---
            try:
                smtp.mail(SMTP_FROM)
            except smtplib.SMTPSenderRefused:
                _smtp_close(smtp)
                return {
                    "estado": ESTADO_INC,
                    "causa": "Servidor requiere autenticacion (no verificable)",
                    "servidor_mx": host,
                    "smtp_codigo": None,
                }

            code_probe, _ = smtp.rcpt(catch_all_probe)

            if code_probe == 250:
                _smtp_close(smtp)
                return {
                    "estado": ESTADO_INC,
                    "causa": "Servidor catch-all: acepta cualquier correo del dominio",
                    "servidor_mx": host,
                    "smtp_codigo": code_probe,
                }

            # --- Fase real: verificar la direccion objetivo ---
            smtp.rset()
            try:
                smtp.mail(SMTP_FROM)
            except smtplib.SMTPSenderRefused:
                _smtp_close(smtp)
                return {
                    "estado": ESTADO_INC,
                    "causa": "Servidor requiere autenticacion",
                    "servidor_mx": host,
                    "smtp_codigo": None,
                }

            code, msg = smtp.rcpt(email)
            _smtp_close(smtp)

            if code == 250:
                return {
                    "estado": ESTADO_OK,
                    "causa": "Buzon verificado por SMTP (250)",
                    "servidor_mx": host,
                    "smtp_codigo": code,
                }
            elif code in (550, 551, 553, 554):
                return {
                    "estado": ESTADO_NO,
                    "causa": f"Buzon rechazado por el servidor ({code})",
                    "servidor_mx": host,
                    "smtp_codigo": code,
                }
            elif code == 552:
                return {
                    "estado": ESTADO_NO,
                    "causa": f"Buzon lleno o desactivado ({code})",
                    "servidor_mx": host,
                    "smtp_codigo": code,
                }
            elif code in (421, 450, 451):
                return {
                    "estado": ESTADO_INC,
                    "causa": f"Servidor temporalmente no disponible / greylisting ({code})",
                    "servidor_mx": host,
                    "smtp_codigo": code,
                }
            else:
                return {
                    "estado": ESTADO_INC,
                    "causa": f"Respuesta inesperada del servidor ({code})",
                    "servidor_mx": host,
                    "smtp_codigo": code,
                }

        except smtplib.SMTPConnectError as exc:
            errors.append(f"SMTPConnect {host}: {str(exc)[:40]}")
        except ConnectionRefusedError:
            errors.append(f"Conexion rechazada: {host}")
        except socket.timeout:
            errors.append(f"Timeout: {host}")
        except OSError as exc:
            s = str(exc)
            sl = s.lower()
            if any(c in s for c in ("10060", "10065", "10051")) or "unreachable" in sl or "timed out" in sl:
                errors.append("Puerto 25 bloqueado en esta red")
            elif any(c in s for c in ("10061",)) or "refused" in sl:
                errors.append(f"Conexion rechazada: {host}")
            else:
                errors.append(f"OSError {host}: {s[:40]}")
        except Exception as exc:
            errors.append(f"Error {host}: {str(exc)[:40]}")
        finally:
            if smtp:
                _smtp_close(smtp)

    # Todos los intentos fallaron
    all_err = " ".join(errors).lower()
    if "bloqueado" in all_err or "unreachable" in all_err:
        causa = "Puerto 25 bloqueado en esta red (servidor MX valido)"
    elif "timeout" in all_err or "timed out" in all_err:
        causa = "Timeout de conexion al servidor de correo"
    elif "rechazada" in all_err or "refused" in all_err:
        causa = "Conexion rechazada por el servidor de correo"
    else:
        causa = errors[-1] if errors else "No fue posible contactar el servidor"

    return {
        "estado": ESTADO_INC,
        "causa": causa,
        "servidor_mx": mx_hosts[0][1] if mx_hosts else None,
        "smtp_codigo": None,
    }


def _smtp_close(smtp: smtplib.SMTP) -> None:
    try:
        smtp.quit()
    except Exception:
        try:
            smtp.close()
        except Exception:
            pass


def verificar_email(email: str, timeout: int = SMTP_TIMEOUT) -> dict:
    """
    Verifica si una direccion de correo es alcanzable.
    Retorna dict con: email, estado, causa, servidor_mx, smtp_codigo, tiempo_ms.
    """
    email = email.strip().lower()
    t0 = time.time()
    base = {
        "fecha_consulta": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "email": email,
        "estado": None,
        "causa": None,
        "servidor_mx": None,
        "smtp_codigo": None,
        "tiempo_ms": 0.0,
    }

    # Fase 1: sintaxis
    if not _sintaxis_valida(email):
        base.update({"estado": ESTADO_NO, "causa": "Sintaxis invalida"})
        base["tiempo_ms"] = round((time.time() - t0) * 1000, 1)
        return base

    domain = email.split("@")[1]

    # Fase 2: DNS MX
    mx_records, dns_error = _get_mx_records(domain)
    if mx_records is None:
        base.update({"estado": ESTADO_NO, "causa": dns_error or "Dominio no encontrado"})
        base["tiempo_ms"] = round((time.time() - t0) * 1000, 1)
        return base
    if not mx_records:
        base.update({"estado": ESTADO_NO, "causa": dns_error or "Sin registros MX"})
        base["tiempo_ms"] = round((time.time() - t0) * 1000, 1)
        return base

    base["servidor_mx"] = mx_records[0][1]

    # Fase 3: SMTP
    smtp_result = _smtp_verify(email, mx_records, timeout)
    base.update(smtp_result)
    base["tiempo_ms"] = round((time.time() - t0) * 1000, 1)
    return base


# ─── Exportacion ─────────────────────────────────────────────────────────────

def exportar_datos(datos: list, formato: str, ruta: str) -> None:
    df = pd.DataFrame([{c: r.get(c, "") or "" for c in COLS_EXPORT} for r in datos])
    fmt = formato.lower()
    if fmt == "xlsx":
        df.to_excel(ruta, index=False, engine="openpyxl")
    elif fmt == "csv":
        df.to_csv(ruta, index=False, encoding="utf-8-sig")
    elif fmt == "txt":
        df.to_csv(ruta, index=False, sep="\t", encoding="utf-8-sig")
    else:
        raise ValueError(f"Formato desconocido: {formato}")


# ─── Widgets personalizados ──────────────────────────────────────────────────

class MacProgressBar(tk.Canvas):
    def __init__(self, parent, height: int = 12, **kwargs):
        super().__init__(
            parent, height=height, bg=BG,
            highlightthickness=1, highlightbackground=FG, **kwargs,
        )
        self._pct = 0.0
        self.bind("<Configure>", lambda e: self._draw())

    def set(self, value: float) -> None:
        self._pct = max(0.0, min(100.0, value))
        self._draw()

    def _draw(self) -> None:
        self.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        if w <= 2:
            return
        fw = int((self._pct / 100.0) * (w - 2))
        if fw > 0:
            self.create_rectangle(1, 1, 1 + fw, h - 1, fill=FG, outline="")


def _mac_btn(parent, text: str, command, inverted: bool = True) -> tk.Label:
    bg_n, fg_n = (FG, BG) if inverted else (BG, FG)
    b = tk.Label(
        parent, text=text, bg=bg_n, fg=fg_n, font=FONT_BOLD,
        cursor="hand2", padx=10, pady=4, relief=tk.FLAT,
        highlightthickness=1, highlightbackground=FG,
    )
    b._enabled = True

    def _click(e):
        if b._enabled:
            command()

    def _enter(e):
        if b._enabled:
            b.config(bg=BG if inverted else FG, fg=FG if inverted else BG)

    def _leave(e):
        if b._enabled:
            b.config(bg=bg_n, fg=fg_n)

    b.bind("<Button-1>", _click)
    b.bind("<Enter>", _enter)
    b.bind("<Leave>", _leave)
    return b


def _entry(parent, textvariable, width: int = 30, **kw) -> tk.Entry:
    return tk.Entry(
        parent, textvariable=textvariable, width=width, font=FONT,
        bg=BG, fg=FG, insertbackground=FG, relief=tk.FLAT,
        highlightthickness=1, highlightbackground=FG, highlightcolor=FG,
        **kw,
    )


def _lbl(parent, text: str, font=None, **kw) -> tk.Label:
    return tk.Label(parent, text=text, bg=BG, fg=FG, font=font or FONT, **kw)


def _spinbox(parent, var, from_, to, increment, width=5) -> tk.Spinbox:
    return tk.Spinbox(
        parent, from_=from_, to=to, increment=increment,
        textvariable=var, width=width,
        bg=BG, fg=FG, insertbackground=FG, relief=tk.FLAT,
        highlightthickness=1, highlightbackground=FG,
        buttonbackground=BG, font=FONT,
    )


# ─── Aplicacion principal ────────────────────────────────────────────────────

class AppEmailGUI(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Verificador de Correos - Email Reachability")
        self.configure(bg=BG)
        self.resizable(False, False)
        self._running        = False
        self._resultados: list = []
        self._placeholder_on = True
        self._tab_btns: dict = {}
        self._panels: dict   = {}
        self._build_ui()
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self._center()

    def _center(self) -> None:
        self.update_idletasks()
        w, h = self.winfo_width(), self.winfo_height()
        x = (self.winfo_screenwidth()  - w) // 2
        y = (self.winfo_screenheight() - h) // 2
        self.geometry(f"+{x}+{y}")

    # ── Construccion UI ───────────────────────────────────────────────────────

    def _build_ui(self) -> None:
        self._build_header()
        self._build_tab_bar()
        self._content = tk.Frame(self, bg=BG, padx=12, pady=10)
        self._content.pack(fill=tk.BOTH)
        for tab_id, builder in [
            ("individual", self._build_panel_individual),
            ("masiva",     self._build_panel_masiva),
            ("tutorial",   self._build_panel_tutorial),
        ]:
            frame = tk.Frame(self._content, bg=BG)
            self._panels[tab_id] = frame
            builder(frame)
        self._show_tab("individual")
        self._build_status_bar()

    def _build_header(self) -> None:
        hdr = tk.Frame(self, bg=FG, padx=10, pady=6)
        hdr.pack(fill=tk.X)
        tk.Label(hdr, text="VERIFICADOR DE ALCANZABILIDAD DE CORREOS",
                 bg=FG, fg=BG, font=FONT_TITLE).pack(side=tk.LEFT)
        tk.Label(hdr, text="RPAPP_BAHC_EMAIL",
                 bg=FG, fg=BG, font=FONT_SMALL).pack(side=tk.RIGHT, pady=2)

    def _build_tab_bar(self) -> None:
        bar = tk.Frame(self, bg=FG)
        bar.pack(fill=tk.X)
        for tab_id, label in [
            ("individual", "  INDIVIDUAL  "),
            ("masiva",     "  MASIVA  "),
            ("tutorial",   "  TUTORIAL  "),
        ]:
            btn = tk.Label(bar, text=label, bg=BG, fg=FG,
                           font=FONT_BOLD, cursor="hand2", pady=5)
            btn.pack(side=tk.LEFT)
            btn.bind("<Button-1>", lambda e, t=tab_id: self._show_tab(t))
            self._tab_btns[tab_id] = btn
        tk.Frame(bar, bg=BG).pack(side=tk.LEFT, fill=tk.X, expand=True)

    def _show_tab(self, tab: str) -> None:
        for t, frame in self._panels.items():
            if t == tab:
                frame.pack(fill=tk.BOTH)
            else:
                frame.pack_forget()
        for t, btn in self._tab_btns.items():
            btn.config(bg=FG if t == tab else BG, fg=BG if t == tab else FG)

    # ── Panel INDIVIDUAL ──────────────────────────────────────────────────────

    def _build_panel_individual(self, p: tk.Frame) -> None:
        row = tk.Frame(p, bg=BG)
        row.pack(fill=tk.X, pady=(0, 6))
        _lbl(row, "Correo:").pack(side=tk.LEFT)
        self._email_var = tk.StringVar()
        e = _entry(row, self._email_var, width=34)
        e.pack(side=tk.LEFT, padx=(6, 8), ipady=4)
        e.bind("<Return>", lambda _: self._verificar_individual())
        _mac_btn(row, "VERIFICAR", self._verificar_individual, inverted=True).pack(side=tk.LEFT)

        self._lbl_err_ind = tk.Label(p, text="", bg=BG, fg=LOG_ERR,
                                      font=FONT_SMALL, anchor="w")
        self._lbl_err_ind.pack(fill=tk.X, pady=(0, 4))

        # Tabla de resultados
        tbl = tk.Frame(p, bg=BG, highlightthickness=1, highlightbackground=FG)
        tbl.pack(fill=tk.X)

        hdr_row = tk.Frame(tbl, bg=FG)
        hdr_row.pack(fill=tk.X)
        tk.Label(hdr_row, text="CAMPO", bg=FG, fg=BG, font=FONT_BOLD,
                 width=16, anchor="w", padx=6, pady=3).pack(side=tk.LEFT)
        tk.Frame(hdr_row, bg=SEPARADOR, width=1).pack(side=tk.LEFT, fill=tk.Y)
        tk.Label(hdr_row, text="VALOR", bg=FG, fg=BG, font=FONT_BOLD,
                 anchor="w", padx=6, pady=3).pack(side=tk.LEFT, fill=tk.X, expand=True)

        self._res_labels: dict = {}
        for idx, (campo, etiqueta) in enumerate(CAMPOS_ETIQUETAS):
            row_bg = BG if idx % 2 == 0 else SEPARADOR
            dr = tk.Frame(tbl, bg=row_bg)
            dr.pack(fill=tk.X)
            tk.Label(dr, text=etiqueta, bg=row_bg, fg=FG, font=FONT_BOLD,
                     width=16, anchor="w", padx=6, pady=3).pack(side=tk.LEFT)
            tk.Frame(dr, bg=SEPARADOR, width=1).pack(side=tk.LEFT, fill=tk.Y)
            val = tk.Label(dr, text="-", bg=row_bg, fg=FG, font=FONT,
                           anchor="w", padx=6, pady=3, wraplength=340)
            val.pack(side=tk.LEFT, fill=tk.X, expand=True)
            self._res_labels[campo] = val

    # ── Panel MASIVA ──────────────────────────────────────────────────────────

    def _build_panel_masiva(self, p: tk.Frame) -> None:
        _lbl(p, "Correos a verificar (separados por coma o por linea):").pack(anchor="w")

        txt_frame = tk.Frame(p, bg=BG, highlightthickness=1, highlightbackground=FG)
        txt_frame.pack(fill=tk.X, pady=(2, 4))
        self._text_emails = tk.Text(
            txt_frame, height=6, bg=BG, fg=FG, insertbackground=FG,
            font=FONT, relief=tk.FLAT, wrap=tk.WORD, highlightthickness=0,
        )
        scr = tk.Scrollbar(txt_frame, orient=tk.VERTICAL, command=self._text_emails.yview,
                           bg=BG, troughcolor=SEPARADOR, relief=tk.FLAT, width=10)
        self._text_emails.configure(yscrollcommand=scr.set)
        self._text_emails.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scr.pack(side=tk.RIGHT, fill=tk.Y)
        self._set_placeholder()
        self._text_emails.bind("<FocusIn>",  self._on_focus_in)
        self._text_emails.bind("<FocusOut>", self._on_focus_out)

        file_row = tk.Frame(p, bg=BG)
        file_row.pack(fill=tk.X, pady=(0, 6))
        _mac_btn(file_row, "CARGAR ARCHIVO (Excel/CSV)", self._cargar_archivo,
                 inverted=False).pack(side=tk.LEFT)
        self._lbl_archivo = tk.Label(file_row, text="", bg=BG, fg=FG,
                                      font=FONT_SMALL, anchor="w")
        self._lbl_archivo.pack(side=tk.LEFT, padx=(8, 0))

        # Opciones: workers y timeout
        opts_row = tk.Frame(p, bg=BG)
        opts_row.pack(fill=tk.X, pady=(0, 6))
        _lbl(opts_row, "Conexiones paralelas:").pack(side=tk.LEFT)
        self._workers_var = tk.IntVar(value=5)
        _spinbox(opts_row, self._workers_var, 1, 20, 1, width=4).pack(
            side=tk.LEFT, padx=(4, 16), ipady=2)
        _lbl(opts_row, "Timeout SMTP (seg):").pack(side=tk.LEFT)
        self._timeout_var = tk.IntVar(value=10)
        _spinbox(opts_row, self._timeout_var, 5, 30, 5, width=4).pack(
            side=tk.LEFT, padx=(4, 0), ipady=2)

        # Barra de progreso
        prog_row = tk.Frame(p, bg=BG)
        prog_row.pack(fill=tk.X, pady=(6, 8))
        self._progressbar = MacProgressBar(prog_row, height=14)
        self._progressbar.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self._lbl_pct = tk.Label(prog_row, text="0%", bg=BG, fg=FG,
                                  font=FONT_SMALL, width=5)
        self._lbl_pct.pack(side=tk.LEFT, padx=(6, 0))

        tk.Frame(p, bg=SEPARADOR, height=1).pack(fill=tk.X, pady=(0, 8))

        # Exportacion
        exp_row = tk.Frame(p, bg=BG)
        exp_row.pack(fill=tk.X, pady=(0, 6))
        _lbl(exp_row, "Formato:").pack(side=tk.LEFT)
        self._formato_var = tk.StringVar(value="xlsx")
        om = tk.OptionMenu(exp_row, self._formato_var, *FORMATOS)
        om.config(bg=BG, fg=FG, font=FONT, relief=tk.FLAT,
                  highlightthickness=1, highlightbackground=FG,
                  activebackground=FG, activeforeground=BG, bd=0)
        om["menu"].config(bg=BG, fg=FG, font=FONT, relief=tk.FLAT, bd=0,
                          activebackground=FG, activeforeground=BG)
        om.pack(side=tk.LEFT, padx=(4, 10))
        _lbl(exp_row, "Nombre:").pack(side=tk.LEFT)
        self._nombre_var = tk.StringVar(
            value=f"verificacion_email_{date.today().isoformat()}")
        _entry(exp_row, self._nombre_var, width=26).pack(
            side=tk.LEFT, padx=(4, 0), ipady=2)

        # Botones principales
        btn_row = tk.Frame(p, bg=BG)
        btn_row.pack(fill=tk.X, pady=(4, 0))
        self._btn_iniciar  = _mac_btn(btn_row, "INICIAR",   self._iniciar_masiva,  inverted=True)
        self._btn_cancelar = _mac_btn(btn_row, "CANCELAR",  self._cancelar,        inverted=False)
        self._btn_exportar = _mac_btn(btn_row, "EXPORTAR",  self._exportar,        inverted=False)
        self._btn_iniciar.pack(side=tk.LEFT)
        self._btn_cancelar.pack(side=tk.LEFT, padx=(6, 0))
        self._btn_exportar.pack(side=tk.LEFT, padx=(6, 0))
        self._btn_cancelar._enabled = False
        self._btn_exportar._enabled = False
        self._btn_cancelar.config(cursor="")
        self._btn_exportar.config(cursor="")

        # Contadores de resultados
        tk.Frame(p, bg=SEPARADOR, height=1).pack(fill=tk.X, pady=(8, 4))
        cnt_row = tk.Frame(p, bg=BG)
        cnt_row.pack(fill=tk.X, pady=(0, 4))
        self._lbl_cnt_ok  = tk.Label(cnt_row, text="Alcanzables: 0",  bg=BG, fg=LOG_OK,  font=FONT_BOLD)
        self._lbl_cnt_no  = tk.Label(cnt_row, text="No alcanzables: 0", bg=BG, fg=LOG_ERR, font=FONT_BOLD)
        self._lbl_cnt_inc = tk.Label(cnt_row, text="Inciertos: 0",    bg=BG, fg=LOG_WARN, font=FONT_BOLD)
        self._lbl_cnt_ok.pack(side=tk.LEFT, padx=(0, 12))
        self._lbl_cnt_no.pack(side=tk.LEFT, padx=(0, 12))
        self._lbl_cnt_inc.pack(side=tk.LEFT)

        # Log en tiempo real
        log_frame = tk.Frame(p, bg=BG, highlightthickness=1, highlightbackground=SEPARADOR)
        log_frame.pack(fill=tk.X)
        self._text_log = tk.Text(
            log_frame, height=5, bg=BG, fg=FG, insertbackground=FG,
            font=FONT_SMALL, relief=tk.FLAT, state=tk.DISABLED,
            wrap=tk.NONE, highlightthickness=0,
        )
        self._text_log.tag_config("ok",   foreground=LOG_OK)
        self._text_log.tag_config("err",  foreground=LOG_ERR)
        self._text_log.tag_config("warn", foreground=LOG_WARN)
        lsy = tk.Scrollbar(log_frame, orient=tk.VERTICAL,   command=self._text_log.yview,
                           bg=BG, troughcolor=SEPARADOR, relief=tk.FLAT, width=10)
        lsx = tk.Scrollbar(log_frame, orient=tk.HORIZONTAL, command=self._text_log.xview,
                           bg=BG, troughcolor=SEPARADOR, relief=tk.FLAT)
        self._text_log.configure(yscrollcommand=lsy.set, xscrollcommand=lsx.set)
        self._text_log.grid(row=0, column=0, sticky="nsew")
        lsy.grid(row=0, column=1, sticky="ns")
        lsx.grid(row=1, column=0, sticky="ew")
        log_frame.grid_rowconfigure(0, weight=1)
        log_frame.grid_columnconfigure(0, weight=1)

    # ── Panel TUTORIAL ────────────────────────────────────────────────────────

    def _build_panel_tutorial(self, p: tk.Frame) -> None:
        txt = tk.Text(
            p, height=30, bg=BG, fg=FG, font=FONT, relief=tk.FLAT,
            wrap=tk.WORD, state=tk.NORMAL,
            highlightthickness=1, highlightbackground=SEPARADOR,
            padx=8, pady=6,
        )
        txt.insert("1.0", _TUTORIAL)
        txt.configure(state=tk.DISABLED)
        txt.pack(fill=tk.BOTH)

    # ── Barra de estado ───────────────────────────────────────────────────────

    def _build_status_bar(self) -> None:
        tk.Frame(self, bg=SEPARADOR, height=1).pack(fill=tk.X, side=tk.BOTTOM)
        bar = tk.Frame(self, bg=BG, padx=8, pady=3)
        bar.pack(fill=tk.X, side=tk.BOTTOM)
        self._status_var = tk.StringVar(value="Listo.")
        tk.Label(bar, textvariable=self._status_var, bg=BG, fg=FG,
                 font=FONT_SMALL, anchor="w").pack(fill=tk.X)

    def _status(self, msg: str) -> None:
        self.after(0, lambda: self._status_var.set(msg))

    def _log_append(self, texto: str, tag: str = "") -> None:
        def _ins():
            self._text_log.configure(state=tk.NORMAL)
            self._text_log.insert(tk.END, texto + "\n", tag)
            self._text_log.see(tk.END)
            self._text_log.configure(state=tk.DISABLED)
        self.after(0, _ins)

    # ── Placeholder ───────────────────────────────────────────────────────────

    def _set_placeholder(self) -> None:
        self._text_emails.delete("1.0", tk.END)
        self._text_emails.insert("1.0", PLACEHOLDER)
        self._text_emails.config(fg=SEPARADOR)
        self._placeholder_on = True

    def _on_focus_in(self, _) -> None:
        if self._placeholder_on:
            self._text_emails.delete("1.0", tk.END)
            self._text_emails.config(fg=FG)
            self._placeholder_on = False

    def _on_focus_out(self, _) -> None:
        if not self._text_emails.get("1.0", tk.END).strip():
            self._set_placeholder()

    def _get_emails_texto(self) -> list[str]:
        if self._placeholder_on:
            return []
        raw = self._text_emails.get("1.0", tk.END)
        tokens = re.split(r"[,\s\n;]+", raw)
        seen: set[str] = set()
        result = []
        for t in tokens:
            t = t.strip().lower()
            if t and t not in seen:
                seen.add(t)
                result.append(t)
        return result

    # ── Pestaña INDIVIDUAL ────────────────────────────────────────────────────

    def _verificar_individual(self) -> None:
        email = self._email_var.get().strip().lower()
        if not email:
            self._lbl_err_ind.config(text="Ingresa una direccion de correo.")
            return
        self._lbl_err_ind.config(text="")
        for campo, _ in CAMPOS_ETIQUETAS:
            self._res_labels[campo].config(text="...", fg=FG)
        self._status(f"Verificando {email}...")

        def _worker():
            timeout = SMTP_TIMEOUT
            try:
                timeout = int(self._timeout_var.get())
            except Exception:
                pass
            resultado = verificar_email(email, timeout)
            self.after(0, lambda r=resultado: self._mostrar_individual(r))

        threading.Thread(target=_worker, daemon=True).start()

    def _mostrar_individual(self, r: dict) -> None:
        color_estado = {
            ESTADO_OK:  LOG_OK,
            ESTADO_NO:  LOG_ERR,
            ESTADO_INC: LOG_WARN,
        }
        for campo, _ in CAMPOS_ETIQUETAS:
            val = str(r.get(campo, "-") or "-")
            lbl = self._res_labels[campo]
            if campo == "estado":
                lbl.config(text=val, fg=color_estado.get(val, FG), font=FONT_BOLD)
            else:
                lbl.config(text=val, fg=FG, font=FONT)
        self._status(
            f"{r['email']} → {r['estado']} | {r['causa']} | {r['tiempo_ms']} ms"
        )

    # ── Pestaña MASIVA ────────────────────────────────────────────────────────

    def _cargar_archivo(self) -> None:
        ruta = filedialog.askopenfilename(
            filetypes=[("Excel y CSV", "*.xlsx *.xls *.csv"),
                       ("Excel", "*.xlsx *.xls"), ("CSV", "*.csv")],
            title="Seleccionar archivo con correos",
        )
        if not ruta:
            return
        try:
            if ruta.lower().endswith((".xlsx", ".xls")):
                df = pd.read_excel(ruta, header=None, dtype=str)
            else:
                df = pd.read_csv(ruta, header=None, dtype=str)
            emails = (
                df.iloc[:, 0].fillna("").astype(str).str.strip().str.lower().tolist()
            )
            emails = [e for e in emails if e and "@" in e and e.lower() != "email"]
            if not emails:
                messagebox.showwarning("Sin datos",
                                       "No se encontraron correos en la columna A.")
                return
            self._text_emails.delete("1.0", tk.END)
            self._text_emails.insert("1.0", "\n".join(emails))
            self._text_emails.config(fg=FG)
            self._placeholder_on = False
            nombre = ruta.replace("\\", "/").split("/")[-1]
            self._lbl_archivo.config(text=f"{nombre} ({len(emails)} correos)")
            self._status(f"Cargado: {nombre} ({len(emails)} correos)")
        except Exception as exc:
            messagebox.showerror("Error al cargar", str(exc))

    def _iniciar_masiva(self) -> None:
        emails = self._get_emails_texto()
        if not emails:
            messagebox.showwarning("Sin datos",
                                   "Ingresa correos o carga un archivo.")
            return

        invalidos = [e for e in emails if not _sintaxis_valida(e)]
        if invalidos:
            lista = ", ".join(invalidos[:5]) + ("..." if len(invalidos) > 5 else "")
            if not messagebox.askyesno(
                "Correos invalidos",
                f"{len(invalidos)} correo(s) con sintaxis invalida seran marcados:\n{lista}"
                "\n\nContinuar?",
            ):
                return

        self._resultados = []
        self._running = True
        self._progressbar.set(0)
        self._lbl_pct.config(text="0%")
        self._lbl_cnt_ok.config(text="Alcanzables: 0")
        self._lbl_cnt_no.config(text="No alcanzables: 0")
        self._lbl_cnt_inc.config(text="Inciertos: 0")
        self._text_log.configure(state=tk.NORMAL)
        self._text_log.delete("1.0", tk.END)
        self._text_log.configure(state=tk.DISABLED)
        self._btn_iniciar._enabled  = False;  self._btn_iniciar.config(cursor="")
        self._btn_cancelar._enabled = True;   self._btn_cancelar.config(cursor="hand2")
        self._btn_exportar._enabled = False;  self._btn_exportar.config(cursor="")

        workers = max(1, self._workers_var.get())
        timeout = max(5, self._timeout_var.get())
        total   = len(emails)
        _cnt    = {"ok": 0, "no": 0, "inc": 0, "done": 0}
        _lock   = threading.Lock()

        def _on_result(r: dict) -> None:
            with _lock:
                self._resultados.append(r)
                _cnt["done"] += 1
                if r["estado"] == ESTADO_OK:
                    _cnt["ok"] += 1
                elif r["estado"] == ESTADO_NO:
                    _cnt["no"] += 1
                else:
                    _cnt["inc"] += 1
                done, ok, no, inc = _cnt["done"], _cnt["ok"], _cnt["no"], _cnt["inc"]

            tag = "ok" if r["estado"] == ESTADO_OK else ("err" if r["estado"] == ESTADO_NO else "warn")
            simbolo = "[OK]" if r["estado"] == ESTADO_OK else ("[NO]" if r["estado"] == ESTADO_NO else "[??]")
            self._log_append(
                f"{simbolo} {r['email']:<40} {r['estado']:<15} {r['causa']}",
                tag,
            )
            pct = (done / total * 100) if total else 0
            self.after(0, lambda p=pct, d=done, o=ok, n=no, i=inc: (
                self._progressbar.set(p),
                self._lbl_pct.config(text=f"{p:.0f}%"),
                self._lbl_cnt_ok.config(text=f"Alcanzables: {o}"),
                self._lbl_cnt_no.config(text=f"No alcanzables: {n}"),
                self._lbl_cnt_inc.config(text=f"Inciertos: {i}"),
                self._status_var.set(f"Verificando {d}/{total}..."),
            ))

        def _worker_thread() -> None:
            def _check_one(email: str) -> dict:
                if not self._running:
                    return {"email": email, "estado": "CANCELADO", "causa": "Cancelado por usuario",
                            "servidor_mx": None, "smtp_codigo": None, "tiempo_ms": 0.0}
                return verificar_email(email, timeout)

            try:
                with ThreadPoolExecutor(max_workers=workers) as pool:
                    futures = {pool.submit(_check_one, e): e for e in emails}
                    for future in as_completed(futures):
                        if not self._running:
                            for f in futures:
                                f.cancel()
                            break
                        try:
                            result = future.result()
                            _on_result(result)
                        except Exception as exc:
                            email_f = futures[future]
                            _on_result({
                                "email": email_f, "estado": ESTADO_INC,
                                "causa": f"Error interno: {str(exc)[:50]}",
                                "servidor_mx": None, "smtp_codigo": None, "tiempo_ms": 0.0,
                            })
            except Exception as exc:
                self._log_append(f"Error fatal: {exc}", "err")
            finally:
                self._running = False
                self.after(0, self._finalizar_masiva)

        threading.Thread(target=_worker_thread, daemon=True).start()

    def _finalizar_masiva(self) -> None:
        self._btn_iniciar._enabled  = True;  self._btn_iniciar.config(cursor="hand2")
        self._btn_cancelar._enabled = False; self._btn_cancelar.config(cursor="")
        if self._resultados:
            self._btn_exportar._enabled = True; self._btn_exportar.config(cursor="hand2")
        self._progressbar.set(100)
        self._lbl_pct.config(text="100%")
        total = len(self._resultados)
        ok  = sum(1 for r in self._resultados if r["estado"] == ESTADO_OK)
        no  = sum(1 for r in self._resultados if r["estado"] == ESTADO_NO)
        inc = sum(1 for r in self._resultados if r["estado"] == ESTADO_INC)
        self._status(
            f"Completado: {total} correos | Alcanzables={ok} | No alcanzables={no} | Inciertos={inc}"
        )

    def _cancelar(self) -> None:
        if self._running:
            self._running = False
            self._status("Cancelando...")

    def _exportar(self) -> None:
        if not self._resultados:
            messagebox.showwarning("Sin datos", "No hay resultados para exportar.")
            return
        fmt    = self._formato_var.get()
        nombre = self._nombre_var.get().strip() or f"verificacion_email_{date.today().isoformat()}"
        if not nombre.endswith(f".{fmt}"):
            nombre = f"{nombre}.{fmt}"
        ext_map = {
            "xlsx": [("Excel", "*.xlsx")],
            "csv":  [("CSV", "*.csv")],
            "txt":  [("Texto tabulado", "*.txt")],
        }
        ruta = filedialog.asksaveasfilename(
            defaultextension=f".{fmt}",
            filetypes=ext_map.get(fmt, [("Todos", "*.*")]),
            initialfile=nombre,
            title="Guardar resultados",
        )
        if not ruta:
            return
        try:
            exportar_datos(self._resultados, fmt, ruta)
            self._status(f"Exportado: {ruta}")
            messagebox.showinfo("Exportacion exitosa", f"Guardado en:\n{ruta}")
        except Exception as exc:
            messagebox.showerror("Error al exportar", str(exc))

    # ── Cierre ────────────────────────────────────────────────────────────────

    def _on_close(self) -> None:
        if self._running:
            if not messagebox.askyesno("En progreso",
                                       "Hay verificaciones activas. Cerrar de todas formas?"):
                return
        self._running = False
        self.destroy()


# ─── Entry point ─────────────────────────────────────────────────────────────

def main() -> None:
    app = AppEmailGUI()
    app.mainloop()


if __name__ == "__main__":
    main()
