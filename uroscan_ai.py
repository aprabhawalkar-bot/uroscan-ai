"""
UroScan AI - Urine Test Strip Reader using Colorimetry (Point-of-Care Technology)
================================================================================
OOP with Python | Mini-project built on Experiments 1 - 8 | Case study KJS-HLC-01

Run:   python uroscan_ai.py          (only the Python standard library is needed)

Where each experiment shows up in this program
----------------------------------------------
Exp 1  Classes & objects       -> Patient class, getter/setter methods, @staticmethod, @classmethod
Exp 2  Constructors & lists    -> parameterised __init__ in every class, lists of pads / results / threads
Exp 3  Strings & inheritance   -> DiagnosticDevice -> UrineTestStripReader, quick-entry text parser,
                                  formatted text report (strip/upper/title/split/f-strings)
Exp 4  Abstract class & poly.  -> StripPad(ABC) with ThresholdPad and PHPad overriding classify()/band()
Exp 5  Exceptions & threads    -> InvalidSampleError, try/except/finally, Batch Lab = one thread per sample
Exp 6  Collections & lambda    -> dict readings, tuple patient info, set of categories, map/filter/reduce
Exp 7  Tkinter Canvas          -> logo, test strip, gauge, charts and every animation are drawn on Canvas
Exp 8  SQLite                  -> patients + tests tables, INSERT/SELECT/WHERE/LIKE/ORDER BY/GROUP BY/DELETE
"""

import csv
import math
import os
import queue
import random
import sqlite3
import threading
import time
import datetime
import tkinter as tk
from abc import ABC, abstractmethod
from functools import reduce
from tkinter import ttk, messagebox, filedialog
import tkinter.font as tkfont

# --------------------------------------------------------------------------------------
# Student details (edit these)
# --------------------------------------------------------------------------------------
STUDENT = "Aaradhya Prabhawalkar"
ROLL_NO = "16010425086"
BATCH = "A3"
CASE_STUDY = "KJS-HLC-01 · Urine Test Strip Reader using Colorimetry"

APP_NAME = "UroScan AI"

# --------------------------------------------------------------------------------------
# Theme
# --------------------------------------------------------------------------------------
BG = "#0b1220"
BG_DEEP = "#070c17"
PANEL = "#111a2c"
PANEL2 = "#17223a"
LINE = "#26344f"
TEXT = "#e7edf7"
MUTED = "#8a9ab3"
ACCENT = "#22d3ee"
ACCENT2 = "#a78bfa"
GREEN = "#34d399"
AMBER = "#fbbf24"
RED = "#f87171"
STRIP = "#eef2f7"
STRIP_HANDLE = "#d3dbe6"

LEVEL_COLORS = {"Normal": GREEN, "Moderate": AMBER, "High": RED}
STATUS_COLORS = {
    "NORMAL": GREEN,
    "FURTHER EVALUATION ADVISED": AMBER,
    "HIGH RISK": RED,
}
STATUS_ADVICE = {
    "NORMAL": "No abnormal analytes detected. Routine follow-up only.",
    "FURTHER EVALUATION ADVISED": "Some analytes are outside the normal range. Repeat the test or consult a clinician.",
    "HIGH RISK": "Several analytes are markedly raised. Refer for a full laboratory urinalysis.",
}

F = {}  # fonts, filled once Tk is running
UI_FONT = "TkDefaultFont"
MONO_FONT = "TkFixedFont"


def init_fonts(root):
    global UI_FONT, MONO_FONT
    families = set(tkfont.families(root))

    def pick(options, fallback):
        for name in options:
            if name in families:
                return name
        return fallback

    UI_FONT = pick(["Segoe UI", "SF Pro Text", "Helvetica Neue", "Inter", "Roboto", "Ubuntu", "DejaVu Sans", "Arial"], "Helvetica")
    MONO_FONT = pick(["Cascadia Mono", "Consolas", "Menlo", "JetBrains Mono", "DejaVu Sans Mono", "Courier New"], "Courier")
    F.update(
        splash=(UI_FONT, 38, "bold"),
        h1=(UI_FONT, 19, "bold"),
        h2=(UI_FONT, 14, "bold"),
        h3=(UI_FONT, 11, "bold"),
        body=(UI_FONT, 10),
        small=(UI_FONT, 9),
        tiny=(UI_FONT, 8),
        tiny_b=(UI_FONT, 8, "bold"),
        label=(UI_FONT, 9, "bold"),
        tab=(UI_FONT, 11, "bold"),
        btn=(UI_FONT, 10, "bold"),
        num=(UI_FONT, 28, "bold"),
        kpi=(UI_FONT, 24, "bold"),
        mono=(MONO_FONT, 10),
        mono_s=(MONO_FONT, 9),
    )


# --------------------------------------------------------------------------------------
# Small helpers: colours, easing, animation, rounded shapes
# --------------------------------------------------------------------------------------
def hex2rgb(h):
    h = h.lstrip("#")
    if len(h) == 3:
        h = "".join(ch * 2 for ch in h)
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


def rgb2hex(rgb):
    return "#%02x%02x%02x" % tuple(max(0, min(255, int(round(v)))) for v in rgb)


def mix(a, b, t):
    """Blend colour a towards colour b (t = 0..1)."""
    t = max(0.0, min(1.0, t))
    ra, rb = hex2rgb(a), hex2rgb(b)
    return rgb2hex([ra[i] + (rb[i] - ra[i]) * t for i in range(3)])


def gradient(stops, t):
    """stops = [(0.0, '#hex'), ..., (1.0, '#hex')]"""
    t = max(0.0, min(1.0, t))
    for (p0, c0), (p1, c1) in zip(stops, stops[1:]):
        if t <= p1:
            return mix(c0, c1, 0 if p1 == p0 else (t - p0) / (p1 - p0))
    return stops[-1][1]


def ease_out_cubic(t):
    return 1 - (1 - t) ** 3


def ease_in_out(t):
    return t * t * (3 - 2 * t)


def ease_out_back(t):
    c1 = 1.70158
    return 1 + (c1 + 1) * (t - 1) ** 3 + c1 * (t - 1) ** 2


def linear(t):
    return t


class Anim:
    """Runs step(progress) for `duration` seconds using Tk's after() loop."""

    def __init__(self, widget, duration, step, done=None, ease=ease_out_cubic, delay=0.0):
        self.w, self.d, self.step, self.done, self.ease = widget, max(0.001, duration), step, done, ease
        self.cancelled = False
        self.job = widget.after(int(delay * 1000), self._start)

    def _start(self):
        self.t0 = time.perf_counter()
        self._tick()

    def _tick(self):
        if self.cancelled:
            return
        t = min(1.0, (time.perf_counter() - self.t0) / self.d)
        try:
            self.step(self.ease(t))
        except tk.TclError:
            return
        if t < 1:
            self.job = self.w.after(15, self._tick)
        elif self.done:
            try:
                self.done()
            except tk.TclError:
                pass

    def cancel(self):
        self.cancelled = True
        try:
            self.w.after_cancel(self.job)
        except (tk.TclError, ValueError):
            pass


def round_rect(c, x0, y0, x1, y1, r=10, **kw):
    r = max(0, min(r, (x1 - x0) / 2, (y1 - y0) / 2))
    pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1,
           x1 - r, y1, x0 + r, y1, x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]
    kw.setdefault("fill", PANEL)
    return c.create_polygon(pts, smooth=True, **kw)


def draw_logo(c, cx, cy, s=1.0, tag="logo"):
    """Exp 7 - the app logo drawn only with Canvas primitives."""
    tags = (tag,)
    c.create_oval(cx - 50 * s, cy - 50 * s, cx + 50 * s, cy + 50 * s, fill="#0e2536", outline=ACCENT, width=max(1, 2 * s), tags=tags)
    c.create_oval(cx - 42 * s, cy - 42 * s, cx + 42 * s, cy + 42 * s, fill="", outline=mix(ACCENT, BG, 0.65), width=1, tags=tags)
    drop = [cx, cy - 34 * s, cx + 7 * s, cy - 22 * s, cx + 21 * s, cy - 2 * s, cx + 21 * s, cy + 9 * s,
            cx + 13 * s, cy + 21 * s, cx, cy + 24 * s, cx - 13 * s, cy + 21 * s, cx - 21 * s, cy + 9 * s,
            cx - 21 * s, cy - 2 * s, cx - 7 * s, cy - 22 * s]
    c.create_polygon(drop, smooth=True, fill="#fcd34d", outline="#f59e0b", width=max(1, 1.5 * s), tags=tags)
    c.create_oval(cx - 13 * s, cy - 8 * s, cx - 7 * s, cy + 2 * s, fill="#fff7d6", outline="", tags=tags)
    c.create_line(cx, cy - 1 * s, cx, cy + 15 * s, fill="#b45309", width=max(1, 3 * s), capstyle="round", tags=tags)
    c.create_line(cx - 8 * s, cy + 7 * s, cx + 8 * s, cy + 7 * s, fill="#b45309", width=max(1, 3 * s), capstyle="round", tags=tags)
    # the little test strip under the drop
    c.create_rectangle(cx - 30 * s, cy + 29 * s, cx + 30 * s, cy + 38 * s, fill=STRIP, outline="", tags=tags)
    pad_colors = ["#86c27a", "#e9c046", "#e1a3a3", "#9a72a8"]
    for k, col in enumerate(pad_colors):
        x = cx - 22 * s + k * 13 * s
        c.create_rectangle(x, cy + 30.5 * s, x + 8 * s, cy + 36.5 * s, fill=col, outline="", tags=(tag, f"{tag}pad{k}"))


# ======================================================================================
#                                   DOMAIN MODEL
# ======================================================================================

class InvalidSampleError(Exception):
    """Exp 5 - raised when a patient record or a strip reading cannot be processed."""


# Exp 6 - lambda used for colour-intensity classification
classify_level = lambda value, normal_max, moderate_max: (
    "Normal" if value <= normal_max else ("Moderate" if value <= moderate_max else "High"))


class StripPad(ABC):
    """Exp 4 - abstract base class for one reagent pad on the strip."""

    def __init__(self, key, name, unit, lo, hi, step, default, stops, note):
        self.key, self.name, self.unit = key, name, unit
        self.lo, self.hi, self.step, self.default = lo, hi, step, default
        self.stops, self.note = stops, note

    @abstractmethod
    def classify(self, value):
        """Return 'Normal', 'Moderate' or 'High'."""

    @abstractmethod
    def band(self, level, rng):
        """Return a random value that falls inside the given level (used for simulation)."""

    @abstractmethod
    def normal_range(self):
        pass

    # shared behaviour -----------------------------------------------------------
    def norm(self, value):
        return max(0.0, min(1.0, (value - self.lo) / (self.hi - self.lo)))

    def color_for(self, value):
        """Colorimetry: the pad colour that this concentration would produce."""
        return gradient(self.stops, self.norm(value))

    def snap(self, value):
        v = round(round((float(value) - self.lo) / self.step) * self.step + self.lo, 2)
        return max(self.lo, min(self.hi, v))

    def fmt(self, value):
        return f"{value:.1f}" if self.step < 1 else f"{value:.0f}"

    def validate(self, value):
        if value is None or (isinstance(value, str) and not value.strip()):
            raise InvalidSampleError(f"{self.name} reading is missing")
        try:
            v = float(value)
        except (TypeError, ValueError):
            raise InvalidSampleError(f"{self.name}: '{value}' is not a number")
        if not self.lo <= v <= self.hi:
            raise InvalidSampleError(f"{self.name} must be between {self.lo:g} and {self.hi:g} {self.unit}".strip())
        return v


class ThresholdPad(StripPad):
    """Pads where 'more colour = more analyte' (glucose, protein, ketones, blood, leukocytes)."""

    def __init__(self, key, name, unit, lo, hi, step, default, stops, note, normal_max, moderate_max):
        super().__init__(key, name, unit, lo, hi, step, default, stops, note)
        self.normal_max, self.moderate_max = normal_max, moderate_max

    def classify(self, value):  # polymorphism: overrides StripPad.classify
        return classify_level(value, self.normal_max, self.moderate_max)

    def band(self, level, rng):
        ranges = {"Normal": (self.lo, self.normal_max),
                  "Moderate": (self.normal_max + self.step, self.moderate_max),
                  "High": (self.moderate_max + self.step, self.hi)}
        a, b = ranges[level]
        return self.snap(rng.uniform(a, b))

    def normal_range(self):
        return f"≤ {self.normal_max:g} {self.unit}"


class PHPad(StripPad):
    """pH is abnormal on BOTH sides, so it classifies differently (polymorphism)."""

    def classify(self, value):
        distance = 0 if 5.0 <= value <= 8.0 else min(abs(value - 5.0), abs(value - 8.0))
        return classify_level(distance, 0, 0.5)

    def band(self, level, rng):
        if level == "Normal":
            return self.snap(rng.uniform(5.2, 7.6))
        if level == "Moderate":
            return self.snap(rng.choice([rng.uniform(4.6, 4.9), rng.uniform(8.1, 8.5)]))
        return self.snap(rng.uniform(8.6, 9.0))

    def normal_range(self):
        return "5.0 – 8.0"


# Exp 2 - list of pad objects (order = order on the physical strip)
PADS = [
    ThresholdPad("glucose", "Glucose", "mg/dL", 0, 500, 5, 80,
                 [(0, "#6fc3c1"), (0.2, "#86c27a"), (0.5, "#9b9440"), (0.8, "#8a5a2b"), (1, "#5a3519")],
                 "High glucose may point to diabetes or a kidney threshold problem.", 100, 250),
    ThresholdPad("protein", "Protein", "mg/dL", 0, 300, 5, 10,
                 [(0, "#e9e27a"), (0.3, "#b9d36e"), (0.65, "#6fae86"), (1, "#2f7f86")],
                 "Persistent protein can be an early sign of kidney stress.", 20, 100),
    PHPad("ph", "pH", "", 4.5, 9.0, 0.1, 6.5,
          [(0, "#ee7d3b"), (0.3, "#e9c046"), (0.55, "#97c25a"), (0.8, "#3f9a8a"), (1, "#2b5fa3")],
          "Very acidic or alkaline urine can relate to diet, stones or infection."),
    ThresholdPad("ketones", "Ketones", "mg/dL", 0, 160, 1, 0,
                 [(0, "#efd8bf"), (0.25, "#e1a3a3"), (0.6, "#a24a6a"), (1, "#5e1a37")],
                 "Ketones appear with fasting, heavy exercise or uncontrolled diabetes.", 15, 40),
    ThresholdPad("blood", "Blood", "Ery/µL", 0, 250, 1, 0,
                 [(0, "#f0d36a"), (0.2, "#b6c95e"), (0.6, "#4f8f4f"), (1, "#1d4a2d")],
                 "Blood may suggest infection, stones or injury in the urinary tract.", 5, 50),
    ThresholdPad("leukocytes", "Leukocytes", "Leu/µL", 0, 500, 5, 5,
                 [(0, "#f1e9d6"), (0.3, "#d7bfd3"), (0.65, "#9a72a8"), (1, "#563576")],
                 "White blood cells most often indicate a urinary tract infection.", 15, 125),
]

FIRST_NAMES = ["Rudra", "Vihaan", "Dev", "Aarav", "Ananya", "Diya", "Kavya", "Ishaan", "Kabir", "Meera",
               "Arjun", "Riya", "Priya", "Tara", "Sai", "Neha", "Rohan", "Sneha", "Aman", "Pooja"]
SURNAMES = ["Sharma", "Patil", "Iyer", "Desai", "Kulkarni", "Mehta", "Nair", "Joshi", "Rao", "Shah",
            "Gupta", "Kapoor", "Menon", "Pawar", "Reddy", "Bhat", "Naik", "Sawant"]


class Patient:
    """Exp 1 & 2 - class with a parameterised constructor and getter / setter methods."""

    total_created = 0                 # class variable
    _lock = threading.Lock()          # threads create patients too (Exp 5)

    def __init__(self, patient_id, name, age=30, gender="Other"):
        self.set_data(patient_id, name, age, gender)
        with Patient._lock:
            Patient.total_created += 1

    # setters ---------------------------------------------------------------------
    def set_data(self, patient_id, name, age, gender):
        self.set_id(patient_id)
        self.set_name(name)
        self.set_age(age)
        self.set_gender(gender)

    def set_id(self, patient_id):
        self._id = patient_id

    def set_name(self, name):
        name = " ".join(str(name or "").split()).title()      # string handling (Exp 3)
        if not name:
            raise InvalidSampleError("Patient information is missing - enter a name")
        if any(ch.isdigit() for ch in name):
            raise InvalidSampleError("Patient name should not contain numbers")
        self._name = name

    def set_age(self, age):
        try:
            age = int(str(age).strip())
        except ValueError:
            raise InvalidSampleError("Age must be a whole number")
        if not 0 <= age <= 120:
            raise InvalidSampleError("Age must be between 0 and 120")
        self._age = age

    def set_gender(self, gender):
        self._gender = gender if gender in ("Female", "Male", "Other") else "Other"

    # getters ---------------------------------------------------------------------
    def get_id(self):
        return self._id

    def get_name(self):
        return self._name

    def get_age(self):
        return self._age

    def get_gender(self):
        return self._gender

    def info(self):
        """Exp 6 - identification stored as an immutable tuple."""
        return (self._id, self._name, self._age, self._gender)

    @staticmethod
    def make_code(number):
        return f"PAT-{number:04d}" if number else "NEW"

    @classmethod
    def random(cls, rng=random):
        return cls(None, f"{rng.choice(FIRST_NAMES)} {rng.choice(SURNAMES)}",
                   rng.randint(6, 84), rng.choice(["Female", "Male"]))


class TestResult:
    def __init__(self, patient, readings, results, abnormal_count, high_count, risk, status, categories,
                 timestamp=None, test_id=None):
        self.patient = patient
        self.readings = readings                # dict  {key: value}
        self.results = results                  # list  [(name, value, level), ...]
        self.abnormal_count = abnormal_count
        self.high_count = high_count
        self.risk = risk
        self.status = status
        self.categories = categories            # set   {'Normal', 'High', ...}
        self.timestamp = timestamp or datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self.test_id = test_id


class DiagnosticDevice:
    """Exp 3 - parent class."""

    def __init__(self, device_id, domain, computing_unit):
        self.device_id = device_id.strip().upper()
        self.domain = domain.strip().title()
        self.computing_unit = computing_unit.strip()

    def device_info(self):
        return f"{self.device_id}  ·  {self.domain}  ·  {self.computing_unit}"


class UrineTestStripReader(DiagnosticDevice):
    """Exp 3 - child class that inherits device details and adds the AI analysis."""

    ALIASES = {"glu": "glucose", "sugar": "glucose", "pro": "protein", "prot": "protein",
               "ket": "ketones", "ketone": "ketones", "bld": "blood", "ery": "blood", "rbc": "blood",
               "leu": "leukocytes", "leuko": "leukocytes", "leukocyte": "leukocytes", "wbc": "leukocytes",
               "ph": "ph", "p.h": "ph"}
    SEVERITY = {"Normal": 0, "Moderate": 1, "High": 2}
    RISK_BANDS = {"NORMAL": (0, 28), "FURTHER EVALUATION ADVISED": (30, 59), "HIGH RISK": (60, 100)}

    def __init__(self, device_id, domain, computing_unit, pads):
        super().__init__(device_id, domain, computing_unit)
        self.pads = pads
        self.pad_by_key = {p.key: p for p in pads}
        self.pad_by_name = {p.name: p for p in pads}

    # ---- string handling: "glucose: 180 mg/dL ; protein: 30 ; pH 6.5" -> dict ----
    def parse_raw(self, raw):
        readings = {}
        text = raw.replace("\n", ";").replace(",", ";")
        for chunk in text.split(";"):
            chunk = chunk.strip()
            if not chunk:
                continue
            if ":" in chunk or "=" in chunk:
                name, value = chunk.replace("=", ":").split(":", 1)
            else:
                parts = chunk.split()
                if len(parts) < 2:
                    raise InvalidSampleError(f"Can't read '{chunk}'. Use  name: value")
                name, value = parts[0], " ".join(parts[1:])
            key = name.strip().lower().replace(" ", "")
            key = self.ALIASES.get(key, key)
            if key not in self.pad_by_key:
                raise InvalidSampleError(f"Unknown parameter '{name.strip()}'")
            value = value.strip().lower()
            for unit in ("mg/dl", "ery/µl", "leu/µl", "ery/ul", "leu/ul", "/µl", "/ul"):
                value = value.replace(unit, "")
            value = value.strip()
            if value in ("negative", "neg", "nil", "none"):
                value = self.pad_by_key[key].lo
            readings[key] = self.pad_by_key[key].snap(self.pad_by_key[key].validate(value))
        if not readings:
            raise InvalidSampleError("Nothing to read - try  glucose: 180; protein: 40; pH: 6.5")
        return readings

    # ---- the "AI" analysis: collections + functional programming (Exp 6) -------------
    def analyse(self, patient, readings):
        if patient is None:
            raise InvalidSampleError("Patient information is missing")
        missing = [p.name for p in self.pads if p.key not in readings]
        if missing:
            raise InvalidSampleError("Missing reading(s): " + ", ".join(missing))
        values = {p.key: p.validate(readings[p.key]) for p in self.pads}

        results = list(map(lambda p: (p.name, values[p.key], p.classify(values[p.key])), self.pads))
        abnormal = list(filter(lambda r: r[2] != "Normal", results))
        abnormal_count = reduce(lambda count, _r: count + 1, abnormal, 0)
        high_count = len(list(filter(lambda r: r[2] == "High", results)))
        points = reduce(lambda total, r: total + self.SEVERITY[r[2]], results, 0)
        categories = set(map(lambda r: r[2], results))

        if abnormal_count == 0:
            status = "NORMAL"
        elif abnormal_count >= 3 or high_count >= 2:
            status = "HIGH RISK"
        else:
            status = "FURTHER EVALUATION ADVISED"

        # 0-100 risk index: each status owns a band; severity + colour spread place it inside the band
        spread = reduce(lambda total, p: total + p.norm(values[p.key]), self.pads, 0) / len(self.pads)
        within = min(1.0, 0.9 * points / (2 * len(results)) + 1.4 * spread)
        lo, hi = self.RISK_BANDS[status]
        risk = round(lo + (hi - lo) * within, 1)
        return TestResult(patient, values, results, abnormal_count, high_count, risk, status, categories)

    def random_readings(self, rng=random):
        profile = rng.choices(["healthy", "mild", "severe"], weights=[55, 30, 15])[0]
        weights = {"healthy": [92, 7, 1], "mild": [60, 32, 8], "severe": [30, 35, 35]}[profile]
        return {p.key: p.band(rng.choices(["Normal", "Moderate", "High"], weights=weights)[0], rng) for p in self.pads}

    # ---- formatted report (Exp 3 string handling) ------------------------------------
    def build_report(self, r):
        pid, name, age, gender = r.patient.info()
        width = 50
        bar = "=" * width
        lines = [bar, "URINE TEST STRIP REPORT".center(width), bar,
                 f"Device      : {self.device_id} ({self.computing_unit})",
                 f"Test ID     : {('#' + str(r.test_id)) if r.test_id else 'not saved'}",
                 f"Patient ID  : {Patient.make_code(pid)}",
                 f"Patient     : {name}  |  {age} y  |  {gender}",
                 f"Timestamp   : {r.timestamp}",
                 "-" * width,
                 f"{'Parameter':<12}{'Value':>8}  {'Unit':<8}{'Ref range':<12}{'Status'}",
                 "-" * width]
        for pname, value, level in r.results:
            pad = self.pad_by_name[pname]
            lines.append(f"{pname:<12}{pad.fmt(value):>8}  {pad.unit:<8}{pad.normal_range().replace(' ' + pad.unit, ''):<12}{level}")
        lines.append("-" * width)
        flagged = ", ".join(n for n, _v, lvl in r.results if lvl != "Normal") or "None"
        lines += [f"Abnormal    : {r.abnormal_count} of {len(r.results)}  ({flagged})",
                  f"Risk index  : {r.risk:.1f} / 100",
                  f"Categories  : {', '.join(sorted(r.categories, key=self.SEVERITY.get))}",
                  f"OVERALL     : {r.status}",
                  "",
                  f"AI advisory : {STATUS_ADVICE[r.status]}",
                  "Note        : Screening aid only - not a medical diagnosis.",
                  bar]
        return "\n".join(lines)


# ======================================================================================
#                                    DATABASE  (Exp 8)
# ======================================================================================

class LabDatabase:
    COLS = [p.key for p in PADS]

    def __init__(self, path):
        self.path = path
        self.conn = sqlite3.connect(path)
        self.conn.execute("PRAGMA foreign_keys = ON")
        self.cur = self.conn.cursor()
        self.cur.execute("""
            CREATE TABLE IF NOT EXISTS patients (
                id      INTEGER PRIMARY KEY AUTOINCREMENT,
                name    TEXT NOT NULL,
                age     INTEGER,
                gender  TEXT
            )""")
        self.cur.execute("""
            CREATE TABLE IF NOT EXISTS tests (
                test_id        INTEGER PRIMARY KEY AUTOINCREMENT,
                patient_id     INTEGER NOT NULL REFERENCES patients(id) ON DELETE CASCADE,
                taken_at       TEXT,
                glucose REAL, protein REAL, ph REAL, ketones REAL, blood REAL, leukocytes REAL,
                abnormal_count INTEGER,
                risk           REAL,
                status         TEXT,
                source         TEXT
            )""")
        self.conn.commit()

    def get_or_create_patient(self, patient):
        _id, name, age, gender = patient.info()
        row = self.cur.execute("SELECT id FROM patients WHERE name = ? AND age = ? AND gender = ?",
                               (name, age, gender)).fetchone()
        if row:
            pid = row[0]
        else:
            self.cur.execute("INSERT INTO patients (name, age, gender) VALUES (?, ?, ?)", (name, age, gender))
            pid = self.cur.lastrowid
        patient.set_id(pid)
        return pid

    def save(self, r, source="Manual", commit=True):
        pid = self.get_or_create_patient(r.patient)
        self.cur.execute(
            f"INSERT INTO tests (patient_id, taken_at, {', '.join(self.COLS)}, abnormal_count, risk, status, source) "
            f"VALUES (?, ?, {', '.join('?' * len(self.COLS))}, ?, ?, ?, ?)",
            (pid, r.timestamp, *[r.readings[k] for k in self.COLS], r.abnormal_count, r.risk, r.status, source))
        r.test_id = self.cur.lastrowid
        if commit:
            self.conn.commit()
        return r.test_id

    def commit(self):
        self.conn.commit()

    SELECT = ("SELECT t.test_id, p.id, p.name, p.age, p.gender, t.taken_at, "
              "t.glucose, t.protein, t.ph, t.ketones, t.blood, t.leukocytes, "
              "t.abnormal_count, t.risk, t.status, t.source "
              "FROM tests t JOIN patients p ON p.id = t.patient_id")
    ORDERS = {"Newest first": "t.test_id DESC", "Oldest first": "t.test_id ASC",
              "Highest risk": "t.risk DESC, t.test_id DESC", "Name A–Z": "p.name ASC, t.test_id DESC"}

    def search(self, name_like="", status="All", order="Newest first"):
        sql = self.SELECT + " WHERE p.name LIKE ?"
        params = [f"%{name_like.strip()}%"]
        if status != "All":
            sql += " AND t.status = ?"
            params.append(status)
        sql += " ORDER BY " + self.ORDERS.get(order, "t.test_id DESC")
        return self.cur.execute(sql, params).fetchall()

    def get(self, test_id):
        return self.cur.execute(self.SELECT + " WHERE t.test_id = ?", (test_id,)).fetchone()

    def delete(self, test_ids):
        self.cur.executemany("DELETE FROM tests WHERE test_id = ?", [(i,) for i in test_ids])
        self.cur.execute("DELETE FROM patients WHERE id NOT IN (SELECT DISTINCT patient_id FROM tests)")
        self.conn.commit()

    def clear(self):
        self.cur.execute("DELETE FROM tests")
        self.cur.execute("DELETE FROM patients")
        self.conn.commit()

    def stats(self):
        row = self.cur.execute(
            "SELECT COUNT(*), AVG(risk), AVG(glucose), AVG(protein), AVG(ph), AVG(ketones), AVG(blood), "
            "AVG(leukocytes), SUM(CASE WHEN status != 'NORMAL' THEN 1 ELSE 0 END) FROM tests").fetchone()
        total = row[0] or 0
        return {
            "total": total,
            "avg_risk": row[1] or 0,
            "avg": dict(zip(self.COLS, row[2:8])),
            "abnormal_rate": (100.0 * (row[8] or 0) / total) if total else 0,
            "patients": self.cur.execute("SELECT COUNT(*) FROM patients").fetchone()[0],
            "by_status": dict(self.cur.execute("SELECT status, COUNT(*) FROM tests GROUP BY status").fetchall()),
            "top": self.cur.execute("SELECT p.name, t.risk, t.status, t.test_id FROM tests t JOIN patients p "
                                    "ON p.id = t.patient_id ORDER BY t.risk DESC LIMIT 5").fetchall(),
        }

    def close(self):
        try:
            self.conn.close()
        except sqlite3.Error:
            pass


def row_to_result(reader, row):
    """Rebuild a TestResult object from a database row."""
    test_id, pid, name, age, gender, taken_at = row[:6]
    readings = dict(zip(LabDatabase.COLS, row[6:12]))
    patient = Patient(pid, name, age, gender)
    result = reader.analyse(patient, readings)
    result.timestamp, result.test_id = taken_at, test_id
    return result


# ======================================================================================
#                               MULTITHREADED BATCH (Exp 5)
# ======================================================================================

class BatchProcessor:
    """Each sample is processed on its own thread; results go back to the GUI through a queue."""

    FAULTS = ["missing_name", "bad_value", "missing_reading", "blurred_image"]

    def __init__(self, reader, out_queue):
        self.reader, self.q = reader, out_queue
        self.threads = []

    def start(self, count, inject_faults):
        self.threads = []
        for idx in range(count):
            t = threading.Thread(target=self._worker, args=(idx, inject_faults), daemon=True)
            self.threads.append(t)
            t.start()

    @staticmethod
    def capture_image(rng, fault):
        time.sleep(rng.uniform(0.05, 1.8))          # simulates the camera + colour sampling
        if fault == "blurred_image":
            raise InvalidSampleError("Strip image is blurred - colour pads unreadable")

    def _worker(self, idx, inject_faults):
        rng = random.Random()
        fault = rng.choice(self.FAULTS) if inject_faults and rng.random() < 0.09 else None
        try:
            self.capture_image(rng, fault)
            patient = Patient(None, "  ", 30) if fault == "missing_name" else Patient.random(rng)
            readings = self.reader.random_readings(rng)
            if fault == "bad_value":
                readings["ph"] = round(rng.uniform(11, 14), 1)
            elif fault == "missing_reading":
                readings.pop(rng.choice(list(readings)))
            result = self.reader.analyse(patient, readings)
            self.q.put(("ok", idx, result))
        except InvalidSampleError as e:
            self.q.put(("error", idx, str(e)))
        except Exception as e:  # anything unexpected must not kill the batch
            self.q.put(("error", idx, f"Unexpected error: {e}"))


# ======================================================================================
#                                  REUSABLE WIDGETS
# ======================================================================================

class GlowButton(tk.Canvas):
    """A canvas-drawn button with an animated hover glow and a press effect."""

    def __init__(self, parent, text, command, width=150, height=38, color=ACCENT, fg="#04222b",
                 font=None, radius=10, bg=None):
        super().__init__(parent, width=width, height=height, bg=bg or parent["bg"], highlightthickness=0,
                         bd=0, cursor="hand2")
        self.text, self.command, self.color, self.fg = text, command, color, fg
        self.font, self.radius = font or F["btn"], radius
        self.enabled, self._h, self._press, self._anim = True, 0.0, 0, None
        self.bind("<Enter>", lambda e: self._hover_to(1))
        self.bind("<Leave>", lambda e: self._hover_to(0))
        self.bind("<ButtonPress-1>", self._down)
        self.bind("<ButtonRelease-1>", self._up)
        self.bind("<Configure>", lambda e: self._draw())

    def _draw(self):
        self.delete("all")
        w = self.winfo_width() if self.winfo_width() > 1 else int(self["width"])
        h = self.winfo_height() if self.winfo_height() > 1 else int(self["height"])
        p = self._press
        if self.enabled:
            fill = mix(self.color, "#ffffff", 0.2 * self._h)
            if self._h > 0.01:
                round_rect(self, 0.5, 0.5, w - 0.5, h - 0.5, self.radius + 2, fill="",
                           outline=mix(self["bg"], self.color, 0.9 * self._h), width=2)
            fg = self.fg
        else:
            fill, fg = mix(self.color, self["bg"], 0.7), mix(self.fg, self["bg"], 0.2)
        round_rect(self, 3 + p, 3 + p, w - 3 - p, h - 3 - p, self.radius, fill=fill, outline="")
        self.create_text(w / 2, h / 2, text=self.text, fill=fg, font=self.font)

    def _hover_to(self, target):
        if self._anim:
            self._anim.cancel()
        start = self._h

        def step(t):
            self._h = start + (target - start) * t
            self._draw()
        self._anim = Anim(self, 0.18, step)

    def _down(self, _e):
        if self.enabled:
            self._press = 2
            self._draw()

    def _up(self, e):
        self._press = 0
        self._draw()
        inside = 0 <= e.x <= self.winfo_width() and 0 <= e.y <= self.winfo_height()
        if self.enabled and inside and self.command:
            self.command()

    def set_enabled(self, on, text=None):
        self.enabled = on
        if text:
            self.text = text
        self.config(cursor="hand2" if on else "arrow")
        self._draw()

    def set_text(self, text):
        self.text = text
        self._draw()


class PlaceholderEntry(tk.Entry):
    def __init__(self, parent, placeholder, textvariable=None, **kw):
        self.var = textvariable or tk.StringVar()
        style = dict(bg=PANEL2, fg=TEXT, insertbackground=TEXT, relief="flat", font=F["body"],
                     highlightthickness=1, highlightbackground=LINE, highlightcolor=ACCENT)
        style.update(kw)
        super().__init__(parent, textvariable=self.var, **style)
        self.placeholder, self._showing = placeholder, False
        self.bind("<FocusIn>", self._clear)
        self.bind("<FocusOut>", self._restore)
        self._restore()

    def _clear(self, _e=None):
        if self._showing:
            self._showing = False
            self.var.set("")
            self.config(fg=TEXT)

    def _restore(self, _e=None):
        if not self.var.get():
            self._showing = True
            self.var.set(self.placeholder)
            self.config(fg=mix(MUTED, PANEL2, 0.25))

    def value(self):
        return "" if self._showing else self.var.get()

    def set_value(self, text):
        self._showing = False
        self.config(fg=TEXT)
        self.var.set(text)
        if not text:
            self._restore()


def flash_border(widget, color=RED, times=3):
    """Blink a widget's border - used to point at the field that raised an exception."""
    def blink(n):
        try:
            widget.config(highlightbackground=color if n % 2 == 0 else LINE,
                          highlightcolor=color if n % 2 == 0 else ACCENT)
        except tk.TclError:
            return
        if n < times * 2 - 1:
            widget.after(140, blink, n + 1)
    blink(0)


def card(parent, **kw):
    return tk.Frame(parent, bg=PANEL, highlightthickness=1, highlightbackground=LINE, **kw)


def section(parent, text, bg=PANEL):
    return tk.Label(parent, text=text.upper(), font=F["label"], fg=MUTED, bg=bg, anchor="w")


class Gauge(tk.Canvas):
    """Animated circular risk gauge."""

    def __init__(self, parent, size=180, bg=PANEL, label="RISK INDEX"):
        super().__init__(parent, width=size, height=size, bg=bg, highlightthickness=0, bd=0)
        self.size, self.value, self.label, self._anim, self.bgc = size, 0.0, label, None, bg
        self._draw(0)

    @staticmethod
    def color_for(v):
        return gradient([(0, GREEN), (0.24, GREEN), (0.4, AMBER), (0.56, "#fb923c"), (0.7, RED), (1, RED)], v / 100)

    def _draw(self, v):
        self.delete("all")
        s = self.size
        pad = 16
        cx = cy = s / 2
        r = (s - 2 * pad) / 2
        col = self.color_for(v)
        # tick marks
        for k in range(31):
            frac = k / 30
            ang = math.radians(225 - 270 * frac)
            r1, r2 = r - 15, r - (21 if k % 5 == 0 else 18)
            on = frac <= v / 100 + 1e-9 and v > 0
            self.create_line(cx + r1 * math.cos(ang), cy - r1 * math.sin(ang),
                             cx + r2 * math.cos(ang), cy - r2 * math.sin(ang),
                             fill=self.color_for(frac * 100) if on else LINE, width=2)
        box = (pad, pad, s - pad, s - pad)
        self.create_arc(box, start=225, extent=-270, style="arc", outline=LINE, width=11)
        if v > 0.3:
            # glow + main arc
            self.create_arc(box, start=225, extent=-270 * v / 100, style="arc", outline=mix(col, self.bgc, 0.6), width=17)
            self.create_arc(box, start=225, extent=-270 * v / 100, style="arc", outline=col, width=11)
        ang = math.radians(225 - 270 * v / 100)
        x, y = cx + r * math.cos(ang), cy - r * math.sin(ang)
        self.create_oval(x - 8, y - 8, x + 8, y + 8, fill=col, outline=mix(col, "#ffffff", 0.6), width=2)
        self.create_text(cx, cy - 6, text=f"{v:.0f}", font=F["num"], fill=TEXT)
        self.create_text(cx, cy + 24, text=self.label, font=F["tiny_b"], fill=MUTED)
        self.create_text(cx, cy + 39, text="out of 100", font=F["tiny"], fill=mix(MUTED, self.bgc, 0.35))

    def set_value(self, target, duration=1.2):
        if self._anim:
            self._anim.cancel()
        start = self.value

        def step(t):
            self.value = start + (target - start) * t
            self._draw(self.value)
        self._anim = Anim(self, duration, step)


class StatusBadge(tk.Canvas):
    """Rounded status pill with a pulsing halo."""

    def __init__(self, parent, bg=PANEL, height=56):
        super().__init__(parent, height=height, bg=bg, highlightthickness=0, bd=0)
        self.bgc = bg
        self.status, self.sub, self.color = "AWAITING SCAN", "Set the readings, then press Scan Strip", "#64748b"
        self.pulse, self._loop = 0.0, None
        self.bind("<Configure>", lambda e: self._draw())

    def _draw(self):
        self.delete("all")
        w, h = max(self.winfo_width(), 200), int(self["height"])
        m = 8
        if self.pulse > 0:
            d = 7 * self.pulse
            round_rect(self, m - d, m - d, w - m + d, h - m + d, 16 + d, fill="",
                       outline=mix(self.color, self.bgc, 0.35 + 0.65 * self.pulse), width=2)
        round_rect(self, m, m, w - m, h - m, 16, fill=mix(self.color, self.bgc, 0.84), outline=self.color, width=2)
        self.create_oval(m + 16, h / 2 - 6, m + 28, h / 2 + 6, fill=self.color, outline="")
        self.create_text(m + 40, h / 2 - 8, text=self.status, anchor="w", font=F["h3"], fill=self.color)
        self.create_text(m + 40, h / 2 + 10, text=self.sub, anchor="w", font=F["small"], fill=MUTED)

    def set(self, status, sub, color, pulse=True):
        self.status, self.sub, self.color = status, sub, color
        if self._loop:
            self._loop.cancel()
            self._loop = None
        self.pulse = 0
        self._draw()
        if pulse:
            self._pulse_once()

    def _pulse_once(self):
        def step(t):
            self.pulse = t
            self._draw()

        def again():
            self.pulse = 0
            self._draw()
            self._loop = Anim(self, 1.4, step, again, ease=ease_out_cubic, delay=0.5)
        self._loop = Anim(self, 1.4, step, again, ease=ease_out_cubic)


class StripView(tk.Canvas):
    """Exp 7 - the urine test strip, its reference colour charts and the scan animation."""

    ABBR = {"glucose": "GLU", "protein": "PRO", "ph": "pH", "ketones": "KET", "blood": "BLD", "leukocytes": "LEU"}

    def __init__(self, parent, pads, interactive=True, on_pad_click=None, bg=PANEL, height=222):
        super().__init__(parent, bg=bg, height=height, highlightthickness=0, bd=0)
        self.bgc, self.pads = bg, pads
        self.values = {p.key: p.default for p in pads}
        self.read = [False] * len(pads)
        self.interactive, self.on_pad_click = interactive, on_pad_click
        self.geo, self.hover, self.pop_i, self.scanning = [], None, None, False
        self._anims = {}
        self.bind("<Configure>", lambda e: self.redraw())
        if interactive:
            self.bind("<Motion>", self._motion)
            self.bind("<Leave>", lambda e: self._set_hover(None))
            self.bind("<Button-1>", self._click)

    # ---- layout & drawing -------------------------------------------------------
    def _layout(self):
        w = max(self.winfo_width(), 520)
        n = len(self.pads)
        left, right, y0, y1 = 14, w - 14, 18, 92
        handle = 84
        ax0, ax1 = left + handle + 8, right - 8
        slot = (ax1 - ax0) / n
        s = min(48, slot * 0.6)
        self.box, self.handle = (left, y0, right, y1), handle
        self.geo = [dict(cx=ax0 + slot * (i + 0.5), cy=(y0 + y1) / 2 - 3, s=s, slot=slot) for i in range(n)]

    def redraw(self):
        if self.scanning:
            return
        self.delete("all")
        self._layout()
        left, y0, right, y1 = self.box
        round_rect(self, left + 3, y0 + 5, right + 3, y1 + 5, 12, fill=mix(self.bgc, "#000000", 0.5), outline="")
        round_rect(self, left, y0, right, y1, 12, fill=STRIP, outline="#c7d1de")
        round_rect(self, left, y0, left + self.handle, y1, 12, fill=STRIP_HANDLE, outline="")
        self.create_rectangle(left + self.handle - 14, y0 + 1, left + self.handle, y1 - 1, fill=STRIP_HANDLE, outline="")
        for k in range(4):
            x = left + 14 + k * 7
            self.create_line(x, y0 + 18, x, y1 - 18, fill="#a9b5c6", width=2)
        self.create_text(left + 58, (y0 + y1) / 2, text="URO\nSCAN", font=F["tiny_b"], fill="#7b8aa0", justify="center")
        for i in range(len(self.pads)):
            self._draw_pad_group(i)
        if self.pop_i is not None:
            self._draw_popover(self.pop_i)

    def _val_text(self, p, v):
        return f"{p.fmt(v)} {p.unit}".strip()

    def _draw_pad_group(self, i):
        g, p = self.geo[i], self.pads[i]
        v = self.values[p.key]
        cx, cy, s = g["cx"], g["cy"], g["s"]
        col = p.color_for(v)
        self.create_rectangle(cx - s / 2, cy - s / 2, cx + s / 2, cy + s / 2, fill=col,
                              outline=mix(col, "#000000", 0.28), width=1, tags=("pad", f"pad{i}"))
        self.create_text(cx, self.box[3] - 7, text=self.ABBR.get(p.key, p.key[:3].upper()), font=F["tiny"], fill="#8593a8")
        self.create_line(cx, self.box[3] + 6, cx, 106, fill=LINE, dash=(2, 3))
        cw = min(g["slot"] * 0.84, 132)
        cx0, ch_y, k = cx - cw / 2, 108, 6
        for j in range(k):
            self.create_rectangle(cx0 + cw * j / k, ch_y, cx0 + cw * (j + 1) / k, ch_y + 12,
                                  fill=gradient(p.stops, (j + 0.5) / k), outline=self.bgc, width=1)
        g.update(cx0=cx0, cw=cw)
        mx = cx0 + cw * p.norm(v)
        self.create_polygon(mx, ch_y + 14, mx - 5, ch_y + 22, mx + 5, ch_y + 22, fill=TEXT, outline="", tags=(f"mark{i}",))
        self.create_text(cx, 144, text=p.name, font=F["label"], fill=TEXT, tags=(f"name{i}",))
        self.create_text(cx, 162, text=self._val_text(p, v), font=F["mono_s"], fill=MUTED, tags=(f"val{i}",))
        self._draw_chip(i)

    def _draw_chip(self, i, scale=1.0):
        self.delete(f"chip{i}")
        if not self.geo or scale < 0.05:
            return
        g, p = self.geo[i], self.pads[i]
        cx, cy = g["cx"], 190
        if self.read[i]:
            level = p.classify(self.values[p.key])
            col = LEVEL_COLORS[level]
            text, fill, outline, fg = level.upper(), mix(col, self.bgc, 0.8), col, col
        else:
            text, fill, outline, fg = "—", mix(LINE, self.bgc, 0.5), LINE, MUTED
        w, h = min(82, g["slot"] * 0.8) * scale, 22 * scale
        round_rect(self, cx - w / 2, cy - h / 2, cx + w / 2, cy + h / 2, h / 2, fill=fill, outline=outline,
                   width=1, tags=(f"chip{i}",))
        self.create_text(cx, cy, text=text, fill=fg, font=(UI_FONT, max(1, int(round(8 * scale))), "bold"), tags=(f"chip{i}",))

    # ---- live updates -----------------------------------------------------------
    def set_values(self, values, animate=False, mark_read=None):
        for i, p in enumerate(self.pads):
            if p.key not in values:
                continue
            nv = float(values[p.key])
            changed = abs(nv - self.values[p.key]) > 1e-9
            self.values[p.key] = nv
            if mark_read is not None:
                self.read[i] = mark_read
            elif changed:
                self.read[i] = False
            if self.geo and not self.scanning:
                self._update_pad(i, animate)

    def _update_pad(self, i, animate):
        p, g = self.pads[i], self.geo[i]
        v = self.values[p.key]
        new = p.color_for(v)
        if i in self._anims:
            self._anims.pop(i).cancel()
        if animate:
            old = self.itemcget(f"pad{i}", "fill") or new

            def step(t, old=old, new=new):
                c = mix(old, new, t)
                self.itemconfig(f"pad{i}", fill=c, outline=mix(c, "#000000", 0.28))
            self._anims[i] = Anim(self, 0.4, step)
        else:
            self.itemconfig(f"pad{i}", fill=new, outline=mix(new, "#000000", 0.28))
        mx, y = g["cx0"] + g["cw"] * p.norm(v), 108
        self.coords(f"mark{i}", mx, y + 14, mx - 5, y + 22, mx + 5, y + 22)
        self.itemconfig(f"val{i}", text=self._val_text(p, v))
        self._draw_chip(i)
        if self.pop_i == i:
            self._draw_popover(i)

    # ---- hover / click / popover ------------------------------------------------
    def _hit(self, x, y):
        for i, g in enumerate(self.geo):
            if abs(x - g["cx"]) < g["slot"] / 2 and self.box[1] - 4 <= y <= 204:
                return i
        return None

    def _motion(self, e):
        if not self.scanning:
            self._set_hover(self._hit(e.x, e.y))

    def _set_hover(self, i):
        if i == self.hover or not self.geo:
            return
        if self.hover is not None:
            g = self.geo[self.hover]
            s = g["s"]
            col = self.itemcget(f"pad{self.hover}", "fill")
            self.coords(f"pad{self.hover}", g["cx"] - s / 2, g["cy"] - s / 2, g["cx"] + s / 2, g["cy"] + s / 2)
            self.itemconfig(f"pad{self.hover}", width=1, outline=mix(col, "#000000", 0.28))
            self.itemconfig(f"name{self.hover}", fill=TEXT)
        self.hover = i
        if i is not None:
            g = self.geo[i]
            s = g["s"] + 8
            self.coords(f"pad{i}", g["cx"] - s / 2, g["cy"] - s / 2, g["cx"] + s / 2, g["cy"] + s / 2)
            self.itemconfig(f"pad{i}", width=2, outline=ACCENT)
            self.itemconfig(f"name{i}", fill=ACCENT)
            self.config(cursor="hand2")
        else:
            self.config(cursor="")

    def _click(self, e):
        if self.scanning:
            return
        i = self._hit(e.x, e.y)
        if i is None or i == self.pop_i:
            self.close_popover()
        else:
            self.pop_i = i
            self._draw_popover(i)
        if i is not None and self.on_pad_click:
            self.on_pad_click(i)

    def close_popover(self):
        self.pop_i = None
        self.delete("pop")

    def _draw_popover(self, i):
        self.delete("pop")
        g, p = self.geo[i], self.pads[i]
        v = self.values[p.key]
        level = p.classify(v)
        w, h = 250, 112
        x0 = max(self.box[0] + 2, min(g["cx"] - w / 2, self.box[2] - w - 2))
        y0 = self.box[3] + 10
        tag = ("pop",)
        self.create_polygon(g["cx"] - 8, y0 + 1, g["cx"], y0 - 8, g["cx"] + 8, y0 + 1, fill=ACCENT, outline="", tags=tag)
        round_rect(self, x0 + 3, y0 + 4, x0 + w + 3, y0 + h + 4, 12, fill=mix(self.bgc, "#000000", 0.5), outline="", tags=tag)
        round_rect(self, x0, y0, x0 + w, y0 + h, 12, fill=PANEL2, outline=ACCENT, width=1, tags=tag)
        self.create_rectangle(x0 + 14, y0 + 14, x0 + 40, y0 + 40, fill=p.color_for(v), outline=mix(p.color_for(v), "#000", 0.3), tags=tag)
        self.create_text(x0 + 50, y0 + 18, text=p.name, anchor="w", font=F["h3"], fill=TEXT, tags=tag)
        self.create_text(x0 + 50, y0 + 36, text=f"{self._val_text(p, v)}  ·  {level}", anchor="w",
                         font=F["label"], fill=LEVEL_COLORS[level], tags=tag)
        self.create_text(x0 + 14, y0 + 56, text=f"Normal range: {p.normal_range()}", anchor="w",
                         font=F["small"], fill=MUTED, tags=tag)
        self.create_text(x0 + 14, y0 + 74, text=p.note, anchor="nw", width=w - 28, font=F["tiny"], fill=TEXT, tags=tag)

    # ---- the scan animation -----------------------------------------------------
    def scan(self, on_read=None, on_done=None, duration=2.3):
        if not self.geo:
            self.redraw()
        self.close_popover()
        self._set_hover(None)
        self.read = [False] * len(self.pads)
        for i in range(len(self.pads)):
            self._draw_chip(i)
        self.scanning = True
        left, y0, right, y1 = self.box
        xs, xe = left + self.handle - 4, right - 4
        for width, a in [(18, 0.10), (11, 0.22), (6, 0.45), (3, 0.8), (1, 1.0)]:
            self.create_line(xs, y0 + 2, xs, y1 - 2, fill=mix(STRIP, ACCENT, a) if a < 1 else "#ffffff",
                             width=width, tags=("head", "headline"))
        self.create_oval(xs - 4, y0 - 9, xs + 4, y0 - 1, fill=ACCENT, outline="", tags=("head", "emit"))
        self.create_oval(xs - 4, y1 + 1, xs + 4, y1 + 9, fill=ACCENT, outline="", tags=("head", "emit"))
        label = self.create_text(right, 7, anchor="e", text="●  SCANNING  ·  sampling pad colours",
                                 font=F["tiny_b"], fill=ACCENT, tags=("head",))
        centers, fired = [g["cx"] for g in self.geo], [False] * len(self.geo)

        def step(t):
            x = xs + (xe - xs) * t
            for item in self.find_withtag("headline"):
                self.coords(item, x, y0 + 2, x, y1 - 2)
            ems = self.find_withtag("emit")
            self.coords(ems[0], x - 4, y0 - 9, x + 4, y0 - 1)
            self.coords(ems[1], x - 4, y1 + 1, x + 4, y1 + 9)
            self.itemconfig(label, fill=ACCENT if int(t * 14) % 2 == 0 else mix(ACCENT, self.bgc, 0.55))
            for i, c in enumerate(centers):
                if not fired[i] and x >= c:
                    fired[i] = True
                    self.read[i] = True
                    self._burst(i)
                    Anim(self, 0.45, lambda k, i=i: self._draw_chip(i, max(0.05, k)), ease=ease_out_back)
                    if on_read:
                        on_read(i)

        def done():
            self.delete("head")
            self.scanning = False
            if on_done:
                on_done()
        Anim(self, duration, step, done, ease=ease_in_out)

    def _burst(self, i):
        g = self.geo[i]
        cx, cy, s = g["cx"], g["cy"], g["s"]
        col = self.itemcget(f"pad{i}", "fill")
        self.itemconfig(f"pad{i}", width=3, outline="#ffffff")
        self.after(220, lambda: self.itemconfig(f"pad{i}", width=1, outline=mix(col, "#000000", 0.28)))
        ring = self.create_rectangle(cx - s / 2, cy - s / 2, cx + s / 2, cy + s / 2, outline=ACCENT, width=3)

        def step(t):
            d = 2 + 8 * t
            self.coords(ring, cx - s / 2 - d, cy - s / 2 - d, cx + s / 2 + d, cy + s / 2 + d)
            self.itemconfig(ring, outline=mix(ACCENT, STRIP, t), width=max(1, 3 - 2 * t))
        Anim(self, 0.55, step, lambda: self.delete(ring))


class Toaster:
    """Slide-in notifications in the bottom-right corner."""

    KINDS = {"ok": GREEN, "info": ACCENT, "warn": AMBER, "error": RED}

    def __init__(self, root):
        self.root, self.items = root, []

    def show(self, title, message="", kind="info", seconds=3.0):
        col = self.KINDS.get(kind, ACCENT)
        w, h = 340, 64
        c = tk.Canvas(self.root, width=w, height=h, bg=BG, highlightthickness=0, bd=0)
        round_rect(c, 1, 1, w - 1, h - 1, 12, fill=PANEL2, outline=mix(col, PANEL2, 0.3), width=1)
        round_rect(c, 1, 1, 9, h - 1, 4, fill=col, outline="")
        c.create_text(22, 20, text=title, anchor="w", font=F["h3"], fill=TEXT)
        c.create_text(22, 42, text=message, anchor="w", font=F["small"], fill=MUTED, width=w - 34)
        c.bind("<Button-1>", lambda e: self._hide(c))
        self.items.append(c)
        self._restack()
        self._slide(c, 1.0, 0.0, 0.35)
        self.root.after(int(seconds * 1000), lambda: self._hide(c))

    def _y_for(self, c):
        idx = self.items.index(c)
        return -18 - idx * 74

    def _slide(self, c, a, b, d, done=None):
        def step(t):
            off = a + (b - a) * t
            c.place(relx=1.0, rely=1.0, x=-18 + off * 380, y=self._y_for(c), anchor="se")
        Anim(c, d, step, done)

    def _restack(self):
        for c in self.items:
            try:
                c.place_configure(y=self._y_for(c))
            except tk.TclError:
                pass

    def _hide(self, c):
        if c not in self.items:
            return

        def gone():
            if c in self.items:
                self.items.remove(c)
            c.destroy()
            self._restack()
        self._slide(c, 0.0, 1.0, 0.3, gone)


# ======================================================================================
#                                   SPLASH SCREEN
# ======================================================================================

class Splash:
    MESSAGES = ["Calibrating RGB colour sensor…", "Loading reference colour charts…",
                "Warming up classification model…", "Opening patient database…", "Ready"]

    def __init__(self, root, on_done, duration=3.6):
        self.root, self.on_done, self.duration = root, on_done, duration
        self.c = tk.Canvas(root, bg=BG, highlightthickness=0)
        self.c.pack(fill="both", expand=True)
        root.update_idletasks()
        self.W = max(root.winfo_width(), 900)
        self.H = max(root.winfo_height(), 600)
        self.finished = False
        self._build()
        self.c.bind("<Button-1>", lambda e: self.finish())
        root.bind("<Escape>", lambda e: self.finish())
        self.t0 = time.perf_counter()
        self._tick()

    def _build(self):
        c, W, H = self.c, self.W, self.H
        rng = random.Random(7)
        cols = [ACCENT, ACCENT2] + [p.stops[-2][1] for p in PADS]
        self.parts = []
        for _ in range(55):
            r = rng.uniform(1.5, 4.5)
            x, y = rng.uniform(0, W), rng.uniform(0, H)
            item = c.create_oval(x - r, y - r, x + r, y + r, fill=mix(rng.choice(cols), BG, rng.uniform(0.2, 0.7)), outline="")
            self.parts.append([item, x, y, r, rng.uniform(20, 70), rng.uniform(0, 6.28)])
        self.cx, self.cy = W / 2, H / 2 - 70
        self.glow = c.create_oval(0, 0, 0, 0, outline=mix(ACCENT, BG, 0.7), width=2)
        rr = 108
        self.ring1 = c.create_arc(self.cx - rr, self.cy - rr, self.cx + rr, self.cy + rr, start=0, extent=90,
                                  style="arc", outline=ACCENT, width=4)
        rr2 = 122
        self.ring2 = c.create_arc(self.cx - rr2, self.cy - rr2, self.cx + rr2, self.cy + rr2, start=180, extent=50,
                                  style="arc", outline=ACCENT2, width=3)
        draw_logo(c, self.cx, self.cy, 1.65, "logo")
        self.title = c.create_text(W / 2, self.cy + 170, text="", font=F["splash"], fill=TEXT)
        self.sub = c.create_text(W / 2, self.cy + 214, text="Colorimetric Urine Test Strip Reader  ·  Point-of-Care AI",
                                 font=F["h3"], fill=BG)
        bw = 360
        self.bar_box = (W / 2 - bw / 2, self.cy + 256, W / 2 + bw / 2, self.cy + 264)
        round_rect(c, *self.bar_box, 4, fill=PANEL2, outline="")
        self.bar = round_rect(c, *self.bar_box, 4, fill=ACCENT, outline="")
        self.msg = c.create_text(W / 2, self.cy + 286, text="", font=F["small"], fill=MUTED)
        c.create_text(W / 2, H - 28, text=f"OOP with Python  ·  {STUDENT}  ·  Roll {ROLL_NO}  ·  Batch {BATCH}",
                      font=F["tiny"], fill=mix(MUTED, BG, 0.3))
        c.create_text(W - 20, 20, text="click to skip", anchor="ne", font=F["tiny"], fill=mix(MUTED, BG, 0.4))

    def _tick(self):
        if self.finished:
            return
        t = time.perf_counter() - self.t0
        c = self.c
        for p in self.parts:
            item, x, y, r, speed, ph = p
            y = (y - speed * 0.016) % self.H
            p[2] = y
            xx = x + math.sin(t * 1.3 + ph) * 12
            c.coords(item, xx - r, y - r, xx + r, y + r)
        c.itemconfig(self.ring1, start=(t * 240) % 360)
        c.itemconfig(self.ring2, start=(-t * 160) % 360)
        g = 96 + 10 * math.sin(t * 4)
        c.coords(self.glow, self.cx - g, self.cy - g, self.cx + g, self.cy + g)
        for k in range(4):
            pad = PADS[[0, 2, 3, 5][k]]
            c.itemconfig(f"logopad{k}", fill=pad.color_for(pad.lo + (pad.hi - pad.lo) * (0.5 + 0.5 * math.sin(t * 2 + k))))
        word = APP_NAME
        c.itemconfig(self.title, text=word[:max(0, min(len(word), int((t - 0.3) * 9)))])
        c.itemconfig(self.sub, fill=mix(BG, MUTED, min(1, max(0, (t - 1.2) / 0.8))))
        prog = min(1.0, t / (self.duration - 0.3))
        x0, y0, x1, y1 = self.bar_box
        c.coords(self.bar, *self._rr_pts(x0, y0, x0 + max(8, (x1 - x0) * ease_in_out(prog)), y1, 4))
        c.itemconfig(self.msg, text=self.MESSAGES[min(len(self.MESSAGES) - 1, int(prog * (len(self.MESSAGES) - 0.01)))])
        if t >= self.duration:
            self.finish()
        else:
            self.root.after(16, self._tick)

    @staticmethod
    def _rr_pts(x0, y0, x1, y1, r):
        r = min(r, (x1 - x0) / 2, (y1 - y0) / 2)
        return [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1,
                x1 - r, y1, x0 + r, y1, x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]

    def finish(self):
        if self.finished:
            return
        self.finished = True
        self.root.unbind("<Escape>")
        iris = self.c.create_oval(self.cx, self.cy, self.cx, self.cy, fill=BG, outline=ACCENT, width=3)
        big = math.hypot(self.W, self.H)

        def step(t):
            r = big * t
            self.c.coords(iris, self.cx - r, self.cy - r, self.cx + r, self.cy + r)
            self.c.itemconfig(iris, outline=mix(ACCENT, BG, t))

        def done():
            self.c.destroy()
            self.on_done()
        Anim(self.c, 0.5, step, done, ease=ease_in_out)


# ======================================================================================
#                                 HEADER & TAB BAR
# ======================================================================================

class Header(tk.Canvas):
    def __init__(self, parent, app):
        super().__init__(parent, height=66, bg=BG_DEEP, highlightthickness=0, bd=0)
        self.app, self.phase = app, 0.0
        self.bind("<Configure>", lambda e: self._build())
        self._build()
        self._animate()
        self._clock()

    def _build(self):
        self.delete("all")
        w = max(self.winfo_width(), 900)
        draw_logo(self, 38, 33, 0.5, "hlogo")
        self.create_text(72, 23, text=APP_NAME, anchor="w", font=F["h1"], fill=TEXT)
        self.create_text(74, 46, text="Colorimetric urine test strip reader  ·  point-of-care screening",
                         anchor="w", font=F["small"], fill=MUTED)
        self.ecg_x0, self.ecg_x1 = w - 620, w - 360
        self.create_line(self.ecg_x0, 33, self.ecg_x1, 33, fill=mix(LINE, BG_DEEP, 0.4))
        self.ecg = self.create_line(self.ecg_x0, 33, self.ecg_x1, 33, fill=ACCENT, width=2, smooth=False)
        self.ecg_dot = self.create_oval(0, 0, 0, 0, fill="#ffffff", outline=ACCENT, width=2)
        self.live = self.create_oval(w - 330, 18, w - 322, 26, fill=GREEN, outline="")
        self.create_text(w - 316, 22, text="DEVICE ONLINE", anchor="w", font=F["tiny_b"], fill=GREEN)
        self.create_text(w - 330, 42, text=self.app.reader.device_id + "  ·  " + self.app.reader.computing_unit,
                         anchor="w", font=F["tiny"], fill=MUTED)
        self.clock = self.create_text(w - 18, 33, anchor="e", justify="right", font=F["mono_s"], fill=TEXT)
        self.create_line(0, 65, w, 65, fill=LINE)

    @staticmethod
    def _beat(x):
        x %= 120
        if 20 <= x < 30:
            return 4 * math.sin((x - 20) / 10 * math.pi)
        if 38 <= x < 42:
            return -4 * (x - 38) / 4
        if 42 <= x < 46:
            return -4 + 24 * (x - 42) / 4
        if 46 <= x < 51:
            return 20 - 30 * (x - 46) / 5
        if 51 <= x < 55:
            return -10 + 10 * (x - 51) / 4
        if 70 <= x < 86:
            return 6 * math.sin((x - 70) / 16 * math.pi)
        return 0

    def _animate(self):
        try:
            self.phase += 2.2
            pts = []
            span = self.ecg_x1 - self.ecg_x0
            for k in range(0, int(span) + 1, 3):
                pts += [self.ecg_x0 + k, 33 - self._beat(k + self.phase)]
            self.coords(self.ecg, *pts)
            ex, ey = pts[-2], pts[-1]
            self.coords(self.ecg_dot, ex - 3, ey - 3, ex + 3, ey + 3)
            on = int(time.time() * 2) % 2 == 0
            self.itemconfig(self.live, fill=GREEN if on else mix(GREEN, BG_DEEP, 0.6))
            self.after(30, self._animate)
        except tk.TclError:
            pass

    def _clock(self):
        try:
            self.itemconfig(self.clock, text=time.strftime("%d %b %Y\n%H:%M:%S"))
            self.after(1000, self._clock)
        except tk.TclError:
            pass


class TabBar(tk.Canvas):
    def __init__(self, parent, tabs, on_select):
        super().__init__(parent, height=46, bg=BG, highlightthickness=0, bd=0)
        self.tabs, self.on_select = tabs, on_select
        self.current, self.pos, self._anim = tabs[0][0], {}, None
        self.font = tkfont.Font(font=F["tab"])
        self.bind("<Configure>", lambda e: self._draw())

    def _draw(self):
        self.delete("all")
        x = 20
        for key, label in self.tabs:
            w = self.font.measure(label) + 30
            self.pos[key] = (x, x + w)
            col = TEXT if key == self.current else MUTED
            r = self.create_rectangle(x, 4, x + w, 42, fill=BG, outline="", tags=(f"tab_{key}",))
            t = self.create_text(x + w / 2, 23, text=label, font=F["tab"], fill=col, tags=(f"tab_{key}", f"txt_{key}"))
            for item in (r, t):
                self.tag_bind(item, "<Button-1>", lambda e, k=key: self.on_select(k))
                self.tag_bind(item, "<Enter>", lambda e, k=key: self._hover(k, True))
                self.tag_bind(item, "<Leave>", lambda e, k=key: self._hover(k, False))
            x += w + 6
        self.create_line(0, 45, max(self.winfo_width(), 900), 45, fill=LINE)
        a, b = self.pos[self.current]
        self.under = round_rect(self, a + 10, 41, b - 10, 46, 2, fill=ACCENT, outline="")
        self.create_text(max(self.winfo_width(), 900) - 20, 23, anchor="e", font=F["tiny"], fill=mix(MUTED, BG, 0.3),
                         text="Ctrl+1…5 switch tabs  ·  Ctrl+Enter scan")

    def _hover(self, key, on):
        self.config(cursor="hand2" if on else "")
        if key != self.current:
            self.itemconfig(f"txt_{key}", fill=ACCENT if on else MUTED)

    def select(self, key):
        if key == self.current:
            return
        old = self.pos[self.current]
        self.itemconfig(f"txt_{self.current}", fill=MUTED)
        self.current = key
        self.itemconfig(f"txt_{key}", fill=TEXT)
        new = self.pos[key]
        if self._anim:
            self._anim.cancel()

        def step(t):
            a = old[0] + (new[0] - old[0]) * t
            b = old[1] + (new[1] - old[1]) * t
            self.coords(self.under, *Splash._rr_pts(a + 10, 41, b - 10, 46, 2))
        self._anim = Anim(self, 0.32, step, ease=ease_out_back)


# ======================================================================================
#                                       PAGES
# ======================================================================================

class Page(tk.Frame):
    """Base page - every page overrides on_show() (polymorphism in the GUI too)."""

    def __init__(self, parent, app):
        super().__init__(parent, bg=BG)
        self.app = app

    def on_show(self):
        pass


class ScanPage(Page):
    def __init__(self, parent, app):
        super().__init__(parent, app)
        self.vars, self.rows, self._guard, self.last_result, self._type_token = {}, [], False, None, 0
        self.columnconfigure(0, minsize=340)
        self.columnconfigure(1, weight=1)
        self.rowconfigure(0, weight=1)
        self._build_left()
        self._build_right()
        for i in range(len(PADS)):
            self._update_row(i)

    # ---- left: patient + sliders --------------------------------------------------
    def _build_left(self):
        left = card(self)
        left.grid(row=0, column=0, sticky="nsew", padx=(16, 8), pady=(12, 14))
        inner = tk.Frame(left, bg=PANEL)
        inner.pack(fill="both", expand=True, padx=16, pady=12)

        top = tk.Frame(inner, bg=PANEL)
        top.pack(fill="x")
        section(top, "Patient").pack(side="left")
        GlowButton(top, "Demo patient", self.demo_patient, width=104, height=26, color=PANEL2, fg=ACCENT,
                   font=F["tiny_b"], radius=8).pack(side="right")
        self.name_var = tk.StringVar()
        self.name_entry = PlaceholderEntry(inner, "Patient name", self.name_var)
        self.name_entry.pack(fill="x", pady=(6, 6), ipady=5)
        row = tk.Frame(inner, bg=PANEL)
        row.pack(fill="x")
        tk.Label(row, text="Age", bg=PANEL, fg=MUTED, font=F["small"]).pack(side="left")
        self.age_var = tk.StringVar(value="30")
        self.age_box = tk.Spinbox(row, from_=0, to=120, textvariable=self.age_var, width=5, bg=PANEL2, fg=TEXT,
                                  buttonbackground=PANEL2, relief="flat", insertbackground=TEXT, justify="center",
                                  font=F["body"], highlightthickness=1, highlightbackground=LINE, highlightcolor=ACCENT)
        self.age_box.pack(side="left", padx=(6, 16), ipady=3)
        tk.Label(row, text="Gender", bg=PANEL, fg=MUTED, font=F["small"]).pack(side="left")
        self.gender_var = tk.StringVar(value="Female")
        ttk.Combobox(row, textvariable=self.gender_var, values=["Female", "Male", "Other"], width=8,
                     state="readonly", font=F["body"]).pack(side="left", padx=6)

        top2 = tk.Frame(inner, bg=PANEL)
        top2.pack(fill="x", pady=(12, 0))
        section(top2, "Strip readings").pack(side="left")
        GlowButton(top2, "Random strip", self.random_strip, width=104, height=26, color=PANEL2, fg=ACCENT,
                   font=F["tiny_b"], radius=8).pack(side="right")

        for i, p in enumerate(PADS):
            r = tk.Frame(inner, bg=PANEL)
            r.pack(fill="x", pady=(3, 0))
            head = tk.Frame(r, bg=PANEL)
            head.pack(fill="x")
            dot = tk.Canvas(head, width=12, height=12, bg=PANEL, highlightthickness=0)
            dot_item = dot.create_rectangle(1, 1, 11, 11, fill=p.color_for(p.default), outline="")
            dot.pack(side="left", padx=(0, 6))
            name = tk.Label(head, text=p.name, bg=PANEL, fg=TEXT, font=F["label"])
            name.pack(side="left")
            lvl = tk.Label(head, text="", bg=PANEL, font=F["tiny_b"])
            lvl.pack(side="right")
            val = tk.Label(head, text="", bg=PANEL, fg=MUTED, font=F["mono_s"])
            val.pack(side="right", padx=8)
            var = tk.DoubleVar(value=p.default)
            sc = ttk.Scale(r, from_=p.lo, to=p.hi, variable=var, orient="horizontal",
                           style="Normal.Horizontal.TScale", command=lambda _s, i=i: self._on_scale(i))
            sc.pack(fill="x", pady=(2, 0))
            self.vars[p.key] = var
            self.rows.append(dict(dot=dot, dot_item=dot_item, name=name, lvl=lvl, val=val, scale=sc))

        section(inner, "Quick entry  (string parser)").pack(fill="x", pady=(12, 4))
        qe = tk.Frame(inner, bg=PANEL)
        qe.pack(fill="x")
        self.quick = PlaceholderEntry(qe, "glucose: 180; protein: 40; pH 6.5", font=F["mono_s"])
        self.quick.pack(side="left", fill="x", expand=True, ipady=5)
        self.quick.bind("<Return>", lambda e: (self.apply_quick(), "break")[1])
        GlowButton(qe, "Apply", self.apply_quick, width=64, height=32, color=ACCENT2, fg="#1e1240",
                   font=F["tiny_b"], radius=8).pack(side="left", padx=(6, 0))

        self.scan_btn = GlowButton(inner, "SCAN STRIP", self.scan, width=300, height=46, font=F["h3"], radius=12)
        self.scan_btn.pack(fill="x", pady=(12, 0))

    # ---- right: strip, gauge, report ---------------------------------------------
    def _build_right(self):
        right = card(self)
        right.grid(row=0, column=1, sticky="nsew", padx=(8, 16), pady=(12, 14))
        right.columnconfigure(0, weight=1)
        right.rowconfigure(2, weight=1)
        head = tk.Frame(right, bg=PANEL)
        head.grid(row=0, column=0, sticky="ew", padx=16, pady=(12, 0))
        tk.Label(head, text="Live colorimetry view", bg=PANEL, fg=TEXT, font=F["h2"]).pack(side="left")
        tk.Label(head, text="pads change colour with concentration, like the real strip", bg=PANEL, fg=MUTED,
                 font=F["small"]).pack(side="left", padx=12, pady=(4, 0))
        self.strip = StripView(right, PADS, on_pad_click=self._pad_clicked)
        self.strip.grid(row=1, column=0, sticky="ew", padx=8, pady=(6, 0))

        res = tk.Frame(right, bg=PANEL)
        res.grid(row=2, column=0, sticky="nsew", padx=12, pady=(0, 12))
        res.columnconfigure(1, weight=1)
        res.rowconfigure(1, weight=1)
        self.badge = StatusBadge(res)
        self.badge.grid(row=0, column=0, columnspan=2, sticky="ew")
        self.badge.set("AWAITING SCAN", "Set the readings, then press Scan Strip", "#64748b", pulse=False)
        gcol = tk.Frame(res, bg=PANEL)
        gcol.grid(row=1, column=0, sticky="n", padx=(4, 8), pady=(4, 0))
        self.gauge = Gauge(gcol, size=178)
        self.gauge.pack()
        self.copy_btn = GlowButton(gcol, "Copy report", self.copy_report, width=150, height=30, color=PANEL2,
                                   fg=TEXT, font=F["tiny_b"], radius=8)
        self.copy_btn.pack(pady=(4, 0))
        tf = tk.Frame(res, bg=PANEL2, highlightthickness=1, highlightbackground=LINE)
        tf.grid(row=1, column=1, sticky="nsew", pady=(4, 0))
        self.report = tk.Text(tf, bg=PANEL2, fg=TEXT, font=F["mono_s"], relief="flat", wrap="none",
                              padx=12, pady=8, height=10, insertbackground=TEXT, highlightthickness=0)
        sb = ttk.Scrollbar(tf, orient="vertical", command=self.report.yview)
        self.report.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.report.pack(fill="both", expand=True)
        for lvl, col in LEVEL_COLORS.items():
            self.report.tag_configure(f"lvl_{lvl}", foreground=col, font=(MONO_FONT, 9, "bold"))
        for st, col in STATUS_COLORS.items():
            self.report.tag_configure(f"st_{st}", foreground=col, font=(MONO_FONT, 10, "bold"))
        self.report.tag_configure("hdr", foreground=ACCENT, font=(MONO_FONT, 10, "bold"))
        self.report.tag_configure("dim", foreground=MUTED)
        self._idle_report()

    def _idle_report(self):
        self.report.config(state="normal")
        self.report.delete("1.0", "end")
        self.report.insert("end", "The AI report appears here after a scan.\n\n", "hdr")
        self.report.insert("end", "Try this:\n"
                                  "  1. Drag a slider - watch that pad change colour.\n"
                                  "  2. Click a pad on the strip to see what it measures.\n"
                                  "  3. Press SCAN STRIP to run the colour analysis.\n"
                                  "  4. Every scan is saved to the SQLite database\n"
                                  "     (see the Records and Insights tabs).\n", "dim")
        self.report.config(state="disabled")

    # ---- slider handling ----------------------------------------------------------
    def _on_scale(self, i):
        if self._guard:
            return
        p, var = PADS[i], self.vars[PADS[i].key]
        v = p.snap(var.get())
        if abs(v - var.get()) > 1e-9:
            self._guard = True
            var.set(v)
            self._guard = False
        self._update_row(i)
        self.strip.set_values({p.key: v})
        self._readings_changed()

    def _update_row(self, i):
        p, row = PADS[i], self.rows[i]
        v = p.snap(self.vars[p.key].get())
        level = p.classify(v)
        row["val"].config(text=f"{p.fmt(v)} {p.unit}".strip())
        row["lvl"].config(text=level.upper(), fg=LEVEL_COLORS[level])
        row["dot"].itemconfig(row["dot_item"], fill=p.color_for(v))
        style = f"{level}.Horizontal.TScale"
        if str(row["scale"].cget("style")) != style:
            row["scale"].config(style=style)

    def _readings_changed(self):
        if self.last_result is not None:
            self.last_result = None
            self.badge.set("READINGS CHANGED", "Press Scan Strip to analyse the new strip", "#64748b", pulse=False)

    def _glide_to(self, readings, duration=0.6):
        """Animate the sliders (and the pad colours) to new readings."""
        start = {k: self.vars[k].get() for k in readings}

        def step(t):
            vals = {}
            for i, p in enumerate(PADS):
                if p.key in readings:
                    v = start[p.key] + (readings[p.key] - start[p.key]) * t
                    v = readings[p.key] if t >= 1 else v
                    self._guard = True
                    self.vars[p.key].set(v)
                    self._guard = False
                    self._update_row(i)
                    vals[p.key] = v
            self.strip.set_values(vals)
        self._readings_changed()
        Anim(self, duration, step, ease=ease_out_cubic)

    def _pad_clicked(self, i):
        row = self.rows[i]
        row["name"].config(fg=ACCENT)
        self.after(500, lambda: row["name"].config(fg=TEXT))
        row["scale"].focus_set()

    # ---- buttons ------------------------------------------------------------------
    def demo_patient(self):
        p = Patient.random()
        self.name_entry.set_value(p.get_name())
        self.age_var.set(str(p.get_age()))
        self.gender_var.set(p.get_gender())
        flash_border(self.name_entry, ACCENT, 2)

    def random_strip(self):
        self._glide_to(self.app.reader.random_readings())

    def apply_quick(self):
        try:
            readings = self.app.reader.parse_raw(self.quick.value())
        except InvalidSampleError as e:
            flash_border(self.quick)
            self.app.toast("Couldn't read that", str(e), "error")
            return
        self._glide_to(readings)
        names = ", ".join(self.app.reader.pad_by_key[k].name for k in readings)
        self.app.toast("Readings applied", names, "info")

    def copy_report(self):
        if not self.last_result:
            self.app.toast("Nothing to copy yet", "Scan a strip first", "warn")
            return
        self.app.root.clipboard_clear()
        self.app.root.clipboard_append(self.app.reader.build_report(self.last_result))
        self.app.toast("Copied", "Report copied to the clipboard", "ok", 2)

    # ---- scanning -----------------------------------------------------------------
    def scan(self):
        if self.strip.scanning:
            return
        try:
            patient = Patient(None, self.name_entry.value(), self.age_var.get(), self.gender_var.get())
            readings = {k: PADS[i].snap(v.get()) for i, (k, v) in enumerate(self.vars.items())}
            result = self.app.reader.analyse(patient, readings)
        except InvalidSampleError as e:
            msg = str(e)
            flash_border(self.age_box if "Age" in msg else self.name_entry)
            self.app.toast("Can't scan yet", msg, "error")
            return
        self.scan_btn.set_enabled(False, "SCANNING…")
        self.badge.set("SCANNING…", "Reading reagent pads with the colour sensor", ACCENT, pulse=True)
        self.gauge.set_value(0, 0.4)
        self._type_token += 1
        self.report.config(state="normal")
        self.report.delete("1.0", "end")
        self.report.insert("end", "Analysing strip colours…\n", "dim")
        self.report.config(state="disabled")
        self.strip.scan(on_read=self._pad_read, on_done=lambda: self._reveal(result))

    def _pad_read(self, i):
        row, p = self.rows[i], PADS[i]
        level = p.classify(self.vars[p.key].get())
        row["name"].config(fg=LEVEL_COLORS[level])
        self.after(600, lambda: row["name"].config(fg=TEXT))
        self.report.config(state="normal")
        self.report.insert("end", f"  ✓ {p.name:<11} → {level}\n", f"lvl_{level}")
        self.report.config(state="disabled")

    def _reveal(self, result):
        saved = True
        try:
            self.app.db.save(result, "Manual")
        except sqlite3.Error as e:
            saved = False
            self.app.toast("Database error", str(e), "error")
        finally:
            self.scan_btn.set_enabled(True, "SCAN STRIP")
        self.last_result = result
        col = STATUS_COLORS[result.status]
        self.badge.set(result.status, f"{result.abnormal_count} of {len(result.results)} analytes outside the normal range"
                                      f"  ·  {result.patient.get_name()}", col)
        self.gauge.set_value(result.risk)
        self._typewriter(self.app.reader.build_report(result))
        if saved:
            self.app.toast(f"Saved as test #{result.test_id}", f"{result.patient.get_name()} · {result.status.title()}",
                           "ok" if result.status == "NORMAL" else ("warn" if "FURTHER" in result.status else "error"))
            self.app.data_changed()

    def _typewriter(self, text):
        self._type_token += 1
        token, pos = self._type_token, [0]
        self.report.config(state="normal")
        self.report.delete("1.0", "end")

        def tick():
            if token != self._type_token:
                return
            chunk = text[pos[0]:pos[0] + 14]
            self.report.insert("end", chunk)
            pos[0] += 14
            self.report.see("end")
            if pos[0] < len(text):
                self.after(12, tick)
            else:
                colorize(self.report)
                self.report.see("1.0")
                self.report.config(state="disabled")
        tick()


def colorize(text):
    """Colour the words Normal / Moderate / High and the overall status inside a report."""
    rules = [(lvl, f"lvl_{lvl}") for lvl in LEVEL_COLORS] + [(st, f"st_{st}") for st in STATUS_COLORS] + \
            [("URINE TEST STRIP REPORT", "hdr")]
    for word, tag in rules:
        idx = "1.0"
        while True:
            idx = text.search(word, idx, stopindex="end")
            if not idx:
                break
            end = f"{idx}+{len(word)}c"
            text.tag_add(tag, idx, end)
            idx = end


class BatchPage(Page):
    def __init__(self, parent, app):
        super().__init__(parent, app)
        self.q, self.running, self.results, self.dots = queue.Queue(), False, [], []
        self.columnconfigure(0, minsize=300)
        self.columnconfigure(1, weight=1)
        self.rowconfigure(0, weight=1)

        left = card(self)
        left.grid(row=0, column=0, sticky="nsew", padx=(16, 8), pady=(12, 14))
        inner = tk.Frame(left, bg=PANEL)
        inner.pack(fill="both", expand=True, padx=16, pady=14)
        tk.Label(inner, text="Batch Lab", bg=PANEL, fg=TEXT, font=F["h2"]).pack(anchor="w")
        tk.Label(inner, text="Simulates a point-of-care clinic reading many strips at once. "
                             "Every sample runs on its own thread; results return through a thread-safe queue.",
                 bg=PANEL, fg=MUTED, font=F["small"], wraplength=260, justify="left").pack(anchor="w", pady=(4, 12))
        row = tk.Frame(inner, bg=PANEL)
        row.pack(fill="x")
        tk.Label(row, text="Samples", bg=PANEL, fg=TEXT, font=F["label"]).pack(side="left")
        self.n_var = tk.StringVar(value="50")
        tk.Spinbox(row, from_=10, to=100, increment=10, textvariable=self.n_var, width=5, bg=PANEL2, fg=TEXT,
                   buttonbackground=PANEL2, relief="flat", justify="center", font=F["body"], insertbackground=TEXT,
                   highlightthickness=1, highlightbackground=LINE, highlightcolor=ACCENT).pack(side="left", padx=10, ipady=3)
        self.fault_var = tk.BooleanVar(value=True)
        tk.Checkbutton(inner, text="Inject faulty samples (exception demo)", variable=self.fault_var, bg=PANEL,
                       fg=TEXT, selectcolor=PANEL2, activebackground=PANEL, activeforeground=TEXT,
                       font=F["small"], highlightthickness=0, bd=0).pack(anchor="w", pady=(10, 0))
        self.run_btn = GlowButton(inner, "RUN BATCH", self.run, width=260, height=44, font=F["h3"], radius=12)
        self.run_btn.pack(fill="x", pady=(16, 14))

        section(inner, "Live counters").pack(fill="x")
        self.counter_lbls = {}
        for key, label, col in [("NORMAL", "Normal", GREEN), ("FURTHER EVALUATION ADVISED", "Further evaluation", AMBER),
                                ("HIGH RISK", "High risk", RED), ("error", "Rejected (exceptions)", "#94a3b8")]:
            r = tk.Frame(inner, bg=PANEL)
            r.pack(fill="x", pady=3)
            dot = tk.Canvas(r, width=12, height=12, bg=PANEL, highlightthickness=0)
            dot.create_oval(1, 1, 11, 11, fill=col, outline="")
            dot.pack(side="left", padx=(0, 8))
            tk.Label(r, text=label, bg=PANEL, fg=TEXT, font=F["small"]).pack(side="left")
            v = tk.Label(r, text="0", bg=PANEL, fg=col, font=F["h3"])
            v.pack(side="right")
            self.counter_lbls[key] = v
        self.thread_lbl = tk.Label(inner, text="Worker threads alive: 0", bg=PANEL, fg=MUTED, font=F["mono_s"])
        self.thread_lbl.pack(anchor="w", pady=(12, 0))
        self.time_lbl = tk.Label(inner, text="Elapsed: 0.00 s", bg=PANEL, fg=MUTED, font=F["mono_s"])
        self.time_lbl.pack(anchor="w")
        self.summary_lbl = tk.Label(inner, text="", bg=PANEL, fg=TEXT, font=F["small"], wraplength=260, justify="left")
        self.summary_lbl.pack(anchor="w", pady=(10, 0))

        right = card(self)
        right.grid(row=0, column=1, sticky="nsew", padx=(8, 16), pady=(12, 14))
        right.columnconfigure(0, weight=1)
        right.rowconfigure(1, weight=3)
        right.rowconfigure(3, weight=2)
        self.prog = tk.Canvas(right, height=34, bg=PANEL, highlightthickness=0)
        self.prog.grid(row=0, column=0, sticky="ew", padx=16, pady=(14, 0))
        self.grid_c = tk.Canvas(right, bg=PANEL, highlightthickness=0)
        self.grid_c.grid(row=1, column=0, sticky="nsew", padx=16, pady=6)
        self.grid_c.bind("<Configure>", lambda e: self._draw_grid())
        self.grid_c.bind("<Button-1>", self._grid_click)
        self.grid_c.bind("<Motion>", self._grid_motion)
        section(right, "Thread log", PANEL).grid(row=2, column=0, sticky="ew", padx=16)
        lf = tk.Frame(right, bg=PANEL2, highlightthickness=1, highlightbackground=LINE)
        lf.grid(row=3, column=0, sticky="nsew", padx=16, pady=(4, 14))
        self.log = tk.Text(lf, bg=PANEL2, fg=TEXT, font=F["mono_s"], relief="flat", height=8, padx=10, pady=6,
                           highlightthickness=0, wrap="none")
        sb = ttk.Scrollbar(lf, orient="vertical", command=self.log.yview)
        self.log.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.log.pack(fill="both", expand=True)
        for st, col in STATUS_COLORS.items():
            self.log.tag_configure(st.replace(" ", "_"), foreground=col)
        self.log.tag_configure("error", foreground=RED)
        self.log.tag_configure("dim", foreground=MUTED)
        self.log.insert("end", "Press RUN BATCH to start. Click any finished dot to open its report.\n", "dim")
        self.log.config(state="disabled")
        self.total, self.disp_p, self.shimmer = 0, 0.0, 0.0
        self._draw_progress()

    # ---- drawing ------------------------------------------------------------------
    def _draw_progress(self):
        c = self.prog
        c.delete("all")
        w = max(c.winfo_width(), 300)
        done = len([r for r in self.results if r is not None])
        c.create_text(0, 8, anchor="w", text=f"Processed {done} / {self.total or '—'}", font=F["label"], fill=TEXT)
        c.create_text(w, 8, anchor="e", text=f"{self.disp_p * 100:.0f}%", font=F["label"], fill=ACCENT)
        round_rect(c, 0, 20, w, 32, 6, fill=PANEL2, outline="")
        fw = w * self.disp_p
        if fw > 6:
            round_rect(c, 0, 20, fw, 32, 6, fill=ACCENT, outline="")
            if self.running:
                sx = (self.shimmer % 1.0) * (fw + 80) - 40
                for k, a in enumerate([0.15, 0.3, 0.45, 0.3, 0.15]):
                    x = sx + k * 8
                    if 4 < x < fw - 4:
                        c.create_line(x, 22, x, 30, fill=mix(ACCENT, "#ffffff", a), width=8)

    def _cell(self, idx):
        c = self.grid_c
        w, h = max(c.winfo_width(), 300), max(c.winfo_height(), 200)
        n = max(self.total, 50)
        cols = 10
        rows = math.ceil(n / cols)
        size = min(w / cols, h / rows)
        x0 = (w - size * cols) / 2
        y0 = (h - size * rows) / 2
        r, col = divmod(idx, cols)
        return x0 + size * (col + 0.5), y0 + size * (r + 0.5), size * 0.36

    def _draw_grid(self):
        c = self.grid_c
        c.delete("all")
        n = max(self.total, 50)
        for idx in range(n):
            x, y, r = self._cell(idx)
            res = self.results[idx] if idx < len(self.results) else None
            if res is None:
                pending = idx < self.total and self.running
                c.create_oval(x - r, y - r, x + r, y + r, fill=PANEL2 if pending else PANEL,
                              outline=mix(LINE, ACCENT, 0.35) if pending else LINE, width=1, tags=(f"d{idx}",))
            else:
                self._dot(idx, res, 1.0)

    def _dot(self, idx, res, k):
        c = self.grid_c
        c.delete(f"d{idx}")
        x, y, r = self._cell(idx)
        if isinstance(res, TestResult):
            col = STATUS_COLORS[res.status]
            rr = r * k
            c.create_oval(x - rr, y - rr, x + rr, y + rr, fill=col, outline=mix(col, "#ffffff", 0.4), tags=(f"d{idx}",))
            if k >= 0.6:
                c.create_text(x, y, text=str(idx + 1), font=(UI_FONT, max(6, int(r * 0.55)), "bold"),
                              fill=mix(col, "#000000", 0.6), tags=(f"d{idx}",))
        else:
            rr = r * k
            c.create_oval(x - rr, y - rr, x + rr, y + rr, fill=PANEL2, outline=RED, width=2, tags=(f"d{idx}",))
            c.create_line(x - rr * 0.45, y - rr * 0.45, x + rr * 0.45, y + rr * 0.45, fill=RED, width=2, tags=(f"d{idx}",))
            c.create_line(x - rr * 0.45, y + rr * 0.45, x + rr * 0.45, y - rr * 0.45, fill=RED, width=2, tags=(f"d{idx}",))

    def _light(self, idx, res):
        x, y, r = self._cell(idx)
        col = STATUS_COLORS[res.status] if isinstance(res, TestResult) else RED
        ring = self.grid_c.create_oval(x - r, y - r, x + r, y + r, outline=col, width=2)

        def step(t):
            self._dot(idx, res, max(0.05, t))
            rr = r * (1 + 0.8 * t)
            self.grid_c.coords(ring, x - rr, y - rr, x + rr, y + rr)
            self.grid_c.itemconfig(ring, outline=mix(col, PANEL, t))
        Anim(self.grid_c, 0.5, step, lambda: self.grid_c.delete(ring), ease=ease_out_back)

    def _hit(self, e):
        for idx in range(len(self.results)):
            x, y, r = self._cell(idx)
            if (e.x - x) ** 2 + (e.y - y) ** 2 <= (r + 2) ** 2:
                return idx
        return None

    def _grid_motion(self, e):
        idx = self._hit(e)
        self.grid_c.config(cursor="hand2" if idx is not None and self.results[idx] is not None else "")

    def _grid_click(self, e):
        idx = self._hit(e)
        if idx is None or self.results[idx] is None:
            return
        res = self.results[idx]
        if isinstance(res, TestResult):
            ReportWindow(self.app, res)
        else:
            self.app.toast(f"Sample {idx + 1} rejected", res, "error", 4)

    def _log(self, text, tag=None):
        self.log.config(state="normal")
        self.log.insert("end", text + "\n", tag)
        self.log.see("end")
        self.log.config(state="disabled")

    # ---- running ------------------------------------------------------------------
    def run(self):
        if self.running:
            return
        try:
            n = int(self.n_var.get())
            if not 1 <= n <= 100:
                raise ValueError
        except ValueError:
            self.app.toast("Invalid sample count", "Choose a number between 1 and 100", "error")
            return
        self.total, self.results, self.running = n, [None] * n, True
        self.counts = {"NORMAL": 0, "FURTHER EVALUATION ADVISED": 0, "HIGH RISK": 0, "error": 0}
        for lbl in self.counter_lbls.values():
            lbl.config(text="0")
        self.summary_lbl.config(text="")
        self.disp_p = 0.0
        self.log.config(state="normal")
        self.log.delete("1.0", "end")
        self.log.config(state="disabled")
        self._log(f"Starting {n} worker threads…", "dim")
        self.run_btn.set_enabled(False, "PROCESSING…")
        self._draw_grid()
        self.t0 = time.perf_counter()
        BatchProcessor(self.app.reader, self.q).start(n, self.fault_var.get())
        self.after(30, self._poll)

    def _poll(self):
        try:
            while True:
                kind, idx, payload = self.q.get_nowait()
                self.results[idx] = payload
                if kind == "ok":
                    try:
                        self.app.db.save(payload, "Batch", commit=False)
                    except sqlite3.Error as e:
                        self._log(f"[{idx + 1:03d}] DB error: {e}", "error")
                    self.counts[payload.status] += 1
                    self.counter_lbls[payload.status].config(text=str(self.counts[payload.status]))
                    self._log(f"[{idx + 1:03d}] {payload.patient.get_name():<18} risk {payload.risk:5.1f}  "
                              f"{payload.status}", payload.status.replace(" ", "_"))
                else:
                    self.counts["error"] += 1
                    self.counter_lbls["error"].config(text=str(self.counts["error"]))
                    self._log(f"[{idx + 1:03d}] REJECTED  {payload}", "error")
                self._light(idx, payload)
        except queue.Empty:
            pass
        except tk.TclError:
            return
        done = len([r for r in self.results if r is not None])
        target = done / self.total
        self.disp_p += (target - self.disp_p) * 0.25
        self.shimmer += 0.03
        self.thread_lbl.config(text=f"Worker threads alive: {max(0, threading.active_count() - 1)}")
        self.time_lbl.config(text=f"Elapsed: {time.perf_counter() - self.t0:.2f} s")
        self._draw_progress()
        if done < self.total or abs(self.disp_p - 1) > 0.002:
            self.after(30, self._poll)
        else:
            self._finish()

    def _finish(self):
        self.running = False
        self.disp_p = 1.0
        self._draw_progress()
        try:
            self.app.db.commit()
        except sqlite3.Error as e:
            self.app.toast("Database error", str(e), "error")
        ok = list(filter(lambda r: isinstance(r, TestResult), self.results))
        avg = reduce(lambda a, r: a + r.risk, ok, 0) / len(ok) if ok else 0
        worst = max(ok, key=lambda r: r.risk) if ok else None
        self.summary_lbl.config(text=f"Average risk index {avg:.1f}."
                                     + (f"\nHighest: {worst.patient.get_name()} ({worst.risk:.0f})." if worst else ""))
        self._log(f"Done - {len(ok)} saved to the database, {self.counts['error']} rejected.", "dim")
        self.run_btn.set_enabled(True, "RUN BATCH")
        self.thread_lbl.config(text=f"Worker threads alive: {max(0, threading.active_count() - 1)}")
        self.app.toast("Batch complete", f"{len(ok)} samples saved · {self.counts['error']} rejected", "ok")
        self.app.data_changed()


class RecordsPage(Page):
    COLUMNS = [("id", "Test", 54), ("patient", "Patient", 150), ("age", "Age", 44), ("gender", "Sex", 64),
               ("when", "Taken at", 140), ("glucose", "Glucose", 66), ("protein", "Protein", 62), ("ph", "pH", 44),
               ("ketones", "Ketones", 64), ("blood", "Blood", 54), ("leukocytes", "Leuko", 56),
               ("risk", "Risk", 54), ("status", "Status", 190), ("source", "Source", 66)]

    def __init__(self, parent, app):
        super().__init__(parent, app)
        self.dirty, self._search_job = True, None
        box = card(self)
        box.pack(fill="both", expand=True, padx=16, pady=(12, 14))
        bar = tk.Frame(box, bg=PANEL)
        bar.pack(fill="x", padx=14, pady=(12, 8))
        tk.Label(bar, text="Patient records", bg=PANEL, fg=TEXT, font=F["h2"]).pack(side="left")
        self.count_lbl = tk.Label(bar, text="", bg=PANEL, fg=MUTED, font=F["small"])
        self.count_lbl.pack(side="left", padx=10, pady=(4, 0))
        GlowButton(bar, "Clear all", self.clear_all, width=86, height=30, color=PANEL2, fg=RED, font=F["tiny_b"],
                   radius=8).pack(side="right")
        GlowButton(bar, "Export CSV", self.export_csv, width=96, height=30, color=PANEL2, fg=TEXT, font=F["tiny_b"],
                   radius=8).pack(side="right", padx=6)
        GlowButton(bar, "Delete", self.delete_sel, width=76, height=30, color=PANEL2, fg=AMBER, font=F["tiny_b"],
                   radius=8).pack(side="right")
        GlowButton(bar, "View report", self.view_sel, width=104, height=30, color=ACCENT, font=F["tiny_b"],
                   radius=8).pack(side="right", padx=6)

        flt = tk.Frame(box, bg=PANEL)
        flt.pack(fill="x", padx=14, pady=(0, 8))
        self.search = PlaceholderEntry(flt, "Search patient name  (SQL LIKE)", width=34)
        self.search.pack(side="left", ipady=4)
        self.search.var.trace_add("write", lambda *_: self._debounced_refresh())
        tk.Label(flt, text="Status", bg=PANEL, fg=MUTED, font=F["small"]).pack(side="left", padx=(16, 6))
        self.status_var = tk.StringVar(value="All")
        cb = ttk.Combobox(flt, textvariable=self.status_var, state="readonly", width=28,
                          values=["All"] + list(STATUS_COLORS))
        cb.pack(side="left")
        cb.bind("<<ComboboxSelected>>", lambda e: self.refresh())
        tk.Label(flt, text="Sort", bg=PANEL, fg=MUTED, font=F["small"]).pack(side="left", padx=(16, 6))
        self.order_var = tk.StringVar(value="Newest first")
        cb2 = ttk.Combobox(flt, textvariable=self.order_var, state="readonly", width=14, values=list(LabDatabase.ORDERS))
        cb2.pack(side="left")
        cb2.bind("<<ComboboxSelected>>", lambda e: self.refresh())

        tf = tk.Frame(box, bg=PANEL)
        tf.pack(fill="both", expand=True, padx=14, pady=(0, 14))
        self.tree = ttk.Treeview(tf, columns=[c[0] for c in self.COLUMNS], show="headings", selectmode="extended")
        for key, title, w in self.COLUMNS:
            self.tree.heading(key, text=title)
            self.tree.column(key, width=w, anchor="w" if key in ("patient", "status", "when") else "center",
                             stretch=key in ("patient", "status"))
        vs = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vs.set)
        vs.pack(side="right", fill="y")
        self.tree.pack(fill="both", expand=True)
        for st, col in STATUS_COLORS.items():
            self.tree.tag_configure(st, foreground=col)
        self.tree.tag_configure("odd", background=mix(PANEL2, PANEL, 0.5))
        self.tree.bind("<Double-1>", lambda e: self.view_sel())
        self.tree.bind("<Delete>", lambda e: self.delete_sel())

    def on_show(self):
        if self.dirty:
            self.refresh()

    def _debounced_refresh(self):
        if self._search_job:
            self.after_cancel(self._search_job)
        self._search_job = self.after(160, self.refresh)

    def refresh(self):
        self.dirty = False
        try:
            rows = self.app.db.search(self.search.value(), self.status_var.get(), self.order_var.get())
        except sqlite3.Error as e:
            self.app.toast("Database error", str(e), "error")
            return
        self.tree.delete(*self.tree.get_children())
        for n, r in enumerate(rows):
            (tid, pid, name, age, gender, when, glu, pro, ph, ket, bld, leu, _abn, risk, status, source) = r
            self.tree.insert("", "end", iid=str(tid), tags=(status, "odd" if n % 2 else "even"),
                             values=(tid, name, age, gender, when, f"{glu:.0f}", f"{pro:.0f}", f"{ph:.1f}",
                                     f"{ket:.0f}", f"{bld:.0f}", f"{leu:.0f}", f"{risk:.1f}", status, source))
        self.count_lbl.config(text=f"{len(rows)} test(s) shown")

    def _selected(self):
        return [int(i) for i in self.tree.selection()]

    def view_sel(self):
        ids = self._selected()
        if not ids:
            self.app.toast("Select a record", "Click a row first (double-click also opens it)", "warn")
            return
        try:
            ReportWindow(self.app, row_to_result(self.app.reader, self.app.db.get(ids[0])))
        except (sqlite3.Error, InvalidSampleError, TypeError) as e:
            self.app.toast("Couldn't open report", str(e), "error")

    def delete_sel(self):
        ids = self._selected()
        if not ids:
            self.app.toast("Select a record", "Choose one or more rows to delete", "warn")
            return
        if not messagebox.askyesno("Delete", f"Delete {len(ids)} test record(s)?", parent=self):
            return
        self.app.db.delete(ids)
        self.app.data_changed()
        self.refresh()
        self.app.toast("Deleted", f"{len(ids)} record(s) removed", "info")

    def clear_all(self):
        if messagebox.askyesno("Clear database", "Delete ALL patients and tests? This cannot be undone.", parent=self):
            self.app.db.clear()
            self.app.data_changed()
            self.refresh()
            self.app.toast("Database cleared", "All records removed", "warn")

    def export_csv(self):
        path = filedialog.asksaveasfilename(parent=self, defaultextension=".csv", initialfile="uroscan_records.csv",
                                            filetypes=[("CSV file", "*.csv")])
        if not path:
            return
        try:
            rows = self.app.db.search(self.search.value(), self.status_var.get(), self.order_var.get())
            with open(path, "w", newline="", encoding="utf-8") as f:
                w = csv.writer(f)
                w.writerow(["test_id", "patient_id", "name", "age", "gender", "taken_at"] + LabDatabase.COLS
                           + ["abnormal_count", "risk", "status", "source"])
                w.writerows(rows)
            self.app.toast("Exported", os.path.basename(path), "ok")
        except (OSError, sqlite3.Error) as e:
            self.app.toast("Export failed", str(e), "error")


class InsightsPage(Page):
    def __init__(self, parent, app):
        super().__init__(parent, app)
        self.c = tk.Canvas(self, bg=BG, highlightthickness=0)
        self.c.pack(fill="both", expand=True, padx=16, pady=(12, 14))
        self.c.bind("<Configure>", lambda e: self.draw(animate=False))
        self._anim = None

    def on_show(self):
        self.draw(animate=True)

    def draw(self, animate=True):
        c = self.c
        c.delete("all")
        if self._anim:
            self._anim.cancel()
        W, H = max(c.winfo_width(), 800), max(c.winfo_height(), 500)
        try:
            st = self.app.db.stats()
        except sqlite3.Error as e:
            c.create_text(W / 2, H / 2, text=f"Database error: {e}", fill=RED, font=F["h3"])
            return
        if st["total"] == 0:
            draw_logo(c, W / 2, H / 2 - 60, 1.0, "empty")
            c.create_text(W / 2, H / 2 + 20, text="No tests recorded yet", fill=TEXT, font=F["h2"])
            c.create_text(W / 2, H / 2 + 46, text="Scan a strip or run the Batch Lab - the charts build themselves here.",
                          fill=MUTED, font=F["body"])
            return
        gap = 14
        cw = (W - 3 * gap) / 4
        kpis = [("Tests recorded", st["total"], "{:.0f}", ACCENT), ("Patients", st["patients"], "{:.0f}", ACCENT2),
                ("Abnormal rate", st["abnormal_rate"], "{:.0f}%", AMBER), ("Avg risk index", st["avg_risk"], "{:.1f}", RED)]
        kpi_items = []
        for k, (label, value, fmt, col) in enumerate(kpis):
            x0 = k * (cw + gap)
            round_rect(c, x0, 0, x0 + cw, 92, 14, fill=PANEL, outline=LINE)
            round_rect(c, x0, 0, x0 + 6, 92, 3, fill=col, outline="")
            c.create_text(x0 + 22, 22, text=label.upper(), anchor="w", font=F["label"], fill=MUTED)
            kpi_items.append((c.create_text(x0 + 22, 58, text=fmt.format(0), anchor="w", font=F["kpi"], fill=TEXT), value, fmt))

        top = 108
        lw = W * 0.42
        # ---- outcomes panel
        round_rect(c, 0, top, lw, top + 196, 14, fill=PANEL, outline=LINE)
        c.create_text(18, top + 22, text="Screening outcomes", anchor="w", font=F["h3"], fill=TEXT)
        c.create_text(18, top + 40, text="GROUP BY status", anchor="w", font=F["mono_s"], fill=MUTED)
        bars = []
        mx = max(st["by_status"].values()) if st["by_status"] else 1
        for k, (status, col) in enumerate(STATUS_COLORS.items()):
            y = top + 66 + k * 42
            n = st["by_status"].get(status, 0)
            c.create_text(18, y, text=status.title(), anchor="w", font=F["small"], fill=TEXT)
            bx0, bx1 = 18, lw - 70
            round_rect(c, bx0, y + 10, bx1, y + 22, 6, fill=PANEL2, outline="")
            bar = round_rect(c, bx0, y + 10, bx0 + 12, y + 22, 6, fill=col, outline="")
            txt = c.create_text(lw - 18, y + 10, text="0", anchor="e", font=F["h3"], fill=col)
            bars.append((bar, txt, bx0, bx0 + (bx1 - bx0) * n / mx, y, n))
        # ---- top risk panel
        t2 = top + 210
        round_rect(c, 0, t2, lw, H - 2, 14, fill=PANEL, outline=LINE)
        c.create_text(18, t2 + 22, text="Highest risk tests", anchor="w", font=F["h3"], fill=TEXT)
        c.create_text(18, t2 + 40, text="ORDER BY risk DESC LIMIT 5", anchor="w", font=F["mono_s"], fill=MUTED)
        for k, (name, risk, status, tid) in enumerate(st["top"]):
            y = t2 + 68 + k * 30
            if y > H - 16:
                break
            col = STATUS_COLORS.get(status, MUTED)
            c.create_oval(18, y - 5, 28, y + 5, fill=col, outline="")
            c.create_text(38, y, text=f"#{tid}  {name}", anchor="w", font=F["small"], fill=TEXT)
            c.create_text(lw - 18, y, text=f"{risk:.0f}", anchor="e", font=F["label"], fill=col)

        # ---- average readings panel (colour = the pad colour of the average reading)
        x0 = lw + gap
        round_rect(c, x0, top, W - 2, H - 2, 14, fill=PANEL, outline=LINE)
        c.create_text(x0 + 18, top + 22, text="Average reading per analyte", anchor="w", font=F["h3"], fill=TEXT)
        c.create_text(x0 + 18, top + 40, text="AVG() - bar colour is the pad colour that average would produce; "
                                              "dashed line = upper normal limit", anchor="w", font=F["tiny"], fill=MUTED)
        n = len(PADS)
        area_x0, area_x1 = x0 + 30, W - 30
        base, ceil = H - 70, top + 74
        slot = (area_x1 - area_x0) / n
        vbars = []
        for k, p in enumerate(PADS):
            avg = st["avg"][p.key] or 0
            cx = area_x0 + slot * (k + 0.5)
            bw = min(54, slot * 0.5)
            c.create_rectangle(cx - bw / 2, ceil, cx + bw / 2, base, fill=PANEL2, outline="")
            level = p.classify(avg)
            frac = p.norm(avg)
            limit = p.normal_max if isinstance(p, ThresholdPad) else 8.0
            ly = base - (base - ceil) * p.norm(limit)
            c.create_line(cx - bw / 2 - 6, ly, cx + bw / 2 + 6, ly, fill=GREEN, dash=(4, 3), width=2, tags=(f"lim{k}",))
            col = p.color_for(avg)
            bar = c.create_rectangle(cx - bw / 2, base, cx + bw / 2, base, fill=col, outline=mix(col, "#000", 0.3))
            vt = c.create_text(cx, base - 10, text="", font=F["label"], fill=TEXT)
            c.create_text(cx, base + 16, text=p.name, font=F["label"], fill=TEXT)
            c.create_text(cx, base + 34, text=level, font=F["tiny_b"], fill=LEVEL_COLORS[level])
            vbars.append((bar, vt, cx, bw, base - (base - ceil) * max(frac, 0.01), p, avg))
            c.tag_raise(f"lim{k}")

        def step(t):
            for item, value, fmt in kpi_items:
                c.itemconfig(item, text=fmt.format(value * t))
            for bar, txt, bx0, bx1, y, n_ in bars:
                c.coords(bar, *Splash._rr_pts(bx0, y + 10, max(bx0 + 12, bx0 + (bx1 - bx0) * t), y + 22, 6))
                c.itemconfig(txt, text=str(int(round(n_ * t))))
            for bar, vt, cx, bw, ytop, p, avg in vbars:
                y = base - (base - ytop) * t
                c.coords(bar, cx - bw / 2, y, cx + bw / 2, base)
                c.coords(vt, cx, y - 12)
                c.itemconfig(vt, text=p.fmt(avg * t))
        if animate:
            self._anim = Anim(self, 1.1, step, ease=ease_out_cubic)
        else:
            step(1.0)


class AboutPage(Page):
    EXPERIMENTS = [
        ("01", "Classes & objects", "Patient class with getter / setter methods, a class variable, "
                                    "@staticmethod make_code() and @classmethod random()."),
        ("02", "Constructors & lists", "Parameterised __init__ in every class. Lists hold the pads, the "
                                       "analysis results, the batch threads and their results."),
        ("03", "Strings & inheritance", "DiagnosticDevice → UrineTestStripReader (super().__init__). Quick-entry "
                                        "parser uses split/strip/lower/replace; the report uses f-strings."),
        ("04", "Abstract class & polymorphism", "StripPad(ABC) with @abstractmethod classify(), band(), normal_range(); "
                                                "ThresholdPad and PHPad override them differently."),
        ("05", "Exceptions, modules & threads", "Custom InvalidSampleError, try/except/finally around every input. "
                                                "Batch Lab starts one thread per sample and uses a queue."),
        ("06", "Collections & functional", "dict readings, tuple patient info, set of categories; "
                                           "map() classifies, filter() finds abnormal pads, reduce() counts them."),
        ("07", "Tkinter Canvas", "Logo, test strip, colour charts, gauge, charts and every animation are "
                                 "drawn with create_oval / rectangle / polygon / arc / line / text."),
        ("08", "SQLite database", "Two tables (patients, tests). INSERT, SELECT with WHERE, LIKE, JOIN, ORDER BY, "
                                  "GROUP BY, AVG, COUNT, LIMIT and DELETE."),
    ]

    def __init__(self, parent, app):
        super().__init__(parent, app)
        wrap = tk.Frame(self, bg=BG)
        wrap.pack(fill="both", expand=True, padx=16, pady=(12, 14))
        head = card(wrap)
        head.pack(fill="x")
        hc = tk.Canvas(head, height=96, bg=PANEL, highlightthickness=0)
        hc.pack(fill="x")
        draw_logo(hc, 56, 48, 0.75, "alogo")
        hc.create_text(104, 30, text=f"{APP_NAME}  ·  {CASE_STUDY}", anchor="w", font=F["h2"], fill=TEXT)
        hc.create_text(104, 54, text=f"{STUDENT}   ·   Roll No. {ROLL_NO}   ·   Batch {BATCH}   ·   OOP with Python",
                       anchor="w", font=F["body"], fill=MUTED)
        hc.create_text(104, 74, text="Device: " + app.reader.device_info() + f"   ·   Database: {os.path.basename(app.db.path)}",
                       anchor="w", font=F["small"], fill=mix(MUTED, PANEL, 0.25))
        grid = tk.Frame(wrap, bg=BG)
        grid.pack(fill="both", expand=True, pady=(12, 0))
        for k in range(2):
            grid.columnconfigure(k, weight=1, uniform="c")
        for k in range(4):
            grid.rowconfigure(k, weight=1)
        for n, (num, title, text) in enumerate(self.EXPERIMENTS):
            cf = card(grid)
            cf.grid(row=n // 2, column=n % 2, sticky="nsew", padx=(0 if n % 2 == 0 else 6, 6 if n % 2 == 0 else 0), pady=4)
            tk.Label(cf, text=f"EXP {num}", bg=PANEL, fg=ACCENT, font=F["tiny_b"]).pack(anchor="w", padx=14, pady=(10, 0))
            tk.Label(cf, text=title, bg=PANEL, fg=TEXT, font=F["h3"]).pack(anchor="w", padx=14)
            lbl = tk.Label(cf, text=text, bg=PANEL, fg=MUTED, font=F["small"], justify="left", anchor="w")
            lbl.pack(fill="x", padx=14, pady=(2, 10))
            lbl.bind("<Configure>", lambda e, l=lbl: l.config(wraplength=max(200, e.width - 4)))
            for wdg in [cf] + list(cf.winfo_children()):
                wdg.bind("<Enter>", lambda e, f=cf: f.config(highlightbackground=ACCENT), add="+")
                wdg.bind("<Leave>", lambda e, f=cf: f.config(highlightbackground=LINE), add="+")


class ReportWindow(tk.Toplevel):
    def __init__(self, app, result):
        super().__init__(app.root, bg=BG)
        self.app, self.result = app, result
        self.title(f"Test #{result.test_id} · {result.patient.get_name()}")
        self.geometry("880x620")
        self.minsize(760, 560)
        self.transient(app.root)
        try:
            self.attributes("-alpha", 0.0)
        except tk.TclError:
            pass
        col = STATUS_COLORS[result.status]
        badge = StatusBadge(self, bg=BG)
        badge.pack(fill="x", padx=12, pady=(10, 0))
        badge.set(result.status, f"Test #{result.test_id}  ·  {result.patient.get_name()}  ·  {result.timestamp}", col)
        strip = StripView(self, PADS, interactive=True, bg=BG)
        strip.pack(fill="x", padx=8)
        strip.set_values(result.readings, mark_read=True)
        body = tk.Frame(self, bg=BG)
        body.pack(fill="both", expand=True, padx=16, pady=(0, 14))
        left = tk.Frame(body, bg=BG)
        left.pack(side="left", fill="y")
        g = Gauge(left, size=170, bg=BG)
        g.pack()
        g.set_value(result.risk, 1.4)
        GlowButton(left, "Copy report", self._copy, width=150, height=32, color=PANEL2, fg=TEXT,
                   font=F["tiny_b"], bg=BG).pack(pady=(8, 4))
        GlowButton(left, "Close", self.destroy, width=150, height=32, color=ACCENT, font=F["tiny_b"], bg=BG).pack()
        tf = tk.Frame(body, bg=PANEL2, highlightthickness=1, highlightbackground=LINE)
        tf.pack(side="left", fill="both", expand=True, padx=(14, 0))
        txt = tk.Text(tf, bg=PANEL2, fg=TEXT, font=F["mono_s"], relief="flat", padx=12, pady=8, wrap="none",
                      highlightthickness=0)
        sb = ttk.Scrollbar(tf, orient="vertical", command=txt.yview)
        txt.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        txt.pack(fill="both", expand=True)
        for lvl, c in LEVEL_COLORS.items():
            txt.tag_configure(f"lvl_{lvl}", foreground=c, font=(MONO_FONT, 9, "bold"))
        for st, c in STATUS_COLORS.items():
            txt.tag_configure(f"st_{st}", foreground=c, font=(MONO_FONT, 10, "bold"))
        txt.tag_configure("hdr", foreground=ACCENT, font=(MONO_FONT, 10, "bold"))
        txt.insert("1.0", app.reader.build_report(result))
        colorize(txt)
        txt.config(state="disabled")
        self.bind("<Escape>", lambda e: self.destroy())

        def fade(t):
            try:
                self.attributes("-alpha", t)
            except tk.TclError:
                pass
        Anim(self, 0.25, fade, ease=linear)

    def _copy(self):
        self.clipboard_clear()
        self.clipboard_append(self.app.reader.build_report(self.result))
        self.app.toast("Copied", "Report copied to the clipboard", "ok", 2)


# ======================================================================================
#                                    APPLICATION
# ======================================================================================

def default_db_path():
    here = os.path.dirname(os.path.abspath(__file__))
    for folder in (here, os.path.expanduser("~")):
        if os.access(folder, os.W_OK):
            return os.path.join(folder, "uroscan.db")
    return ":memory:"


class UroScanApp:
    TABS = [("scan", "Scan Strip"), ("batch", "Batch Lab"), ("records", "Records"),
            ("insights", "Insights"), ("about", "About")]

    def __init__(self, root, db_path=None, splash=True):
        self.root = root
        root.title(f"{APP_NAME} — Urine Test Strip Reader")
        root.configure(bg=BG)
        sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
        w, h = min(1320, sw - 40), min(820, sh - 80)
        root.geometry(f"{w}x{h}+{max(0, (sw - w) // 2)}+{max(0, (sh - h) // 3)}")
        root.minsize(1100, 680)
        if sh < 860:
            try:
                root.state("zoomed")
            except tk.TclError:
                try:
                    root.attributes("-zoomed", True)
                except tk.TclError:
                    pass
        init_fonts(root)
        self._style()
        self.reader = UrineTestStripReader(" kjs-hc-03 ", " healthcare ", "Raspberry Pi 5", PADS)
        try:
            self.db = LabDatabase(db_path or default_db_path())
        except sqlite3.Error as e:
            messagebox.showwarning(APP_NAME, f"Could not open the database file ({e}).\nUsing a temporary in-memory database.")
            self.db = LabDatabase(":memory:")
        root.protocol("WM_DELETE_WINDOW", self.quit)
        if splash:
            Splash(root, self.build)
        else:
            self.build()

    def _style(self):
        st = ttk.Style(self.root)
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
        st.configure(".", background=PANEL, foreground=TEXT, fieldbackground=PANEL2, bordercolor=LINE,
                     font=F["body"])
        st.configure("TCombobox", fieldbackground=PANEL2, background=PANEL2, foreground=TEXT, arrowcolor=TEXT,
                     bordercolor=LINE, lightcolor=PANEL2, darkcolor=PANEL2, padding=4)
        st.map("TCombobox", fieldbackground=[("readonly", PANEL2)], foreground=[("readonly", TEXT)],
               selectbackground=[("readonly", PANEL2)], selectforeground=[("readonly", TEXT)],
               bordercolor=[("focus", ACCENT)])
        self.root.option_add("*TCombobox*Listbox.background", PANEL2)
        self.root.option_add("*TCombobox*Listbox.foreground", TEXT)
        self.root.option_add("*TCombobox*Listbox.selectBackground", ACCENT)
        self.root.option_add("*TCombobox*Listbox.selectForeground", "#04222b")
        for level, col in LEVEL_COLORS.items():
            st.configure(f"{level}.Horizontal.TScale", background=col, troughcolor=PANEL2, bordercolor=PANEL,
                         lightcolor=col, darkcolor=mix(col, "#000000", 0.25), gripcount=0)
            st.map(f"{level}.Horizontal.TScale", background=[("active", mix(col, "#ffffff", 0.3))])
        st.configure("Treeview", background=PANEL2, fieldbackground=PANEL2, foreground=TEXT, rowheight=26,
                     bordercolor=LINE, lightcolor=PANEL2, darkcolor=PANEL2, font=F["small"])
        st.map("Treeview", background=[("selected", "#1d4060")], foreground=[("selected", "#ffffff")])
        st.configure("Treeview.Heading", background=PANEL, foreground=MUTED, relief="flat", font=F["label"],
                     bordercolor=LINE, lightcolor=PANEL, darkcolor=PANEL, padding=(6, 6))
        st.map("Treeview.Heading", background=[("active", PANEL2)], foreground=[("active", ACCENT)])
        st.configure("Vertical.TScrollbar", background=PANEL2, troughcolor=PANEL, bordercolor=PANEL,
                     arrowcolor=MUTED, lightcolor=PANEL2, darkcolor=PANEL2, gripcount=0)
        st.map("Vertical.TScrollbar", background=[("active", LINE)])

    def build(self):
        self.header = Header(self.root, self)
        self.header.pack(fill="x")
        self.tabbar = TabBar(self.root, self.TABS, self.show)
        self.tabbar.pack(fill="x")
        self.container = tk.Frame(self.root, bg=BG)
        self.container.pack(fill="both", expand=True)
        self.pages = {
            "scan": ScanPage(self.container, self),
            "batch": BatchPage(self.container, self),
            "records": RecordsPage(self.container, self),
            "insights": InsightsPage(self.container, self),
            "about": AboutPage(self.container, self),
        }
        self.current = None
        self.toaster = Toaster(self.root)
        self.show("scan")
        for n, (key, _label) in enumerate(self.TABS, start=1):
            self.root.bind(f"<Control-Key-{n}>", lambda e, k=key: self.show(k))
        self.root.bind("<Control-Return>", lambda e: (self.show("scan"), self.pages["scan"].scan()))
        self.root.after(400, lambda: self.toast("Welcome to UroScan AI", "Drag a slider or click a pad to begin", "info"))

    def show(self, key):
        if key == self.current:
            return
        self.tabbar.select(key)
        old = self.pages.get(self.current)
        if old:
            old.place_forget()
        page = self.pages[key]
        self.current = key
        page.place(relx=0.03, rely=0, relwidth=1, relheight=1)
        page.lift()

        def step(t):
            page.place_configure(relx=0.03 * (1 - t))
        Anim(page, 0.28, step, ease=ease_out_cubic)
        page.on_show()

    def toast(self, title, message="", kind="info", seconds=3.0):
        if hasattr(self, "toaster"):
            self.toaster.show(title, message, kind, seconds)

    def data_changed(self):
        self.pages["records"].dirty = True
        if self.current == "records":
            self.pages["records"].refresh()

    def quit(self):
        self.db.close()
        self.root.destroy()


def main():
    root = tk.Tk()
    UroScanApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
