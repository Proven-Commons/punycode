#!/usr/bin/env python3
"""Differential tests: the Lean Punycode encoder and decoder against a
model of RFC 3492 and four implementations.

The tool answers `encode` and `decode` requests (see the header of
Main.lean). Its answers are checked two ways.

1. Against `model_encode` and `model_decode`, Python transcriptions of
   the pseudocode of RFC 3492, sections 6.2 and 6.3, with unbounded
   integers, and a check that every decoded value is a Unicode scalar
   value. They share nothing with the Lean code, which builds its
   encoding a different way. Every answer must agree.

2. Against four oracles, on every input:

   - RFC 3492: the sample implementation of appendix C, the library
     part unchanged, in tests/oracles/rfc3492, compiled here with `cc`;
   - Python: the standard library's `punycode` codec;
   - Node: the punycode.js module Node bundles, through
     tests/oracles/node/oracle.js;
   - libidn2: `idn2_punycode_encode` and `idn2_punycode_decode`, through
     ctypes.

   A disagreement is allowed only for a known reason, checked against
   the model, and is counted under it:

   - the oracle returns a value that is not a Unicode scalar value (a
     surrogate, or past U+10FFFF), where the tool fails;
   - Node returns surrogates where the tool fails, and two of them
     next to each other pair up into one code point in its UTF-16
     string, as the model, run with surrogates let through, confirms;
   - the oracle overflows its integers (2**32 - 1 for the RFC code and
     libidn2, 2**31 - 1 for Node) where the model's largest number
     passes that bound and the tool, with unbounded integers, does not
     fail;
   - Python's codec reads a delimiter with nothing before it, which
     RFC 3492 does not (`-tda`);
   - libidn2 refuses a string with no deltas, such as `abc-` or the
     empty string, and basic code points other than letters, digits,
     `-` and `_` before the delimiter, both of which RFC 3492 allows;
   - libidn2 reads `_` after the delimiter as the digit `a`, where the
     tool fails: `td_` gives what `tda` gives. The model, run on the
     string with `_` there replaced by `a`, confirms it.

   Any other disagreement is a failure.

Inputs come from a recorded seed, after fixed sets:

- the 19 samples of section 7.1, both ways;
- strings at the edges: U+10FFFF and past it, around the surrogates,
  a delimiter first, digits in upper case;
- every string of up to five characters over `a`, `Z`, `0`, `9`, `-`,
  `.` and `u+00FC`, decoded;
- random text, from ASCII, Latin, Greek, Cyrillic, CJK, Hangul,
  emoji, private use and the code points next to the surrogates,
  encoded, and its encodings decoded, with digits in upper case;
- mutations of those encodings: a character changed, dropped, added
  or doubled, a delimiter added or moved, the string cut short, digits
  added;
- long text, with deltas past 2**31 and 2**32;
- malformed requests, which the tool must answer with `error`.

Every seventh request ends in CR LF.

    python3 tests/run_tests.py [--seed N] [--count N]

`--count` is the number of random texts after the fixed sets. The
script builds the executable and the RFC 3492 oracle first, writes
tests/TEST-RESULTS.md, and exits non-zero if any check fails.
"""

import argparse
import ctypes
import ctypes.util
import itertools
import os
import platform
import random
import subprocess
import sys
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "punycode"
RFC_SRC = ROOT / "tests" / "oracles" / "rfc3492"
RFC_EXE = ROOT / ".lake" / "oracle-rfc3492" / "rfc3492-oracle"
NODE_ORACLE = ROOT / "tests" / "oracles" / "node" / "oracle.js"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
TIMEOUT = 3600
BUILD_TIMEOUT = 3600

# ---------------------------------------------------------------------
# The model: RFC 3492, sections 5, 6.1, 6.2 and 6.3, with unbounded
# integers.

BASE, TMIN, TMAX, SKEW, DAMP, INITIAL_BIAS, INITIAL_N = 36, 1, 26, 38, 700, 72, 0x80
DIGITS = "abcdefghijklmnopqrstuvwxyz0123456789"


def adapt(delta, numpoints, firsttime):
    delta = delta // DAMP if firsttime else delta // 2
    delta += delta // numpoints
    k = 0
    while delta > ((BASE - TMIN) * TMAX) // 2:
        delta //= BASE - TMIN
        k += BASE
    return k + (((BASE - TMIN + 1) * delta) // (delta + SKEW))


def threshold(k, bias):
    return TMIN if k <= bias else TMAX if k >= bias + TMAX else k - bias


def digit_value(c):
    o = ord(c)
    if 0x41 <= o <= 0x5A:
        return o - 0x41
    if 0x61 <= o <= 0x7A:
        return o - 0x61
    if 0x30 <= o <= 0x39:
        return o - 0x30 + 26
    return None


def scalar(n):
    return n <= 0x10FFFF and not 0xD800 <= n <= 0xDFFF


def model_decode(s, surrogates=False):
    """Section 6.2. Returns (code points or None, why it failed, the
    largest number the procedure needed). With `surrogates`, it lets
    surrogates through, as some oracles do, and fails only past
    U+10FFFF."""
    n, i, bias = INITIAL_N, 0, INITIAL_BIAS
    b = s.rfind("-")
    if b > 0:
        literal, rest = s[:b], s[b + 1:]
    else:
        literal, rest = "", s
    if any(ord(c) >= 0x80 for c in literal):
        return None, "non-basic before the delimiter", 0
    out = [ord(c) for c in literal]
    peak = 0
    pos = 0
    while pos < len(rest):
        oldi, w, k = i, 1, BASE
        while True:
            if pos >= len(rest):
                return None, "input ends inside an integer", peak
            digit = digit_value(rest[pos])
            pos += 1
            if digit is None:
                return None, "not a digit", peak
            i += digit * w
            peak = max(peak, i)
            t = threshold(k, bias)
            if digit < t:
                break
            w *= BASE - t
            peak = max(peak, w)
            k += BASE
        bias = adapt(i - oldi, len(out) + 1, oldi == 0)
        n += i // (len(out) + 1)
        peak = max(peak, n)
        i %= len(out) + 1
        if not (n <= 0x10FFFF if surrogates else scalar(n)):
            return None, "not a scalar value", peak
        out.insert(i, n)
        i += 1
    return out, None, peak


def model_encode(cps):
    """Section 6.3. Returns (the Punycode string, the largest number
    the procedure needed)."""
    n, delta, bias = INITIAL_N, 0, INITIAL_BIAS
    out = [chr(c) for c in cps if c < 0x80]
    b = h = len(out)
    if b > 0:
        out.append("-")
    peak = 0
    while h < len(cps):
        m = min(c for c in cps if c >= n)
        delta += (m - n) * (h + 1)
        peak = max(peak, delta, m)
        n = m
        for c in cps:
            if c < n:
                delta += 1
                peak = max(peak, delta)
            if c == n:
                q, k = delta, BASE
                while True:
                    t = threshold(k, bias)
                    if q < t:
                        break
                    out.append(DIGITS[t + (q - t) % (BASE - t)])
                    q = (q - t) // (BASE - t)
                    k += BASE
                out.append(DIGITS[q])
                bias = adapt(delta, h + 1, h == b)
                delta = 0
                h += 1
        delta += 1
        n += 1
    return "".join(out), peak


# ---------------------------------------------------------------------
# The oracles.

def run_lines(cmd, lines, timeout=TIMEOUT, cwd=None):
    """Send `lines` to `cmd` and return its answer lines and a note on
    how the run failed, or None."""
    raw = "".join(lines).encode("utf-8")
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, cwd=cwd)
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf):
        while chunk := stream.read1(1 << 16):
            buf += chunk

    threads = [threading.Thread(target=feed),
               threading.Thread(target=drain, args=(proc.stdout, out)),
               threading.Thread(target=drain, args=(proc.stderr, err))]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if proc.returncode != 0 and not problem:
        tail = " / ".join(err.decode("utf-8", "backslashreplace").splitlines()[-3:])
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    answers = text.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    return answers, problem


def build_rfc():
    RFC_EXE.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["cc", "-O2", "-o", str(RFC_EXE), str(RFC_SRC / "punycode.c"),
                    str(RFC_SRC / "wrapper.c")], check=True, timeout=BUILD_TIMEOUT)


def parse_cps(text):
    return [int(x, 16) for x in text.split(",")] if text else []


def rfc_answers(kind, items):
    """Encode or decode every item with the RFC 3492 sample code."""
    if kind == "e":
        lines = ["e " + (",".join(f"{c:x}" for c in cps) or "-") + "\n" for cps in items]
    else:
        lines = ["d " + s.encode("utf-8").hex() + "\n" for s in items]
    answers, problem = run_lines([str(RFC_EXE)], lines)
    if problem or len(answers) != len(items):
        raise RuntimeError(f"RFC 3492 oracle: {problem or 'wrong number of answers'}")
    return [unwrap(kind, a) for a in answers]


def node_answers(kind, items):
    if kind == "e":
        lines = ["e " + "".join(map(chr, cps)).encode("utf-8").hex() + "\n" for cps in items]
    else:
        lines = ["d " + s.encode("utf-8").hex() + "\n" for s in items]
    answers, problem = run_lines(["node", str(NODE_ORACLE)], lines)
    if problem or len(answers) != len(items):
        raise RuntimeError(f"Node oracle: {problem or 'wrong number of answers'}")
    return [unwrap(kind, a) for a in answers]


def unwrap(kind, answer):
    """An oracle's answer: the output, or None when it failed."""
    if not answer.startswith("OK"):
        return None
    payload = answer[3:]
    if kind == "e":
        return bytes.fromhex(payload).decode("utf-8")
    return parse_cps(payload)


def python_encode(cps):
    try:
        return "".join(map(chr, cps)).encode("punycode").decode("ascii")
    except (UnicodeError, ValueError):
        return None


def python_decode(s):
    try:
        return [ord(c) for c in s.encode("utf-8").decode("punycode")]
    except (UnicodeError, ValueError):
        return None


class Idn2:
    def __init__(self):
        path = ctypes.util.find_library("idn2")
        if path is None:
            raise OSError("no libidn2")
        lib = ctypes.CDLL(path)
        lib.idn2_check_version.restype = ctypes.c_char_p
        self.version = lib.idn2_check_version(None).decode()
        self.dec = lib.idn2_punycode_decode
        self.dec.argtypes = [ctypes.c_char_p, ctypes.c_size_t, ctypes.POINTER(ctypes.c_uint32),
                             ctypes.POINTER(ctypes.c_size_t)]
        self.enc = lib.idn2_punycode_encode
        self.enc.argtypes = [ctypes.POINTER(ctypes.c_uint32), ctypes.c_size_t, ctypes.c_char_p,
                             ctypes.POINTER(ctypes.c_size_t)]

    def encode(self, cps):
        arr = (ctypes.c_uint32 * (len(cps) + 1))(*cps)
        cap = 16 * len(cps) + 64
        buf = ctypes.create_string_buffer(cap)
        n = ctypes.c_size_t(cap)
        if self.enc(arr, len(cps), buf, ctypes.byref(n)) != 0:
            return None
        return buf.raw[:n.value].decode("latin-1")

    def decode(self, s):
        b = s.encode("utf-8")
        out = (ctypes.c_uint32 * (len(b) + 1))()
        n = ctypes.c_size_t(len(b) + 1)
        if self.dec(b, len(b), out, ctypes.byref(n)) != 0:
            return None
        return [out[j] for j in range(n.value)]


# ---------------------------------------------------------------------
# Why an oracle may differ.

BOUND = {"RFC 3492": 2 ** 32 - 1, "libidn2": 2 ** 32 - 1, "Node": 2 ** 31 - 1,
         "Python": None}


def utf16_code_points(cps):
    """The code points a UTF-16 string holds when the values `cps` are
    written into it: a high surrogate followed by a low one reads back
    as one code point."""
    units = []
    for c in cps:
        if c > 0xFFFF:
            units += [0xD800 + ((c - 0x10000) >> 10), 0xDC00 + ((c - 0x10000) & 0x3FF)]
        else:
            units.append(c)
    out, j = [], 0
    while j < len(units):
        u = units[j]
        if 0xD800 <= u <= 0xDBFF and j + 1 < len(units) and 0xDC00 <= units[j + 1] <= 0xDFFF:
            out.append(0x10000 + ((u - 0xD800) << 10) + (units[j + 1] - 0xDC00))
            j += 2
        else:
            out.append(u)
            j += 1
    return out


def decode_reason(oracle, s, lean, got, model_peak, model_why):
    """The known reason the oracle's decoding differs, or None."""
    if lean is None and got is not None and not all(scalar(c) for c in got):
        return "the oracle returns a value that is not a scalar value"
    if lean is None and got is not None and oracle == "Node" and model_why == "not a scalar value":
        raw, _, _ = model_decode(s, surrogates=True)
        if raw is not None and utf16_code_points(raw) == got:
            return "Node returns surrogates, which pair up in its UTF-16 string"
    if lean is None and got is not None and oracle == "libidn2":
        b = s.rfind("-")
        if "_" in s[b + 1:]:
            want, _, _ = model_decode(s[:b + 1] + s[b + 1:].replace("_", "a"))
            if want == got:
                return "libidn2 reads _ in the deltas as the digit a"
    if (lean is None and got is not None and oracle == "Python"
            and s.rfind("-") == 0 and model_why is not None
            and got == model_decode(s[1:], surrogates=True)[0]):
        return "Python reads a delimiter with nothing before it"
    if lean is not None and got is None and BOUND[oracle] and model_peak > BOUND[oracle]:
        return f"the oracle's integers overflow at {BOUND[oracle] + 1:,}"
    if (lean is not None and got is None and oracle == "libidn2"
            and not any(c >= 0x80 for c in lean)):
        return "libidn2 refuses a string with no deltas"
    if (lean is not None and got is None and oracle == "libidn2"
            and any(not (c.isascii() and (c.isalnum() or c in "-_")) for c in s[:s.rfind("-")])):
        return "libidn2 refuses basic code points other than letters, digits, - and _"
    return None


def encode_reason(oracle, cps, lean, got, model_peak):
    if got is None and BOUND[oracle] and model_peak > BOUND[oracle]:
        return f"the oracle's integers overflow at {BOUND[oracle] + 1:,}"
    return None


# ---------------------------------------------------------------------
# The inputs.

SAMPLES = [
    ([0x0644, 0x064A, 0x0647, 0x0645, 0x0627, 0x0628, 0x062A, 0x0643, 0x0644, 0x0645, 0x0648,
      0x0634, 0x0639, 0x0631, 0x0628, 0x064A, 0x061F], "egbpdaj6bu4bxfgehfvwxn"),
    ([0x4ED6, 0x4EEC, 0x4E3A, 0x4EC0, 0x4E48, 0x4E0D, 0x8BF4, 0x4E2D, 0x6587],
     "ihqwcrb4cv8a8dqg056pqjye"),
    ([0x4ED6, 0x5011, 0x7232, 0x4EC0, 0x9EBD, 0x4E0D, 0x8AAA, 0x4E2D, 0x6587],
     "ihqwctvzc91f659drss3x8bo0yb"),
    ([0x0050, 0x0072, 0x006F, 0x010D, 0x0070, 0x0072, 0x006F, 0x0073, 0x0074, 0x011B, 0x006E,
      0x0065, 0x006D, 0x006C, 0x0075, 0x0076, 0x00ED, 0x010D, 0x0065, 0x0073, 0x006B, 0x0079],
     "Proprostnemluvesky-uyb24dma41a"),
    ([0x05DC, 0x05DE, 0x05D4, 0x05D4, 0x05DD, 0x05E4, 0x05E9, 0x05D5, 0x05D8, 0x05DC, 0x05D0,
      0x05DE, 0x05D3, 0x05D1, 0x05E8, 0x05D9, 0x05DD, 0x05E2, 0x05D1, 0x05E8, 0x05D9, 0x05EA],
     "4dbcagdahymbxekheh6e0a7fei0b"),
    ([0x092F, 0x0939, 0x0932, 0x094B, 0x0917, 0x0939, 0x093F, 0x0928, 0x094D, 0x0926, 0x0940,
      0x0915, 0x094D, 0x092F, 0x094B, 0x0902, 0x0928, 0x0939, 0x0940, 0x0902, 0x092C, 0x094B,
      0x0932, 0x0938, 0x0915, 0x0924, 0x0947, 0x0939, 0x0948, 0x0902],
     "i1baa7eci9glrd9b2ae1bj0hfcgg6iyaf8o0a1dig0cd"),
    ([0x306A, 0x305C, 0x307F, 0x3093, 0x306A, 0x65E5, 0x672C, 0x8A9E, 0x3092, 0x8A71, 0x3057,
      0x3066, 0x304F, 0x308C, 0x306A, 0x3044, 0x306E, 0x304B],
     "n8jok5ay5dzabd5bym9f0cm5685rrjetr6pdxa"),
    ([0xC138, 0xACC4, 0xC758, 0xBAA8, 0xB4E0, 0xC0AC, 0xB78C, 0xB4E4, 0xC774, 0xD55C, 0xAD6D,
      0xC5B4, 0xB97C, 0xC774, 0xD574, 0xD55C, 0xB2E4, 0xBA74, 0xC5BC, 0xB9C8, 0xB098, 0xC88B,
      0xC744, 0xAE4C],
     "989aomsvi5e83db1d2a355cv1e0vak1dwrv93d5xbh15a0dt30a5jpsd879ccm6fea98c"),
    ([0x043F, 0x043E, 0x0447, 0x0435, 0x043C, 0x0443, 0x0436, 0x0435, 0x043E, 0x043D, 0x0438,
      0x043D, 0x0435, 0x0433, 0x043E, 0x0432, 0x043E, 0x0440, 0x044F, 0x0442, 0x043F, 0x043E,
      0x0440, 0x0443, 0x0441, 0x0441, 0x043A, 0x0438],
     "b1abfaaepdrnnbgefbaDotcwatmq2g4l"),
    ([0x0050, 0x006F, 0x0072, 0x0071, 0x0075, 0x00E9, 0x006E, 0x006F, 0x0070, 0x0075, 0x0065,
      0x0064, 0x0065, 0x006E, 0x0073, 0x0069, 0x006D, 0x0070, 0x006C, 0x0065, 0x006D, 0x0065,
      0x006E, 0x0074, 0x0065, 0x0068, 0x0061, 0x0062, 0x006C, 0x0061, 0x0072, 0x0065, 0x006E,
      0x0045, 0x0073, 0x0070, 0x0061, 0x00F1, 0x006F, 0x006C],
     "PorqunopuedensimplementehablarenEspaol-fmd56a"),
    ([0x0054, 0x1EA1, 0x0069, 0x0073, 0x0061, 0x006F, 0x0068, 0x1ECD, 0x006B, 0x0068, 0x00F4,
      0x006E, 0x0067, 0x0074, 0x0068, 0x1EC3, 0x0063, 0x0068, 0x1EC9, 0x006E, 0x00F3, 0x0069,
      0x0074, 0x0069, 0x1EBF, 0x006E, 0x0067, 0x0056, 0x0069, 0x1EC7, 0x0074],
     "TisaohkhngthchnitingVit-kjcr8268qyxafd2f1b9g"),
    ([0x0033, 0x5E74, 0x0042, 0x7D44, 0x91D1, 0x516B, 0x5148, 0x751F], "3B-ww4c5e180e575a65lsy2b"),
    ([0x5B89, 0x5BA4, 0x5948, 0x7F8E, 0x6075, 0x002D, 0x0077, 0x0069, 0x0074, 0x0068, 0x002D,
      0x0053, 0x0055, 0x0050, 0x0045, 0x0052, 0x002D, 0x004D, 0x004F, 0x004E, 0x004B, 0x0045,
      0x0059, 0x0053], "-with-SUPER-MONKEYS-pc58ag80a8qai00g7n9n"),
    ([0x0048, 0x0065, 0x006C, 0x006C, 0x006F, 0x002D, 0x0041, 0x006E, 0x006F, 0x0074, 0x0068,
      0x0065, 0x0072, 0x002D, 0x0057, 0x0061, 0x0079, 0x002D, 0x305D, 0x308C, 0x305E, 0x308C,
      0x306E, 0x5834, 0x6240], "Hello-Another-Way--fc4qua05auwb3674vfr0b"),
    ([0x3072, 0x3068, 0x3064, 0x5C4B, 0x6839, 0x306E, 0x4E0B, 0x0032], "2-u9tlzr9756bt3uc0v"),
    ([0x004D, 0x0061, 0x006A, 0x0069, 0x3067, 0x004B, 0x006F, 0x0069, 0x3059, 0x308B, 0x0035,
      0x79D2, 0x524D], "MajiKoi5-783gue6qz075azm5e"),
    ([0x30D1, 0x30D5, 0x30A3, 0x30FC, 0x0064, 0x0065, 0x30EB, 0x30F3, 0x30D0], "de-jg4avhby1noc0d"),
    ([0x305D, 0x306E, 0x30B9, 0x30D4, 0x30FC, 0x30C9, 0x3067], "d9juau41awczczp"),
    ([0x002D, 0x003E, 0x0020, 0x0024, 0x0031, 0x002E, 0x0030, 0x0030, 0x0020, 0x003C, 0x002D],
     "-> $1.00 <--"),
]

EDGE_DECODE = ["", "-", "--", "---", "-tda", "tda", "TDA", "TdA", "a", "abc-", "abc--", "a-b-",
               "ib9b", "zy0c", "0y0c", "dn32g", "en32g", "DN32G", "a-rc4g", "a-g023p",
               "ü-tda", "a b", "ab-c!", "ab-c١", "t9", "99999999999999999999",
               "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzz", "-a", "a-", "bcher-kva", "BCHER-KVA",
               "xn--bcher-kva", "a\x00-tda", "\x7f-tda", "a-\x00",
               # surrogates that pair up in UTF-16 (U+D83D U+DE00, U+DBFF U+DFFF)
               "8c9bk9h", "a-7z5g82h",
               # _ where a digit belongs
               "_", "td_", "a_b-a", "a_b-_"]

RANGES = [
    (0x20, 0x7E), (0x00, 0x1F), (0x80, 0xFF), (0x100, 0x24F), (0x370, 0x3FF), (0x400, 0x4FF),
    (0x4E00, 0x9FFF), (0xAC00, 0xD7A3), (0xD7F0, 0xD7FF), (0xE000, 0xE00F), (0xFFF0, 0xFFFF),
    (0x10000, 0x1000F), (0x1F300, 0x1FAFF), (0x10FFF0, 0x10FFFF),
]


def random_text(rng):
    n = rng.choice([0, 1, 1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 30, 40])
    if rng.random() < 0.3:  # a few ranges, as a real label would mix
        ranges = rng.sample(RANGES, rng.randint(1, 3))
    else:
        ranges = RANGES
    return [rng.randint(*rng.choice(ranges)) for _ in range(n)]


def recase(rng, s):
    b = s.rfind("-")
    head, tail = (s[:b + 1], s[b + 1:]) if b > 0 else ("", s)
    r = rng.random()
    if r < 0.5:
        return s
    if r < 0.7:
        return head + tail.upper()
    return head + "".join(c.upper() if rng.random() < 0.5 else c for c in tail)


def mutate(rng, s):
    choice = rng.randrange(9)
    if not s:
        return rng.choice(["-", "a", "9", "-a"])
    i = rng.randrange(len(s))
    if choice == 0:
        return s[:i] + rng.choice(DIGITS + "-Aü .") + s[i + 1:]
    if choice == 1:
        return s[:i] + s[i + 1:]
    if choice == 2:
        return s[:i] + rng.choice(DIGITS + "-") + s[i:]
    if choice == 3:
        return s[:i] + s[i] + s[i:]
    if choice == 4:
        return "-" + s
    if choice == 5:
        return s[:i]
    if choice == 6:
        return s + "".join(rng.choice(DIGITS) for _ in range(rng.randint(1, 8)))
    if choice == 7:
        return s.replace("-", "", 1)
    return s + "-" + rng.choice(["", "a", "tda"])


def long_texts():
    """Texts whose deltas pass 2**31 and 2**32, which some oracles
    cannot hold."""
    out = []
    for k in [500, 1000, 1500, 2000, 2500, 3000, 3500, 4000, 5000]:
        out.append([0x61] * k + [0x10FFFF])
        out.append([0x61] * k + [0x4E00, 0x10FFFF, 0x80])
    out.append([0x10FFFF] * 300)
    out.append([0x80 + j for j in range(1500)][::-1])
    return out


GRID_ALPHABET = "aZ09-.ü"


def grid(n):
    for k in range(n + 1):
        for t in itertools.product(GRID_ALPHABET, repeat=k):
            yield "".join(t)


def hexs(s):
    return s.encode("utf-8").hex()


MALFORMED = ["encode", "decode", "encode 0g", "decode 616", "decode ff", "decode c0af",
             "decode eda080", "ENCODE 61", "encode 61 62", "", "decode  61", "decode 6A"]

# The command-line modes: the arguments, the output (None: not checked),
# and the exit status.
ARGV_CASES = [
    (["encode", "bücher"], "bcher-kva\n", 0),
    (["decode", "bcher-kva"], "bücher\n", 0),
    (["decode", "BCHER-KVA"], "BüCHER\n", 0),
    (["decode", "-tda"], "", 1),
    (["decode", "td_"], "", 1),
    (["encode", ""], "\n", 0),
    ([], None, 2),
    (["frobnicate", "x"], None, 2),
]

AT_EOF = [(f"decode {hexs('tda')}", f"OK {hexs(chr(0xFC))}"),
          (f"encode {hexs(chr(0xFC))}\r\n", f"OK {hexs('tda')}"),
          (f"decode {hexs('-tda')}\r\n", "FAIL")]


def inputs(seed, count):
    """(label, kind, item): kind is "e" with a list of code points, or
    "d" with a string."""
    for cps, enc in SAMPLES:
        yield ("sample", "e", cps)
        yield ("sample", "d", enc)
        yield ("sample", "d", enc.upper() if "-" not in enc else enc)
    for s in EDGE_DECODE:
        yield ("edge", "d", s)
    for cps in [[], [0x2D], [0x10FFFF], [0xD7FF], [0xE000], [0x80], [0x7F, 0x80], [0x00],
                [0x2D, 0x2D, 0xFC], [0xFC] * 5, [0x61, 0x2D]]:
        yield ("edge", "e", cps)
    for s in grid(5):
        yield ("grid", "d", s)
    for cps in long_texts():
        yield ("long", "e", cps)
        yield ("long", "d", model_encode(cps)[0])
    rng = random.Random(seed)
    for _ in range(count):
        cps = random_text(rng)
        yield ("random", "e", cps)
        enc = model_encode(cps)[0]
        yield ("random", "d", recase(rng, enc))
        yield ("mutated", "d", mutate(rng, enc))


# ---------------------------------------------------------------------

def lean_version():
    try:
        out = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             capture_output=True, text=True, errors="backslashreplace",
                             timeout=300)
        first = out.stdout.strip().splitlines()[:1]
        return first[0] if first else "unknown"
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


def count_arg(text):
    n = int(text)
    if n < 1:
        raise argparse.ArgumentTypeError("the count must be at least 1")
    return n


def write(lines):
    RESULTS.write_text("\n".join(lines), encoding="utf-8")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261026)
    ap.add_argument("--count", type=count_arg, default=100_000)
    args = ap.parse_args()

    def give_up(why):
        write(["# Test results", "", "- Oracle: none ran", f"- Seed: {args.seed}", "- Inputs: 0",
               f"- Failures: 1 ({why})", ""])
        sys.exit(why)

    try:
        build = subprocess.run(["lake", "build", "punycode"], cwd=ROOT, capture_output=True,
                               text=True, errors="backslashreplace", timeout=BUILD_TIMEOUT)
        if build.returncode != 0:
            print(build.stdout + build.stderr)
            give_up("`lake build punycode` failed")
        build_rfc()
    except (OSError, subprocess.SubprocessError) as e:
        give_up(f"a build failed: {e}")
    try:
        idn2 = Idn2()
        node_version = subprocess.run(["node", "-e", "process.noDeprecation = true; "
                                       "console.log(process.version + ', punycode.js ' + "
                                       "require('punycode').version)"],
                                      capture_output=True, text=True).stdout.strip()
    except (OSError, AttributeError) as e:
        give_up(f"an oracle could not be loaded: {e}")

    items = list(inputs(args.seed, args.count))
    requests = [(f"encode {hexs(''.join(map(chr, x)))}" if k == "e" else f"decode {hexs(x)}")
                for _, k, x in items]
    lines = [r + ("\r\n" if i % 7 == 6 else "\n") for i, r in enumerate(requests)]
    malformed_at = len(lines)
    lines += [m + "\n" for m in MALFORMED]
    out, problem = run_lines([str(EXE), "serve"], lines)
    failures = [("(whole run)", "a clean run", problem)] if problem else []
    if len(out) != len(lines):
        failures.append(("(whole run)", f"{len(lines)} answers", f"{len(out)} answers"))
        out += [""] * (len(lines) - len(out))
    malformed_right = sum(1 for a in out[malformed_at:] if a == "error")
    if malformed_right != len(MALFORMED):
        failures.append(("malformed requests", "error for each",
                         str(out[malformed_at:])))
    eof_right = 0
    for req, want in AT_EOF:
        got, problem = run_lines([str(EXE), "serve"], [req], timeout=60)
        if got == [want] and not problem:
            eof_right += 1
        else:
            failures.append((req + " (at end of input)", want, f"{got} {problem or ''}".strip()))

    # The tool's answers, as code point lists and strings.
    lean = []
    for (label, kind, x), a in zip(items, out):
        if a.startswith("OK"):
            text = bytes.fromhex(a[3:]).decode("utf-8")
            lean.append(text if kind == "e" else [ord(c) for c in text])
        else:
            lean.append(None if a == "FAIL" else ("error", a))

    # Against the model.
    model = []
    differ_model = 0
    for (label, kind, x), got in zip(items, lean):
        if kind == "e":
            want, peak = model_encode(x)
            model.append((want, None, peak))
        else:
            want, why, peak = model_decode(x)
            model.append((want, why, peak))
        if got != want:
            differ_model += 1
            failures.append((f"{'encode' if kind == 'e' else 'decode'} {x!r}"[:160],
                             repr(want)[:120], repr(got)[:120]))

    # The round trip, as a check of the tool on its own encodings: each
    # string the tool wrote is sent back to it to decode.
    encoded = [(x, got) for (label, kind, x), got in zip(items, lean)
               if kind == "e" and isinstance(got, str)]
    back, problem = run_lines([str(EXE), "serve"], [f"decode {hexs(t)}\n" for _, t in encoded])
    if problem or len(back) != len(encoded):
        failures.append(("(round trip run)", f"{len(encoded)} answers", f"{len(back)} {problem or ''}"))
    round_trips = 0
    for (x, t), a in zip(encoded, back):
        if a.startswith("OK") and [ord(c) for c in bytes.fromhex(a[3:]).decode("utf-8")] == x:
            round_trips += 1
        else:
            failures.append((f"decode of the tool's own encoding {t!r}"[:160], repr(x)[:120], a[:120]))

    # The command-line modes other than serve.
    argv_right = 0
    for argv, want_out, want_code in ARGV_CASES:
        run = subprocess.run([str(EXE), *argv], capture_output=True, text=True, timeout=60)
        if run.returncode == want_code and (want_out is None or run.stdout == want_out):
            argv_right += 1
        else:
            failures.append((f"punycode {' '.join(argv)}", f"{want_out!r}, exit {want_code}",
                             f"{run.stdout!r}, exit {run.returncode}"))

    # Against the oracles.
    enc_items = [(i, x) for i, (_, k, x) in enumerate(items) if k == "e"]
    dec_items = [(i, x) for i, (_, k, x) in enumerate(items) if k == "d"]
    answers = {}
    try:
        answers["RFC 3492"] = dict(zip([i for i, _ in enc_items],
                                       rfc_answers("e", [x for _, x in enc_items])))
        answers["RFC 3492"].update(zip([i for i, _ in dec_items],
                                       rfc_answers("d", [x for _, x in dec_items])))
        answers["Node"] = dict(zip([i for i, _ in enc_items],
                                   node_answers("e", [x for _, x in enc_items])))
        answers["Node"].update(zip([i for i, _ in dec_items],
                                   node_answers("d", [x for _, x in dec_items])))
    except RuntimeError as e:
        give_up(str(e))
    answers["Python"] = {i: python_encode(x) for i, x in enc_items}
    answers["Python"].update({i: python_decode(x) for i, x in dec_items})
    answers["libidn2"] = {i: idn2.encode(x) for i, x in enc_items}
    answers["libidn2"].update({i: idn2.decode(x) for i, x in dec_items})

    oracles = ["RFC 3492", "Python", "Node", "libidn2"]
    agree = {o: 0 for o in oracles}
    named = {o: {} for o in oracles}
    for i, (label, kind, x) in enumerate(items):
        got = lean[i]
        want, why, peak = model[i]
        for o in oracles:
            theirs = answers[o][i]
            if theirs == got:
                agree[o] += 1
                continue
            if kind == "e":
                reason = encode_reason(o, x, got, theirs, peak)
            else:
                reason = decode_reason(o, x, got, theirs, peak, why)
            if reason is None:
                failures.append((f"{o}: {'encode' if kind == 'e' else 'decode'} {x!r}"[:160],
                                 repr(got)[:120], repr(theirs)[:120]))
            else:
                key = (reason, "encoding" if kind == "e" else "decoding")
                named[o][key] = named[o].get(key, 0) + 1

    by_label = {}
    for label, kind, _ in items:
        key = f"{label} {'encode' if kind == 'e' else 'decode'}"
        by_label[key] = by_label.get(key, 0) + 1
    decoded = sum(1 for (_, k, _), g in zip(items, lean) if k == "d" and isinstance(g, list))
    decodes = sum(1 for _, k, _ in items if k == "d")
    big = sum(1 for (_, k, _), (_, _, p) in zip(items, model) if p > 2 ** 31 - 1)

    lines = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        f"- Lean: {lean_version()}",
        "- Oracle: the model of RFC 3492, `model_encode` and `model_decode` in "
        "`tests/run_tests.py`, and the four implementations below",
        "- RFC 3492: the sample implementation of appendix C, compiled with "
        + subprocess.run(["cc", "--version"], capture_output=True, text=True)
        .stdout.splitlines()[0],
        f"- Python: the `punycode` codec of Python {platform.python_version()}",
        f"- Node: {node_version}",
        f"- libidn2: {idn2.version}",
        f"- Seed: {args.seed}",
        f"- Inputs: {len(items)}",
        "- By kind: " + ", ".join(f"{k} {v}" for k, v in sorted(by_label.items())),
        f"- Answers that differ from the model: {differ_model}",
        f"- Strings decoded: {decodes}, of which {decoded} are Punycode strings and "
        f"{decodes - decoded} are not",
        f"- Texts encoded: {len(enc_items)}",
        f"- Inputs whose processing needs a number past 2**31 - 1: {big}",
        "- Agreement with each oracle over all inputs: "
        + ", ".join(f"{o} {agree[o]} of {len(items)}" for o in oracles),
        f"- Malformed requests answered `error`: {malformed_right} of {len(MALFORMED)}",
        f"- The tool's encodings decoded back by the tool: {round_trips} of {len(encoded)}",
        f"- Command-line modes other than `serve` answered right: {argv_right} of {len(ARGV_CASES)}",
        f"- Requests ending in CR LF: every seventh, {len(requests) // 7}",
        f"- Last lines sent alone, with no LF or with CR LF, answered right: {eof_right} of "
        f"{len(AT_EOF)}",
        f"- Failures: {len(failures)}",
        "",
        "## Where the oracles differ",
        "",
        "Each disagreement is counted under the reason the model confirms.",
        "",
    ]
    for o in oracles:
        lines.append(f"### {o}")
        lines.append("")
        if not named[o]:
            lines.append("No disagreement.")
        for (reason, kind), n in sorted(named[o].items(), key=lambda kv: -kv[1]):
            lines.append(f"- {reason}, {kind}: {n}")
        lines.append("")
    if failures:
        lines += ["## Failures", ""]
        lines += [f"- `{req}`: expected `{want}`, got `{got}`" for req, want, got in failures[:50]]
        lines.append("")
    write(lines)
    print(f"{len(items)} inputs, {len(failures)} failures; results in {RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
