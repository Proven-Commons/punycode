#!/usr/bin/env python3
"""Check that the differential tests catch planted bugs.

Each bug is a one-line change to Hostname/Basic.lean. The script
copies the project to a temporary folder, plants one bug at a time,
runs tests/run_tests.py there with a small count, and records how many
failures the tests report. Every planted bug must give at least one.
The unchanged copy must give none. Each bug also breaks a proof, so
`lake build` of the whole project fails with it in place; the tests
build only the executable, so they run.

    python3 tests/plant_bugs.py [--count N]

The script writes tests/PLANTED-BUGS.md and exits non-zero if any bug
goes uncaught.
"""

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "tests" / "PLANTED-BUGS.md"
CODE = "Punycode/Basic.lean"

# (what the bug does, the line as written, the line with the bug)
BUGS = [
    ("tmin is 2, not 1",
     "def tmin : Nat := 1",
     "def tmin : Nat := 2"),
    ("bias adaptation ignores the first delta",
     "let delta := if firsttime then delta / damp else delta / 2",
     "let delta := delta / 2"),
    ("the digits 0 to 9 are worth one less",
     "else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat + 26)",
     "else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat + 25)"),
    ("a delimiter with nothing before it is read as one",
     "  | some (c :: before, after) => (c :: before, after)",
     "  | some (before, after) => (before, after)"),
    ("surrogates are decoded",
     "if 0xD800 ≤ n + i' / (out.length + 1) ∧ n + i' / (out.length + 1) ≤ 0xDFFF then none",
     "if 0xD800 ≤ n + i' / (out.length + 1) ∧ n + i' / (out.length + 1) ≤ 0xD7FF then none"),
    ("code points past U+10FFFF are let through the limit",
     "match h : decodeInt bias ((0x110000 - n) * (out.length + 1) - 1) (c :: cs) i 1 base with",
     "match h : decodeInt bias ((0x110100 - n) * (out.length + 1) - 1) (c :: cs) i 1 base with"),
    ("code points outside ASCII are let into the literal portion",
     "if (splitLiteral s.toList).1.all isBasic then",
     "if true then"),
    ("equal code points are inserted from the first occurrence",
     "| c :: cs, j, (v, p) => if v ≤ c.toNat then maxPos cs (j + 1) (c.toNat, j)",
     "| c :: cs, j, (v, p) => if v < c.toNat then maxPos cs (j + 1) (c.toNat, j)"),
    ("a delta counts one state change too few",
     "(n * (b + j + 1) + i - (pn * (b + j + 1) + pi)) :: deltas b n (i + 1) (j + 1) rest",
     "(n * (b + j + 1) + i - (pn * (b + j + 1) + pi + 1)) :: deltas b n (i + 1) (j + 1) rest"),
    ("the encoder adapts the bias with one code point too few",
     "encodeInt bias d base ++ encodeDeltas b (adapt d (b + j + 1) first) false (j + 1) ds",
     "encodeInt bias d base ++ encodeDeltas b (adapt d (b + j) first) false (j + 1) ds"),
]


def failures(copy, count):
    run = subprocess.run([sys.executable, "tests/run_tests.py", "--count", str(count)],
                         cwd=copy, capture_output=True, text=True)
    text = (copy / "tests" / "TEST-RESULTS.md").read_text(encoding="utf-8")
    m = re.search(r"^- Failures: (\d+)(.*)$", text, re.M)
    if m is None or "build" in m.group(2):
        return None, run.stdout + run.stderr  # the bug did not build: not a catch
    return int(m.group(1)), None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=2000)
    args = ap.parse_args()
    rows, missed = [], 0
    with tempfile.TemporaryDirectory() as tmp:
        copy = Path(tmp) / "hostname"
        shutil.copytree(ROOT, copy, symlinks=True,
                        ignore=shutil.ignore_patterns("PLANTED-BUGS.md", "oracle-venv"))
        code = copy / CODE
        original = code.read_text(encoding="utf-8")
        n, err = failures(copy, args.count)
        rows.append(("none", n))
        if n != 0:
            missed += 1
        for what, line, bug in BUGS:
            if original.count(line) != 1:
                sys.exit(f"{CODE} no longer holds, once, the line for {what!r}: {line}")
            code.write_text(original.replace(line, bug), encoding="utf-8")
            n, err = failures(copy, args.count)
            code.write_text(original, encoding="utf-8")
            rows.append((what, n))
            if not n:
                missed += 1
            print(f"{what}: {n} failures" + (" (did not build)" if err else ""))
    lines = ["# Planted bugs", "",
             "Written by `tests/plant_bugs.py`. Each bug is a one-line change to "
             f"`{CODE}`, tested with `tests/run_tests.py --count {args.count}`. "
             "Every bug must give failures, and the unchanged code none.", "",
             "| Planted bug | Failures |", "|---|---|"]
    lines += [f"| {what} | {'did not build' if n is None else n} |" for what, n in rows]
    lines += ["", f"Bugs caught: {sum(1 for what, n in rows[1:] if n)} of {len(BUGS)}", ""]
    RECORD.write_text("\n".join(lines), encoding="utf-8")
    return 1 if missed else 0


if __name__ == "__main__":
    sys.exit(main())
