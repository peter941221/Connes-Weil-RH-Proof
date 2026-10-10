#!/usr/bin/env python3
"""Record-2663 slot extractor / generator for the 190-panel 2662 instances.

Reads the COMMITTED Lean literals (no float display text) for a panel tag and
returns every numeric slot the record-2662 instance template needs:

  - the analytic residual exponential literal spelling (N/D or 2*(N/D)),
    rationalized exponent n = ceil(eE) for the `3^n` upper bound;
  - the squared-deficit literal (K/L)^2 of the record-2656 module;
  - amp/phase pin literal sanity data (ampValue may be 0 on boundary panels);
  - the table-module and analytic-module names (k = 109 is special-cased by
    the committed naming).
  - the string fraction "E, F/100" fragments used to fill the target text.

`--check k [k ...]` prints the slots; `--emit` writes the panel modules.
"""

import json
import os
import re
import sys
from fractions import Fraction as F

sys.set_int_max_str_digits(200000)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEV = os.path.join(ROOT, "ConnesWeilRH", "Dev")

RAT_ASCRIBED = re.compile(r"\(\s*(-?\d+)\s*:\s*[ℚℝ]\s*\)\s*/\s*(\d+)")
RAT_PLAIN = re.compile(r"(-?\d+)\s*/\s*(\d+)")


def read(name):
    with open(os.path.join(DEV, name), encoding="utf-8") as fh:
        return fh.read()


def exists(name):
    return os.path.exists(os.path.join(DEV, name))


def def_body(text, name):
    m = re.search(
        r"^(?:noncomputable )?def " + re.escape(name)
        + r"\b[^\n]*?:=\s*(.*?)(?=\n\s*\n|\n/--|\n(?:noncomputable )?def "
        r"|\ntheorem |\n#print )", text, re.M | re.S)
    if not m:
        raise KeyError(name)
    return m.group(1)


def body_rats(body):
    out = [F(int(a), int(b)) for a, b in RAT_ASCRIBED.findall(body)]
    if not out:
        out = [F(int(a), int(b)) for a, b in RAT_PLAIN.findall(body)]
    return out


def rats(text, name):
    return body_rats(def_body(text, name))


def pair(text, name):
    r = rats(text, name)
    if len(r) < 2:
        raise ValueError(f"{name}: expected a rational pair, got {r}")
    return (r[0], r[1])


VAR_STRICT = re.compile(
    r"Real\.exp \(2 \* \(\((\d+)\s*/\s*(\d+)\)\s*:\s*[ℝℚ]\)\)")
VAR_PLAIN = re.compile(r"Real\.exp \((\d+)\s*/\s*(\d+)\)")


def eE_spelling(text):
    """(value, def_body) of the analytic exponential argument as spelled in
    the committed certificate."""
    ms = VAR_STRICT.search(text)
    if ms:
        val = 2 * F(int(ms.group(1)), int(ms.group(2)))
        return val, f"2 * (({ms.group(1)} / {ms.group(2)}) : ℝ)"
    ms = VAR_PLAIN.search(text)
    if ms:
        return F(int(ms.group(1)), int(ms.group(2))), \
            f"(({ms.group(1)} / {ms.group(2)}) : ℝ)"
    raise ValueError("no eE literal")


def ceil_frac(x: F) -> int:
    return -((-x.numerator) // x.denominator)


def slots(k):
    tag = f"{k:03d}"
    amp = read(f"C1RouteAAmpPin2657P{tag}.lean")
    ph = read(f"C1RouteAPhasePin2658P{tag}.lean")
    tb_name = f"C1RouteAComplexPanelTable2655P{tag}.lean"
    if not exists(tb_name):
        tb_name = f"C1RouteAComplexPanelTable2648P{tag}.lean"
    tb = read(tb_name)
    an_name = (f"C1RouteAComplexPanelAnalytic2649P109.lean" if k == 109
               else f"C1RouteAComplexPanelAnalytic2656P{tag}.lean")
    an = read(an_name)
    eE, eE_body = eE_spelling(an)
    deficit = None
    # 2656 spelling: (((K / L) : ℚ) ^ 2);  2649 spelling: (((K : ℚ) / L) ^ 2)
    for pat in (r"\(\(\((\d+)\s*/\s*(\d+)\)\s*:\s*[ℚℝ]\)\s*\^\s*2\)",
                r"\(\(\((\d+)\s*:\s*[ℚℝ]\)\s*/\s*(\d+)\)\s*\^\s*2\)"):
        m = re.search(pat, an)
        if m:
            deficit = (int(m.group(1)), int(m.group(2)))
            break
    return dict(
        k=k, tag=tag, amp_module=f"C1RouteAAmpPin2657P{tag}",
        phase_module=f"C1RouteAPhasePin2658P{tag}", table_module=tb_name,
        analytic_module=an_name,
        center=rats(tb, f"complexPanelCenter2648P{tag}")[0],
        amp_val=rats(amp, f"ampValue2657P{tag}")[0],
        amp_rad=rats(amp, f"ampRadius2657P{tag}")[0],
        ph_rad=rats(ph, f"phaseRadius2658P{tag}")[0],
        eE=eE, n=ceil_frac(eE), eE_body=eE_body,
        deficit=deficit,
        has_sup=re.search(r"supArg2657P" + tag, amp) is not None,
    )


def main():
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    args = sys.argv[1:]
    ks = [int(a) for a in args] or [0, 94, 95, 109, 189]
    rows = []
    for k in ks:
        s = slots(k)
        rows.append(s)
        print(json.dumps({kk: (str(vv) if isinstance(vv, F) else vv)
                          for kk, vv in s.items()}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())