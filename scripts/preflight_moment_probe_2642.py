#!/usr/bin/env python3
"""Generic mechanical preflight for the moment-diagonal probes
ZProbe2628K{dd}.lean (records 2636-2644 campaign).

Checks, per owner d:
  1. the verbatim def `entry{dd}Interval2628` token stream (paren- and
     ascription-insensitive) equals row_d element d of the committed
     2597 table (the entry-(d, d) analytic interval);
  2. every rfl succ-chain site (entry_eq + four support theorems)
     carries exactly the expected `(Fin.succ)^d 0` chain, twice;
  3. the four per-field rfl bridges (hreLo / hreHi / imLo / imHi) quote
     the matching element field;
  4. the capstone `actualOwnerMomentMatrix2351_entry{dd}_mem2628`
     is present;
  5. the edge ref `actualMomentEntry{dd}_bothEdgeCharge_le2620`
     occurs exactly once;
  6. the theorem census is 213.

Spelling differences (extra parens, `(NUM : ℝ)` ascriptions) are
cosmetic and policed by kernel rfl at build time (AGENTS 2ce law), so
all comparisons run on normalized token streams.

Usage: python scripts/preflight_moment_probe_2642.py 26 27 28 29
Exit code 0 iff every requested probe passes every check.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH" / "Dev"
TABLE = DEV / "C1RouteACorrectionAnalyticIntervals2597.lean"


def normalize(text: str) -> str:
    """Paren-insensitive canonical token stream (AGENTS 2ce).

    Replaces every `(NUM : ℝ)` numeric ascription by the placeholder
    NUM first, then strips all parentheses and whitespace.
    """
    text = re.sub(r"\(\s*(-?[0-9]+)\s*:\s*ℝ\s*\)", r"NUM\1NUM", text)
    return re.sub(r"[()\s]", "", text)


def row_blocks(d: int) -> list[str]:
    """The 30 top-level `{...}` elements of `analyticMomentInterval2597_row_{d}`."""
    src = TABLE.read_text(encoding="utf-8")
    name = f"analyticMomentInterval2597_row_{d:02d}"
    start = src.index(f"{name} :")
    end = len(src) if d == 29 else src.index(f"analyticMomentInterval2597_row_{d + 1:02d}", start)
    row = src[start:end]
    body_at = row.index("![")
    blocks: list[str] = []
    depth = 0
    open_at = None
    for k in range(body_at, len(row)):
        ch = row[k]
        if ch == "{":
            if depth == 0:
                open_at = k
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                blocks.append(row[open_at:k + 1])
    if len(blocks) != 30:
        raise SystemExit(f"{name}: expected 30 elements, found {len(blocks)}")
    return blocks


def field(block: str, name: str) -> str:
    """One field's value text from a `{ reLo := ..., ... }` element."""
    match = re.search(rf"{name} := (.*?),", block, re.S)
    if match is None:  # last field has no trailing comma
        match = re.search(rf"{name} := (.*?)\s*\}}\s*$", block, re.S)
    if match is None:
        raise SystemExit(f"field {name} not found in element")
    return match.group(1)


def slice_at(probe: str, start_pat: str, end_pat: str) -> str:
    begin = re.search(start_pat, probe)
    if begin is None:
        raise SystemExit(f"pattern not found: {start_pat!r}")
    tail = probe[begin.start():]
    stop = re.search(end_pat, tail)
    if stop is None:
        raise SystemExit(f"pattern not found: {end_pat!r}")
    return tail[:stop.end()]


def check_probe(d: int) -> list[str]:
    dd = f"{d:02d}"
    tag = f"K{dd}"
    failures: list[str] = []
    blocks = row_blocks(d)
    element = blocks[d]
    probe = (DEV / f"ZProbe2628{tag}.lean").read_text(encoding="utf-8")

    # 1. verbatim def vs row element d
    def_text = slice_at(
        probe,
        rf"noncomputable def entry{dd}Interval2628 : ComplexRect2427 :=",
        r"\n\n",
    )
    def_text = def_text[def_text.index("\n") + 1:]
    if normalize(def_text) != normalize(element):
        failures.append("verbatim def != row element (normalized)")

    # 2. succ-chain sites (owner 0 peels by rfl with no chain)
    chain = "Fin.succ" * d + "0"
    sites = [("entry_eq", slice_at(probe, rf"theorem entry{dd}Interval2628_eq :", r":= rfl"))]
    for sup in ("marginLo", "marginHi", "imLo_nonpos", "imHi_nonneg"):
        sites.append((sup, slice_at(
            probe,
            rf"have hsucc : \(analyticMomentInterval2597 {d} {d}\) =",
            r":= rfl",
        )))
    for label, seg in sites:
        got = normalize(seg)
        want = re.sub(r"[()\s]", "", chain)
        if d == 0:
            continue  # no hsucc bridge at owner 0 (record-2618 head peel)
        if got.count(want) != 2:
            failures.append(f"{label}: succ-chain count {got.count(want)} != 2")

    # 3. per-field rfl bridges
    bridge_of = {
        "reLo": r"have hreLo :",
        "reHi": r"have hreHi :",
        "imLo": r"have himLo :",
        "imHi": r"have himHi :",
    }
    for name, pat in bridge_of.items():
        seg = slice_at(probe, pat, r":= rfl")
        want = normalize(field(element, name))
        got = normalize(seg)
        if want not in got:
            failures.append(f"bridge {name}: field value mismatch")

    # 4. capstone
    if f"theorem actualOwnerMomentMatrix2351_entry{dd}_mem2628" not in probe:
        failures.append("capstone theorem missing")

    # 5. edge ref exactly once (either digit spelling — same string for d >= 10)
    edge_names = {
        f"actualMomentEntry{d}_bothEdgeCharge_le2620",
        f"actualMomentEntry{dd}_bothEdgeCharge_le2620",
    }
    edge_total = sum(probe.count(name) for name in edge_names)
    if edge_total != 1:
        failures.append(f"edge ref count {edge_total} != 1")

    # 6. theorem census (pipeline convention: unanchored, private included)
    census = len(re.findall(r"(?:private )?theorem ", probe))
    if census != 213:
        failures.append(f"theorem census {census} != 213")

    return failures


def main() -> None:
    owners = [int(a) for a in sys.argv[1:]] or list(range(30))
    all_ok = True
    for d in owners:
        failures = check_probe(d)
        status = "PASS" if not failures else "FAIL"
        print(f"K{d:02d}: {status}")
        for failure in failures:
            print(f"  - {failure}")
        all_ok = all_ok and not failures
    raise SystemExit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
