#!/usr/bin/env python3
"""Bounded model audit; historical 2720 engine/artifacts are not modified.

Fix cell distance through a disclosed source clone. Add a two-sided tail
bound conditional on the parent's stored constants and D-table. This is
not a directed-rounding certificate or a Lean proof.
"""
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import struct
import sys
import types

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "scripts/p3_certified_strip_constants_2720.py"
OUT = ROOT / "results/2729_full_line_envelope_reaudit.json"
PINS = {"C4": 61000000., "C2": 29000000., "q": 26e-17}


def interval_distance(lo, hi, center):
    if lo > hi:
        raise ValueError("reversed cell")
    return max(lo - center, center - hi, 0)


def tail_bound(consts, D, power, T):
    """For x=|t|>=T, each term <= A_k x^(m+power-10k).

    |t-im| >= x*(1-|im|/T); each polynomial factor <=
    x*sqrt((ds/T)^2+(1+|im_w|/T)^2). Choose a nonpositive
    exponent per term and evaluate its supremum at T. Both signs covered.
    """
    total = mp.mpf(0)
    choices = []
    for c in consts:
        if T <= abs(c["im"]):
            raise ValueError("tail threshold must exceed active heights")
        m = len(c["others"])
        poly = mp.mpf(1)
        for ds, iw in c["others"]:
            poly *= mp.sqrt((ds / T) ** 2 + (1 + abs(iw) / T) ** 2)
        candidates = []
        for k, dk in D.items():
            exponent = m + power - 10 * k
            if exponent <= 0 and mp.isfinite(dk):
                seed = c["Ez"] * dk * 2 ** k / (1 - abs(c["im"]) / T) ** k
                value = c["c_abs"] * poly * seed ** 10 * T ** exponent
                value /= (2 * mp.pi) ** power
                candidates.append((value, k, exponent))
        if not candidates:
            return None, {"unbounded_envelope_degree": m + power - 10 * max(D)}
        value, k, exponent = min(candidates)
        total += value
        choices.append({"rung": k, "exponent": exponent})
    return float(total * (1 + mp.mpf("1e-12"))), choices


def main():
    source = PARENT.read_text(encoding="utf-8")
    spec = importlib.util.spec_from_file_location("legacy2729", PARENT)
    old = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(old)
    needle = 'min(abs(t_lo - cz["im"]), abs(t_hi - cz["im"]))'
    assert source.count(needle) == 1
    fixed = types.ModuleType("corrected2729")
    fixed.__file__ = str(PARENT)
    exec(compile(source.replace(needle, 'interval_distance(t_lo, t_hi, cz["im"])'),
                 str(PARENT), "exec"), fixed.__dict__)
    fixed.interval_distance = interval_distance
    checks = {}

    def check(name, condition):
        checks[name] = bool(condition)
        print(("PASS " if condition else "FAIL ") + name, flush=True)

    check("crossing_cell_distance", interval_distance(0, 1, .5) == 0)
    check("endpoint_distance", interval_distance(0, 1, 1) == 0)
    check("external_distance_both_sides", interval_distance(0, 1, 2) == 1
          and interval_distance(-1, 0, -2) == 1)
    synthetic = [{"im": mp.mpf(0), "others": [], "Ez": mp.mpf(1),
                  "c_abs": mp.mpf(1)}]
    b, _ = tail_bound(synthetic, {1: mp.mpf(1)}, 0, mp.mpf(10))
    check("tail_exact_monomial", 1024e-10 <= b <= 1024e-10 * (1 + 2e-12))
    high_degree = [dict(synthetic[0], others=[(mp.mpf(0), mp.mpf(0))] * 55)]
    b, _ = tail_bound(high_degree, {k: mp.mpf(1) for k in range(1, 5)}, 2, mp.mpf(600))
    check("reject_positive_tail_degree", b is None)
    art = json.loads((ROOT / "results/2720_p3_certified_strip_constants.json").read_text())
    row = old.Row_(old.CANDIDATES[1])
    D, _ = old.certified_D_table()
    cb = old.make_consts(row.base_nodes, [1.] * len(row.base_nodes))
    cc = old.make_consts(row.owner, row.values)
    legacy = {"C4": old.scan_channel(cb, 4, D)[1],
              "C2": old.scan_channel(cc, 2, D)[1], "q": old.q_star_at(cb, 64, D)}
    ref = art["rows"][1]["certified"]
    for key, field in [("C4", "C4_star"), ("C2", "C2_star_corr"), ("q", "q_star_T64")]:
        check("legacy_bitwise_" + key,
              struct.pack("d", legacy[key]) == struct.pack("d", ref[field]))
    if not all(checks.values()):
        OUT.write_text(json.dumps({"status": "CONTROL-FAIL", "checks": checks}, indent=2) + "\n")
        return 1
    results = {}
    for cut in [4, 12]:
        dc = {k: D[k] if k <= cut else mp.inf for k in D}
        finite = {"C4": fixed.scan_channel(cb, 4, dc)[1],
                  "C2": fixed.scan_channel(cc, 2, dc)[1], "q": fixed.q_star_at(cb, 64, dc)}
        tails, choices, global_values = {}, {}, {}
        for key, consts, power in [("C4", cb, 4), ("C2", cc, 2), ("q", cb, 0)]:
            bound, selection = tail_bound(consts, {k: D[k] for k in D if k <= cut},
                                          power, mp.mpf(old.TAIL_T))
            tails[key], choices[key] = bound, selection
            global_values[key] = None if bound is None else max(finite[key], bound)
        results[str(cut)] = {"finite": finite, "tail": tails, "tail_choices": choices,
                             "global": global_values,
                             "clears": {k: v is not None and v <= PINS[k] for k, v in global_values.items()}}
        print("rungs <= %d: %s" % (cut, json.dumps(results[str(cut)])), flush=True)
    payload = {"record": 2729, "status": "MODEL-AUDIT-COMPLETE", "checks": checks,
               "legacy": legacy, "pins": PINS, "results": results,
               "parent_sha256": hashlib.sha256(PARENT.read_bytes()).hexdigest(),
               "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               "nonclaims": ["Stored model constants and D-table are conditional inputs.",
                             "Padded mpf arithmetic is not a directed-rounding proof.",
                             "D-table endpoint sliver proof remains unaudited here.",
                             "No Lean pin or universal-rho producer is established."]}
    OUT.write_text(json.dumps(payload, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
