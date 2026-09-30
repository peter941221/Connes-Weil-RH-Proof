#!/usr/bin/env python3
"""2270 - Exact middle-k enumeration for the two open rows (reserve item).

Record 2266 closed the two ends exactly (k <= 6 and k >= 24) and bracketed
the middle with certified ceilings plus 1-swap lower bounds.  The two open
rows are decided in the middle: corr_M0 at k = 8 (bracket
[6.1624990602415091, 6.1654080613840732], rel width 4.72e-4) and corr_D2 at
k = 7 ([6.0894516916697183, 6.0917247299667272], 3.73e-4).  This reserve
driver enumerates those two k's exhaustively on the committed float64
machinery of 2266 (index tables shared by fork, chunked matmul), replacing
the climb lower bounds at the deciding k by exact maxima.

Run: python3 script.py
Writes results/2270_middle_exact.json.  This is a float64 deepening of the
2266 brackets; the directed-MPFR certification of the same quantities is
record 2269, and a revived count side consumes the certified bracket, not
this one.
"""
import itertools
import json
import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_weighted_zero_direct_product_outward_2234 as o34  # noqa: E402  # pyright: ignore[reportMissingImports]
import routea_weighted_zero_cancellation_split_2258 as c58  # noqa: E402  # pyright: ignore[reportMissingImports]
import routea_weighted_zero_hall_exact_2266 as h66  # noqa: E402  # pyright: ignore[reportMissingImports]

R = ROOT / "results"
ANCHOR_2266 = R / "2266_hall_exact.json"
OUTPUT = R / "2270_middle_exact.json"
JOBS = (("corr_M0", 8), ("corr_D2", 7))


def main():
    t0 = time.time()
    rec66 = json.loads(ANCHOR_2266.read_text(encoding="utf-8"))
    fam, base, corr, a_max = o34.build_construction()
    x = np.linspace(-a_max, a_max, h66.NX)
    wgt = c58.trap_weights(x, a_max)
    coef_of = {"corr_M0": corr, "corr_D2": corr}
    kind_of = {"corr_M0": "M0", "corr_D2": "D2"}
    out = {"record": 2270, "jobs": {}}
    for row, k in JOBS:
        tr = time.time()
        M, AG, S = h66.row_arrays(fam, coef_of[row], kind_of[row], x)
        c = AG - S
        row_norm = float(np.sum(wgt * AG))
        comb = np.asarray(list(itertools.combinations(range(h66.NFAM), k)),
                          dtype=np.int32)
        h66._G.update(M=M, c=c, wgt=wgt, S=S, COMB={k: comb})
        hall, combo = h66.exhaustive(k, "in")
        del comb, h66._G["COMB"]
        rec_row = rec66["rows"][row]
        ratio = h66.BUDGET_DENOM * hall / (k * row_norm)
        out["jobs"][row] = {
            "k": k, "hall_exact": hall, "witness": list(combo),
            "ratio": ratio, "row_norm": row_norm,
            "bracket_2266": [rec_row["t_star_lo"], rec_row["t_star_hi"]],
            "k_star_2266": rec_row["k_star_lo"],
            "width_rel_before": ((rec_row["t_star_hi"]
                                  - rec_row["t_star_lo"])
                                 / rec_row["t_star_lo"]),
            "wall_seconds": time.time() - tr,
        }
        print(f"[{row}] k={k} exact hall {hall!r} ratio {ratio!r} "
              f"({time.time()-tr:.0f}s)", flush=True)
    out["wall_seconds_total"] = time.time() - t0
    out["nonclaims"] = [
        "float64 enumeration on the committed 2197/2258 grid; the exact "
        "maxima at these two k's are exact in the enumeration sense only, "
        "the arithmetic is float64",
        "the middle ceiling upper ends of 2266 are unchanged; this record "
        "only lifts the lower end at the deciding k",
        "certified-grade brackets of the same quantities are record 2269 "
        "(directed MPFR); no producer GO, no gate sign change, no RH claim",
    ]
    OUTPUT.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    print(json.dumps({r: {kk: v[kk] for kk in
                          ("k", "hall_exact", "ratio", "width_rel_before")}
                      for r, v in out["jobs"].items()}, indent=2), flush=True)


if __name__ == "__main__":
    main()