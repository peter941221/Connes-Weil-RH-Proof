import json
import math
import os
import sys
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_completion_1980 as r80
import routea_opposite_gates_height_1994 as r94

OUTPUT = ROOT / "results" / "2100_truncated_zero_owner_audit.json"
DELTA = 0.15
FIRST_ZERO_COUNT = 30
GAMMAS = (
    r94.G7,
    (r94.G7 + r94.G8) / 2.0,
    r94.G8,
    48.005150881167159,
)


def main():
    mp.mp.dps = 50
    zero_heights = [float(mp.im(mp.zetazero(index)))
                    for index in range(1, FIRST_ZERO_COUNT + 1)]
    rows = []
    for gamma in GAMMAS:
        rho = (0.5 + DELTA) + 1j * gamma
        radius = r80.ball_radius(rho, 0)
        listed = [height for height in r94.GAMMAS_EXT
                  if abs((0.5 + 1j * height) - rho) <= radius
                  and abs(height - gamma) > 1e-9]
        in_ball = [(index, height) for index, height in enumerate(zero_heights, 1)
                   if abs((0.5 + 1j * height) - rho) <= radius]
        omitted = [(index, height) for index, height in in_ball
                   if all(abs(height - listed_height) > 1e-6
                          for listed_height in r94.GAMMAS_EXT)
                   and abs(height - gamma) > 1e-6]
        nodes, _values = r94.owner_nodes_ext(rho, gamma)
        row = {
            "gamma": gamma,
            "delta": DELTA,
            "radius": radius,
            "upper_ordinate": gamma + radius,
            "listed_ball_zeros": len(listed),
            "computed_ball_zeros_first_30": len(in_ball),
            "omitted_distinct_from_gamma": [
                {"index": index, "height": height} for index, height in omitted
            ],
            "surrogate_nodes": len(nodes),
            "minimum_nodes_if_omitted_zeros_added": len(nodes) + len(omitted),
        }
        rows.append(row)
        print(json.dumps(row), flush=True)
    assert len(rows[1]["omitted_distinct_from_gamma"]) == 12
    assert rows[1]["surrogate_nodes"] == 18
    result = {
        "record": 2100,
        "status": "TRUNCATED-ZERO-OWNER-NO-GO-FOR-COVER-INFERENCE",
        "owner_formula": "healthyCorrectionNodes rho 0 empty: closed-ball zeros union orbit/real target nodes",
        "source_zero_sample": "mpmath.zetazero(1..30), 50-digit computation cast to float",
        "registered_list": "routea_opposite_gates_height_1994.GAMMAS_EXT",
        "rows": rows,
        "nonclaims": [
            "mpmath zeros are numerical diagnostics, not Lean-certified zeros",
            "the first-30 list is a lower bound on missing nodes, not a complete actual owner",
            "no cellwise COVER or producer theorem is established",
            "the no-go is only for inference from the truncated list, not Route A globally",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "owner_source": "ConnesWeilRH/Dev/C1ExplicitHealthyCorrectionBudget.lean",
            "truncated_list_source": "scripts/routea_opposite_gates_height_1994.py",
            "numerical_library": "mpmath " + mp.__version__,
        },
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps({"record": 2100, "omitted_counts":
                      [len(row["omitted_distinct_from_gamma"]) for row in rows]}))


if __name__ == "__main__":
    main()
