import json
import math
from pathlib import Path

record = 2120
gamma = 39.25244858548658
delta = 0.445
rho = complex(0.5 + delta, gamma)
N = 0
R = 2.0 ** (N + 1) + 2.0 + abs(2.0 - rho)
small = math.pi ** -0.25 * math.gamma(0.25)
tail = 2.0 / (1.0 - math.exp(-math.pi))
fixed = 2.0 * tail * (small + 1.0)
rows = []
for center_re in [1.0, 1.1, 1.2, 1.3, 1.4, 1.5]:
    center = complex(center_re, gamma)
    A = R + abs(center - rho)
    hscale_left = 2.0 * A + abs(center) + 1.0
    n = 0
    while 2.0 ** (n + 4) < hscale_left:
        n += 1
    G = fixed + 1.0 + 2.0 * (n + 4) + (n + 4) * 2.0 ** (n + 4)
    # Standard xi normalization used only to translate the exact Lean expression.
    s = center
    zeta = complex(__import__('mpmath').zeta(s))
    import mpmath as mp
    xi_abs = abs(0.5 * s * (s - 1.0) * math.pi ** (-s.real / 2.0) *
                 complex(mp.power(mp.pi, -s / 2.0)) / (math.pi ** (-s.real / 2.0)) *
                 complex(mp.gamma(s / 2.0)) * zeta)
    bound = (G - math.log(xi_abs)) / math.log(2.0)
    rows.append({"center_re": center_re, "distance_center_rho": abs(center-rho),
                 "radius_for_jensen": A, "dyadic_rung_n": n,
                 "xi_abs_numeric": xi_abs, "source_owner_bound_numeric": bound})
result = {"record": record, "status": "NEARBY_ZERO_FREE_ANCHOR-IMPROVES-BUT-NOT-GO",
          "rho": [rho.real, rho.imag], "closed_ball_radius": R,
          "rows": rows, "best_screened_row": min(rows, key=lambda x: x["source_owner_bound_numeric"]),
          "compact_family_max_nodes_screened": 62,
          "formal_theorem": "sourceNontrivialZerosInClosedBall_ncard_le_dyadic_xi_growth_at_center",
          "nonclaims": ["xi values are numerical translations, not Lean numeral certificates",
                        "no measured zero count claim", "no producer/RH claim"]}
out = Path(__file__).resolve().parents[1] / "results" / "2120_routea_nearby_anchor_cardinality_screen.json"
out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps(result, indent=2))
