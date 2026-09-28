import json, math
from pathlib import Path

gamma_floor = 3.0e12
delta = 0.445
rho = complex(0.5 + delta, gamma_floor)
N = 0
radius = 2.0 ** (N + 1) + 2.0 + abs(2.0 - rho)
center = complex(1.5, gamma_floor)
jensen_radius = radius + abs(center - rho)
hscale = 2.0 * jensen_radius + abs(center) + 1.0
n = 0
while 2.0 ** (n + 4) < hscale:
    n += 1
small = math.pi ** (-0.25) * math.gamma(0.25)
tail = 2.0 / (1.0 - math.exp(-math.pi))
fixed = 2.0 * tail * (small + 1.0)
exponent = fixed + 1.0 + 2.0 * (n + 4) + (n + 4) * 2.0 ** (n + 4)
# Conservative translation only; the exact Lean expression retains ||xi(center)||.
count_bound = (exponent - math.log(1.0e-10)) / math.log(2.0)
result = {
    "record": 2121,
    "status": "HIGH-HEIGHT-OWNER-BUDGET-CRUSHES-COMPACT-LADDER",
    "gamma_floor": gamma_floor,
    "delta": delta,
    "N": N,
    "closed_ball_radius": radius,
    "nearby_anchor_re": center.real,
    "jensen_radius": jensen_radius,
    "hscale_left": hscale,
    "dyadic_rung_n": n,
    "dyadic_radius": 2.0 ** (n + 4),
    "xi_growth_exponent": exponent,
    "translation_count_bound_with_xi_norm_1e-10": count_bound,
    "compact_family_max_nodes_screened": 62,
    "bound_over_62": count_bound / 62.0,
    "source_basis": "docs/proofs/1114_IC_problem_statement.md:131-137",
    "nonclaims": [
        "parameterized upper-bound translation, not a measured zero count",
        "xi center magnitude is not a Lean numeral certificate",
        "no producer/RH claim",
    ],
}
out = Path(__file__).resolve().parents[1] / "results" / "2121_routea_high_height_owner_budget.json"
out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps(result, indent=2))
