import json
import math
from pathlib import Path

record = 2119
gamma = 39.25244858548658
delta = 0.445
n_shell = 0
rho = complex(0.5 + delta, gamma)
distance = abs(2.0 - rho)
ball_radius = 2.0 ** (n_shell + 1) + 2.0 + distance
height_proxy = ball_radius + distance
hscale_left = 2.0 * height_proxy + 7.0
n_dyadic = 0
while 2.0 ** (n_dyadic + 4) < hscale_left:
    n_dyadic += 1
small = (1.0 / math.pi) ** 0.25 * math.gamma(0.25)
tail = 2.0 / (1.0 - math.exp(-math.pi))
fixed = 2.0 * tail * (small + 1.0)
G = fixed + 1.0 + 2.0 * (n_dyadic + 4) + (n_dyadic + 4) * 2.0 ** (n_dyadic + 4)
xi_two = math.pi / 6.0
source_bound = (G - math.log(xi_two)) / math.log(2.0)
result = {
    "record": record,
    "status": "FORMAL-OWNER-COUNT-BRIDGE-NUMERIC-TRANSLATION",
    "rho": [rho.real, rho.imag],
    "delta": delta,
    "n_shell": n_shell,
    "distance_two_rho": distance,
    "closed_ball_radius": ball_radius,
    "symmetric_height_proxy": height_proxy,
    "hscale_left": hscale_left,
    "dyadic_rung_n": n_dyadic,
    "dyadic_radius": 2.0 ** (n_dyadic + 4),
    "xi_growth_fixed_constant": fixed,
    "xi_growth_exponent": G,
    "xi_two_numeric_normalization": xi_two,
    "source_owner_ncard_upper_bound_numeric": source_bound,
    "compact_family_max_nodes_screened": 62,
    "gap_factor_vs_62_nodes": source_bound / 62.0,
    "formal_theorem": "ConnesWeilRH.Source.C1RouteAOwnerCardinality.sourceNontrivialZerosInClosedBall_ncard_le_dyadic_xi_growth",
    "nonclaims": [
        "the numeric xi(2)=pi/6 translation is not itself a Lean numeral certificate",
        "no claim that the owner has this many zeros",
        "no producer theorem or RH claim",
    ],
}
output = Path(__file__).resolve().parents[1] / "results" / "2119_routea_formal_owner_cardinality_bound.json"
output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps(result, indent=2))
