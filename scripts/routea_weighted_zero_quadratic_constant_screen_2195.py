"""Record 2195: candidate quadratic Laplace-constant screen.

Decision: estimate the unavoidable quantity
  sup_{sigma,t} |t/(2*pi)|^2 |laplaceAt F(sigma+i*t)|
for the same candidate owner used by records 2109/2187.  This is a lower
screen for the analytic C in the formal quadratic-decay theorem, not an
interval certificate and not a producer claim.  If it already exceeds the
candidate signed margin after the analytic multiplicity factor, the generic
global-C route is a scoped no-go for this candidate and the proof must use a
local/owner-specific enclosure.
"""

import json
import math
import os
import sys
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_completion_1980 as r80
import fourpoint_owner_density_1959 as r59
import routea_opposite_gates_height_1994 as r94
import fourpoint_offline_owner_1981 as r81

OUTPUT = ROOT / "results" / "2195_weighted_zero_quadratic_constant_screen.json"
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTA = 0.445
SCALE = 0.80
K = 30.0
M = 6400
SIGNED_MARGIN = 1675397327895.099


def owner_family():
    rho = (0.5 + DELTA) + 1j * GAMMA
    nodes, values = r94.owner_nodes_ext(rho, GAMMA)
    radius = r80.ball_radius(rho, 0)
    mp.mp.dps = 60
    for index in range(1, 31):
        height = float(mp.im(mp.zetazero(index)))
        z = 0.5 + 1j * height
        if abs(z - rho) <= radius and all(abs(z - existing) > 1e-6 for existing in nodes):
            nodes.append(z)
            values.append(0j)
    plan = {"main": 0, "real": 0}
    fam = []
    for z in nodes:
        height = float(z.imag)
        if abs(abs(height) - GAMMA) < 1e-9:
            idx = plan["main"]
            plan["main"] += 1
            width = r81.WIDTHS_H1[idx]
        elif abs(height) < 1e-9:
            idx = plan["real"]
            plan["real"] += 1
            width = r81.WIDTHS_REAL[idx]
        else:
            width = 2.2
        fam.append((SCALE * width, -height))
    return rho, nodes, values, fam


def main():
    rho, nodes, values, fam = owner_family()
    xw = [r59.phi_weights(a, panels=6, m=M) for a, _theta in fam]
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(a_mat, np.asarray(values, complex))

    # The strip variable is sampled at five real parts and a logarithmic plus
    # linear height grid.  This is intentionally a screening lower bound.
    sigmas = np.linspace(0.0, 1.0, 5)
    heights = np.unique(np.concatenate([
        np.linspace(0.0, 80.0, 801),
        np.geomspace(1.0, 2000.0, 1200),
    ]))
    points = np.concatenate([s + 1j * heights for s in sigmas])
    V = r80.family_values(fam, K, points, xw)
    transform = np.dot(base, V) * np.dot(corr, V)
    scale = (np.abs(points.imag) / (2.0 * math.pi)) ** 2
    values_screen = scale * np.abs(transform)
    i = int(np.argmax(values_screen))
    c_lower = float(values_screen[i])

    # The exact xi-growth constant contains explicit kernel/Gamma constants;
    # this mpmath value is only a scale diagnostic for the existing formula.
    try:
        xi2 = abs(float(mp.riemann_xi(2)))
        kernel_small = (1.0 / math.pi) ** 0.25 * float(mp.gamma(0.25))
        xi_tail = 2.0 / (1.0 - math.exp(-math.pi))
        xi_growth = 2.0 * xi_tail * (kernel_small + 1.0)
        mult_constant = (xi_growth + 1.0 + abs(math.log(xi2)) + 192.0) / math.log(2.0)
    except Exception:
        # mpmath in the workstation image has no riemann_xi symbol.  The
        # project normalization completedRiemannXi(2) is xi(2)=pi/6; retain
        # this as an explicitly labelled diagnostic fallback.
        xi2 = math.pi / 6.0
        kernel_small = (1.0 / math.pi) ** 0.25 * math.gamma(0.25)
        xi_tail = 2.0 / (1.0 - math.exp(-math.pi))
        xi_growth = 2.0 * xi_tail * (kernel_small + 1.0)
        mult_constant = (xi_growth + 1.0 + abs(math.log(xi2)) + 192.0) / math.log(2.0)

    # Since B = (2*pi)^2 C in the formal shell estimate, this is the
    # candidate lower-screen for the tail budget 4*M*B.
    b_lower = (2.0 * math.pi) ** 2 * c_lower
    tail_lower = 4.0 * mult_constant * b_lower
    result = {
        "record": 2195,
        "status": "CANDIDATE-LOWER-SCREEN",
        "owner": {"gamma": GAMMA, "delta": DELTA, "scale": SCALE,
                  "nodes": len(nodes), "support": 2 * max(a for a, _ in fam)},
        "grid": {"sigma_count": len(sigmas), "height_count": len(heights),
                 "max_height": float(max(heights))},
        "screen": {"C_lower": c_lower, "B_lower": b_lower,
                   "spectralMultiplicityConstant_proxy": mult_constant,
                   "high_shell_budget_lower": tail_lower,
                   "signed_margin_anchor": SIGNED_MARGIN,
                   "tail_lower_over_margin": tail_lower / SIGNED_MARGIN},
        "argmax": {"sigma": float(points[i].real), "height": float(points[i].imag)},
        "nonclaims": [
            "sampled grid is not a supremum certificate",
            "stored quadrature and solve are not interval enclosed",
            "multiplicity constant proxy is diagnostic only",
            "no producer theorem or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "owner_source": "scripts/routea_weighted_zero_measure_screen_2187.py"},
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
