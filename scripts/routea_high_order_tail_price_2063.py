import json
import math
import os
import sys
import time
from pathlib import Path
from mpmath import mp
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_completion_1980 as r80
import fourpoint_owner_density_1959 as r59
import routea_g8h_basis_comparison_2037 as r37
import routea_health_cone_2006 as r06
import routea_opposite_gates_height_1994 as r94

mp.dps = 32
K = 30
RMAX = 48
SAFETY = 100.0
X0 = 160.0
OUTPUT = ROOT / "results" / "2063_route_a_high_order_tail_price.json"


def derivative_terms(n):
    terms = {(0, 0, 0): mp.mpf(1)}
    for _ in range(n):
        out = {}
        for (a, b, p), c in terms.items():
            if a >= 1:
                out[(a - 1, b, p)] = out.get((a - 1, b, p), 0) + c * a
            if b >= 1:
                out[(a + 1, b + 1, p)] = out.get((a + 1, b + 1, p), 0) + c * 2 * b
            out[(a + 1, b + 2, p + 1)] = out.get((a + 1, b + 2, p + 1), 0) - 2 * c
        terms = {key: value for key, value in out.items() if value}
    return terms


def total_variation(n):
    terms = derivative_terms(n)
    def f(u):
        u = mp.mpf(u)
        s = 1 - u * u
        if abs(u) >= 1 or s <= 0:
            return mp.mpf(0)
        value = sum(c * K**p * u**a * s**(-b) for (a, b, p), c in terms.items())
        return abs(mp.exp(-K / s) * value)
    s_star = mp.mpf(K) / (2 * n)
    grid = [mp.mpf("0.5"), mp.mpf("0.9"), mp.mpf("0.999")]
    if s_star < 1:
        width = mp.sqrt(2 * n)
        for s in (s_star * (1 - 1 / width), s_star, s_star * (1 + 1 / width)):
            if 0 < s < 1:
                grid.append(mp.sqrt(1 - s))
    return 2 * mp.quad(f, [mp.mpf(0)] + sorted(set(grid)) + [mp.mpf(1)])


def main():
    t0 = time.time()
    n_values = {n: float(total_variation(n)) for n in range(1, RMAX + 1)}
    rho, nodes, values, fam, _xw, gram, _a, _, _ = r37.setup(False)
    xw = [r59.phi_weights(a, panels=6, m=6400) for a, _theta in fam]
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    corr, solve_info = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    base, _ = r37.min_h1(gram, a_mat, np.ones(len(nodes), complex))
    prime_powers = r59.rig.prime_powers_up_to(math.exp(9.504))
    c_book = sum(2.0 * weight / math.sqrt(number) for number, weight in prime_powers)
    sigma_peak = max(abs(float(r59.rig.sigma_vec(np.array([2 * math.pi * x]))[0])) for x in np.linspace(X0, 400, 2000))
    env = c_book + sigma_peak + 2.0
    family_data = []
    for (a, theta), bcoef, ccoef in zip(fam, base, corr):
        family_data.append((float(a), float(theta), abs(bcoef), abs(ccoef)))

    def v_bound(a, t, r):
        log_value = (0.5 * a * a + math.log(SAFETY) + math.log(n_values[r])
                      - (2 * r - 2) * math.log(a) - r * math.log(math.hypot(0.5, t)))
        if log_value < -745.0:
            return 0.0
        return math.exp(min(log_value, 700.0))

    def envelope(x):
        lb = 0.0
        cc = 0.0
        for a, theta, bcoef, ccoef in family_data:
            t = theta - 2 * math.pi * x
            bound = min(v_bound(a, t, r) for r in range(1, RMAX + 1))
            lb += bcoef * bound
            cc += ccoef * bound
        p = abs(float(np.real(r59.P_from_nodes(np.array([x]), r59.counterpart_nodes(rho))[0])))
        return env * p * p * lb * lb * cc * cc

    grid = np.geomspace(X0, 1.0e6, 5000)
    values_env = np.array([envelope(float(x)) for x in grid])
    tail_160_1e6 = float(np.trapezoid(values_env, grid))
    # The last active rung at 1e6 is r=48, so bound the remaining algebraic tail
    # by freezing its coefficient and integrating x^(8-4r).
    x_last = float(grid[-1])
    remainder = float(values_env[-1] * x_last / (4 * RMAX - 9))
    result = {
        "record": 2063,
        "status": "HIGH-ORDER-TAIL-CANDIDATE",
        "owner": "one-copy G8-H",
        "rule_m_for_coefficients": 6400,
        "derivative_order": RMAX,
        "safety_multiplier_on_Nr": SAFETY,
        "x0": X0,
        "xmax_numeric": 1.0e6,
        "n_values_k30": n_values,
        "env_constant": env,
        "tail_160_to_1e6": tail_160_1e6,
        "tail_remainder_model": remainder,
        "tail_total_candidate": tail_160_1e6 + remainder,
        "q1600_abs": 3.406049871881275e12,
        "l2_charge": 4.412215566637855e10,
        "tail_over_q1600": (tail_160_1e6 + remainder) / 3.406049871881275e12,
        "tail_over_l2": (tail_160_1e6 + remainder) / 4.412215566637855e10,
        "solve": solve_info,
        "nonclaims": [
            "Nr values are measured mpmath total variations, not proved enclosures",
            "the 100x safety factor is a stress test, not a theorem",
            "remainder uses an asymptotic model and is not yet an enclosure",
            "no producer theorem or RH claim",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "prior_tail_law": "docs/proofs/2053_route_a_l4_horizon.md",
            "owner_source": "results/2058_l5_solve.json",
        },
        "elapsed_s": round(time.time() - t0, 1),
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
