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
import routea_g8h_basis_comparison_2037 as r37
import routea_interval_kernel_2043 as r2043

OUTPUT = ROOT / "results" / "2070_infinity_tail_bound.json"
K = 30.0
R = 48
N48_UPPER = 1.2466403887652727e81
START = 1.0e6


def interval_abs_upper(value):
    return max(abs(float(value.a)), abs(float(value.b)))


def sigma_upper(lo, hi):
    u = mp.iv.mpf([str(2.0 * math.pi * lo), str(2.0 * math.pi * hi)])
    return interval_abs_upper(r2043.sigma_arch_iv(u))


def main():
    rho, nodes, values, fam, _xw, gram, _a, _, _ = r37.setup(False)
    xw = [r59.phi_weights(a, panels=6, m=6400) for a, _theta in fam]
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    corr, solve_info = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    base, _ = r37.min_h1(gram, a_mat, np.ones(len(nodes), complex))
    prime_powers = r59.rig.prime_powers_up_to(math.exp(9.504))
    book = sum(2.0 * weight / math.sqrt(number) for number, weight in prime_powers)
    counterpart = r80.counterpart_nodes(rho)
    theta_max = max(abs(float(theta)) for _a, theta in fam)
    node_abs = [abs(complex(z)) for z in counterpart]
    family_data = [(float(a), abs(b), abs(c)) for (a, _theta), b, c in zip(fam, base, corr)]

    def v_bound(a, t_lower):
        log_value = (0.5 * a * a + math.log(N48_UPPER)
                      - (2 * R - 2) * math.log(a) - R * math.log(t_lower))
        if log_value < -745.0:
            return 0.0
        return math.exp(min(log_value, 700.0))

    def logsum(values):
        peak = max(values)
        return peak + math.log(sum(math.exp(value - peak) for value in values))

    def band_bound(lo, hi):
        t_lower = 2.0 * math.pi * lo - theta_max
        lb_logs = []
        cc_logs = []
        for a, bcoef, ccoef in family_data:
            log_value = (0.5 * a * a + math.log(N48_UPPER)
                         - (2 * R - 2) * math.log(a) - R * math.log(t_lower))
            lb_logs.append(math.log(bcoef) + log_value)
            cc_logs.append(math.log(ccoef) + log_value)
        log_lb = logsum(lb_logs)
        log_cc = logsum(cc_logs)
        log_p = sum(math.log(2.0 * math.pi * hi + zabs) for zabs in node_abs)
        sig_upper = sigma_upper(lo, hi)
        env = book + sig_upper + 2.0
        log_bound = math.log(hi - lo) + math.log(env) + 2.0 * log_p + 2.0 * log_lb + 2.0 * log_cc
        return log_bound, sig_upper, env
    rows = []
    lo = START
    for _ in range(12):
        hi = 2.0 * lo
        log_bound, sig, env = band_bound(lo, hi)
        rows.append({"lo": lo, "hi": hi, "log_bound": log_bound, "sigma_upper": sig, "env": env})
        lo = hi
    first = rows[0]["log_bound"]
    ratios = [math.exp(rows[i + 1]["log_bound"] - rows[i]["log_bound"]) for i in range(len(rows) - 1)]
    ratio_max = max(ratios)
    geometric_remainder = math.exp(rows[-1]["log_bound"]) * 2.0 if ratio_max < 0.5 else float("inf")
    total = sum(math.exp(row["log_bound"]) for row in rows) + geometric_remainder
    result = {
        "record": 2070,
        "status": "INFINITY-TAIL-BOUND-CANDIDATE",
        "owner": "one-copy G8-H",
        "rung": R,
        "start": START,
        "bands": rows,
        "max_observed_band_ratio": ratio_max,
        "geometric_remainder_after_12_bands": geometric_remainder,
        "tail_bound_candidate": total,
        "q1600_abs": 3.406049871881275e12,
        "l2_charge": 4.412215566637855e10,
        "tail_over_q1600": total / 3.406049871881275e12,
        "tail_over_l2": total / 4.412215566637855e10,
        "solve": solve_info,
        "nonclaims": [
            "the dyadic ratio-to-infinity step still needs a symbolic monotonicity proof",
            "sigma interval uses the committed shifted Stirling enclosure and must be audited at unbounded bands",
            "no producer theorem or RH claim",
        ],
        "provenance": {
            "interval_kernel": "scripts/routea_interval_kernel_2043.py",
            "variation_upper": "results/2068_interval_variation_bound.json",
            "owner_source": "results/2058_l5_solve.json",
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
        },
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
