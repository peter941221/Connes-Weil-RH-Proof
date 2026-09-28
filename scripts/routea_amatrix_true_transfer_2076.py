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

OUTPUT = ROOT / "results" / "2076_amatrix_true_transfer.json"
K = 30.0
XMAX = 40.0
STEP = 0.02
MP_DPS = 50


def true_entry(a, theta, node):
    aa = mp.mpf(repr(float(a)))
    kk = mp.mpf(repr(K))
    zm = aa * (mp.mpc(repr(complex(node).real), repr(complex(node).imag))
              + 1j * mp.mpf(repr(float(theta))))
    def integrand(x):
        xx = x / aa
        if abs(xx) >= 1:
            return mp.mpc(0)
        return mp.exp(-kk / (1 - xx * xx) + zm * x)
    return aa * mp.quad(integrand, [-aa, -aa / 2, 0, aa / 2, aa])


def evaluate_q(fam, xw, base, corr, rho, grid):
    s = 0.5 - 2j * np.pi * grid
    v = r80.family_values(fam, K, s, xw)
    p = np.real(r59.P_from_nodes(grid, r80.counterpart_nodes(rho)))
    kernel = r59.rig.sigma_vec(2 * np.pi * grid)
    for number, weight in r59.rig.prime_powers_up_to(math.exp(9.504)):
        kernel = kernel + (2.0 * weight / math.sqrt(number)) * np.cos(
            2 * np.pi * grid * math.log(number))
    value = np.abs(p) ** 2 * np.abs(base @ v) ** 2 * np.abs(corr @ v) ** 2
    return float(np.trapezoid(kernel * value, grid))


def main():
    mp.mp.dps = MP_DPS
    rho, nodes, values, fam, _xw400, gram, _a, _, _ = r37.setup(False)
    xw6400 = [r59.phi_weights(a, panels=6, m=6400) for a, _theta in fam]
    a_stored = r80.family_values(fam, K, np.asarray(nodes, complex),
                                 [r59.phi_weights(a, panels=6, m=400)
                                  for a, _theta in fam]).T
    a_true = np.empty_like(a_stored)
    max_abs = 0.0
    rows = []
    for i, node in enumerate(nodes):
        for j, (a, theta) in enumerate(fam):
            val = true_entry(a, theta, node)
            a_true[i, j] = complex(float(mp.re(val)), float(mp.im(val)))
            max_abs = max(max_abs, abs(a_true[i, j] - a_stored[i, j]))
        print(json.dumps({"node": i, "max_abs_so_far": max_abs}), flush=True)
    base_stored, info_bs = r37.min_h1(gram, a_stored, np.ones(len(nodes), complex))
    corr_stored, info_cs = r37.min_h1(gram, a_stored, np.asarray(values, complex))
    base_true, info_bt = r37.min_h1(gram, a_true, np.ones(len(nodes), complex))
    corr_true, info_ct = r37.min_h1(gram, a_true, np.asarray(values, complex))
    grid = np.arange(-XMAX, XMAX + STEP / 2, STEP)
    q_stored = evaluate_q(fam, xw6400, base_stored, corr_stored, rho, grid)
    q_true = evaluate_q(fam, xw6400, base_true, corr_true, rho, grid)
    q_cross = evaluate_q(fam, xw6400, base_true, corr_true, rho,
                         np.arange(-XMAX, XMAX + 0.01 / 2, 0.01))
    result = {
        "record": 2076,
        "status": "AMATRIX-TRUE-TRANSFER-MEASUREMENT",
        "owner": "one-copy G8-H",
        "matrix_shape": list(a_true.shape),
        "mp_dps": MP_DPS,
        "max_abs_entry_gap": max_abs,
        "frobenius_entry_gap": float(np.linalg.norm(a_true - a_stored)),
        "stored_solve_residuals": {"base": info_bs["resid"], "corr": info_cs["resid"]},
        "true_solve_residuals": {"base": info_bt["resid"], "corr": info_ct["resid"]},
        "stored_coeff_norms": {"base": float(np.linalg.norm(base_stored)), "corr": float(np.linalg.norm(corr_stored))},
        "true_coeff_norms": {"base": float(np.linalg.norm(base_true)), "corr": float(np.linalg.norm(corr_true))},
        "q_stored_step_002": q_stored,
        "q_true_step_002": q_true,
        "q_true_step_001": q_cross,
        "q_transfer_abs": abs(q_true - q_stored),
        "q_transfer_over_margin": abs(q_true - q_stored) / abs(q_stored),
        "nonclaims": [
            "mpmath quadrature is not a formal interval enclosure",
            "Gram rule and coefficient/model-to-real gaps remain open",
            "no producer theorem or RH claim",
        ],
        "provenance": {
            "stored_source": "results/2058_l5_solve.json",
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
        },
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()