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

OUTPUT = ROOT / "results" / "2077_gram_true_transfer.json"
K = 30.0
XMAX = 40.0
STEP = 0.02
MP_DPS = 45


def phi_and_derivative(a, theta, x):
    aa = mp.mpf(repr(float(a)))
    tt = mp.mpf(repr(float(theta)))
    if abs(x) >= aa:
        return mp.mpc(0), mp.mpc(0)
    u = x / aa
    den = 1 - u * u
    core = mp.exp(-mp.mpf(K) / den)
    phase = mp.exp(1j * tt * x)
    phi = core * phase
    dcore = core * (-2 * mp.mpf(K) * x / (aa * aa * den * den))
    return phi, (dcore + 1j * tt * core) * phase


def true_gram_entry(ai, ti, aj, tj):
    radius = max(mp.mpf(repr(float(ai))), mp.mpf(repr(float(aj))))
    cuts = sorted(set([-radius, -min(mp.mpf(repr(float(ai))), mp.mpf(repr(float(aj)))),
                       mp.mpf(0), min(mp.mpf(repr(float(ai))), mp.mpf(repr(float(aj)))), radius]))
    def integrand(x):
        pi, di = phi_and_derivative(ai, ti, x)
        pj, dj = phi_and_derivative(aj, tj, x)
        return mp.conj(pi) * pj + mp.conj(di) * dj
    return mp.quad(integrand, cuts)


def evaluate_q(fam, xw, base, corr, rho, grid):
    s = 0.5 - 2j * np.pi * grid
    v = r80.family_values(fam, K, s, xw)
    p = np.real(r59.P_from_nodes(grid, r80.counterpart_nodes(rho)))
    kernel = r59.rig.sigma_vec(2 * np.pi * grid)
    for number, weight in r59.rig.prime_powers_up_to(math.exp(9.504)):
        kernel = kernel + 2.0 * weight / math.sqrt(number) * np.cos(
            2 * np.pi * grid * math.log(number))
    g = np.abs(p) ** 2 * np.abs(base @ v) ** 2 * np.abs(corr @ v) ** 2
    return float(np.trapezoid(kernel * g, grid))


def solve_pair(gram, a_mat, nodes, values):
    base, bi = r37.min_h1(gram, a_mat, np.ones(len(nodes), complex))
    corr, ci = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    return base, corr, {"base": bi, "corr": ci}


def main():
    mp.mp.dps = MP_DPS
    rho, nodes, values, fam, _xw400, gram_stored, _a, _, _ = r37.setup(False)
    xw400 = [r59.phi_weights(a, panels=6, m=400) for a, _theta in fam]
    xw6400 = [r59.phi_weights(a, panels=6, m=6400) for a, _theta in fam]
    a_stored = r80.family_values(fam, K, np.asarray(nodes, complex), xw400).T
    gram_true = np.empty_like(gram_stored)
    max_gap = 0.0
    for i, (ai, ti) in enumerate(fam):
        for j in range(i, len(fam)):
            aj, tj = fam[j]
            val = true_gram_entry(ai, ti, aj, tj)
            z = complex(float(mp.re(val)), float(mp.im(val)))
            gram_true[i, j] = z
            gram_true[j, i] = np.conj(z)
            max_gap = max(max_gap, abs(z - gram_stored[i, j]))
        print(json.dumps({"family": i, "max_abs_so_far": max_gap}), flush=True)
    gram_true = (gram_true + gram_true.conj().T) / 2.0
    a_true = np.empty_like(a_stored)
    for i, node in enumerate(nodes):
        for j, (a, theta) in enumerate(fam):
            aa = mp.mpf(repr(float(a)))
            tt = mp.mpf(repr(float(theta)))
            zm = aa * (mp.mpc(repr(complex(node).real), repr(complex(node).imag)) + 1j * tt)
            def fn(x):
                xx = x / aa
                if abs(xx) >= 1:
                    return mp.mpc(0)
                return mp.exp(-mp.mpf(K) / (1 - xx * xx) + zm * x)
            val = aa * mp.quad(fn, [-aa, -aa / 2, 0, aa / 2, aa])
            a_true[i, j] = complex(float(mp.re(val)), float(mp.im(val)))
    combos = {
        "stored_stored": (gram_stored, a_stored),
        "truegram_stored_a": (gram_true, a_stored),
        "storedgram_true_a": (gram_stored, a_true),
        "true_true": (gram_true, a_true),
    }
    grid = np.arange(-XMAX, XMAX + STEP / 2, STEP)
    rows = {}
    q0 = None
    for name, (gram, amat) in combos.items():
        base, corr, info = solve_pair(gram, amat, nodes, values)
        q = evaluate_q(fam, xw6400, base, corr, rho, grid)
        rows[name] = {
            "q": q,
            "base_norm": float(np.linalg.norm(base)),
            "corr_norm": float(np.linalg.norm(corr)),
            "solve_residuals": {"base": info["base"]["resid"], "corr": info["corr"]["resid"]},
        }
        if q0 is None:
            q0 = q
    result = {
        "record": 2077,
        "status": "GRAM-AMATRIX-TRUE-TRANSFER-MEASUREMENT",
        "owner": "one-copy G8-H",
        "matrix_shape": list(gram_true.shape),
        "mp_dps": MP_DPS,
        "max_abs_gram_entry_gap": max_gap,
        "frobenius_gram_gap": float(np.linalg.norm(gram_true - gram_stored)),
        "rows": rows,
        "transfers": {
            "gram_only": abs(rows["truegram_stored_a"]["q"] - rows["stored_stored"]["q"]),
            "amatrix_only": abs(rows["storedgram_true_a"]["q"] - rows["stored_stored"]["q"]),
            "both": abs(rows["true_true"]["q"] - rows["stored_stored"]["q"]),
        },
        "nonclaims": [
            "mpmath quadrature is not a formal interval enclosure",
            "COVER and remaining model-to-real transfer remain open",
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