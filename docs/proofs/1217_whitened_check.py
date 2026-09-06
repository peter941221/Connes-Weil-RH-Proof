"""1217 falsifier (b): whitened-top inflation check on the finished
M-box bundle (prereg 1217 section 3; run AFTER the box engine).

The whitening is PORTED VERBATIM from the committed probe
1216_true_gate_matrix_probe.py (record 1216): the kernel V is the null
space of the 3-scale moment matrix R[si, j] = sum_l w_l w_j(s_l)
exp(s s_l), s in {0, 0.5, 1}, computed on the probe's own 1200-node
Gauss-Legendre quadrature, and the Gram is the probe's C0[i, j] =
int w_i w_j.  NOT the 1112 cert matrices R_mid / G_mid (a first draft
of this script used those and produced a phantom top of +0.345; the
dry-run against a synthetic cert caught it).

With Delta = (MHi - MLo)/2 entrywise:

    require top(L^-1 Z^T M_mid Z L^-T) + spectral_radius(L^-1 Z^T Delta Z L^-T)
            <= U - 1e-8,

where top is the largest eigenvalue of the symmetrized whitened matrix
and the spectral radius is the Weyl bound for the worst-case entrywise
box perturbation.  Self-check: the recomputed top of M_mid must match
the committed cert value top_mid to 1e-9, else ABORT (architecture
mismatch - do not issue a verdict).  Failure of falsifier (b) -> the
boxes cannot support the margin consumption; the run is
ABORTED-UNINFORMATIVE (no hand-narrowing).  Appends whitened_check to
the cert JSON.
"""
import json
import os
from fractions import Fraction

import numpy as np
from numpy.polynomial.legendre import leggauss

HERE = os.path.dirname(os.path.abspath(__file__))
CERT = os.path.join(HERE, "1217_m_boxes_cert.json")
C1112 = os.path.join(HERE, "1112_cert.json")

A = 2.0
K = 8
VANISH_S = (0.0, 0.5, 1.0)
SELF_CHECK_TOL = 1e-9

cls = json.load(open(C1112))["classes"][0]
M_mid = np.array([[float(Fraction(v)) for v in row]
                  for row in cls["M_mid"]])
U = float(Fraction(cls["U"]))
cert_top_mid = float(cls["top_mid"])


def class_bump(x):
    x = np.asarray(x, dtype=float)
    out = np.zeros_like(x)
    m = np.abs(x) < 1.0
    xm = x[m]
    out[m] = np.exp(-1.0 / (1.0 - xm * xm))
    return out


def legendre_vals(i, x):
    x = np.asarray(x, dtype=float)
    p0 = np.ones_like(x)
    if i == 0:
        return p0
    p1 = x.copy()
    for n in range(0, i - 1):
        p2 = ((2 * n + 3) * x * p1 - (n + 1) * p0) / (n + 2)
        p0, p1 = p1, p2
    return p1


def window(i, u):
    return legendre_vals(i, u / A) * class_bump(u / A)


# probe quadrature (verbatim): 1200-node GL on (-2, 2)
gx, gw = leggauss(1200)
sx = A * gx
sw = A * gw
W = np.vstack([window(i, sx) for i in range(K)])

# Gram: C0[i, j] = int w_i w_j (probe's own value)
C0 = W @ (sw[:, None] * W.T)

# kernel of the 3-scale moment matrix (probe verbatim)
R = np.empty((3, K))
for si, s in enumerate(VANISH_S):
    for j in range(K):
        R[si, j] = float(np.sum(sw * W[j] * np.exp(s * sx)))
u, sv, vh = np.linalg.svd(R, full_matrices=True)
rank_r = int(np.sum(sv > 1e-11 * max(sv[0], 1.0)))
Zn = vh[rank_r:].T
Pz = Zn.T @ C0 @ Zn
L = np.linalg.cholesky((Pz + Pz.T) / 2.0)
Li = np.linalg.inv(L)


def whitened_top(M):
    H = Li @ Zn.T @ M @ Zn @ Li.T
    ev = np.linalg.eigvalsh((H + H.T) / 2.0)
    return float(ev[-1]), ev


top, _ = whitened_top(M_mid)
if abs(top - cert_top_mid) > SELF_CHECK_TOL:
    raise SystemExit(
        f"SELF-CHECK FAIL: recomputed top {top:+.6e} vs committed "
        f"top_mid {cert_top_mid:+.6e} - whitening does not reproduce "
        "the 1112 architecture; no verdict issued.")

cert = json.load(open(CERT))
entries = cert["entries"]
DELTA = np.array([[float(Fraction(entries[f"{i},{j}"]["hi"]))
                   - float(Fraction(entries[f"{i},{j}"]["lo"]))
                   for j in range(K)] for i in range(K)]) / 2
infl = float(np.linalg.norm(Li @ Zn.T @ DELTA @ Zn @ Li.T, ord=2))
passed = top + infl <= U - 1e-8
cert["whitened_check"] = {
    "construction": "ported verbatim from 1216_true_gate_matrix_probe.py "
                    "(3-scale moment kernel, C0 Gram)",
    "dim_V": int(Zn.shape[1]),
    "top_mid_recomputed": top,
    "cert_top_mid": cert_top_mid,
    "self_check_deviation": abs(top - cert_top_mid),
    "inflation_radius": infl,
    "top_plus_inflation": top + infl,
    "U": U,
    "slack_required": 1e-8,
    "pass": bool(passed),
}
with open(CERT, "w") as fh:
    json.dump(cert, fh, indent=1)
print(f"dim V = {Zn.shape[1]}   self-check |top - top_mid| = "
      f"{abs(top - cert_top_mid):.2e}")
print(f"top(mid|V whitened) = {top:+.6e}")
print(f"inflation radius    = {infl:.3e}")
print(f"top + inflation     = {top + infl:+.6e}")
print(f"U - 1e-8            = {U - 1e-8:+.6e}")
print("FALSIFIER-B " + ("PASS" if passed else "FAIL"))
raise SystemExit(0 if passed else 6)
