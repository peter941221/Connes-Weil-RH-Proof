#!/usr/bin/env python3
# Record 1700 rig: is the archimedean sign field NONVACUOUS on the confined
# triple-vanishing class?
#
# Committed forms (F27/F28 hand derivation, rig = decisive measurement):
#   arch(F) = (log 4pi + gamma_E) F(0)
#             + int_0^inf [e^{y/2}(F(y)+F(-y)) - 2F(0)] / (e^y - e^-y) dy
#                                                (C1SameOwnerWeil.lean:61)
#   F = starConvolution g (correlation scheme, validated 1696/1699)
#   root class = {g confined to [-w,w], w < 3/10} intersect
#                {ghat(0) = ghat(1/2) = ghat(1) = 0}
#   WHY the 3 moments: g = tripleVanishingRoot h = D(D+1/2)(D+1)h satisfies
#   the adjoint conditions ker L* = span{1, e^{x/2}, e^x} (adjoint of D+a is
#   -D+a, order reversed), and <g, phi> on that span = ghat(1), ghat(1/2),
#   ghat(0) — the adjoint conditions ARE the node moments, so the constraint
#   class here is EXACTLY the frame theorem's root class (C1LaneRD3Root
#   .lean:264 + :316).  Q[g] = arch(starConvolution g) is symmetric
#   quadratic.
#
# DECISIVE QUESTION: sign of lambda_max(w) = max Q[g]/mass(g) over the class.
#   lambda_max > 0  =>  shaped seeds EXIST: P1's sign piece becomes an
#                       explicit construction problem (the maximizer is the
#                       first shape candidate);
#   lambda_max <= 0 =>  the window-confined route to premise 1 is EMPTY and
#                       P1 must drop confinement (merging into premise 2).
# RH is not claimed; this is a map-deciding measurement, not a proof.

import json
import numpy as np
from scipy.integrate import quad
from scipy.linalg import circulant, eigh

EULER_GAMMA = 0.57721566490153286060651209008240243
A_COEF = float(np.log(4.0 * np.pi) + EULER_GAMMA)
Y_MAX = 40.0          # arch tail: integrand = -2F(0)/(e^y-e^-y) beyond supp F
N_PAD = 2400          # padded grid over [-4w, 4w]


def wfun(y):
    return 1.0 / (np.exp(y) - np.exp(-y))


def build_M(xgrid, w):
    """Arch quadratic form on the padded periodic grid.

    M = A*dx*I - 2I * S_all + circulant(c) + circulant(c)^T,
      c_k   = dx * wfun(k dx) * e^{k dx / 2},  k = 1 .. ksup (y <= 2w)
      S_all = dx * sum_{k=1}^{k40} wfun(k dx)  (the full -2F(0) integral;
              beyond 2w the correlation vanishes on the padded torus, whose
              length 8w > 4w guarantees no wrap)."""
    n = len(xgrid)
    dx = xgrid[1] - xgrid[0]
    ksup = int(round(2.0 * w / dx))
    k40 = int(round(Y_MAX / dx))
    ks = np.arange(1, k40 + 1)
    wall = dx * wfun(ks * dx)
    c = np.zeros(n)
    kp = np.arange(1, ksup + 1)
    c[kp] = dx * wfun(kp * dx) * np.exp(kp * dx / 2.0)
    M = A_COEF * dx * np.eye(n) - 2.0 * dx * wall.sum() * np.eye(n) \
        + dx * (circulant(c) + circulant(c).T)
    return (M + M.T) / 2.0


def star_square(u, dx):
    """Correlation square on the padded periodic grid (1696 scheme)."""
    n = len(u)
    out = np.empty(n, dtype=complex)
    for i in range(n):
        out[i] = dx * np.sum(u * np.roll(u, i))
    return out


def F_at(F, x, xgrid):
    return float(np.interp(x, xgrid, F.real, left=0.0, right=0.0))


def arch_sum(g, xgrid):
    """Independent arch readout as a DIRECT DISCRETE SUM: F from the roll
    correlation (same scheme as star_square), the integrand trapezoid-summed
    on a y-grid of step dx up to Y_MAX.  No circulant, no quad - a second
    path for cross-checking the quadratic form.  (quad-based readouts are
    unreliable on the padded grid: adaptive roundoff eats the small-y
    structure, observed as spurious ~0 totals.)"""
    n = len(xgrid)
    dx = xgrid[1] - xgrid[0]
    F = star_square(g, dx)
    # star_square is indexed by SHIFT amount: F[k] = R(k*dx), F[n-k] = R(-k*dx)
    F0 = float(F[0].real)
    ks = np.arange(0, int(round(Y_MAX / dx)) + 1)
    ys = ks * dx
    Fy = F[ks % n].real
    Fm = F[(n - ks) % n].real
    den = np.exp(ys) - np.exp(-ys)
    integ = np.where(den < 1e-12, F0 / 2.0,
                     (np.exp(ys / 2.0) * (Fy + Fm) - 2.0 * F0) / den)
    return A_COEF * F0 + float(np.sum(integ) * dx)


def moment_matrix(xa, da):
    return np.vstack([np.exp(s * xa) for s in (0.0, 0.5, 1.0)]) * da


def solve_width(w):
    pad = 4.0 * w
    n = N_PAD
    xgrid = -pad + (2.0 * pad) / n * np.arange(n)
    dx = xgrid[1] - xgrid[0]
    Mmat = build_M(xgrid, w)
    active = np.abs(xgrid) <= w + 1e-12
    Mact = Mmat[np.ix_(active, active)]
    xa = xgrid[active]
    Cm = moment_matrix(xa, dx)
    P = np.eye(len(xa)) - Cm.T @ np.linalg.pinv(Cm @ Cm.T) @ Cm
    sym = (P @ Mact @ P.T + P @ Mact.T @ P.T) / 2.0
    vals, vecs = eigh(sym)
    lam = vals[-1] / dx                        # normalize by mass = dx|g|^2
    gmax = np.zeros(n)
    gmax[active] = vecs[:, -1]
    return lam, gmax, xgrid, Mmat


def main():
    print("== 1700: arch sign field on the confined triple-vanishing class ==")
    out = {"scan": [], "validators": {}}
    rng = np.random.default_rng(7)

    for w in (0.10, 0.15, 0.20, 0.25, 0.29):
        lam, gmax, xgrid, Mmat = solve_width(w)
        act = np.abs(xgrid) <= w + 1e-12
        dx = xgrid[1] - xgrid[0]

        # validator A: quadratic form vs direct quad readout on a random
        # admissible g (moments + support)
        xa = xgrid[act]
        Cm = moment_matrix(xa, dx)
        pinvCC = np.linalg.pinv(Cm @ Cm.T)

        def project(u):
            v = u.copy()
            for _ in range(2):
                v[act] = v[act] - Cm.T @ (pinvCC @ (Cm @ v[act]))
            return v

        gv = project(rng.standard_normal(len(xgrid)) * act
                     + 0.3 * np.sin(7.0 * xgrid) * act)
        q_form = float(gv @ Mmat @ gv)
        q_dir = arch_sum(gv, xgrid)
        errA = abs(q_form - q_dir) / max(1e-12, abs(q_dir))

        # validator B: direct sum readout of the maximizer confirms the sign
        qd_max = arch_sum(gmax, xgrid)

        # maximizer shape: sign flips inside the support
        s = np.sign(gmax[act])
        s = s[s != 0]
        flips = int(np.sum(np.diff(s) != 0))
        row = dict(w=w, lam_max=lam, q_dir_max=qd_max, sign_flips=flips,
                   err_validatorA=errA)
        out["scan"].append(row)
        verdict = "POSITIVE" if lam > 0 else "NEGATIVE/EMPTY"
        print(f"   w={w:4.2f}: lambda_max={lam:+.6f} ({verdict})  "
              f"Q_dir(max)={qd_max:+.6f}  flips={flips}  "
              f"validatorA relerr={errA:.2e}")

    # 1699 cross-check: plain bump (unconstrained) arch must stay positive
    w = 0.29
    xgrid = -4.0 * w + (8.0 * w) / N_PAD * np.arange(N_PAD)
    dx = xgrid[1] - xgrid[0]
    plain = np.exp(-1.0 / np.maximum(1e-300, 1.0 - (xgrid / w) ** 2))
    plain *= (np.abs(xgrid) < w)
    plain /= np.linalg.norm(plain) * np.sqrt(dx)
    Mmat = build_M(xgrid, w)
    q_plain = float(plain @ Mmat @ plain)
    out["validators"]["plain_unconstrained_arch"] = q_plain
    print(f"   cross-check plain bump (unconstrained, w=0.29): "
          f"Q_form={q_plain:+.6f} (expect ~ +0.82, the 1699 sanity row)")

    with open("results/1700_arch_sign_field.json", "w") as f:
        json.dump(out, f, indent=1)
    print("saved results/1700_arch_sign_field.json")
    pos = [r["w"] for r in out["scan"] if r["lam_max"] > 0]
    if pos:
        print(f"verdict: lambda_max > 0 at w in {pos} — the sign field is "
              "NONVACUOUS on the confined class; shaped seeds exist and the "
              "maximizer is the first explicit shape candidate.")
    else:
        print("verdict: lambda_max <= 0 at every width — the window-confined "
              "route to premise 1 is EMPTY; P1 must drop confinement and "
              "merge into premise 2.")


if __name__ == "__main__":
    main()
