#!/usr/bin/env python3
# 1683 — Phase -> measure surrogate rig (record 1683 companion).
#
# F61-compliant: function evaluations and root finding only.  No carrier-grid
# readouts, no truncated-grid carrier statements.
#
# Committed inputs (all hand-pinned, see docs/proofs/1682):
#   m(xi)   = G_R(1/2 - 2 pi i xi) / G_R(1/2 + 2 pi i xi),  G_R(z) = pi^(-z/2) Gamma(z/2)
#   Theta(xi) = e^{4 pi i (log lam) xi} * m(-xi)
# Phase: gamma(xi) = Im log Theta(xi)  (continuous branch via loggamma)
# Exact derivative via digamma; atoms = {gamma = alpha mod pi}; surrogate
# atom mass = pi / |gamma'(x_k)| (1682 section 2, Clark-type).
#
# Deliverables:
#   [PHASE]  exact gamma' vs the 1631 budget candidates (convention check)
#   [CALIB]  m = 1 row: uniform lattice, constant mass, density constant
#   [BRANCH] committed symbol: per-window atom mass density vs calibration
#   [DEGEN]  approach to the degeneration |xi| = lam^2 (gamma' -> 0)
#   [INTEG]  smooth-branch integrability surrogate for a concrete C_c^oo
#            representative of the committed test class

import mpmath as mp
import json
import math
import os
import numpy as np

mp.mp.dps = 30

RESULTS = {}

# ---------------------------------------------------------------- symbol ----

def dlog_GR(z):
    """d/dz log G_R(z), G_R(z) = pi^(-z/2) Gamma(z/2)."""
    return -mp.mpf('0.5') * mp.log(mp.pi) + mp.mpf('0.5') * mp.digamma(z / 2)


def log_GR(z):
    """log G_R(z) = -(z/2) log pi + log Gamma(z/2)."""
    return -(z / 2) * mp.log(mp.pi) + mp.loggamma(z / 2)


def log_Theta(xi, lam, m_is_one=False):
    """Continuous-branch log of Theta(xi) = e^{4 pi i log(lam) xi} m(-xi),
    m(-xi) = G_R(1/2 + 2 pi i xi) / G_R(1/2 - 2 pi i xi)."""
    half = mp.mpf('0.5')
    t = 2 * mp.pi * xi
    if m_is_one:
        return 4j * mp.pi * mp.log(lam) * xi
    return (4j * mp.pi * mp.log(lam) * xi
            + log_GR(half + 1j * t) - log_GR(half - 1j * t))


def gamma_of(xi, lam, m_is_one=False):
    return mp.im(log_Theta(xi, lam, m_is_one))


def gamma_prime_of(xi, lam, m_is_one=False):
    """Exact gamma' = Im(d/dxi log Theta)."""
    if m_is_one:
        return 4 * mp.pi * mp.log(lam)
    half = mp.mpf('0.5')
    t = 2 * mp.pi * xi
    d = (4j * mp.pi * mp.log(lam)
         + 2j * mp.pi * dlog_GR(half + 1j * t)
         + 2j * mp.pi * dlog_GR(half - 1j * t))
    return mp.im(d)


# ------------------------------------------------------------ [PHASE] -------

def fd_check(lams=(mp.mpf('0.2'), mp.mpf('0.1'))):
    """Self-check F27/F28: central finite difference of gamma vs the exact
    digamma derivative.  The derivative is trusted only if these agree."""
    print("== [FD] finite-difference check of gamma' ==")
    rows = []
    for lam in lams:
        for xi in (mp.mpf('0.05'), mp.mpf('1'), mp.mpf('10'), mp.mpf('100')):
            h = mp.mpf('1e-6') * xi
            fd = (gamma_of(xi + h, lam) - gamma_of(xi - h, lam)) / (2 * h)
            gp = gamma_prime_of(xi, lam)
            rel = abs(fd - gp) / max(1, abs(gp))
            rows.append({"lam": float(lam), "xi": float(xi),
                         "fd": float(fd), "gp": float(gp), "rel": float(rel)})
            print(f"  lam={float(lam):<5} xi={float(xi):<7} gp={float(gp):>14.6f}"
                  f"  fd={float(fd):>14.6f}  rel={float(rel):.2e}")
    RESULTS["fd"] = rows


def fold_locator(lams=(mp.mpf('0.2'), mp.mpf('0.1'))):
    """Locate the phase fold (gamma' = 0) by bisection; compare with lam^-2."""
    print("== [FOLD] phase degeneration point ==")
    rows = []
    for lam in lams:
        lo, hi = mp.mpf('1e-3'), mp.mpf('1000')
        # gamma' increases through the fold (negative near 0, positive far):
        f = lambda x: gamma_prime_of(x, lam)
        for _ in range(300):
            mid = (lo + hi) / 2
            if f(mid) < 0:
                lo = mid
            else:
                hi = mid
        fold = (lo + hi) / 2
        pred = 1 / (lam ** 2)
        rows.append({"lam": float(lam), "fold": float(fold),
                     "pred_lam^-2": float(pred),
                     "ratio": float(fold / pred)})
        print(f"  lam={float(lam):<5} fold={float(fold):.8f}  lam^-2={float(pred):.4f}"
              f"  ratio={float(fold / pred):.8f}")
    RESULTS["fold"] = rows


def phase_check(lams=(mp.mpf('0.2'), mp.mpf('0.1'))):
    print("== [PHASE] exact gamma' vs asymptotic candidate 2 pi log(xi) + 4 pi log(lam) ==")
    rows = []
    for lam in lams:
        for xi in (mp.mpf('10'), mp.mpf('100'), mp.mpf('1000')):
            gp = gamma_prime_of(xi, lam)
            cand = 2 * mp.pi * mp.log(xi) + 4 * mp.pi * mp.log(lam)
            rows.append({
                "lam": float(lam), "xi": float(xi),
                "gp": float(gp), "cand": float(cand),
                "rel": float(abs(gp - cand) / abs(gp)),
            })
            print(f"  lam={float(lam):<5} xi={float(xi):<7} gp={float(gp):>14.6f}"
                  f"  cand={float(cand):>14.6f}  rel={rows[-1]['rel']:.2e}")
    RESULTS["phase"] = rows


# ------------------------------------------------------------ [CALIB] -------

def calibration(lam=mp.mpf('0.2')):
    """m = 1: gamma = 4 pi log(lam) xi, uniform lattice, constant masses."""
    print("== [CALIB] m = 1 uniform-lattice row ==")
    gp = abs(4 * mp.pi * mp.log(lam))
    spacing = mp.pi / gp
    mass = mp.pi / gp
    density = mass / spacing
    print(f"  lam={float(lam)}  spacing={float(spacing):.6f}  mass={float(mass):.6f}"
          f"  density(mass per unit xi)={float(density):.8f}")
    RESULTS["calib"] = {"lam": float(lam), "spacing": float(spacing),
                        "mass": float(mass), "density": float(density)}
    return float(density)


# ------------------------------------------------------------ [BRANCH] ------

def atoms_on_branch(lam, lo, hi, alpha=mp.mpf('0'), m_is_one=False):
    """All xi in (lo, hi) with gamma(xi) = alpha (mod pi), by monotone
    inversion, each atom VALIDATED by its mod-pi residual (F27/F28: the set
    is never trusted without a per-atom check)."""
    ga, gb = gamma_of(lo, lam, m_is_one), gamma_of(hi, lam, m_is_one)
    klo = int(mp.floor((min(ga, gb) - alpha) / mp.pi)) + 1
    khi = int(mp.ceil((max(ga, gb) - alpha) / mp.pi)) - 1
    out = []
    for k in range(klo, khi + 1):
        target = alpha + k * mp.pi
        f = lambda x: gamma_of(x, lam, m_is_one) - target
        xk = None
        try:
            frac = (mp.mpf(float(k - klo)) + mp.mpf('0.5')) / max(1, khi - klo)
            xk = mp.findroot(f, lo + (hi - lo) * frac)
        except Exception:
            xk = None
        ok = False
        if xk is not None and lo < xk < hi:
            # residual check: sin(gamma(xk) - target) = 0 to tolerance
            res = abs(mp.sin(gamma_of(xk, lam, m_is_one) - target))
            ok = res < mp.mpf('1e-15')
        if ok:
            out.append(xk)
    return out


def branch_density(lam, windows, m_is_one=False):
    """Per-window atom mass density on the monotone upper branch, with
    windows expressed relative to the fold lam^-2 (never straddling it)."""
    print("== [BRANCH] committed symbol: atom mass density per window ==")
    rows = []
    fold = float(1 / (float(lam) ** 2))
    for (a_rel, b_rel) in windows:
        A = fold * a_rel
        B = fold * b_rel
        xs = atoms_on_branch(lam, mp.mpf(str(A)), mp.mpf(str(B)),
                             mp.mpf('0'), m_is_one)
        xs = sorted(set(xs))
        msum = mp.mpf('0')
        for xk in xs:
            gp = abs(gamma_prime_of(xk, lam, m_is_one))
            msum += mp.pi / gp
        density = msum / (mp.mpf(str(B)) - mp.mpf(str(A)))
        rows.append({"lam": float(lam), "A": A, "B": B, "n_atoms": len(xs),
                     "mass_sum": float(msum), "density": float(density)})
        print(f"  lam={float(lam):<5} window=({A:.2f},{B:.2f})  atoms={len(xs):<6}"
              f"  sum_mass={float(msum):>12.4f}  density={float(density):.8f}")
    return rows


# ------------------------------------------------------------ [DEGEN] -------

def degeneration(lam):
    print("== [DEGEN] approach to the fold xi = lam^-2 ==")
    rows = []
    x0 = 1 / (float(lam) ** 2)
    for eps in ('2.0', '1.2', '1.05'):
        xi = x0 * float(eps)
        gp = gamma_prime_of(mp.mpf(str(xi)), lam)
        mass = mp.pi / abs(gp)
        rows.append({"lam": float(lam), "xi_over_fold": float(eps),
                     "gp": float(gp), "mass": float(mass)})
        print(f"  lam={float(lam):<5} xi/fold={float(eps):<6}"
              f"  gamma'={float(gp):>12.4f}  surrogate mass={float(mass):.4f}")
    RESULTS["degen"] = rows


# ------------------------------------------------------------ [INTEG] -------

def bump(t):
    if abs(t) >= 1:
        return mp.mpf('0')
    return mp.exp(-1 / (1 - t * t))


from scipy.integrate import quad


def fourier_bump(xi):
    """F h(xi) for the C_c^oo bump on [-1,1] by adaptive quadrature (scipy),
    e^{-2 pi i xi t} convention.  Fast at all xi, no aliasing."""
    x = float(xi)

    def fre(t):
        return bump(t) * math.cos(-2.0 * math.pi * x * t) if abs(t) < 1 else 0.0

    def fim(t):
        return bump(t) * math.sin(-2.0 * math.pi * x * t) if abs(t) < 1 else 0.0

    re, _ = quad(fre, -1.0, 1.0, limit=2000)
    im, _ = quad(fim, -1.0, 1.0, limit=2000)
    return complex(re, im)


def integrability(lam, rel_lo=1.05, rel_hi=3.0):
    print("== [INTEG] smooth-branch integrability surrogate ==")
    fold = 1 / (float(lam) ** 2)
    A, B = fold * rel_lo, fold * rel_hi
    xs = atoms_on_branch(lam, mp.mpf(str(A)), mp.mpf(str(B)), mp.mpf('0'))
    xs = sorted(set(xs))
    ga, gb = gamma_of(mp.mpf(str(A)), lam), gamma_of(mp.mpf(str(B)), lam)
    expected = int(mp.ceil((gb - ga) / mp.pi)) - 1
    print(f"  window=({A:.2f},{B:.2f})  atoms={len(xs)}  count-check = {expected}")
    partial_mass, partial_weighted = [], []
    sm, sw = mp.mpf('0'), mp.mpf('0')
    for xk in xs:
        gp = abs(gamma_prime_of(xk, lam))
        sm += mp.pi / gp
        fh = fourier_bump(xk)
        sw += (mp.pi / gp) * (fh.real ** 2 + fh.imag ** 2)
        partial_mass.append(float(sm))
        partial_weighted.append(float(sw))
    # smooth integral of |F h|^2 over the same range (same quadrature, fine grid)
    ref_grid = np.linspace(float(A), float(B), 801)
    fh_vals = []
    for g in ref_grid:
        fh = fourier_bump(g)
        fh_vals.append(fh.real ** 2 + fh.imag ** 2)
    ref_int = 0.0
    for i in range(len(ref_grid) - 1):
        ref_int += 0.5 * (fh_vals[i] + fh_vals[i + 1]) * (ref_grid[i + 1] - ref_grid[i])
    print(f"  lam={float(lam)}  window=({A:.1f},{B:.1f})  atoms={len(xs)}")
    print(f"  mass-only partial sum      = {float(sm):.4f}")
    print(f"  weighted partial sum       = {float(sw):.8f}")
    print(f"  reference int |Fh|^2 dxi   = {ref_int:.8f}")
    print(f"  ratio weighted/reference   = {float(sw) / ref_int:.6f}")
    RESULTS["integ"] = {"lam": float(lam), "window": [A, B], "n_atoms": len(xs),
                        "count_check": expected,
                        "mass_sum": float(sm), "weighted_sum": float(sw),
                        "ref_integral": ref_int,
                        "ratio": float(sw) / ref_int,
                        "partial_mass_tail": partial_mass[-5:],
                        "partial_weighted_tail": partial_weighted[-5:]}


# ---------------------------------------------------------------- main ------

def main():
    print(f"mpmath dps = {mp.mp.dps}")
    fd_check()
    fold_locator()
    phase_check()
    calibration()
    all_branch_rows = []
    for lam in (mp.mpf('0.2'), mp.mpf('0.1')):
        rows = branch_density(
            lam,
            windows=[(2.0, 5.0), (5.0, 10.0)],
        )
        all_branch_rows.extend(rows)
        degeneration(lam)
    RESULTS["branch"] = all_branch_rows
    print("== density vs the pointwise invariant (density x mass = 1) ==")
    print("  far-window densities (theory: -> 1 as the window moves out):")
    dens = [r["density"] for r in all_branch_rows]
    print(f"    {['%.6f' % d for d in dens]}")
    RESULTS["densities"] = dens
    integrability(mp.mpf('0.2'))
    os.makedirs("tmp", exist_ok=True)
    with open("tmp/phase_clark_surrogate_1683_results.json", "w") as f:
        json.dump(RESULTS, f, indent=1)
    print("results -> tmp/phase_clark_surrogate_1683_results.json")


if __name__ == "__main__":
    main()
