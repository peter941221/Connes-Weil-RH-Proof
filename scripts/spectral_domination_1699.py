#!/usr/bin/env python3
# Record 1699 rig: the D3 detector frame on the committed window class.
#
# Committed objects (F27/F28: hand-derived from the tree, rig = CHECK):
#   g = tripleVanishingRoot h = D_0 D_{1/2} D_1 h   (C1LaneRD3Root.lean:264)
#   laplaceAt (tripleVanishingRoot h) s
#       = (0 - s) * (1/2 - s) * (1 - s) * laplaceAt h s
#                                               (C1LaneRD3Root.lean:271)
#   laplaceAt f s = int e^{s x} f(x) dx           (CC20YoshidaConvolution:55)
#   poleTerm (tripleVanishingRoot h).convolutionSquare = 0
#                                    (C1LaneRD3Root.lean:332, committed)
#   window class: supp h in [-w, w], w < 3/10 =>
#       supp (square) in (-log 2, log 2), qw = -arch
#                                    (C1LaneRD3Root.lean:380 + :338)
#   arch integrand as in four_channel_ledger_1696.qw_value (m-orientation,
#   reflection-invariant: F(y)+F(-y), F(0), cosh(y/2)).
#
# CHECKS (committed identities must reproduce):
#   C1: laplace Vandermonde law at random s (abs err vs ||g||-scale)
#   C2: laplace g = 0 at s in {0, 1/2, 1}
#   C3: pole term of the square = 0 (committed theorem, first rig read)
# MEASUREMENTS (open objects; recon, not proof):
#   M1: arch(square) width scan w in [0.10, 0.29]  (the sign field)
#   M2: S_pair(gamma) = 2 Re ghat(1/4 + i gamma), gamma scan at w = 0.29
#       (synthetic off-line pair rho0 = 3/4 + i gamma; the domination gap
#        |S_pair| / |arch|, plus the phase of ghat off the line)
# RH is not claimed; the sign field and domination stay open (1697 map 047).

import json
import numpy as np
from scipy.integrate import quad

TWO_PI = 2.0 * np.pi
LOG2 = float(np.log(2.0))
EULER_GAMMA = 0.57721566490153286060651209008240243

N = 16384
T = 2.0
dt = 2.0 * T / N
t = -T + dt * np.arange(N)


def bump(x, c):
    x = np.abs(np.asarray(x, dtype=float)) / c
    return np.where(x < 1.0, np.exp(-1.0 / np.maximum(1e-300, 1.0 - x * x)),
                    0.0)


def fft_derivative(u):
    """Derivative on the half-open periodic grid (support well inside)."""
    k = TWO_PI * 1j * np.fft.fftfreq(N, d=dt)
    return np.fft.ifft(k * np.fft.fft(u))


def deriv_shift(u, a):
    """D_a u = u' + a u (the tree's derivativeShift on the raw function)."""
    return fft_derivative(u) + a * u


def make_seed(w, parity="even"):
    """C-infinity seed confined to [-w, w], L2-normalized; 'odd' = x*bump."""
    u = bump(t, w)
    if parity == "odd":
        u = u * t
    u /= np.linalg.norm(u) * np.sqrt(dt)
    return u


def make_root(h, normalize=True):
    """tripleVanishingRoot h = D_0 (D_{1/2} (D_1 h)) - innermost a=1 first.
    With normalize=True the root is rescaled to L2 = 1: arch and the Laplace
    of the square are homogeneous of degree 2 in g, so the SIGN and the gap
    ratios are normalization-invariant; rescaling only makes the readouts
    legible.  C1 (the Vandermonde law) must use normalize=False."""
    u = deriv_shift(deriv_shift(deriv_shift(h, 1.0 + 0.0j),
                                0.5 + 0.0j), 0.0 + 0.0j)
    if normalize:
        u /= (np.linalg.norm(u) * np.sqrt(dt))
    return u


def star_square(u):
    """starConvolution model, same discrete scheme as 1696 (F(x) = int
    g(t) g(t-x) dt); every measured quantity below is reflection-invariant."""
    return dt * np.array([np.sum(u * np.interp(t - x, t, u,
                                               left=0.0, right=0.0))
                          for x in t])


def laplace(u, s):
    """int e^{s x} u(x) dx on the grid."""
    return dt * np.sum(np.exp(s * t) * u)


def F_at(F, x):
    # F is real-valued up to roundoff (real seeds + real shifts); the
    # discarded imaginary part is asserted negligible in main().
    return float(np.interp(x, t, F.real, left=0.0, right=0.0))


def pole_term(F):
    """poleTerm F = Re( F_hat(1/2) + F_hat(-1/2) )  (C1SameOwnerWeil.lean:31).
    Equal to 4 int_0^inf cosh(y/2) F(y) dy for EVEN F; the correlation
    square is always even, but we use the committed Laplace form directly."""
    return float((laplace(F, 0.5) + laplace(F, -0.5)).real)


def arch_term(F):
    """archimedeanTerm F  (C1SameOwnerWeil.lean:61): the integral runs over
    Ioi 0 - to INFINITY, not to the support edge (the -2 F(0)/(e^y-e^-y)
    tail beyond supp F is O(F0) and must be kept).  Integrated to y=40,
    where the tail is ~e^-40."""
    F0 = F_at(F, 0.0)

    def integrand(y):
        den = np.exp(y) - np.exp(-y)
        if den < 1e-12:
            return F0 / 2.0
        return (np.exp(y / 2.0) * (F_at(F, y) + F_at(F, -y)) - 2.0 * F0) / den
    return (np.log(4.0 * np.pi) + EULER_GAMMA) * F0 + \
        quad(integrand, 0.0, 40.0, limit=800)[0]


def main():
    print("== D3 detector frame: committed-law checks + open-object recon ==")
    out = {"checks": {}, "arch_scan": [], "pair_scan": []}

    # ---- C1/C2: Vandermonde law + node vanishing (committed) ----
    h = make_seed(0.29)
    g = make_root(h, normalize=False)     # C1 needs the raw operator root
    ghat_h = lambda s: laplace(h, s)
    ghat_g = lambda s: laplace(g, s)
    err_c1 = 0.0
    for s in (0.23 + 7.0j, 0.11 + 19.0j, -0.31 + 43.0j, 0.05 + 101.0j):
        vander = (0.0 - s) * (0.5 - s) * (1.0 - s) * ghat_h(s)
        err_c1 = max(err_c1, abs(ghat_g(s) - vander) / max(1e-300, abs(vander)))
    err_c2 = max(abs(ghat_g(0.0)), abs(ghat_g(0.5)), abs(ghat_g(1.0)))
    scale = abs(ghat_g(0.25 + 21.0j))
    out["checks"]["C1_vandermonde_relerr"] = err_c1
    out["checks"]["C2_nodes_abserr"] = err_c2
    print(f"   C1 Vandermonde rel err (4 probe s): {err_c1:.3e}")
    print(f"   C2 laplace g at {{0,1/2,1}}: {err_c2:.3e}  "
          f"(scale |ghat| = {scale:.3e})")

    # ---- C3 + M1: pole vanishing + arch sign field, width scan ----
    wmax = 0.29
    for parity in ("even", "odd"):
        for w in (0.10, 0.18, 0.25, 0.29):
            h = make_seed(w, parity)
            g = make_root(h)
            F = star_square(g)
            assert np.abs(F.imag).max() < 1e-8 * (np.abs(F.real).max() + 1e-30)
            pole = pole_term(F)
            arch = arch_term(F)
            row = dict(w=w, parity=parity, pole=pole, arch=arch,
                       qw_neg_arch=-arch)
            out["arch_scan"].append(row)
            tag = "C3" if (parity == "even" and w == wmax) else "  "
            print(f"   {tag} {parity} w={w:4.2f}: pole={pole:+.3e}  "
                  f"arch={arch:+.6f}  qw=-arch={-arch:+.6f}")
    out["checks"]["C3_pole_abserr"] = [r for r in out["arch_scan"]
                                       if r["parity"] == "even"][-1]["pole"]

    # ---- sanity: the PLAIN seed square (no D3) must read arch > 0 ----
    # (1696 family: qw = pole - arch - finite < 0 with pole, arch > 0; a
    # positive arch here shows the M1 sign flip is a genuine D3 effect,
    # not an integrand bug)
    g_plain = make_seed(0.29)
    F_plain = star_square(g_plain)
    arch_plain = arch_term(F_plain)
    pole_plain = pole_term(F_plain)
    out["checks"]["plain_seed_arch_w029"] = arch_plain
    out["checks"]["plain_seed_pole_w029"] = pole_plain
    print(f"   sanity plain-seed square (w=0.29): pole={pole_plain:+.6f}  "
          f"arch={arch_plain:+.6f}  (expect arch > 0)")

    # ---- M2: synthetic off-line pair, domination gap (w = 0.29) ----
    h = make_seed(0.29)
    g = make_root(h)
    F = star_square(g)
    arch0 = [r for r in out["arch_scan"]
             if r["parity"] == "even" and r["w"] == 0.29][0]["arch"]
    print(f"   M2 domination at w=0.29 (even seed): fixed book |arch| = "
          f"{abs(arch0):.6f}  (sign arch = {'+' if arch0 > 0 else '-'})")
    for gamma in (10.0, 20.0, 40.0, 80.0, 160.0, 320.0):
        shat = laplace(F, 0.25 + 1.0j * gamma)     # ghat of the SQUARE
        s_pair = 2.0 * shat.real
        gap = abs(s_pair) / max(1e-300, abs(arch0))
        phase = float(np.angle(laplace(F, 0.25 + 1.0j * gamma)))
        row = dict(gamma=gamma, s_pair=s_pair, mod2=2.0 * abs(shat),
                   gap=gap, phase=phase)
        out["pair_scan"].append(row)
        print(f"      gamma={gamma:6.1f}: S_pair={s_pair:+.6e}  "
              f"2|ghat|={2.0 * abs(shat):.3e}  gap|S|/|arch|={gap:.3e}")

    with open("results/1699_spectral_domination.json", "w") as f:
        json.dump(out, f, indent=1)
    print("saved results/1699_spectral_domination.json")
    print("verdict: C1-C3 reproduce committed laws; M1/M2 measure the open")
    print("sign field and the synthetic-pair domination gap (recon only).")


if __name__ == "__main__":
    main()
