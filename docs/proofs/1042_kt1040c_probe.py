#!/usr/bin/env python3
"""KT-1040c numerical probe: synthetic off-line zero stress test (1040 §7).

QUESTION.  The W4b-bound says qw >= 0 follows once the right-half spectral
residual is controlled by the on-line mass on the F-vanishing subspace
(C1SpectralQwAssembly.qw_nonneg_of_rightHalfSpectralSum_re_ge_neg_half_onLine
and its modulus form qw_nonneg_of_offLineNormMass_le_onLineSpectralMass).
How much slack does that inequality really have?  KT-1040a/b measured qw on
the actual (all on-line) zero configuration; this probe RELOCATES the first
K zeta zeros off the critical line to abscissa beta = 1/2 + delta and
watches the margin.

INJECTION ARITHMETIC (repo identities, real g):
  Hermitian square law   L_{g^2}(s) = conj(L_g(-conj s)) * L_g(s)
                          (C1HealthyYoshidaDetector.lean:48)
  W4b-pairing            offLineSpectralMass = 2 * Re(right-half tsum)
                          (C1SpectralOfflinePairing.lean:143)
  W1 on-line collapse    term(i*gamma) = |L_g(i*gamma)|^2
                          (C1SpectralOnlineNonneg.lean:50)
A zero at beta+i*gamma arrives with its three mirrors (delta, -delta) x
(+gamma, -gamma), all multiplicity 1.  Putting w = delta + i*gamma,
  u = L_g(+delta + i*gamma),   v = L_g(-delta + i*gamma),
  right-half tsum gains  term(w) + term(conj w) = 2 Re[conj(v) u],
  off-line mass gains    2 * Re(right-half)     = 4 Re[conj(v) u],
  on-line mass loses     |L(i gamma)|^2 + |L(-i gamma)|^2 = 2 |L(i gamma)|^2.
So the visible margin moves by
  Delta_j(delta) = 4 Re[conj(v_j) u_j] - 2 |L_g(i gamma_j)|^2,
and the hypothetical-world value is  qw_hyp = qw_true + sum_{j<=K} Delta_j.
Phase-worst floor (modulus ladder, |term| = |v||u|):
  qw_hyp >= qw_true - sum_{j<=K} (4 |v_j||u_j| + 2 |L_j|^2).

CAVEATS (steering only, 1040 §7): first 16 ordinates; tail uncontrolled;
the relocated configuration is synthetic (the zero count jumps: a self-
partnered on-line pair becomes a four-zero orbit, so small delta injects
EXTRA positive mass — conservative in the safe direction only near delta=0;
large delta is the genuine stress).  Not a witness, not a bound.

Numerics: reuses the validated KT-1040a/b pipeline (1041) unchanged via
importlib; grid 2^18 (2^19 spot check), L_g(s) = int e^{s x} g(x) dx by
trapz on the periodic grid (CC20YoshidaConvolution.lean:55 convention).
"""
import importlib.util
import os
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "p1041", os.path.join(HERE, "1041_kt1040_probe.py"))
p1041 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(p1041)

DELTAS = [0.01, 0.05, 0.1, 0.2, 0.3, 0.4, 0.49]      # beta = 0.51 .. 0.99
KS = [1, 2, 4, 8, 16]


def Lg_at(P, g, sig):
    """L_g(sig + i*gamma_j), j = 1..16 (repo sign convention +s*x)."""
    E = np.exp(np.outer(sig + 1j * p1041.GAMMAS, P.xs))
    return (E * P.wt) @ g


def member_g(P, c):
    """The normalized test g behind pipeline member(c) (int g^2 = 1)."""
    g = c @ P.G
    f0 = float(np.sum(P.wt * g * g))
    return g / np.sqrt(f0)


def scan(P, c):
    """Full (delta, K) sweep for one member; returns qw_true and the grids."""
    g = member_g(P, c)
    d = P.member(c)
    qw = d["qw"]
    L0 = (P.E * P.wt) @ g
    on2 = 2.0 * np.abs(L0) ** 2                        # on-line pair |L|^2 * 2
    hyp = np.empty((len(DELTAS), len(KS)))
    worst = np.empty((len(DELTAS), len(KS)))
    amp = np.empty(len(DELTAS))
    for a, delta in enumerate(DELTAS):
        u = Lg_at(P, g, delta)
        v = Lg_at(P, g, -delta)
        pair = 4.0 * np.real(np.conj(v) * u)           # injected off-line mass
        floor = -(4.0 * np.abs(v) * np.abs(u) + on2)   # phase-worst Delta_j
        amp[a] = float(np.max(np.abs(v) * np.abs(u) / (np.abs(L0) ** 2 + 1e-300)))
        for b, K in enumerate(KS):
            hyp[a, b] = qw + float(np.sum(pair[:K] - on2[:K]))
            worst[a, b] = qw + float(np.sum(floor[:K]))
    return dict(qw=qw, on2=on2, hyp=hyp, worst=worst, amp=amp,
                L0=L0, g=g, diag=d)


def main():
    P18 = p1041.Pipeline(1 << 18)
    names = list(p1041.WITNESSES)
    members = {n: p1041.build_witness_c(P18, n) for n in names}
    names.append("K=8 SVD kill")
    members["K=8 SVD kill"] = p1041.svd_kill_c(P18, 8)

    print(f"basis {P18.M} members; grid 2^{18}; deltas {DELTAS}; K {KS}")
    print(f"beta = 1/2 + delta; pairs inject 4 Re[conj(v)u], remove 2|L|^2\n")

    rows = []
    for n in names:
        r = scan(P18, members[n])
        i, j = np.unravel_index(np.argmin(r["hyp"]), r["hyp"].shape)
        wv = float(np.min(r["worst"]))
        rows.append((n, r))
        print(f"[{n}]  qw_true = {r['qw']:+.6f}")
        print(f"    min qw_hyp = {r['hyp'][i, j]:+.6f} "
              f"at delta={DELTAS[i]:.2f} (beta={0.5 + DELTAS[i]:.2f}), K={KS[j]}")
        print(f"    phase-worst floor over all (delta,K) = {wv:+.6f}")
        print(f"    max off-line/on-line modulus amplification |vu|/|L|^2: "
              f"{', '.join(f'{a:.2f}' for a in r['amp'])}")

    # 2^19 spot check on the global-worst member
    worst_name, worst_r = min(rows, key=lambda t: float(np.min(t[1]["hyp"])))
    P19 = p1041.Pipeline(1 << 19)
    c19 = (p1041.build_witness_c(P19, worst_name)
           if worst_name in p1041.WITNESSES else p1041.svd_kill_c(P19, 8))
    r19 = scan(P19, c19)
    i, j = np.unravel_index(np.argmin(r19["hyp"]), r19["hyp"].shape)
    print(f"\n2^19 spot check on global-worst [{worst_name}]: "
          f"min qw_hyp = {r19['hyp'][i, j]:+.6f} "
          f"(2^18 gave {float(np.min(worst_r['hyp'])):+.6f})")

    min_all = min(float(np.min(r["hyp"])) for _, r in rows)
    min_worst = min(float(np.min(r["worst"])) for _, r in rows)
    print("\n== VERDICT (steering only; 1040 §7) ==")
    v = ("GREEN (margin positive at every beta, K)" if min_all > 0 else
         "RED: margin dies - W4b-bound is tight there")
    print(f"KT-1040c: min qw_hyp over all (member, delta, K) = {min_all:+.6f}  -> {v}")
    vw = ("phase-worst floor also positive: W4 slack is structural" if min_worst > 0
          else f"phase-worst floor dips to {min_worst:+.6f}: slack relies on phases")
    print(f"          min phase-worst floor                    = {min_worst:+.6f}  -> {vw}")
    print("caveat: synthetic relocated zeros, first 16 ordinates only, tail")
    print("uncontrolled; steering evidence for W4b-bound, not a bound.")


if __name__ == "__main__":
    main()
