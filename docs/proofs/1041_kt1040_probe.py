#!/usr/bin/env python3
"""KT-1040a/b numerical probe: qw on wide F-vanishing families (1040 §7).

KT-1040a  second-witness sweep: qw on plain wide F-vanishing tests from
          several bump shapes/centers/widths (plateau and non-plateau
          profiles).  GREEN = all witnesses positive.
KT-1040b  adversarial on-line-mass minimization: SVD combinations of a
          20-member bump basis that kill the Fourier coefficients at the
          first K zeta-zero ordinates (K = 1..8); watch qw.

Every formula is the repo's own (Lean refs):
  F-vanishing = laplaceAt g = 0 at s in {0, 1/2, 1}
      criticalVanishingPointValue, CC20RHExit.lean:21-29; the healthy space's
      mellinAt := CompactLogTest.laplaceAt, C1HealthyTestSpace.lean:47.
  g = P(D)h with P(D) = D(D+1/2)(D+1)  =>  L_g(s) = (0-s)(1/2-s)(1-s) L_h(s)
      (integration by parts on compact support; the SAME operator as the
      proven-positive narrow root: tripleVanishingRoot, C1LaneRD3Root.lean:264;
      g_v(x) = t''' + (3/2)t'' + (1/2)t', from the archived narrow-width probe header).
      Hence for EVERY h: poleTerm(g^2) = Re[L_F(1/2)+L_F(-1/2)] = 0 exactly,
      by the Hermitian square law L_{g^2}(s) = conj(L_g(-conj s)) * L_g(s)
      (C1HealthyYoshidaDetector.lean:48), and the probe tracks qw by
  qw g = poleTerm F - archTerm F - primeSum F,   F = g.convolutionSquare
      C1SameOwnerWeil.lean:192-197.
  archTerm F = Re[(log 4pi + gamma) F(0)
                 + int_{y>0} (e^{y/2}(F(y)+F(-y)) - 2 F(0)) / (e^y-e^{-y}) dy]
      C1SameOwnerWeil.lean:48-64; denominator SelectedWeilFormula.lean:103.
      F is even (autocorrelation of a real test) => F(y)+F(-y) = 2 F(y);
      y->0 limit of the integrand = F(0)/2 (F'(0)=0 by evenness);
      beyond the support radius A of F the integrand is -2F(0)/(2 sinh y),
      whose tail integral is -2 F(0) atanh(e^{-A}).
  primeSum F = sum_{n prime power, log n <= A} Lambda(n) n^{-1/2} 2 F(log n)
      C1SameOwnerWeil.lean:36-46,161 (globalPrimeIndexSet; F even used once).
  on-line pair mass = sum_j 2 * |L_g(i gamma_j)|^2   (m(rho_j)=1: the first
      zeros are simple and on the critical line; W1 collapses the term to the
      square modulus, C1SpectralOnlineNonneg.lean; conjugate partners carry
      equal multiplicity, W4a: C1SpectralHermitianPartner.lean:152).
      L_g(s) = int e^{sx} g(x) dx, CC20YoshidaConvolution.lean:55.
      Partial (first 16 zeros only): the tail is NOT controlled here.

Numerics: the validated p3_probe pipeline — spectral differentiation on a
periodic grid, FFT autocorrelation for F, trapz for the arch integral,
cubic-spline sampling of F at log n.  Zero ordinates are the standard tabulated
first 16 (all simple, on the line).  Steering-grade evidence only (1040 §7);
not a rigorous witness.

Grid: period T = 16, basis supports inside [-2.4, 2.4] => supp F <= [-4.8, 4.8]
(4.8 < 16 - 4.8, so circular autocorrelation is uncontaminated), visible prime
powers n <= e^{4.8} = 121.  Convergence: N = 2^17 vs 2^18 (+ 2^19 spot check).
"""
import numpy as np
from scipy.interpolate import CubicSpline

BSQ = 0.9 ** 2                                          # Wall14PlateauExplicit.lean:24
GAMMA = 0.57721566490153286060                          # eulerMascheroniConstant
C_ARCH = float(np.log(4 * np.pi) + GAMMA)               # C1SameOwnerWeil.lean:62
SUPP_HALF = 2.4                                         # basis support window
A_SUPP = 2 * SUPP_HALF                                  # supp radius of F = 4.8
NPP_MAX = int(np.floor(np.exp(A_SUPP)))                 # 121
T = 16.0                                                # grid period

GAMMAS = np.array([                                     # first 16 zero ordinates
    14.1347251417346938, 21.0220396387715550, 25.0108575801456879,
    30.4248761258595132, 32.9350615877399967, 37.5861781588256713,
    40.9187190121474952, 43.3270732809149996, 48.0051508811671597,
    49.7738324776723022, 52.9703214777144606, 56.4462476970633958,
    59.3470440026028033, 60.8317785245594897, 65.1125440480865287,
    67.0798105294981736])


def bumpEx(x):
    """Wall-14 plateau bump, support [-1,1], plateau [-0.9,0.9]; as P3-0/P3-a·0."""
    u = (x * x - BSQ) / (1.0 - BSQ)
    if np.ndim(u) == 0:
        a, b = glue(x), glue(1.0 - x)
        return float(1.0 - (a / (a + b)))
    out = np.empty_like(np.asarray(x, dtype=float))
    uu = np.asarray(u, dtype=float)
    m0 = uu <= 0
    m1 = uu >= 1
    mid = ~(m0 | m1)
    out[m0] = 1.0
    out[m1] = 0.0
    if np.any(mid):
        um = uu[mid]
        a = np.exp(-1.0 / um)
        b = np.exp(-1.0 / (1.0 - um))
        out[mid] = 1.0 - a / (a + b)
    return out


def glue(u):
    return float(np.exp(-1.0 / u)) if u > 0 else 0.0


def smoothBump(u):
    """Non-plateau C^inf bump on [-1,1]: exp(-1/(1-u^2)); genuinely different
    mass distribution from the plateau profile (no flat core)."""
    u = np.asarray(u, dtype=float)
    out = np.zeros_like(u)
    mid = np.abs(u) < 1.0
    out[mid] = np.exp(-1.0 / (1.0 - u[mid] ** 2))
    return out


def prime_powers(nmax):
    """(n, Lambda(n)) for every prime power n <= nmax."""
    pp = []
    sieve = np.ones(nmax + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, nmax + 1):
        if sieve[p]:
            sieve[p * p:: p] = False
            pk = p
            while pk <= nmax:
                pp.append((pk, float(np.log(p))))
                pk *= p
    return pp


PP = prime_powers(NPP_MAX)
PP_N = np.array([n for n, _ in PP], dtype=float)
PP_L = np.array([l for _, l in PP])


class Pipeline:
    """Shared grid, basis, and derivative machinery at resolution nfft."""

    def __init__(self, nfft):
        self.N = nfft
        self.hgrid = T / nfft
        j = np.arange(nfft)
        self.xs = -T / 2 + j * self.hgrid               # monotone grid, [-8, 8)
        wt = np.full(nfft, self.hgrid)
        wt[0] = wt[-1] = self.hgrid / 2                 # trapz weights
        self.wt = wt
        wmode = 2.0 * np.pi * np.fft.fftfreq(nfft, d=self.hgrid)
        self.E = np.exp(1j * np.outer(GAMMAS, self.xs))  # (16, N) for L(i*gamma)

        # basis: (profile, center, width); supports stay inside [-2.4, 2.4]
        self.basis = [(prof, a, w)
                      for prof in ("plateau", "smooth")
                      for a in (-1.5, -0.75, 0.0, 0.75, 1.5)
                      for w in (0.6, 0.9)]
        self.M = len(self.basis)
        H0 = np.empty((self.M, nfft))
        G = np.empty((self.M, nfft))                    # P(D) h_i per basis
        for i, (prof, a, w) in enumerate(self.basis):
            f = self._profile(prof, (self.xs - a) / w)
            H0[i] = f
            spec = np.fft.fft(f)
            B1 = np.real(np.fft.ifft(1j * wmode * spec))
            B2 = np.real(np.fft.ifft((1j * wmode) ** 2 * spec))
            B3 = np.real(np.fft.ifft((1j * wmode) ** 3 * spec))
            G[i] = B3 + 1.5 * B2 + 0.5 * B1             # P(D) = D^3+3/2 D^2+1/2 D
        self.H0, self.G = H0, G
        self.A = (self.E * wt) @ H0.T                     # (16, M) = L_{h_i}(i gamma_j)

    @staticmethod
    def _profile(prof, u):
        return bumpEx(u) if prof == "plateau" else smoothBump(u)

    def member(self, c):
        """g = sum c_i P(D)h_i, normalized to int g^2 = 1; returns a dict of
        every readback quantity (all under F(0) = int g^2 = 1)."""
        g = c @ self.G
        f0 = float(np.sum(self.wt * g * g))
        g = g / np.sqrt(f0)
        hgrid = self.hgrid
        N = self.N

        # F = autocorrelation of g on the grid (circular; support uncontaminated)
        C = np.fft.ifft(np.abs(np.fft.fft(g)) ** 2).real
        F_mono = np.concatenate([C[N // 2:], C[: N // 2]]) * hgrid  # y = -8..8
        y_mono = self.xs
        F0 = float(C[0] * hgrid)

        # archimedean term: c*F0 + int_0^A_eff + tail -2 F0 atanh(e^-A_eff)
        kmax = int(np.floor(A_SUPP / hgrid))
        yk = np.arange(kmax + 1) * hgrid
        Fk = C[: kmax + 1] * hgrid
        num = 2.0 * (np.exp(0.5 * yk) * Fk - F0)
        J = np.empty_like(num)
        J[1:] = num[1:] / (2.0 * np.sinh(yk[1:]))
        J[0] = F0 / 2.0                                  # analytic y->0 limit
        I_main = float(np.trapezoid(J, yk))
        arch = C_ARCH * F0 + I_main - 2.0 * F0 * float(np.arctanh(np.exp(-yk[-1])))

        # finite prime sum: Lambda(n) n^{-1/2} * 2 F(log n), spline-sampled
        spl = CubicSpline(y_mono, F_mono)
        prime_sum = float(np.sum(PP_L * PP_N ** -0.5 * 2.0 * spl(np.log(PP_N))))

        # spectral coefficients and vanishing diagnostics
        Lg = (self.E * self.wt) @ g                      # L_g(i gamma_j), j=1..16
        on_line16 = 2.0 * float(np.sum(np.abs(Lg) ** 2))
        Mhalf = float(np.sum(self.wt * g * np.exp(0.5 * self.xs)))
        Mmhalf = float(np.sum(self.wt * g * np.exp(-0.5 * self.xs)))
        M0 = float(np.sum(self.wt * g))
        M1 = float(np.sum(self.wt * g * np.exp(self.xs)))
        nc = float(np.linalg.norm(c))
        killres = float(np.linalg.norm(self.A @ c)) / nc if nc > 0 else 0.0

        qw = -arch - prime_sum                           # poleTerm == 0 exactly
        return dict(F0=F0, F0_trapz=float(np.sum(self.wt * g * g)), arch=arch,
                    I_main=I_main, prime=prime_sum, qw=qw, on16=on_line16,
                    diag_pole=2.0 * Mhalf * Mmhalf, diag_v0=M0,
                    diag_vh=Mhalf, diag_v1=M1, killres=killres,
                    Lg2_first8=2.0 * float(np.sum(np.abs(Lg[:8]) ** 2)))


def fmt_row(name, d, extra=""):
    return (f"{name:<26} qw={d['qw']:+.6f}  arch={d['arch']:+.6f}  "
            f"prime={d['prime']:+.6f}  on16={d['on16']:.6f}  "
            f"qw-on16={d['qw'] - d['on16']:+.6f} {extra}")


def build_witness_c(P, name):
    """Coefficient vector of a named KT-1040a witness in pipeline P."""
    i = lambda prof, a, w: P.basis.index((prof, a, w))
    if name == "wA plateau c=0 w=0.9":
        c = np.zeros(P.M); c[i("plateau", 0.0, 0.9)] = 1.0
    elif name == "wB plateau c=0.75 w=0.9":
        c = np.zeros(P.M); c[i("plateau", 0.75, 0.9)] = 1.0
    elif name == "wC smooth c=0 w=0.9":
        c = np.zeros(P.M); c[i("smooth", 0.0, 0.9)] = 1.0
    elif name == "wD smooth c=-0.75 w=0.6":
        c = np.zeros(P.M); c[i("smooth", -0.75, 0.6)] = 1.0
    else:  # wE combo
        c = np.zeros(P.M)
        c[i("plateau", 0.0, 0.9)] = 1.0
        c[i("plateau", 1.5, 0.6)] = 0.7
    return c


def svd_kill_c(P, K):
    """Smallest right-singular direction of the first K on-line coefficients."""
    if K == 0:
        return build_witness_c(P, "wA plateau c=0 w=0.9")
    S = np.vstack([P.A[:K].real, P.A[:K].imag])
    _, _, Vt = np.linalg.svd(S)
    return Vt[-1]


WITNESSES = ["wA plateau c=0 w=0.9", "wB plateau c=0.75 w=0.9",
             "wC smooth c=0 w=0.9", "wD smooth c=-0.75 w=0.6", "wE combo"]


def main():
    print(f"c = log(4*pi)+gamma = {C_ARCH:.15f}")
    print(f"basis: {len(Pipeline(8).basis)} members (plateau+smooth x 5 centers x 2 widths),"
          f" supports within +-{SUPP_HALF};  supp F <= +-{A_SUPP};"
          f" prime powers <= {NPP_MAX} ({len(PP)} terms)")
    print("first-16 on-line pair mass uses m=1 (simple zeros), W4a partner factor 2\n")

    P17, P18 = Pipeline(1 << 17), Pipeline(1 << 18)

    print("== KT-1040a: second witnesses (plain, no kills) ==")
    a_results = {}
    for name in WITNESSES:
        d18 = P18.member(build_witness_c(P18, name))
        d17 = P17.member(build_witness_c(P17, name))
        a_results[name] = d18
        conv = abs(d18["qw"] - d17["qw"])
        print(fmt_row(name, d18) + f"  conv(d17)={conv:.2e}")
        print(f"{'':>26} diagnostics: pole={d18['diag_pole']:+.2e} "
              f"vanish(0,1/2,1)=({d18['diag_v0']:+.1e},{d18['diag_vh']:+.1e},"
              f"{d18['diag_v1']:+.1e})  F0={d18['F0']:.12f}"
              f" (trapz {d18['F0_trapz']:.12f})")

    print("\n== KT-1040b: kill first K on-line coefficients (SVD), watch qw ==")
    print(f"{'K':>3} | {'qw':>12} | {'arch':>10} | {'prime':>12} | "
          f"{'on16':>10} | {'qw-on16':>12} | kill resid")
    b_trend = []
    for K in (0, 1, 2, 4, 6, 8):
        d18 = P18.member(svd_kill_c(P18, K))
        d17 = P17.member(svd_kill_c(P17, K))
        conv = abs(d18["qw"] - d17["qw"])
        Lg = (P18.E * P18.wt) @ (svd_kill_c(P18, K) @ P18.G) / np.sqrt(d18["F0"])
        killed = 2.0 * float(np.sum(np.abs(Lg[:K]) ** 2)) if K else 0.0
        b_trend.append((K, d18))
        print(f"{K:>3} | {d18['qw']:+12.6f} | {d18['arch']:+10.6f} | "
              f"{d18['prime']:+12.6f} | {d18['on16']:10.6f} | "
              f"{d18['qw'] - d18['on16']:+12.6f} | {d18['killres']:.2e}"
              f"  killed~{killed:.1e}  conv={conv:.1e}")

    # 2^19 spot check on the most adversarial member across both tests
    all_members = [(name, d) for name, d in a_results.items()] + \
                  [(f"K={k}", d) for k, d in b_trend]
    worst_name, worst = min(all_members, key=lambda t: t[1]["qw"])
    P19 = Pipeline(1 << 19)
    c19 = build_witness_c(P19, worst_name) if worst_name in WITNESSES \
        else svd_kill_c(P19, int(worst_name[2:]))
    d19 = P19.member(c19)
    print(f"\n2^19 spot check on most adversarial member [{worst_name}]: "
          f"qw = {d19['qw']:+.6f}  (2^18 gave {worst['qw']:+.6f})")

    min_a = min(d["qw"] for d in a_results.values())
    min_b = min(d["qw"] for _, d in b_trend)
    print("\n== VERDICT (steering only; 1040 §7) ==")
    a_verdict = "GREEN (all positive)" if min_a > 0 else "RED: negative witness"
    b_verdict = ("qw stays positive: W4 slack signal" if min_b > 0 else
                 "qw <= 0 at small on-line mass: W4 tight/false - "
                 "find the compensating term first")
    print(f"KT-1040a: min witness qw = {min_a:+.6f}  -> {a_verdict}")
    trend = ", ".join(f"K={k}:{d['qw']:+.3f}" for k, d in b_trend)
    print(f"KT-1040b trend: {trend}")
    print(f"KT-1040b: min qw = {min_b:+.6f}  -> {b_verdict}")
    print("caveat: on16 counts only the first 16 zeros; tail mass is uncontrolled,")
    print("so 'slack' means no negative-qw signal inside this bounded family.")


if __name__ == "__main__":
    main()
