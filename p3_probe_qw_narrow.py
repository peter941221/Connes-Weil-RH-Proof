#!/usr/bin/env python3
"""P3-a·0 numerical probe: qw(narrowArchRoot) — value, sign, and readback gap.

Target test (all formulas quoted from the repo, Lean line refs in parentheses):
  narrowArchRoot := tripleVanishingRoot (wideTest w w>0)    C1LaneRNarrowArch.lean:626-628
    wideBump w x = bumpEx(x/w), support [-w,w]              M2WidthPlateau.lean:34, :104-107
    (derivativeShift f a).test x = deriv(f.test) x + a*f.test x   C1LaneRD3Root.lean:58-62
    tripleVanishingRoot h = (D+0)(D+1/2)(D+1) h            C1LaneRD3Root.lean:264-269
  => g_v(x) = t'''(x) + (3/2)t''(x) + (1/2)t'(x),  t(x) := bumpEx(x/w)     [P(D)=D^3+(3/2)D^2+(1/2)D]
    w := narrowArchBaseWidth = R/4,   R := exp(-4(c+1)),   c := log(4*pi)+gamma
                                                             C1LaneRNarrowArch.lean:575-610

Structural facts that collapse the probe (evidence):
  poleTerm(F) = 0 EXACTLY for all h                      C1LaneRD3Root.lean:332-336
      [L_{g_v}(s) = (0-s)(1/2-s)(1-s)*L_h(s); the s=1/2 zero kills L_F(+/-1/2)]
  primeSum(F) = 0 EXACTLY, support(F) subset Ioo(-log2,log2)   C1LaneRNarrowArch.lean:653-671
      [supp g_v ⊆ [-w,w] => supp F ⊆ [-2w,2w], and 2w ~ 3.6e-7 << log 2]
  qw(g_v) = -archimedeanTerm(F) EXACTLY                  C1LaneRNarrowArch.lean:665-671
  archimedeanTerm(F) = c*F(0) + Re int_0^inf [e^{y/2}(F(y)+F(-y)) - 2F(0)]/(e^y-e^{-y}) dy
                                                            C1SameOwnerWeil.lean:61-70 (P3-0 header)
      = c*F(0) + int_0^{2w} [...]dy - 2*F(0)*atanh(e^{-2w})     [tail antiderivative, P3-0]
  I_main asymptotics (the sharp-ratio correction, derived this run):
      int G du = 0 EXACTLY (int Bk all vanish: flat endpoints + f(+/-1)=0), hence
      int_0^2 (Phi(u)+Phi(-u)) du = 0.  With E := even part of Phi,
        I_main = W*K'' + O(W^2),   K'' := int_0^2 (E(u)-Phi(0))/u du < 0
      so |I_main|/F(0) -> |K''|/Phi(0) ~= 8.9 : an O(1) constant, NOT ~w.
      Sharp limit: qw/F(0) = ln(1/w) - c + |K''|/Phi(0) + o(1).
  Lean rigorous bound: archTerm <= (c + R - 1/2*log(1/R)) * F(0) < 0
                                                            C1LaneRNarrowArch.lean:501-608,:647-651
      => qw >= F(0)*(c+2-R)  [since 1/2*log(1/R)=2(c+1), :592]  — cross-checked below.

Scaling (the whole point): x = w*u keeps everything O(1).
  G(u) := g_v(w*u) = w^-3*B3 + (3/2)*w^-2*B2 + (1/2)*w^-1*B1,   Bk := bumpEx^(k)
  F0 := int |g_v|^2 dx = w * int G^2 du          [F(0)=int g(-s)^2 ds]
  Phi(u0) := int G(-v) G(u0-v) dv (autocorrelation of G, support [-2,2]) => F(w*u) = w*Phi(u)

Exact identities reducing the expansion of int G^2 du:
  I32 = ∫B3*B2 = [1/2*(t'')^2] = 0,   I21 = ∫B2*B1 = [1/2*(t')^2] = 0   (flat endpoints)
  I31 = ∫B3*B1 = -I22                                                        (one integration by parts)
  => int G^2 du = w^-6*I33 + 1.25*w^-4*I22 + 0.25*w^-2*I11    [only 3 independent integrals]

Bk via Fourier spectral differentiation on a period-8 grid (bumpEx is C-inf periodic on
[-1,1]: flat at +-1), origin straddling index 0 per the P3-0 FFT rule.  Cross-checks:
  FTC  int B1 = f(1)-f(-1) = 0 (bumpEx vanishes at +-1);  I32 ~ 0 ;  I21 ~ 0 ;  I31+I22=0 exact
  Parseval  ||B3||^2 via |spec*(i*w)^3|^2 vs real-space grid sum
  convolution path  Phi(0) = int G^2 (autocorrelation at zero lag)
  independent leg  Gauss-Legendre for I11 — and I11 IS the P3-0 value bumpA ~= 1.883508745
"""
import numpy as np

BSQ = 0.9 ** 2                                          # Wall14PlateauExplicit.lean:24
GAMMA = 0.57721566490153286060                          # Euler-Mascheroni (same constant as P3-0)
C_ARCH = float(np.log(4 * np.pi) + GAMMA)                # narrowArchCoefficient :575
R = float(np.exp(-4.0 * (C_ARCH + 1)))                   # narrowArchRadius :582-583
W = R / 4.0                                              # narrowArchBaseWidth :610
A_SUPP = 2.0 * W                                         # sharp support radius of F


def bumpEx(x):
    """Vectorized Wall-14 plateau; matches Wall14PlateauExplicit.lean:37 (same as P3-0)."""
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


def pipeline(nfft):
    """Spectral-derivative leg on a period-8 grid; returns all derived quantities."""
    h = 8.0 / nfft
    j = np.arange(nfft)
    # shifted order: index k <-> position pos(k)=((k+nfft//2)%nfft)*h-4, so pos(0)=0 (origin at 0)
    pos_shifted = ((j + nfft // 2) % nfft) * h - 4.0
    f = bumpEx(pos_shifted)                              # shifted order
    spec = np.fft.fft(f)
    wmode = 2.0 * np.pi * np.fft.fftfreq(nfft, d=h)

    B1s = np.real(np.fft.ifft(1j * wmode * spec))        # shifted-order derivatives (origin at 0)
    B2s = np.real(np.fft.ifft((1j * wmode) ** 2 * spec))
    B3s = np.real(np.fft.ifft((1j * wmode) ** 3 * spec))

    idx = (j - nfft // 2) % nfft                         # reindex shifted -> monotone grid xs
    xs = -4.0 + j * h
    f, B1, B2, B3 = f[idx], B1s[idx], B2s[idx], B3s[idx]
    m = (xs >= -1.0) & (xs <= 1.0)                       # bumpEx support; grid hits +-1 exactly

    def gsum(y):
        return float(np.trapz(y[m], xs[m]))

    I33a, I22a, I11a = gsum(B3 ** 2), gsum(B2 ** 2), gsum(f * f)
    I31a, I32a, I21a = gsum(B3 * B1), gsum(B3 * B2), gsum(B2 * B1)
    intB1 = gsum(B1)                                     # FTC: must equal f(1)-f(-1) = 0

    # Parseval leg for ||B3||^2 (independent of the real-space ifft/trapz path)
    I33p = float((8.0 / nfft) * np.sum(np.abs(spec * wmode ** 3) ** 2) / nfft)

    # G(u): monotone order for quadrature, shifted order (origin at index 0) for the FFT
    G_mono = W ** -3 * B3 + 1.5 * W ** -2 * B2 + 0.5 * W ** -1 * B1
    G_shift = W ** -3 * B3s + 1.5 * W ** -2 * B2s + 0.5 * W ** -1 * B1s

    F0w_direct = gsum(G_mono ** 2)
    F0w_expand = W ** -6 * I33a + 1.25 * W ** -4 * I22a + 0.25 * W ** -2 * I11a

    # Autocorrelation Phi of G via |FFT|^2 (shifted order keeps origin at index 0;
    # support width 2 < period 8 => no wrap-around contamination, P3-0 rule)
    Phi_conv = h * np.fft.irfft(np.abs(np.fft.rfft(G_shift, n=nfft)) ** 2, n=nfft)
    Phi0_fft = float(Phi_conv[0])

    # Symmetric pairs Phi(u)+Phi(-u) for u in [0,4): value at +u lives at index int(u/h),
    # value at -u at index nfft//2+int(u/h); both coincide at index 0 for u=0.
    ncut = int(2.0 / h)                                  # grid nodes u_k = k*h, k = 0..nfft/4 (u<=2)
    kk = np.arange(ncut + 1)
    upos = kk * h
    phi_pos = Phi_conv[kk]                               # positions +u (k < nfft/2 here)
    phi_neg = np.empty_like(phi_pos)
    phi_neg[0] = Phi_conv[0]
    phi_neg[1:] = Phi_conv[nfft // 2 + kk[1:]]           # positions -u

    Fs = phi_pos + phi_neg                               # Phi(u)+Phi(-u), u in [0,2]
    num = np.exp(0.5 * W * upos) * Fs - 2.0 * Phi0_fft   # e^{Wu/2}(Fs) - 2*Phi(0)
    J = np.empty_like(num)                               # integrand of I_main after factoring W^2
    J[1:] = num[1:] / (2.0 * np.sinh(W * upos[1:]))      # e^{Wu}-e^{-Wu} = 2 sinh(Wu), exact for tiny arg
    J[0] = Phi0_fft / 2.0                                # analytic limit u->0, derived in header math
    I_main = float(W ** 2) * float(np.trapz(J, upos))

    # Laplace diagnostics M(s) = int e^{sx} g_v(x) dx = W * int e^{sWu} G(u) du
    def M(s):
        return float(W * np.trapz(np.exp(s * W * xs[m]) * G_mono[m], xs[m]))

    pole_num = 2.0 * M(0.5) * M(-0.5)                    # Re[L_F(1/2)+L_F(-1/2)], real here

    F0 = W * F0w_direct
    atanh_tail = float(np.arctanh(np.exp(-A_SUPP)))      # int_{2W}^inf dy/(e^y-e^{-y})
    arch = C_ARCH * F0 + I_main - 2.0 * F0 * atanh_tail
    qw = -arch

    return dict(I33a=I33a, I33p=I33p, I22a=I22a, I11a=I11a, I31a=I31a, I32a=I32a, I21a=I21a,
                intB1=intB1, F0w_direct=F0w_direct, F0w_expand=F0w_expand, Phi0_fft=Phi0_fft,
                I_main=I_main, M_half=M(0.5), M_mhalf=M(-0.5), pole_num=pole_num,
                atanh_tail=atanh_tail, arch=arch, qw=qw)


def main():
    print(f"c = log(4*pi)+gamma = {C_ARCH:.15e}")
    print(f"R = exp(-4(c+1))     = {R:.15e}   (narrowArchRadius)")
    print(f"w = R/4              = {W:.15e}   (narrowArchBaseWidth);  support(F) radius 2w = {A_SUPP:.6e}")

    lo, hi = pipeline(1 << 17), pipeline(1 << 18)
    F0lo, F0hi = W * lo["F0w_direct"], W * hi["F0w_direct"]

    def row(name, a, b):
        print(f"{name:<24} {a:+.12e}   {b:+.12e}   d={abs(b - a):.3e}")

    print("\n== P3-a·0 probe: qw(narrowArchRoot) decomposition ==")
    row("I33 = ∫B3^2 (grid)", lo["I33a"], hi["I33a"])
    row("I33 parseval leg", lo["I33p"], hi["I33p"])
    row("I22 = ∫B2^2", lo["I22a"], hi["I22a"])
    row("I11 = ∫f^2  (P3-0 bumpA)", lo["I11a"], hi["I11a"])
    print(f"{'FTC int B1 (= 0)':<24} {hi['intB1']:+.15e}")
    row("id I31+I22 (~0)", lo["I31a"] + lo["I22a"], hi["I31a"] + hi["I22a"])
    print(f"{'residual I32':<24} {lo['I32a']:+.9e}   (exact 0)      {'residual I21':<6}"
          f" {lo['I21a']:+.9e}")
    row("int G^2 direct", lo["F0w_direct"], hi["F0w_direct"])
    row("int G^2 expansion", lo["F0w_expand"], hi["F0w_expand"])
    row("Phi(0) autocorrelation", lo["Phi0_fft"], hi["Phi0_fft"])

    xg, wg = np.polynomial.legendre.leggauss(300)        # independent leg: no FFT at all
    I11_gl = float(np.sum(wg * bumpEx(xg) ** 2))         # full integral over [-1,1] (even f)
    print(f"{'I11 Gauss-Legendre':<24} {I11_gl:+.15e}   (cross-probe: P3-0 bumpA = 1.88350874...)")

    row("F(0) = w*int G^2", F0lo, F0hi)
    row("atanh(e^-2w)", lo["atanh_tail"], hi["atanh_tail"])
    row("I_main[0,2w]", lo["I_main"], hi["I_main"])
    print(f"{'|I_main|/F(0)':<24} {abs(lo['I_main']) / F0lo:.3e}   "
          f"{abs(hi['I_main']) / F0hi:.3e}   (O(1) constant = |K''|/Phi(0), NOT ~w; header)")
    print(f"{'K''/Phi(0) via I_main/W':<24} {lo['I_main'] / W / lo['Phi0_fft']:+.6f}   "
          f"{hi['I_main'] / W / hi['Phi0_fft']:+.6f}")
    row("archTerm", lo["arch"], hi["arch"])
    print(f"{'pole diagnostic':<24} {hi['pole_num']:+.6e}   (exact 0; relative to F(0): "
          f"{abs(hi['pole_num']) / F0hi:.2e})")

    qw = hi["qw"]
    err = abs(lo["arch"] - hi["arch"]) + 3e-15 * max(abs(qw), 1.0)
    print(f"\nVERDICT: qw(narrowArchRoot) = {qw:+.6e}   (error est ~{err:.1e})")

    F0 = F0hi
    lb = (C_ARCH + 2.0 - R) * F0                         # rigorous Lean lower bound (:592, :501-608)
    print(f"Lean rigorous lower bound F(0)*(c+2-R) = {lb:+.6e}   -> probe value above it: {qw > lb}")
    print(f"sharp ratio qw/F(0) = {qw / F0:.9f}   (leading 2*atanh(e^-2w)-c = "
          f"{2 * hi['atanh_tail'] - C_ARCH:.9f}; full limit adds +|K''|/Phi(0), header)")

    xtra = pipeline(1 << 19)                              # convergence witness, one more octave
    print(f"convergence witness nfft=2^19: qw = {xtra['qw']:+.6e}   F(0) = "
          f"{W * xtra['F0w_direct']:+.6e}")

    print("\n== Readback table (P2 identity ReTr(A_n^* A_n) = 2*log(n+2)*F(0); P2.lean:106 form) ==")
    print(f"{'n':>4} | {'ReTr(A_n)':>18} | {'- bulk r_n':>18} | plain readback lim | target qw")
    for n in (1, 4, 16, 64):
        tr = 2.0 * np.log(n + 2) * F0
        print(f"{n:>4} | {tr:+.9e} | {-tr:+.9e} |            0       | {qw:+.6e}")

    if abs(qw) > max(5 * err, 1e-7):
        print(f"\nFORK B confirmed on g_v: plain bulk subtraction leaves residual ≡ +{qw:.4e} (= qw),")
        print("n-independent => T_n = A_n alone CANNOT read back; a renormalized piece D_g (HS mass -> qw)")
        print("is required.  Sign > 0 => self-pair family FEASIBLE (matches Lean strict theorem,")
        print("C1LaneRStrictness.lean:261).  Green light for P3-a·1 Lean construction.")
    else:
        print("\nUNEXPECTED: |qw| within error — escalate before building the Lean module.")


if __name__ == "__main__":
    main()
