# 1582 — P1 paid: T0c/T0d with signed cross-validation, compact-zone caps,
# and the N=2 negative-ray envelope for the 1571 model kernel (wave V CONT-6)

Date: 2026-09-17.

Status: PAPER DERIVATION + EXACT-RATIONAL NUMERIC SENTINEL. Zero Lean. This
record executes brick P1 of record 1581 section 6: the analytic inputs of the
no-saddle integration-by-parts lemma are paid (third and fourth phase
derivative bounds, compact-zone caps, threshold), and the lemma itself is
proved in full for N = 2 with explicit constants. One modeling correction is
made on the way (the model kernel is the FULL-LINE even-folded integral; the
half-line reading creates a fake endpoint). The gate is not advanced: this
prices the MODEL kernel; bridging model to the gate is P2 (1581 §6). RH not
claimed.

## 1. Derivative chain from the committed transcription

The phase is pinned by the committed identity (1511 §6 via
`logDeriv_GammaR_eq_log_pi_add_digamma`, restated 1570 §1)

```text
theta'(xi) = -2*pi*( Re psi(1/4 - i*pi*xi) - log pi ).
```

With `z := 1/4 + i*tau`, `tau = pi*|xi|` (conjugation invariance), and
`d/dxi = i*pi*sign(xi) d/dtau`, differentiating twice more gives

```text
theta'''(xi) = +2*pi^3 * Re psi''(z)     (even in xi)
theta''''(xi) = -2*pi^4 * Im psi'''(z)   (odd in xi)
```

Parity follows from the committed `ccm24ArchimedeanScatteringPhase_neg`
(theta odd => theta' even, theta'' odd, theta''' even, theta'''' odd), so
bounds are stated for |xi| >= 2 with parity-matched anchors, exactly as 1570
did for theta' / theta''.

Tool rows (same tool (b) as 1570 §2; r^2 = tau^2 + 1/16):

```text
Re(1/z^3) = (1/64 - (3/4)*tau^2)/r^6
Re(1/z^4) = (tau^4 - (3/16)*tau^2 + 1/256)/r^8
Im(1/z^4) = (tau^3 - tau/16)/r^8
Im(1/z^5) = -(tau^5 + (5/8)*tau^3 + (5/256)*tau)/r^10     (note the sign)
```

Tool (a) is the same DLMF §5.11 Stieltjes family with the 4*sqrt(2)
sec-factor paid (law F18); for psi'' / psi''' the derivative reference is
again Nemes 2013b (cited in 1570 for psi').  Truncations: psi'' keeping
`-1/z^2 - 1/z^3 - 1/(2 z^4)` has first omitted term `+(1/6) z^-6`,
`|R| <= (4 sqrt 2 / 6) r^-6`;  psi''' keeping `2/z^3 + 3/z^4 + 2/z^5` has
first omitted `-z^-7`, `|R| <= 4 sqrt 2 r^-7`.

## 2. (T0c): the third-derivative bound

Rows for tau >= 2*pi (each converted to tau^-4):

```text
row  term                                                  |  bound
---  ----------------------------------------------------- | --------
 1   |(tau^2-1/16)/r^4 - tau^-2|  = |(1-e)(1+e)^-2 - 1|,    | 0.188 tau^-4
     e = 1/(16 tau^2): |diff| <= 3.01 e tau^-2             |
 2   |Re(1/z^3)| = ((3/4)tau^2 - 1/64)/r^6                 | 0.751 tau^-4
 3   (1/2)|Re(1/z^4)|                                      | 0.501 tau^-4
 4   |R| <= (4 sqrt2/6) r^-6  <= 0.024 tau^-4 (tau >= 2pi) | 0.024 tau^-4
     ------------------------------------------------------ | --------
     sum                                                    | 1.464 tau^-4
```

```text
(T0c)  |theta'''(xi) - 2*pi/xi^2|  <=  C3 / xi^4,
       C3 = 2.928/pi < 0.933,                       |xi| >= 2.
```

Signed drift, rows 1-3 at tau^-4 order: `-3/16 + 12/16 - 8/16 = +1/16`:

```text
theta'''(xi) = 2*pi/xi^2 + (1/(8*pi)) xi^-4 + O(xi^-6).
```

Cross-validation (1570 §4 pattern): differentiating 1570's signed T0b drift
`theta'' = -2*pi/xi - (1/(24 pi)) xi^-3 + O(xi^-5)` termwise gives
`2*pi/xi^2 + (3/(24 pi)) xi^-4 = 2*pi/xi^2 + (1/(8 pi)) xi^-4` — exact match.

## 3. (T0d): the fourth-derivative bound

Rows for tau >= 2*pi (converted to tau^-5):

```text
row  term                                                  |  bound
---  ----------------------------------------------------- | --------
 1   |2 Im(1/z^3) - 2 tau^-3|  <= 12.2 e tau^-3            | 0.763 tau^-5
 2   3|Im(1/z^4)|                                          | 3.001 tau^-5
 3   2|Im(1/z^5)|                                          | 2.010 tau^-5
 4   |R| <= 4 sqrt2 r^-7  <= 0.143 tau^-5                  | 0.143 tau^-5
     ------------------------------------------------------ | --------
     sum                                                    | 5.917 tau^-5
```

```text
(T0d)  |theta''''(xi) + 4*pi/xi^3|  <=  C4 / xi^5,
       C4 = 23.67/pi < 7.54,                        |xi| >= 2.
```

Signed drift, rows 1-3 at tau^-5 order: `-12/16 + 48/16 - 32/16 = +4/16`:

```text
theta''''(xi) = -4*pi/xi^3 - (1/(2*pi)) xi^-5 + O(xi^-7).
```

Cross-validation: differentiating §2's signed T0c drift termwise gives
`-4*pi/xi^3 - (4/(8 pi)) xi^-5 = -4*pi/xi^3 - (1/(2 pi)) xi^-5` — exact match.
(Derivation note, filed for honesty: a first pass at row 3 missed the sign of
Im(1/z^5) and inflated the tau^-5 coefficient by ~10x; the row-1/2/3 signed
sum then contradicted the derivative chain, which is what exposed the slip.
The chain check is load-bearing and is retained in both records.)

## 4. Compact-zone caps and the threshold

On [0, 2] (hence by parity on [-2, 2]) no asymptotics are used; the caps
come from the order-8 recurrence `psi^(k)(z) = psi^(k)(z+8)
- (-1)^k k! sum_{j=0}^{7} (z+j)^-(k+1)` with the Stieltjes caps at
`w = z + 8` (Re w = 8.25, |w| in [8.25, 10.45]) and the singular sums at
`|z+j| >= j + 1/4`:

```text
singular sums:  sum 1/|z+j|    <= 6.276
                sum 1/|z+j|^2  <= 17.069
                sum 1/|z+j|^3  <= 64.656
                sum 1/|z+j|^4  <= 256.463
Stieltjes caps: |psi(w)| <= 2.409   |psi'(w)| <= 0.129
                |psi''(w)| <= 0.017  |psi'''(w)| <= 0.0045
```

```text
B1 <= 2*pi * (2.409 + 6.276 + log pi)      <= 61.8     (sharp ~ 33.8)
B2 <= 2*pi^2 * (0.129 + 17.069)            <= 340
B3 <= 2*pi^3 * (0.017 + 2*64.656)          <= 8.03e3
B4 <= 2*pi^4 * (0.0045 + 6*256.463)        <= 3.00e5
```

with `Bk := sup_{|eta| <= 2} |theta^(k)(eta)|`.  Finiteness is what the lemma
consumes; the constants are deliberately unoptimized.  Two honest remarks:
(i) psi'(1/4) and psi''(1/4) are REAL, so theta''(0) = 0 and the B2 cap
overstates the sup of |Im psi'| by well over an order of magnitude;
(ii) B3/B4 are near-sharp (the polygamma values at 1/4 are genuinely large),
so the large B4 is a fact about the phase, not slack.  The threshold

```text
U0 := B1/pi + 1  <=  20.7        (sharp-cap value ~ 11.7)
```

## 5. The model kernel and the N=2 envelope

Model correction first.  CCM24 uses the EVEN additive Fourier transform
(`CCM24HardyTitchmarsh.lean:16`), so the 1571 model kernel is the full-line
even-folded integral

```text
K(u) = integral over R of  a(eta) * exp(i (2 pi u eta + theta(eta))) d eta,
a even, C^infinity, a(eta) = (1 + eta^2)^-2 - profile.
```

Reading the model as a HALF-LINE integral would put a fake endpoint at
eta = 0 whose boundary term decays only like 1/|u| and would cap the lemma
one rung early; on the full line there are no boundary terms and the
concrete amplitude below has bounded norms

```text
||a||_1 = pi/2,   ||a'||_1 <= 2 + eps,   ||a''||_1 <= 28.4   (triangle).
```

(The 1571 prose "|amplitude root| ~ (1+eta)^-k" is ambiguous between
amplitude and amplitude-root readings; the lemma only consumes the norms
above, so both readings are served.)

Lemma (N = 2, stationary-free).  Let u <= -B1/pi, put
`lam(u) := pi*|u|`, so that on the whole line
`|dPhi/deta| = |2 pi u + theta'(eta)| >= 2 pi|u| - B1 >= lam(u)` (uniform,
since theta' <= B1 on [-2,2] and theta' decreases on [2, inf) by T0a).  Two
integrations by parts with `exp(i Phi) = (1/(i Phi')) d(exp(i Phi))/d eta`
give, with no boundary terms,

```text
|K(u)| <= ||a''||_1 / lam^2
        + (3 ||a'||_1 THETA2 + ||a||_1 THETA3) / lam^3
        + 3 ||a||_1 THETA2^2 / lam^4,
```

where `THETAk := max(Bk, sup_{|eta| >= 2}|theta^(k)(eta)|)`:
`THETA2 <= 340` (T0b: |theta''| <= 2*pi/eta + C2 eta^-3 <= 3.19), and
`THETA3 <= 8.03e3` (T0c).  Numerically,

```text
|K(u)| <=  28.4 / lam^2  +  14,640 / lam^3  +  544,900 / lam^4 ,
lam = pi*|u|,   u <= -B1/pi.
```

Proposition (negative-ray envelope).  For u <= -U0,

```text
|K(u)| <= 43 * (1 + |u|)^-2 ,
```

and trivially |K(u)| <= ||a||_1 = pi/2 everywhere.  (Conversion: lam = pi|u|
>= 0.954 pi (1+|u|) on the range, so 1/lam^k <= (0.334)^k (1+|u|)^-k; the
three terms absorb into (1+|u|)^-2 as 3.2 + 25.0 + 14.3 <= 43, using
(1+|u|)^-3 <= (1+U0)^-1 (1+|u|)^-2 and (1+|u|)^-4 <= (1+U0)^-2 (1+|u|)^-2.)

Corollary (the corrected negative-ray row, at this rung).  With N = 2:

```text
int_{-inf}^{0} (1 + |u|)^b |K(u)|^2 du  <  inf     for every b;
in particular  int_0^inf u |K(-u)|^2 du < inf   and   K in L^2(-inf, 0).
```

The positive ray is NOT re-priced here: for u > 0 the phase HAS a saddle
(eta* = e^u in the valid zone for u >= log 2), the lemma's hypothesis fails
there by design, and 1571's beta_+ = 5/2 stationary-phase row stands
unchanged.  The |u| <= U0 band is a bounded function on a finite interval.

## 6. Numeric sentinel (exact rational, WSL, PASS 16/16)

`scripts/t0_digamma_sentinel/d34_stieltjes_sentinel.py` validates the two
Stieltjes chains on the positive real axis, with NO stored constants
(polygamma sums evaluated directly by the Euler-Maclaurin Hurwitz form with
rational Bernoulli terms and a same-sign remainder bracket; a first version
that computed zeta at a fixed split and subtracted partial sums carried an
off-by-one in the EM start point — a 5.96e-8 = 1*N^-3 shift that the m=16
row exposed immediately; the committed version evaluates the tail starting
at q = m and is self-checking):

```text
D3(x) := psi''(x) + x^-2 + x^-3 + x^-4/2          in (0, (6 x^6)^-1]
E4(x) := (2x^-3 + 3x^-4 + 2x^-5) - psi'''(x)      in (0, x^-7]
```

```text
m=2    D3/bound=0.823438 pred=0.862500 PASS   E4/bound=0.776042 pred=0.854167 PASS
m=4    D3/bound=0.943921 pred=0.944531 PASS   E4/bound=0.927165 pred=0.928385 PASS
m=8    D3/bound=0.984805 pred=0.984814 PASS   E4/bound=0.979880 pred=0.979899 PASS
m=16   D3/bound=0.996121 pred=0.996121 PASS   E4/bound=0.994837 pred=0.994837 PASS
m=32   D3/bound=0.999025 pred=0.999025 PASS   E4/bound=0.998701 pred=0.998701 PASS
m=64   D3/bound=0.999756 pred=0.999756 PASS   E4/bound=0.999675 pred=0.999675 PASS
m=128  D3/bound=0.999939 pred=0.999939 PASS   E4/bound=0.999919 pred=0.999919 PASS
m=256  D3/bound=0.999985 pred=0.999985 PASS   E4/bound=0.999980 pred=0.999980 PASS
```

(log at `scripts/t0_digamma_sentinel/d34_stieltjes_sentinel.log`.)  Scope
note, as in 1570 §5: the sentinel checks the coefficient chain and the
constant structure on the real axis (where the DLMF bound is exactly the
sec-free one); the vertical-line passage is pure tool-(a)+(b) algebra with
the 4*sqrt(2) factor paid.  No Lean consumer may quote the sentinel as a
proof.

## 7. Boundary

Moved: T0c/T0d paid with signed cross-validation; compact caps and the
threshold U0 <= 20.7 in hand; the N=2 no-saddle envelope PROVED with explicit
constants; the 1571 u<0 row superseded at model level by the polynomial
envelope (the e^{-beta|u|} beta-language itself was part of the modeled
artifact — the honest statement is polynomial decay of every order that the
paid rungs support, here beta-equivalent: all polynomial-weighted L2
functionals converge).  NOT moved: (star), B4, rho5, R4, (OB)/W1 all OPEN;
this record prices the MODEL kernel only — the true composed tail differs by
the sharp-cut smearing (the non-local counter-term structure), and the gate's
remaining content is the P2 restriction functional (1581 §6).  No sign input
anywhere; nothing machine-checked; RH NOT claimed.
