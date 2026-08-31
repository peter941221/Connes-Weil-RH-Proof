# 1070 - LEVEL-1: the Weil-functional hunting probe for the tuned detector family

Date: 2026-08-31. Follows 1069 (H1: the continuum detector mass blows up like
k^-0.54, one-shot unit-scale LINE-5 shaping dead; path verdict: PRIMARY = G
dual hunter via LEVEL-1). This record pins the Weil functional VERBATIM from
the CC20 tex, builds the detector-to-test dictionary, and pre-registers the
first decisive closed-form probe: can the tuned Gaussian detector family
actually FLIP the Weil functional at a hypothetical off-line zero, at what
scale-price, and how does that price scale with the height? No proof of RH is
claimed anywhere; this is a measurement of our own family's hunting power.

## 0. Fork (stated BEFORE the run)

```text
Objects per test g (delta = detector width, zero j, beta = hypothetical
off-line abscissa; definitions in s2-s3):
  margin(delta) := sum_rho f~(rho)                (trivial side = 0 by F)
  P_j(delta)    := 2 Re f~(1/2 + i gamma_j)       (on-line pair at gamma_j)
  A_j(beta)     := 2 Re[f~(beta+i gamma_j) + f~(1-beta+i gamma_j)]
  flip condition:  margin + A_j(beta) - P_j < 0   (certificate sinks)

ANCHOR GATE (must pass or NOTHING is trusted):
  the explicit formula identity, evaluated on CC20's own example test
  (f~(s) = (1-4s^2)^2 e^{s^2/2}, tex:697-699), must close the zero side,
  the archimedean side and the prime side to <= 1e-6 relative.
  Internal sub-gates: A_j(beta) = A_j(1-beta) (symmetry); margin has no
  trivial-side contribution (f~(1) = f~(-1) = 0 exactly, from F-vanishing).

FORK on the flip scan (delta from coarse tuning 1.177/gamma_j down to the
zero-spacing width ~ 2pi/(gamma_j log gamma_j), beta in (0, 1/2]):
  H1' (family HUNTS coarsely): flip occurs already near delta ~ 1.177/gamma_j
     => G is live with the Gaussian family; schedule the semilocal-S
     restriction design record next.
  H2' (family hunts only resolved): no flip at coarse tuning, but flips
     appear as delta -> spacing width, with a measurable price law
     delta_flip(gamma) -> 0. => the family hunts only with Yoshida-type
     resolution; the price law becomes the design constraint for the
     per-scale certificate chain (A's adaptive frame).
  H3' (family never flips): no flip at any delta >= spacing width =>
     smooth detectors are positivity-robust and CANNOT hunt; hunting needs
     zero-engineered tests (Yoshida construction), i.e. the G path must
     adopt engineered tests; record the measured robustness margin as the
     obstruction quantifier.
```

## 1. Pinned formulas (every line to the tex)

Source: `/home/peter/cc20-2006.13771-016/weil-compo.tex`
(Connes-Consani arXiv:2006.13771, "Weil positivity and Trace formula - the
archimedean place"; the copy fetched by scripts/fetch_cc20.sh, sha-pinned by
record 1057).

| object | pin | content |
|--------|-----|---------|
| Mellin transform | tex:2037-2039 `\label{mellin}` | `f~(s) := int_0^inf f(x) x^{s-1} dx` |
| explicit formula | tex:2039-2041 `\label{bombieriexplicit}` | `sum_rho f~(rho) = int f + int f^sharp - sum_v W_v(f)` over all places {R, 2, 3, 5, ...} |
| finite prime term | tex:2043-2045 `\label{bombieriexplicit1}` | `W_p(f) = (log p) sum_{m>=1} (f(p^m) + f^sharp(p^m))` |
| archimedean term | tex:2047-2049 `\label{bombieriexplicit2}` | `W_R(f) = (log 4pi + gamma) f(1) + int_1^inf (f + f^sharp - (2/x) f(1)) dx/(x - x^{-1})` (pv at 1) |
| involution | tex:2039 | `f^sharp(x) := x^{-1} f(x^{-1})` |
| archimedean instance | tex:692-694 `\label{sch22}` | `W_inf(f) = -int f(rho^{-1}) tau(rho) d*rho`, support in [1/2, 2] |
| vanishing conditions | tex:694-696 `\label{vanishing}` | `int f(rho) rho^{+-1/2} d*rho = 0` (Mellin zeros at z = +-1/2) |
| positivity criterion | tex:2111-2133 `\label{mainprop}` (after Yoshida) | `RH iff sum_v W_v(g* gbar^sharp) <= 0 for all g in C_c^inf with g~(z) = 0 for z in F, {0,1} subset F, F finite disjoint from zeros` |
| CC20 example test | tex:697-699 | `g~(t) = (1+4t^2) e^{-t^2/4}`, `f~(t) = (1+4t^2)^2 e^{-t^2/2}` with `f = g*g^*`, the test whose W_inf < 0 |
| repo correspondence | AGENTS 7d (1060 block) | repo `qw >= 0` on triple-vanishing tests = the `-sum_v W_v` positive form; vanishing nodes {0, 1/2, 1} in the chain coordinates, Mellin-z union {0, 1, +-1/2} |

Sign bookkeeping used throughout: with `f = g * gbar^sharp` and real-coeff
`g~` one has `f~(s) = g~(s+1) g~(s-1)` (derived: Mellin of multiplicative
convolution; reflection principle for real coefficients), and
`int f = f~(1)`, `int f^sharp = f~(-1)`, so the F-vanishing at {0,1} makes
BOTH trivial terms vanish identically and the criterion reduces to
`sum_rho f~(rho) <= 0` on the geometric side. On-line zeros come in the pair
{1/2 +- i gamma}; an off-line abscissa beta gives the quadruple
{beta +- i gamma, (1-beta) +- i gamma} with `f~(conj) = conj(f~)`.

## 2. The detector-to-test dictionary (and its three stated gaps)

The rig detector `D_k = F* diag(w_k) F`, `w_k(xi) = exp(-(k xi)^2/2)` in the
rig coordinate xi (Fourier on log-scale with 2pi normalization, so the
multiplicative-Fourier coordinate is t = 2 pi xi). Dictionary: a test whose
Mellin image on the critical strip carries the detector symbol is

```text
  g~_delta(s) = Norm(delta) * V_F(s) * exp(delta^2 s^2 / 2),
  V_F(s) = s (s-1) (s^2 - 1/4)     (vanishes exactly at F = {0, 1, +-1/2}),
  delta = k / (2 pi)               (rig k <-> tex-t width),
  Norm chosen so max_t |g~_delta(1/2 + i t)| = 1  (found numerically).
```

`exp(delta^2 s^2/2)` is the bilateral-Laplace image of a u-Gaussian of width
delta (converges for every real s, decays like e^{-delta^2 t^2/2} on vertical
lines - so all zero sums converge superfast). `V_F` puts the test inside the
Yoshida/CC20 vanishing class (F = union of the Yoshida {0,1} and CC20's
{+-1/2}; the repo's triple set maps to the same union per 1060).

STATED GAPS (honesty ledger, mirrors 1068 s1):
  (gap-1) FAMILY: g~_delta is Gaussian-type, NOT C_c^inf (Paley-Wiener
     fails). CC20 itself evaluates W_inf on exactly such a test (tex:697),
     so this is an in-house class, but the Yoshida equivalence quantifies
     over C_c tests - our family is a SUBCLASS probe, not the criterion.
  (gap-2) SCOPE: the probe evaluates the FULL Weil functional (all primes),
     not the semilocal-S restriction the repo's detectors carry. The
     hunting-power question is answered at the Weil level first.
  (gap-3) SIGNS: the flip condition is derived from mainprop's
     `sum_v W_v <= 0` and bombieriexplicit's bookkeeping; the ANCHOR GATE
     (s0) validates the whole sign chain on the paper's own test before
     any fork data is read.

## 3. Measured quantities (all closed-form in the family)

```text
  f~(s)    := g~_delta(s+1) g~_delta(s-1)
  margin   := sum over zeros of 2 Re f~(1/2 + i gamma_j)   (+ tail bound)
  P_j      := 2 Re f~(1/2 + i gamma_j)
  A_j(beta):= 2 Re [f~(beta + i gamma_j) + f~(1-beta + i gamma_j)]
  flip_j(delta, beta) := margin(delta) + A_j(beta) - P_j < 0
  beta grid: {0.05, 0.10, 0.20, 0.30, 0.40, 0.50}; symmetry gate
  |A(beta) - A(1-beta)| < 1e-10 relative.

Scan: j in {1, 2, 3, 5, 10, 20, 30} (mpmath zetazero, dps 30);
delta_j-loggrid from 1.177/gamma_j down to 0.05 * 2pi/(gamma_j log gamma_j)
(5 points per octave, ~3 octaves); zero-sum cutoff |gamma| <= max(6/delta,
3 gamma_j) with an explicit density tail bound printed at every call.
```

ANCHOR implementation (independent closed forms, tex:697 test):
`G(u) = f(e^u) = sqrt(2pi) (16 u^4 - 104 u^2 + 57) e^{-u^2/2}` (inverse
Fourier of `(1+4t^2)^2 e^{-t^2/2}` under `f~(s) = int G(u) e^{su} du`;
Hermite recurrence, verifiable by numerical inversion sub-gate);
`f~(s) = f^(is) = (1-4s^2)^2 e^{s^2/2}`; zero side `2 sum_j Re f~(1/2+i
gamma_j)` (converges by e^{-gamma^2/2}, first ~15 zeros enough, tail < 1e-30);
`f~(1) + f~(-1) = 18 sqrt(e)`; prime side `sum_p log p sum_m [G(m log p) +
e^{-m log p} G(-m log p)]` (p to ~e^6 with Gaussian tail bound); archimedean
side via bombieriexplicit2 in the u-coordinate
`W_R = (log 4pi + gamma) G(0) + int_0^inf [G(u) + e^{-u} G(-u) - 2 e^{-u}
G(0)] du/(1 - e^{-2u})` (mpmath quadrature; the pv-subtraction makes the
integrand regular at 0). Gate: |zero - (trivial - archi - prime)|/|trivial|
<= 1e-6.

## 4. Acceptance

mpmath dps 30 throughout; the anchor gate and both symmetry sub-gates are
hard asserts; every margin/flip number prints its own tail bound; acceptance
= the flushed log's gate lines + fork table (Linux-side log, per the 1063
convention), never exit codes. The fork verdict is written into s5 by hand
from the table.

## 5. Post-run addendum (filled after execution)
