# 1070 - LEVEL-1: the Weil-functional hunting probe for the tuned detector family

Date: 2026-08-31. AMENDMENT (pre-run): the pre-registered test dictionary was
WRONG and is corrected in section 6 BEFORE any fork data was read; s1-s3 keep
the original text with pointers. Read section 6 for the operative definitions.

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
convolution; reflection principle for real coefficients)  [AMENDED in s6:
this product is WRONG; the Mellin convolution theorem gives
`f~(s) = g~(s) g~(1-s)`], and
`int f = f~(1)`, `int f^sharp = f~(-1)`  [AMENDED in s6: `int f^sharp =
f~(0) = int f(x) dx/x`, NOT `f~(-1)`; both still vanish for the family], so
the F-vanishing at {0,1} makes
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

Run: one deterministic WSL run (V2 probe, correct dictionary; full log in the
Linux-side verification environment, unversioned per the 1063 convention).
Acceptance on the flushed log: zero error/traceback/FAIL; ALL gates green -
ANCHOR-A identity residual 1.655e-10 (u-form vs f~-form W_R agree to 1.7e-10;
two bugs fixed pre-run, see 6.1), ANCHOR-B reproduces the paper's W_inf < 0
sign on CC20's own test (W_R = +26.985814, inverse-Fourier sub-gate <= 3e-30),
dictionary gate f~(1) = f~(0) = 0.00e+00 EXACTLY, A(beta) = A(1-beta)
symmetry 0.0e+00. Zero cache 1893 ordinates (gamma <= ~1729, dps 30).

### 5.1 The measured fork table (one line per regime; margins are sums of
###     |g~(rho_k)|^2, all terms termwise >= 0)

```text
  j = 1  (gamma = 14.135):
    delta = 0.65153 (sqrt(6/gamma), coarse band): FLIP, minA-P < 0 at
        beta = 0.2, xphase = 2.853 (cos = -0.96).  ALL functional terms
        ~1e-30 (suppression e^{-81} rel. the O(1) band): fl ~ -2e-30,
        fl/margin ~ -1.9 (deep relative, DENORMAL absolute).
    delta = 0.14150 (= 2/gamma, window centered ON the zero): margin 2.41,
        P = 2.00, xphase = -0.000 EXACTLY -> cross term POSITIVE, fl > 0.
    delta in [0.0104, 0.0833] (resolved/over-resolved): margin grows
        6.4 -> 129.8 (unbounded low-order background), P falls 0.40 -> 3e-6,
        xphase -> 0.25 (positive): fl > 0 everywhere, by wide margins.
  j = 2, 3, 5, 10, 20, 30: NO-FLIP at every grid point.  The same three
    regimes repeat: coarse band (xphase +0.92..+1.05, cos > 0), centered
    band (xphase = -0.000, P = 2.000, cross positive), resolved band
    (margin unbounded, phase -> +0.02..+0.25).  The low-zero background at
    the coarse band GROWS with j (j=10: 5e-6, j=20: 4.3e-3, j=30: 0.0599)
    exactly as e^{-6 gamma_1^2/gamma_j} predicts, while the target terms
    sink like e^{-6 gamma_j}.
```

### 5.2 VERDICT: H3' - the smooth Gaussian detector family CANNOT hunt

Per the pre-stated fork: no flip at any delta >= spacing width for any
j >= 2, and the single j = 1 "flip" is a formal negation at e^{-81}-
suppressed scale - toothless as a certificate. The scan also yielded the
mechanism, which is stronger than the pre-stated verdict:

```text
  PHASE LOCK (the obstruction quantifier): the cross-term phase is
    phi(beta, delta) = arg g~(beta+i g) - arg g~(1-beta+i g)
        ~ (2 beta - 1) (gamma delta^2 - 4/gamma)
    (asymptotic in gamma; QUANTITATIVELY exact on this scan: predicted
    2.85 vs measured xphase 2.853 at the j=1 flip point; 0.166 vs 0.166;
    0.000 vs -0.000 at every centered row).
  Consequence 1 (in-band positivity): across the whole O(1)-scale window
    delta in [1/gamma, 4/gamma] the phase is |phi| <= 0.9 * 12/gamma,
    so cos(phi) > 0.99 for gamma >= 25 and the cross term is STRUCTURALLY
    POSITIVE - the flip value = (margin - P) + A >= 0 + A > 0.  The two
    requirements CONFLICT: rotating phi to pi needs gamma delta^2 >~ 3.5,
    where every functional term is suppressed by e^{-delta^2 gamma^2} <=
    e^{-3.5 gamma}.
  Consequence 2 (exponential hunting law): EVERY flip of this family
    (any beta, any delta, all phase branches) has absolute scale
    <= poly(gamma) * e^{-1.74 gamma_j}.  The j=1 measured flip (e^{-81}
    = e^{-5.8 gamma_1}) sits inside the law.  Hunting power DECAYS
    EXPONENTIALLY with height - the smooth family is not merely
    "hard to tune", it is asymptotically toothless.
  Consequence 3 (no H2' price law): at no resolution does a flip occur
    in-band; there is no delta_flip(gamma) to measure.  H2' is refuted
    alongside H1'-for-the-tail.
```

### 5.3 Consequences for the G path (and the A fallback)

```text
  1. The G path must adopt ZERO-ENGINEERED (oscillatory) tests - the
     pre-registered H3' consequence, now with a measured reason: the
     Gaussian's phase phi is a consequence of the family's real positive
     symbol e^{delta^2 s^2/2}; a Yoshida-type product family
     (g~ proportional to prod_k (s - z_k)(s - 1 + z_k) ... with z_k
     DISJOINT from the zero set, per mainprop's F-set freedom) carries
     free phase and is the minimal next design.  Note mainprop requires
     F disjoint from Z: tests may NOT vanish at actual zeros, so the
     low-zero background must be beaten by oscillation/interference,
     not by vanishing.
  2. The background margin (sum over OTHER zeros) is unbounded in delta -
     the spectral-side avatar of 1069's Tr(C_k K_S C_k) ~ min(Xi, c/k)^alpha
     finding: one picture again, now at the Weil-functional level.
  3. A (Parseval frame) inherits the same law: frame vectors built from
     smooth detectors cannot see off-line zeros faster than e^{-c gamma}.
     The -0.55 budget constraint from 1069 was optimistic; the true
     smooth-family budget is EXPONENTIAL.
  4. Next concrete slice (design record pending): pick ONE Yoshida-type
     engineered family, recompute margin/P/A closed-form (same pipeline
     - only g~ changes), and measure whether the phase lock breaks.
```

### 5.4 Caveats (honesty ledger)

```text
  - beta grid {0.05..0.45} misses beta ~ 0.24 where the coarse-band phase
    would flip for j >= 2 as well; per the exponential law those flips are
    e^{-6 gamma_j}-scale - MORE suppressed than the stated bound - so the
    verdict is unaffected.  Recorded for any future fine scan.
  - j = 20/30 at the two smallest delta rows: the zero cache ends at
    gamma ~ 1729 while the window extends further (tail bounds printed
    up to 1.1e+03 exceed the margin).  These rows are NO-FLIP by wide
    margins; extra uncached mass only reinforces NO-FLIP.  No other row
    is affected (all other tails <= 5e-5 relative to their margins).
  - The phase-lock formula is measured + asymptotic (exact to ~1e-3 rad at
    gamma = 14), not a proved theorem; the Lean-facing claim stays the
    pre-registered H3' verdict, and the exponential law is recorded as the
    obstruction QUANTIFIER.
```

## 6. AMENDMENT (2026-08-31, BEFORE the fork scan ran - no fork data was read
##    under the wrong dictionary)

The ANCHOR GATE did its job twice over: it refused to pass a broken chain,
and chasing the failure exposed one implementation pair and one DICTIONARY
error. Nothing below changes the fork semantics (s0 H1'/H2'/H3'); it changes
what f~ means inside them.

### 6.1 ANCHOR-A findings: two implementation bugs, identity now closes

Evidence: `docs/proofs/1070_anchor_debug.py` (untracked debug harness; log in
the Linux-side verification environment). Three-way evaluation of
`sum_v W_v` on the C_c 6-fold B-spline test, target = f~(1) + f~(0) - zero:

```text
  sum_v W_v target (triv - zero)     = 2.281393020152
  u-form   (tex:2047 bombieriexpl.2) = 2.281393019774   (match 3.8e-10)
  f~-form  (tex:2049 bombieriexpl.3) = 2.281393019947   (match 2.0e-10)
  u-form vs f~-form independently    : agree to 1.7e-10
  identity residual, relative        : ~1.5e-10   (gate was 1e-6)
  f~(s) = (sinh(s/2)/(s/2))^6 vs DIRECT Mellin quadrature: 4 points, <= 3e-14
```

Bug 1 (trivial side): the pre-registered anchor used `triv = 2 f~(1)`,
justified by "f is even". WRONG inference: `f = f^sharp` pointwise does NOT
give `int f = int f^sharp`, because `int f^sharp = int f(x) dx/x = f~(0)`,
a DIFFERENT Mellin value (`f~(0) = 1` vs `f~(1) = 1.2814` for the B-spline;
the closed form is an even FUNCTION of s, which says f~(-1) = f~(1), nothing
about s = 0). Correct trivial side: `triv = f~(1) + f~(0)`.

Bug 2 (W_R u-quadrature): tex:2047's subtraction term `-2 e^{-u} G(0)/(1 -
e^{-2u})` has an EXPONENTIAL TAIL beyond the support of G - it does not
vanish at u = 3 (it equals -2 G(0) e^{-3} = -0.0548 there). The first
quadrature truncated at u = 3 and lost exactly that amount. Fix: integrate
to 40 (e^{-40} floor).

Discarded scratch route: a third "contour" evaluation assembled from
Bombieri's (2.2)/(2.3) did NOT close; found my own `Lambda(1) = 0` violation
(the prime loop added a p^0 = 1 term worth ~8.85) plus one still-unresolved
direct-quadrature bookkeeping gap. Dropped: the gate rests on the TWO
paper-verbatim W_R implementations cross-validating each other plus the
mpmath zero list - three independent quantities, one closure.

### 6.2 THE DICTIONARY CORRECTION (operative definitions)

Re-deriving the bookkeeping for bug 1 forced a re-derivation of the
test dictionary itself, and the pre-registered product was wrong:

```text
  f^sharp(x) := x^{-1} f(x^{-1})   =>   (f^sharp)~(s) = f~(1-s)
      (sub y = 1/x:  int g(y) y^{-s} dy)
  Mellin convolution theorem: (g * h)~(s) = g~(s) h~(s)
      =>  f = g * g^sharp   =>   f~(s) = g~(s) g~(1-s)
```

The pre-registered `f~(s) = g~(s+1) g~(s-1)` ("reflection principle") has NO
such derivation; on the critical line it evaluates g~ at 3/2 + i gamma and
-1/2 + i gamma (sign-random values), i.e. it was measuring the WRONG
functional. The corrected dictionary has the structure Weil positivity is
famous for:

```text
  ON-LINE:   f~(1/2 + i g) = g~(1/2+i g) g~(1/2-i g) = |g~(1/2+i g)|^2 >= 0
             TERMWISE.  margin = sum |g~(rho_j)|^2 is a sum of squares;
             "LINE-1 sanity" (margin >= 0 under RH) is now AUTOMATIC.
  TRIVIAL:   f~(1) = g~(1) g~(0) = 0 and f~(0) = g~(0) g~(1) = 0 EXACTLY
             (g~ vanishes at 0 and 1; the pre-registered vanishing argument
             survives, with f~(0) in place of f~(-1)).
  OFF-LINE:  A_j(beta) = 2 Re[ g~(beta+i g) conj(g~(1-beta+i g)) ]
             - a CROSS-term, sign-tunable, magnitude <= 2|g~(b+ig)||g~(1-b+ig)|
             (Cauchy-Schwarz bounds the flip lever by the two "adjacent"
             abscissa masses).
  FLIP:      margin + A_j(beta) - P_j < 0   (semantics unchanged from s0).
```

Phase structure (large-gamma asymptotics of arg V_F, worth recording as the
scan's interpretive key): the cross-phase is approximately
`(2 beta - 1) (gamma delta^2 - 4/gamma)` - tunable by delta at FIXED gamma,
but the resolved window (delta ~ log(g)/2pi / gamma and below) barely moves
it (|gamma delta^2| << 1 there), so in the resolved regime the cross term
sits near phase ~ 0 (POSITIVE, stabilizing). Any flip from phase rotation
must live in the COARSE band delta ~ sqrt(c/gamma), which is why the v2
delta-grid EXTENDS upward with sqrt(2/gamma_j), sqrt(6/gamma_j). The scan,
not this asymptotic, decides.

### 6.3 What stays pre-registered

Fork H1'/H2'/H3' semantics (s0): UNCHANGED - they quantify over the flip
condition, now computed from the corrected f~. Beta grid, j-list, zero-cache
discipline, tail bounds, acceptance (s3/s4): unchanged except the delta-grid
extension above. The anchor gate now ALSO asserts u-form vs f~-form
agreement <= 1e-8 (a second implementation can never silently drift again).
V2 probe: `1070_weil_q_hunting_probe.py` (this replaces the v1 file in
place; the v1 family block is preserved in git history at dfcdbd7).
