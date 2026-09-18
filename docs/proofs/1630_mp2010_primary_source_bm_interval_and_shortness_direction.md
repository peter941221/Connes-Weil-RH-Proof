# 1630 — The MP 2010 primary source retrieved: the BM interval of the tree's phase, the shortness direction corrected, and the p = 2 gap identified

Date: 2026-09-18.

Status: route record plus **one Lean brick** (`Dev/StripDensityTraceLedger`, the
trace-level repair of 1625 section 2, with the audit companion
`Dev/StripDensityTraceLedgerAudit`). Analytic content: the exact definitions
and statements of the primary source, one numerical computation of the
Beurling–Malliavin interval family of the tree's phase, the resulting class
audit (law F40 continued), and **two errata**: 1629 section 3 (direction of
shortness, and a vacuous `H² \ N⁺` phrase) and 1625 section 2 (an invalid
operator-level sandwich). Three numerics rigs (sections 3, 10, 11) test the BM
interval family, the committed B4-scalar premise per column, and the Toeplitz
kernel by finite sections. The carrier base stays **OPEN**, but it is now
reformulated as the primary source's `p = 2` criterion, and the exact missing
statement is named. RH is not claimed.

Consumer (named, unchanged): the healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](../map/012_g8_same_owner_readback_rh_reachability.md)).

## 1. Verdict

```text
(A) PRIMARY SOURCE   retrieved in full text (DVI scraped): the BM-interval
                     definition, the shortness sum, Theorems A/B/C, the
                     corollary, the (1.6) criteria, section 4.1's little
                     multiplier proposition, and section 5.1's multiplier
                     theorem with its proof skeleton (items (1)-(6)).
(B) BM COMPUTATION   BM(gamma + a xi) is ONE interval, it CONTAINS THE ORIGIN
                     for every a >= 0, and its right edge is
                          e^{a/(2 pi)} = lambda^{-2}             (lambda = e^{-a/(4 pi)});
                     the shortness sum (over intervals with d >= 1) is
                     therefore VACUOUS: the tree's phase is (beta)-almost
                     decreasing for EVERY beta >= 0 and EVERY lambda <= 1.
(C) DIRECTION        in this class "short => nontrivial kernel" (Theorem A(ii),
                     C(ii), section 4.1).  1629 section 3 recorded the opposite
                     heuristic.  ERRATUM A.
(D) CLASS AUDIT      the phase hypothesis (1.4) is ONE-SIDED and our phase
                     satisfies it for every beta > 0; but our phase is not of
                     power-law type (|gamma'| ~ 2 pi log|x|), and m is not
                     inner, so Theorems B/C transfer only partially.  The
                     nontriviality obtained this way lives in N_p for
                     p < 1/2 (corollary p < 1/3) - NOT at p = 2.
(E) THE GAP, NAMED  the carrier base is (up to reflection) the SN kernel at
                     p = 2, because N^2[U] = {F in H^2 : conj(U) F in H^2}
                     (Smirnov: N^+ cap L^2 = H^2).  The missing statement is
                     exactly "Theorem A(ii) at p = 2", i.e. the Hardy-space
                     case = the survey's big multiplier theorem (8.5).
(F) CRITERION FORM  at p = 2 the primary source's (1.6) criterion rewrites the
                     base as a decomposition problem: base  <=>  psi = arg
                     Theta + h~ with Theta inner and h in L^1(dPi),
                     e^h in L^1(R), psi = -gamma - a xi.  Convention flags
                     (half-plane of "inner", sign of h~) pinned in section 5.
(G) BRICK            Dev/StripDensityTraceLedger: real trace positivity,
                     Loewner trace monotonicity, the named compression
                     obligation, and 1625's chain with that step as a
                     hypothesis.  1625 section 2's operator sandwich is FALSE
                     (counterexample in section 7 and in the audit companion).
(H) B4-SCALAR (2)    tested literally on three explicit committed column
                     classes by the slice definition of H^2(C_+): the premise
                     FAILS for all three, and the mechanism is quantitative and
                     convention-free: |m(x + I y)| / |x|^{2 pi y} -> 1 (the
                     committed growth caveat), so a column's psi decaying like
                     1/|x| keeps every slice L^2 exactly up to y < 1/(4 pi) and
                     loses it beyond (measured: G500/G20 = 1.27 at the
                     threshold, 86 at y = 0.3, 1.2e8 at y = 1), while an entire
                     column's slice norms grow without bound (0.697 -> 0.930 ->
                     8.27 -> 2.3e9).  Flagged for the next source read: with K
                     and the columns on the same committed half-line, the
                     product's inverse transform lives on that half-line too,
                     so the literal statement is DEGENERATE (only zero
                     satisfies it); the live form must be the reflected pairing
                     of the carrier base (section 10).
(I) TOEPLITZ PROBE (4)  the finite section of T_U = P_+ M_U P_+ on the
                     translate family of one bump: sigma_min(K) SATURATES in K
                     from K = 2 on (enlarging the finite-type section buys
                     nothing) and depends only on lambda:
                     0.4125 (lambda = 1), 0.06824 (1/2), 0.02600 (1/e),
                     2.991e-6 (0.1), <= floor (0.01).  No finite-type witness
                     exists at any lambda (consistent with 1627), and the
                     distance to the base decays steadily as lambda -> 0: the
                     base is APPROXIMABLE by finite-type data but never
                     attained by it (section 11).
(J) FLOOR CALIBRATION  the rig's numerical floor is the xi-window-edge
                     leakage: with an exactly-known witness (model m = 1,
                     lambda = 1/2) it reads 4.15e-8 at |xi| <= 64 and 1.82e-11
                     at |xi| <= 128, i.e. it tracks |H| at the window edge; the
                     grid-aligned witness (c = -2) sits at 3.6e-16.  All
                     verdicts above are quoted against the calibrated floor
                     (section 11).
```

## 2. The primary source and how it was read

Source: N. Makarov, A. Poltoratski, "Beurling–Malliavin theory for Toeplitz
kernels", Invent. Math. **180** (2010) 443–480; DVI file retrieved from the
author's page,

```text
URL    https://people.math.wisc.edu/~poltoratski/MIF2.dvi   (116 216 bytes)
Method a minimal DVI interpreter (set_char/set1-4, right/down moves,
       fnt_def, pre/post leak) dumping prose as latin1 text; formulas
       set in math fonts are lost, prose is intact.  The extraction
       (44 158 bytes) is the source of every quote below.
```

Roadmap of the paper's own proofs (retrieved verbatim, section 1.7):

```text
(1) Upper density estimate:      phi(-inf) != +inf  =>  N^+[U S_eps] = 0
(2) Effective density estimate:  SUM d^{beta-2} l^2 = infinity  =>
                                 N^+[U S_eps] = 0
(3) Little multiplier theorem:   phi almost decreasing  =>  N^+[U_eps S_eps] != 0
                                 (extraction shows "= 0"; section 4.1's
                                 Proposition states != 0)
(4) BM multiplier theorem:       weighted Dirichlet norm of log W finite =>
                                 W in a Hardy space up to a factor N^+[. S_eps]
                                 (sections 5.1-5.2)
(5) a version of BM1:            used to show non-triviality of N^+ kernels
                                 implies non-triviality of N^p kernels FOR
                                 SYMBOLS INVOLVING INNER FUNCTIONS
                                 (sections 5.3-5.4)
(6) L^p multipliers:             approximation by inner functions, down to H^1
                                 (section 6)
```

Item (5) is the pivot of this round's audit: the passage from `N^+` to `N^p`
is done **for symbols involving inner functions**.

Definitions, verbatim (section 1.3/1.4):

```text
"Let phi be a continuous function R -> R such that phi(-inf) = +inf,
 phi(+inf) = -inf.  The family BM(phi) is defined as the collection of the
 components of the open set  { x : phi(x) != max_{[x,+inf)} phi }."
"phi is (beta)-almost decreasing if  phi(-inf) = +inf,
 SUM_{l in BM(phi), d(l) >= 1} d^{beta-2} l^2 < infinity"        (1.3)
"the family BM(phi) is short if phi is almost decreasing; otherwise long"
```

Theorem A, verbatim (`f ⪅ g` means `f <= c g` for some `c > 0` and all
`|x| >= 1` — one-sided, section 1.4):

```text
Theorem A.  Let beta >= 0, U = e^{i phi}, S = e^{i psi} smooth unimodular with
  phi'(x) <~ |x|^beta,  psi'(x) <~ |x|^beta                       (1.4)
  (i)  if phi is NOT (beta)-almost decreasing then N^+[U S_eps] = 0;
  (ii) if phi IS (beta)-almost decreasing then N_p[U_eps S_eps] != 0
       for all eps > 0 and all p < 1/2.

Corollary (beta >= 0, c = c(U,S,beta) = inf{a : phi + a psi is
(beta)-almost decreasing}):  for all p < 1/3:
  N_p[U_eps S_a] = 0 (a < c),   N_p[U_eps S_a] != 0 (a > c).

Theorem B.  J meromorphic inner, (arg S)'(x) ~ |x|^beta, c = c(J,S,beta):
  for all p >= 1:  N_p[J_eps S_a] = 0 (a < c),  N_p[J_eps S_a] != 0 (a > c).
```

The two (1.6) criteria, verbatim (section 1.6):

```text
"Suppose phi : R -> R is a smooth function.  Then N^+[e^{i phi}] != 0 if and
 only if  phi = ff + h~  (1.6)  for some smooth increasing ff and some
 h in L^1(dPi).  There is a similar criterion for Toeplitz kernels in Hardy
 spaces:  N^p[e^{i phi}] != 0 if and only if phi admits a representation (1.6)
 with ff being the argument of some inner function and with h in L^1(dPi)
 such that e^h in L^{p/2}(R)."
```

Little multiplier (section 4.1), verbatim:

```text
"Let beta >= 0 and suppose that U = e^{i phi}, S = e^{i psi} satisfy
 conditions (1.4) of Theorem A.
 Proposition.  If phi is almost (beta)-decreasing, then N^+[U_eps S_eps] != 0
 for all eps > 0."
```

The proof's two quantitative inputs (sections 4.1–4.2), verbatim:

```text
SUM_{l in BM(phi)} d^{beta-2} l^2 < infinity                      (4.1)
"f = phi* - phi, so f = 0 outside the union of BM intervals, and
 f'(x) <~ |x|^beta on BM intervals.  By (4.1) we have l >~ d, and therefore
 0 <= f <~ l d^beta on l"                                        (4.2)
"we can assume l >~ d for all BM intervals; otherwise we can eliminate short
 intervals by adding a bounded function to phi (this will not affect the
 N^+-kernel).  In particular, we will assume that BM intervals don't cluster
 to a finite point."
section 4.2: construct disjoint l_n covering all BM intervals with
 SUM_n d_n^{beta-2} l_n^2 < infinity                              (4.3)
 for all n there is phi_n in [0, eps] with
   INT_{l_n} ( f(x) - phi_n |x|^beta ) T_n(x) / (1+x^2) dx = 0    (4.4)
 (T_n the tent function of l_n), then beta(x) = SUM phi_n |x|^beta T_n(x)
 satisfies |beta'| <~ |x|^beta and f + beta in the real Hardy space.
```

BM multiplier (section 5.1), verbatim in outline:

```text
"M_p(S)": w in L^1(dPi) with outer function W = e^{w + i w~} such that
 for all eps > 0 there is G in N^+[. S_eps] with W G in H^p.
Lemma:      w in M_p(S) iff for all eps > 0, N_p[. S_eps . W] != 0.
Theorem:    (arg S)' <~ |x|^beta and  |x|^{2+beta} m^2 w_0'(x)^2 in D(R;inf)
            => w_0 in M_p(S) for all p < 1.
```

Two immediate class observations from the statements themselves: the whole
multiplier section produces `p < 1` only, and the `H^1`-level machinery of
item (5) is stated for symbols involving inner functions.

## 3. The BM interval family of the tree's phase (computed)

The tree's phase, in the paper's normalization (`U = e^{i phi}`, `S = e^{i xi}`,
`phi_a = phi + a psi`, `a = 4 pi log(1/lambda) >= 0`):

```text
phi_a(x) = gamma(x) + a x,        gamma(x) = 2 pi x log(pi) - 2 arg Gamma(1/4 + pi i x)
gamma(0) = 0, gamma odd, gamma(1) = 7.0619421332  (recorded max ~7.07),
gamma'(x) = -2 pi log|x| + O(1/|x|),  gamma' > 0 on (-1,1), < 0 outside.
```

Structure: `phi_a` increases on `(-R_a, R_a)` and decreases outside with
`phi_a -> +inf` as `x -> -inf`, where the right turning point solves
`gamma'(R) + a = 0`, i.e.

```text
R_a = exp(a/(2 pi)) = exp(2 log(1/lambda)) = lambda^{-2}.
```

Since `phi_a(0) = 0 < phi_a(R_a) = 2 pi R_a` for every `a >= 0` and the running
maximum `phi_a*` equals `phi_a(R_a)` up to `R_a`, the set `{phi_a != phi_a*}`
is the single interval `(x*_a, R_a)` with `x*_a < 0 < R_a`:

```text
x*_a = the unique solution of  phi_a(x) = phi_a(R_a)   on the decreasing branch.
```

Numerics (`scripts/bm_intervals_1630.py`, mpmath 25 digits, window `[-14,14]`,
5601 grid points; log `tmp_bm1630.txt`):

+----------------------+---------------------------+--------+-----+----------------+
| a = 4 pi log(1/lamb) | BM interval(s) in window  | l      | d   | INT f dPi      |
+----------------------+---------------------------+--------+-----+----------------+
| 0      (lambda = 1)  | 1: [-3.7800, 0.9950]      | 4.7750 | 0.0 | 5.39872        |
| 1.0                  | 1: [-4.4000, 1.1700]      | 5.5700 | 0.0 | 6.47686        |
| 8.710344 (lambda=1/2)| 1: [-14.00*, 3.9950]      | 17.995 | 0.0 | 24.2531        |
| 28.943517(lambda=1/10)| 1: [-14.00*, 13.9950]    | 27.995 | 0.0 | 249.873        |
+----------------------+---------------------------+--------+-----+----------------+

`*` the left end is the window edge, the true crossing lies further left.

Independent checks: `argmax gamma = 1.00105848886` with `gamma = 7.06194565803`
(the recorded maximum `~7.07`); `x* = -3.78173516455`, `l = 4.78279365341`;
right edges `3.995` and `13.995` against the prediction `lambda^{-2} = 4` and
`100`; the deficit integral is finite (`f in L^1(dPi)`, values above) and the
`a = 0` deficit is bounded by `max f = 7.06`.

Class-gap numerics (same log):

+-------+----------------+-------------------------+-------------------------+
| x     | abs gamma      | abs gamma/(\|x\| log x) | abs gamma/\|x\|^{1/2}   |
+-------+----------------+-------------------------+-------------------------+
| 10    | 81.05910017    | 3.520352                | 25.633138               |
| 100   | 2264.409902    | 4.9171036               | 226.44099               |
| 1000  | 37118.73578    | 5.3734874               | 1173.7975               |
| 10000 | 515870.1145    | 5.6009886               | 5158.7011               |
+-------+----------------+-------------------------+-------------------------+

`abs gamma/(|x| log|x|)` tends to `2 pi = 6.283...` from below exactly as
`2 pi (1 - 1/log x)` predicts; `abs gamma/|x|^{beta}` diverges for
`beta = 1, 1/2, 1/10` and tends to `0` for `beta > 1`.  **No single beta makes
`|gamma'| ~ |x|^beta`**, so Theorem B's and C's two-sided power-law
hypotheses, and the multiplier theorem's `(arg S)' <~ |x|^beta` reading as a
match, are not met; Theorem A's `(1.4)` is one-sided and IS met (see next).

Consequence for shortness:

```text
BM(phi_a) is a single interval with d = 0 for every a >= 0
==> the sum in (1.3) runs over NO interval
==> phi_a is (beta)-almost decreasing for every beta >= 0, every a >= 0,
==> the transition parameter of the corollary is  c = -infinity
==> (Theorem A(ii), Corollary, section 4.1) the SHORT branch is in force.
```

## 4. Class audit (law F40, continued)

```text
hypothesis / class check                                     status
+-----------------------------------------------------------------------+
| (1.4) one-sided: phi_a'(x) = gamma'(x) + a <= a on |x| >= 1, and       |
| psi'(x) = 1                                              SATISFIED    |
| (m = e^{i gamma} is smooth unimodular, phi_a(-inf) = +inf,            |
|  phi_a(+inf) = -inf)                                                  |
| (1.3) shortness sum                                      VACUOUS      |
| Theorem A(ii): N_p[U_eps S_eps] != 0, p < 1/2            APPLIES       |
| Corollary (p < 1/3)                                      APPLIES       |
| section 4.1 little multiplier proposition                APPLIES       |
| Theorem B (p >= 1, incl. p = 2): needs J inner           OUT OF CLASS  |
|   (|m(x+iy)| ~ |x|^{2 pi y}, m is not inner, not in N)                |
| Theorem C (beta in (-1,0], sub-exponential)              NOT APPLICABLE|
| power-law hypotheses of B/C and section 5.1 (='~')        FAIL          |
+-----------------------------------------------------------------------+
```

Three caveats, each of them a named gap rather than a verdict:

1. **Transfer gap (section 4.2).** The section 4.1 proof consumes `l >~ d`
   and the level constraint `phi_n in [0, eps]` of (4.4).  Our interval has
   `d = 0` and a deficit of size `f(0) = phi_a(R_a) - 0 = 2 pi R_a`
   (`= 7.06` at `a = 0`), so the natural level `phi_n = INT f T dPi / INT
   |x|^beta T dPi` is of order `R_a`, far above `eps`.  The proposition is
   *stated* for every phase satisfying (1.4), but its *proof* is written for
   intervals away from the origin.  The transfer to `d = 0` intervals is
   therefore expected but not verified.
2. **p-range gap.** Everything the little-multiplier chain gives is
   `p < 1/2` (corollary `p < 1/3`); section 5 reaches `p < 1`; item (5) of
   the roadmap needs inner functions to climb to `p >= 1`.  Our base lives at
   `p = 2` (section 5 below).
3. **Direction.** With the freshly retrieved text the direction is now
   unambiguous: `short => nontrivial`.  1629 section 3's "expected to be
   trivial" is withdrawn (Erratum A).

## 5. The base at p = 2, and the criterion form

Smirnov's identity `N^+ cap L^2 = H^2` gives, for `p = 2`,

```text
N^2[U] = {F in N^+ cap L^2 : conj(U) F in N^+}
       = {F in H^2(C_+) : conj(U) F in H^2(C_+)}.
```

The carrier base (1629 section 3, exact Toeplitz form) is

```text
carrier(lambda) != {0}  <=>  exists H in H^2(C_+) \ {0}, U_tree H in H^2(C_-),
U_tree(xi) = e^{4 pi i (log lambda) xi} m(-xi),     log lambda < 0 for lambda < 1.
```

Reflecting the half-plane (`F(z) -> conj(F(conj z))`, then `z -> -z`) identifies
this kernel with `N^2[e^{i psi}]` for `psi = -gamma - a xi`, `a = 4 pi
log(1/lambda)`.  Combining with the retrieved (1.6) criterion at `p = 2`
(`e^h in L^1(R)`):

```text
BASE  <=>  there are an inner function Theta and h in L^1(dPi) with
           e^h in L^1(R) such that      -gamma(x) - a x = arg Theta(x) + h~(x).
```

Consistency checks and convention flags:

* Model `m = 1`: `psi = -a x` is represented by `Theta(z) = e^{-i a z}` (inner
  in the lower half-plane, argument `-a x`, `h = 0`), matching the model check
  of 1629 (`lambda < 1` nontrivial) - **provided** the criterion's "inner"
  admits lower-half-plane inner functions.  This is a convention flag to pin
  against [23, section 2] (the reference given in the paper for (1.6)).
* Growth is not an obstruction by itself: arguments of inner functions are not
  asymptotically linear in general (a singular inner function with a slowly
  growing singular measure has an argument growing like `x log x`), and the
  classical asymptotic-linearity `arg Theta = Cx + O(log x)` is a statement
  about functions of bounded type, which our `m` is not.
* What the criterion demands of a super-linear `psi` is quantitative: a
  conjugate `h~` with `h in L^1(dPi)` following `|x| log|x|` on a set of full
  density.  Whether the `L^1(dPi)` budget forbids or allows that is exactly
  the still-unretrieved quantitative layer ([23, section 2]); the paper's
  section 2 (Lemmas 1-5, one-sided Lipschitz estimates for the Hilbert
  transform) is the natural place to settle it.

This is the sharpest form the carrier obligation has had: not a construction
problem, but one decomposition question with a named source for the answer.

## 6. Erratum A: 1629 section 3's two clauses

Both clauses of 1629 section 3 are corrected by the retrieved text.

**(a) The `H² \ N⁺` phrasing is vacuous.** 1629 section 3 says:

```text
"so at the paper level the SN kernel of our symbol is expected to be trivial.
 The base is therefore a **Hardy-only** phenomenon: any witness must live in
 `H²(ℂ₊) \ N⁺` - precisely the gap between the Hardy and Smirnov-Nevanlinna
 kernels, which is what the *big* multiplier theorem (Theorem 8.5) addresses
 and what the missing retrieval covers."
```

There is no such gap: `H^p ⊂ N⁺` for every `p > 0` (outer factors are Smirnov),
so `H² \ N⁺ = ∅` and "a witness in `H² \ N⁺`" describes nothing. The correct
statement is the specialization `N⁺ ∩ L² = H²` (Smirnov), which gives

```text
N₂[U] = {F in N⁺ : conj(U) F in N⁺} ∩ L² = {F in H² : conj(U) F in H²},
```

i.e. the two-sided kernel at `p = 2` IS the Hardy kernel: the base is the
`p = 2` endpoint of the same kernel family `N_p[U]` as the classical theory,
not a class outside it. Likewise 1629 section 5's closing clause "if true it is
a Hardy-only phenomenon (`H² \ N⁺`)" should read "it is the `p = 2` case of the
multiplier problem".

**(b) The shortness direction was reversed.** 1629 section 3 derives from the
single short BM interval that "the SN kernel of our symbol is expected to be
trivial". The primary source says the opposite: Theorem A(ii), the corollary
(`p < 1/3`), Theorem C(ii), and section 4.1's Proposition all read

```text
phi (beta)-almost decreasing  ==>  N_p[U_eps S_eps] != 0   (short => NONtrivial),
phi NOT (beta)-almost decreasing ==> N⁺[U S_eps] = 0       (long => trivial),
```

so shortness is the *nonvanishing* side. With `d = 0` for every `a` (section 3
above) our phase is short for every `β ≥ 0`, hence lies on the nonvanishing
side - which is consistent with the base being open rather than false, and with
1627's obstruction being about finite exponential type rather than about
shortness. The retrieval also exposes the exact reason the transfer stops short
of `p = 2`: the nontriviality statements stop at `p < 1/2`, and the route from
`N⁺` to `N^p` for `p ≥ 1` (section 1.7 item (5)) is written for symbols
involving inner functions, which `m` is not.

## 7. Erratum B: 1625 section 2's operator sandwich is false

1625 section 2 proved `StripDensity(Lambda) <= Lambda` by the chain

```text
P M_Delta P = P (E M_Delta E) P        (sandwich at the E level)
0 <= E M_Delta E                       (M_Delta an orthogonal projection)
0 <= P (E M_Delta E) P <= E M_Delta E  (0 <= P <= 1, positive sandwich)
Tr(P M_Delta P) <= Tr(E M_Delta E) = Tr(M_{Delta cap S}) = volume(Delta cap S)
```

The third line is **false as an operator inequality**.  Counterexample, in raw
vector coordinates on `C^2`: let `E = 1`, let `M` be the rank-one positive
operator `M z = <u, z> u` with `u = e_1 + e_2`, and let `P` be the orthogonal
projection onto `span e_2` (so `P <= E`).  Then

```text
w = e_1 - e_2:   <w, M w> = |<u,w>|^2 = 0,        (u orthogonal to w)
                 <w, P M P w> = |<u,e_2>|^2 |<e_2,w>|^2 = 1,
so  <w, (M - P M P) w> = -1 < 0,   yet M = E M E >= 0 and 0 <= P <= 1.
```

The *conclusion* of 1625 is unaffected: the trace-level statement
`re Tr(P T P) <= re Tr(T)` holds for every positive `T` (standard proof:
`Tr(P T P) = Tr(T^{1/2} P T^{1/2})` and `T^{1/2} P T^{1/2} <= T` because
`P <= 1`).  What changes is the proof: the compression inequality is the
irreducible input, and it is exactly the layer that no brick had named.

## 8. The base as a two-tap convolution equation, and the B3 insurance verdict

**The tap.** The Γ-factor has an elementary inverse transform. With
`F(h)(ξ) = ∫_ℝ h(u)e^{-2πiuξ}du` and the substitution `t = e^{2u}`,

```text
∫_R w(u) e^{-2πiuξ} du = (1/2) π^{-1/4+πiξ} Γ(1/4 - πiξ) = (1/2) Γ_R(1/2 - 2πiξ)
    for   w(u) = e^{u/2} e^{-π e^{2u}},
```

so with `A(ξ) = Γ_ℝ(1/2 − 2πiξ)` and `B = A(−·)`:

```text
A = 2 F(w),        B = 2 F(w(-.)),        m = A/B = F(w)/F(w(-.)).
```

(`w` is the "Γ-tap": `w(u) = e^{u/2}e^{−πe^{2u}} = t^{1/4}e^{−πt}` in `t = e^{2u}`;
it decays doubly exponentially at `+∞` and doubly exponentially in `1/t` at
`−∞`.)  The identity is checked numerically at `ξ = 0` (law F39 bookkeeping):
`A(0) = Γ_ℝ(1/2) = 2.7233`, `∫_ℝ w = 1.3617 = A(0)/2` (section 9 rig).

**The convolution form of the base.** Start from the committed Toeplitz form
(1629 section 3), `∃H ∈ H²(ℂ₊)\{0}` with `e^{4πi(log λ)ξ}m(−ξ)H ∈ H²(ℂ₋)`, write
`c = 2 log λ ≤ 0` and `G := e^{2πicξ}m(−ξ)H`, and use `m(−ξ) = A(−ξ)/B(−ξ)`,
`B(−ξ) = A(ξ)` to clear denominators:

```text
e^{2 pi I c xi} A(-xi) H(xi) = B(-xi) G(xi).
```

Multiplying by `e^{2πicξ}` acts on inverse transforms as the shift
`h ↦ h(· + c)` (`F(h(·+c)) = e^{2πicξ}Fh`), and products become convolutions
with the taps `w`.  Pulling the identity back to the `u`-line:

```text
BASE  <=>  there are h in L^2((-inf,0]), g in L^2([0,inf)), not both zero, with
           w(.- ã/(2 pi)) * h  =  w * g,          ã = 4 pi log(1/lambda) >= 0.
```

The two half-line constraints are Paley–Wiener in the same convention
(`H ∈ H²(ℂ₊) ⟺ supp h ⊆ (−∞,0]`, `G ∈ H²(ℂ₋) ⟺ supp g ⊆ [0,∞)`, both with the
`e^{−2πiuξ}` kernel, matching the committed dictionary of 1626 section 2).
Model check: for `m ≡ 1` the taps degenerate to `δ`, the equation reads
`h(· + c) = g`, and a nonzero solution exists iff `[c, ∞) ∩ (−∞,0] ≠ ∅` iff
`c < 0` iff `λ < 1` - exactly 1629's model verdict, re-derived in the new
variables.

What this buys: the base is now a *concrete two-tap matching equation between
one shift of the same Schwartz tap*, with no division by the symbol and no
hyperfunction (the taps are honest Schwartz functions and both sides are
`L² ∩ C₀`).  A nonzero solution requires the left-half-line side to reproduce
the right-tap image of a right-half-line `g`, i.e. it is precisely the
"cancellation" of 1628 section 3 (zeros of `m` against `F v`) in convolution
clothes.

**B3 insurance verdict (map 043 section 5, option B3).** B3 asks for a
re-decomposition in which the carrier is replaced by a *provably nonempty*
object.  The analysis this round:

```text
candidate substitution                     verdict
+--------------------------------------------------------------------------+
| C' strictly inside the carrier            C' != {0} witnesses the base     |
|                                           itself: no gain (law F33)       |
| C' strictly larger (range E, H^2(C_+),    dist(h_i, C') can vanish only    |
| whole space)                              if h_i already lies there; the  |
|                                           residual's content collapses    |
| a DIFFERENT skeleton (drop G8, prove      available only via the           |
| (star) elsewhere)                         S3-type estimate, which is       |
|                                           already filed in five forms     |
|                                           (1620: "any further              |
|                                           rearrangement is a rename")      |
+--------------------------------------------------------------------------+
```

So B3 does not produce insurance: the carrier is the *minimal* closed object
adapted to the `E/Q` pair (`range E ⊓ range Q`, 1589), any proper provably
nonempty subspace of it is the base in disguise, and any proper enlargement
destroys the distance terms.  What survives from the B3 lane is the
*conjunction* re-typing of F37 and the convolution form above: both are
re-formulations of the same object, not bypasses.  The honest consequence is
that B3 is struck from the decision tree; only B1 (criterion/witness) and B2
(the same, negatively) remain, plus B4's separate premise.

## 9. The Lean brick landed this round

`Dev/StripDensityTraceLedger.lean`, no `sorry`, four declarations plus one
named obligation, all at the trace level for
`ordinaryTraceAlong (basis : HilbertBasis iota C H) (T : H ->L[C] H) : C`:

```text
re_ordinaryTraceAlong_eq_tsum_re   re Tr = SUM_i re <b_i, T b_i>   (Complex.reCLM.map_tsum)
ordinaryTraceAlong_re_nonneg       T >= 0, summable => 0 <= re Tr T
re_inner_self_le_of_le             A <= B => re <b_i, A b_i> <= re <b_i, B b_i>
ordinaryTraceAlong_re_mono         A <= B, both summable => re Tr A <= re Tr B
StripDensityCompressionObligation  (def)  re Tr(P T P) <= re Tr(T)
stripDensity_trace_le_of_compression  P E = E P = P and the obligation for
                                   E M E  =>  re Tr(P M P) <= re Tr(E M E)
```

`ordinaryTraceAlong_re_mono` is 1625 section 4's "irreducible ingredient 2";
`StripDensityCompressionObligation` is the exact remaining ingredient (the
literature proof needs an operator square root, absent from the tree's layer;
the alternative reading of the same missing layer is the measure-theoretic
basis-to-integral identity of 1625 section 4 item 3).

**Audit companion.** `Dev/StripDensityTraceLedgerAudit.lean` carries the
refutation of 1625's operator-level sandwich, at the smallest possible model:
`E = 1`, `M = rankOne u u >= 0`, `P = rankOne e e` a rank-one projection with
`<e, u> = 1`, a test vector `w` with `<u, w> = 0`, `<e, w> = -1`, giving
`(M - P M P) w = e` and `re <w, (M - P M P) w> = -1 < 0`.  Declarations:
`rankOne_compression_not_le` (general), the projection facts
`isIdempotentElem_rankOne_of_inner_self`,
`isSelfAdjoint_rankOne_of_inner_self` (via
`ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint`), the `C^2`
witness `eTwo = e_2`, `uTwo = e_1 + e_2`, `wTwo = e_1 - e_2` with its four
inner-product lemmas, and `rankOne_compression_counterexample`.  One standard
step is deliberately *not* formalized: `P <= 1` for a rank-one projection
(Cauchy-Schwarz); it is the only hypothesis of 1625's sandwich that the
refutation does not verify inside Lean, and the refutation does not use it.

**Acceptance (log `build-logs/1630_strip_density_trace_ledger_audit.log`).**
`Build completed successfully (2662 jobs)`, zero `^error`, zero `sorryAx`,
zero warnings in either new module; all six `#print axioms` lines return
`[propext, Classical.choice, Quot.sound]`.  (The log also replays two
pre-existing warnings in `Source/CC20Concrete/PositiveTrace.lean`, lines 68
and 628, untouched this round.)

## 10. B4-scalar, tested literally (map 043 item 2)

**The committed line.** 1628 section 3 states the premise per column as

```text
(B4-scalar)   xi |-> e^{2 pi I (log lambda'') xi} m(xi) psi(xi)  in  H^2(C_+),
              psi := F^{-1} v for the committed column v,
```

with `lambda'' = 1/2` committed, and, on the same page, the caveat
"`|m| ~ |x|^{2 pi y}` is not uniformly polynomial in `C_+`".  H^2(C_+) is
tested here by its definition, not by a surrogate: `Psi = e^{2 pi I C xi} m psi`
is analytic in `C_+` (m is analytic there, psi is explicit), so membership is
exactly the boundedness of `sup_y ||Psi(. + I y)||_{L^2}`.

**Rig** `scripts/b4_scalar_1630.py`, grid `|xi| <= 512`, `dxi = 9.77e-4`,
symbol from `scripts/rh_symbol_num.py` (Stirling + mpmath patch; self-test
against mpmath at 25 digits: worst absolute error 5.9e-13 at xi = 500, and the
identities `|m| = 1`, `m(-xi) = 1/m(xi)` to 1.2e-16).

```text
(1) growth caveat, measured:  |m(x + I y)| / |x|^{2 pi y}
       y        x = 20        x = 100       x = 500
    0.005      0.9999999     1.0000000     1.0000000
    0.0796     1.0000000     1.0000000     1.0000000
    0.300      1.0000660     1.0000030     1.0000000
    1.000      1.0026030     1.0001040     1.0000040
    (so |m(x + I y)| = |x|^{2 pi y} (1 + o(1)): the caveat is exact, with
     relative error below 3e-3 at y = 1.)
```

```text
(2) slice norms G(y, X) = (INT_{-X}^{X} |Psi|^2 dx)^{1/2}, C = log(1/2)
    column                        y        G(20)      G(100)     G(500)   G500/G20
    v = 1_[0,1]                 0.0200   0.859502   0.865672   0.867512    1.0093
    v = 1_[0,1]                 0.0796   0.846351   0.969207   1.078157    1.2739
    v = 1_[0,1]                 0.3000   32.00882   297.4331   2763.335   86.3304
    v = 1_[0,1]                 1.0000   1.726e+08  1.899e+12  2.093e+16  1.213e+08
    v = C^inf bump on [0,1]     0.0200   0.6977206  0.6977207  0.6977207   1.0000
    v = C^inf bump on [0,1]     0.1000   0.9302324  0.9302332  0.9302332   1.0000
    v = C^inf bump on [0,1]     0.3000   8.253124   8.266255   8.266255    1.0016
    v = C^inf bump on [0,1]     1.0000   3.749e+08  2.256e+09  2.280e+09   1.0001
    v = e^{-s/2} 1_[0,inf)      0.0796   0.6913802  0.8006697  0.8967396   1.2970
    v = e^{-s/2} 1_[0,inf)      0.3000   31.64070   294.0610   2732.023   86.3452
```

**Verdict.**  For all three column classes the premise fails, at the
quantitative threshold `y = 1/(4 pi) = 0.0795774715` for the algebraically
decaying columns and with no threshold at all for the entire one:

* `G500/G20 -> 1` below the threshold (the slice is in `L^2(R)`) and
  `G500/G20` grossly exceeding 1 above it (the slice is not), because
  `|Psi|^2 ~ |x|^{4 pi y} |psi|^2` and `|psi| ~ 1/(2 pi |x|)`: the slice
  integral converges iff `4 pi y < 1`.  At `y = 1/(4 pi)` the growth is exactly
  marginal and the observed ratio is 1.27 - 1.30;
* the entire column converges on every slice but its slice norms grow
  `0.698 -> 0.930 -> 8.27 -> 2.28e9`, so `sup_y` is infinite: not in
  `H^2(C_+)` either;
* this is the same obstruction as (1) seen from the other side: no column
  decay class beats a growth that is `|x|^{2 pi y}` for every `y
  simultaneously, and the sup over `y` is what `H^2` asks for.

**Flag (erratum candidate, not resolved here).**  The literal statement is
*degenerate* under the committed support facts, independently of any numerics:
1628 section 3 itself places the kernel `K = F^{-1}(m)` on the half-line
`[0, inf)`, and the confinement header quoted there puts the columns on a
half-line; then `F^{-1}(m psi) = K * v` (a convolution of the two inverse
transforms) is supported on that same half-line, while
`Psi in H^2(C_+)` requires its inverse transform to be supported on the
*opposite* one - so only `Psi = 0` can satisfy the literal line.  Either the
half-line orientation of one of the quoted pieces is reflected, or
`psi := F^{-1} v` in 1628 section 3 denotes a reflected object.  The live
form, matching the committed carrier base, is the reflected pairing
`e^{2 pi I c xi} m(-xi) H`, `H in H^2(C_+)` - which is exactly what the item-4
probe of section 11 tests, and which does have solutions in the model case.
This is a convention question for the next source read of 1622's `U_m` and
1626 section 2's dictionary; no claim beyond the quotation is made here.

## 11. The Toeplitz kernel, probed by finite sections (map 043 item 4)

**Rig** `scripts/toeplitz_probe_1630.py`.  The committed carrier base is
`carrier != {0} <=> exists H in H^2(C_+) \\ {0}, U H in H^2(C_-)` with
`U(xi) = e^{2 pi i c xi} m(-xi)`, `c = 2 log lambda`.  In the dictionary of
1626 section 2 (`supp F^{-1}(H) subset (-inf, 0] <=> H in H^2(C_+)`), the
membership `U H in H^2(C_-)` is `P_{xi-spectrum >= 0}(U H) = 0`, one FFT mask,
and the finite section is the translate family `H_j = e^{2 pi I j xi} H`,
`j = 0 .. K-1`, `H = F(h)` for one fixed `C^inf` bump `h` on `[-1, 0]` (every
`H_j in H^2(C_+)`, all of finite exponential type).  The section matrix is the
compression of `T_U = P_+ M_U P_+`, `M_{jk} = <P_+(U H_j), P_+(U H_k)>`,
`N_{jk} = <H_j, H_k>`, and `sigma_min(K)` is the smallest relative defect
`||P_+(U H)|| / ||H||` over the section.

**Calibrations (both model cases have known answers).**

```text
setting                          K = 1        K = 2        K = 48      exact
model m = 1, lambda = 1          1.000000     1.000000     1.000000      1
model m = 1, lambda = e^-1       3.55e-16     3.03e-16     3.32e-16      0
model m = 1, lambda = 1/2        4.146e-8     4.146e-8     4.146e-8      0
   (all three at |xi| <= 64, N = 2^15; the first two are the same at N = 2^17)
   same model, |xi| <= 128 (window edge twice as far):
model m = 1, lambda = 1/2        1.8208e-11   1.8208e-11   1.8208e-11     0
```

The floor is not round-off and not the grid: for `lambda = e^{-1}` the witness
is a *grid-aligned* translate (`c = -2`, a multiple of the spatial step) and the
rig returns machine zero; for `lambda = 1/2` the shift is not aligned and the
residual is the `xi`-window-edge leakage, whose size tracks `|H|` at `|xi| = 64`
(resp. 128) - the diagnostic run `tmp_diag_spec*.py` localized it to the
truncation pedestal near `eta = 0` and confirmed that the construction is exact
where the shift is aligned.  **All readings below are quoted against this
calibrated floor.**

**Result (real symbol, `|xi| <= 128`, floor 1.8e-11).**

```text
lambda        sigma_min(K=1)   sigma_min(K>=2)   D[H_0]        D[H_1]
1             0.412477         0.412477          0.432930      0.803072
1/2           0.068243         0.068243          0.069457      0.342051
1/e           0.026005         0.026005          0.026997      0.137805
0.1           2.9905e-06       2.9905e-06        2.9976e-06    3.3500e-04
0.01          0.000000 (<= floor)                1.6611e-12    1.9371e-12
```

**Verdict.**

* **Saturation in K.**  `sigma_min(K)` stabilizes by `K ~ 16` at every scale:
  at `lambda = 1` it drifts `0.432930 -> 0.414809 -> 0.413658 -> 0.412507 ->
  0.4124768` over `K = 1, 2, 4, 8, 16` (total drift below 0.5%), and at
  `lambda = 0.1` it drifts `2.997552e-6 -> 2.996225e-6 -> 2.994533e-6 ->
  2.990652e-6 -> 2.990549e-6` (below 0.25%): enlarging the finite-type section
  buys almost nothing.  The single translate `H_0` already carries essentially
  the whole section minimum.  This is the finite-section fingerprint of 1627's
  theorem (no witness of finite exponential type): the section can never
  contain a kernel vector, and here it does not even come closer.
* **Decay in lambda.**  The defect is a function of the shift alone:
  `0.4125, 0.0682, 0.0260, 2.99e-6, <= 1.8e-11`.  The last two are five orders
  apart and the `lambda = 0.1` value sits five orders above the floor, so it is
  resolved; the `lambda = 0.01` value is at the floor (unresolved).  So the
  finite-type class approaches the base as `lambda -> 0` without ever reaching
  it - the base is *approximable but not attained* by finite-type data, and no
  compactness argument from finite type can be expected to produce a witness
  (consistent with 1627's Paley-Wiener obstruction, now with a rate attached).
* **No verdict on the carrier.**  `sigma_min > 0` for every finite section is
  not triviality of the carrier: the section is finite-type, and the carrier
  asks for arbitrary `H in H^2(C_+)`.  What the probe rules out is only the
  finite-type route; the infinite-type (Gamma-factor / prolate) route is
  untouched and remains the single open gate.

## 12. Boundaries

* The carrier base, S3 (form v), WO-S, WO-B, `EndpointMass(eps)`, T1, (★), B4,
  B3, rho5, R4/(OB)/W1, and RH are unchanged and open.  No gap premise,
  `SourceRH`, or universal gate is introduced.
* Nothing in this record uses the unretrieved [23, section 2]; where the
  criterion's hypotheses would be needed, the convention flag is stated
  instead of a claim.
* The numerics are a self-check of committed definitions (`m`, `gamma`,
  `(1.3)`, `(1.6)`), not an authority (F27/F28).
* The three rigs of this record are `scripts/bm_intervals_1630.py`,
  `scripts/b4_scalar_1630.py` and `scripts/toeplitz_probe_1630.py`, all on the
  shared symbol evaluator `scripts/rh_symbol_num.py` (whose self-test is quoted
  in section 11).  Section 11 quotes every reading against its calibrated
  floor; the `lambda = 0.01` row is *at* that floor and is not evidence either
  way.  The section 10 refutation of the literal (B4-scalar) is a support
  statement about the quoted committed lines, not a re-derivation of 1622's
  `U_m`.
* The `2 pi y`-growth law `|m(x + I y)| / |x|^{2 pi y} -> 1` and the
  `1/(4 pi)` slice threshold are convention-free (they are properties of the
  modulus of the committed symbol), so they survive any later repair of the
  orientation flag in section 10.