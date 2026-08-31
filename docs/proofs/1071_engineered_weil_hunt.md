# 1071 - LEVEL-1 slice 2: the engineered (Yoshida-type) Weil hunt

Date: 2026-08-31. Follows 1070 (VERDICT H3': the smooth Gaussian detector
family CANNOT hunt; cross-phase locked positive in-band; exponential hunting
law flips <= poly(gamma) e^{-1.74 gamma_j}; consequence 4: pick ONE
Yoshida-type engineered family, same closed-form pipeline, only g~ changes).
This record pre-registers that family and its fork BEFORE any run.

## 0. Fork (stated BEFORE the run)

```text
Family E (engineered, symmetric; section 1):
  flip_j(delta, mu, beta) := margin + A_j(beta) - P_j  < 0
  with margin = sum_k 2|g~(rho_k)|^2, P_j = 2|g~(rho_j)|^2,
  A_j = 4 Re[ g~(beta + i gamma_j)^2 ]      (symmetry collapses the pair),
  lever := 4 |g~(beta+i gamma_j)|^2          (max |A|, Cauchy-Schwarz),
  wall   := margin - P_j                     (the low-zero background),
  scale check: a flip is called O(1)-scale if lever AND wall are both
  >= e^{-2} at that row (NOT exponentially suppressed in gamma_j).

  E-H1 (ENGINEERED FAMILY HUNTS): an O(1)-scale flip occurs (at least at
     j = 1). => the G path is LIVE with zero-engineered tests; record the
     (delta, mu*, beta) recipe and the measured wall/lever law as the
     schedule constraint.
  E-H2 (flip only suppressed): flips exist but every one sits at
     lever or wall <= e^{-c gamma_j} => phase freedom alone does not pay;
     record the suppression law.
  E-H3 (wall family-independent): no O(1)-scale flip at any delta, mu = mu*,
     beta => the background wall is a FAMILY-INDEPENDENT obstruction
     (uncertainty-type); hunting needs support-location freedom (prime-local
     / semilocal tests), i.e. the G path must change SCOPE, not just shape.
```

PRE-REGISTERED MECHANISM PREDICTION (from continuum estimates, to be checked
against the table, not assumed): for g~ with on-line mass envelope
Q e^{-delta^2 Q} (Q = t^2 + 1/4) the wall/lever ratio behaves like

```text
  wall / lever  ~  (3 sqrt(pi) / 16) * gamma_j * e^{2 c^2} / c^5,
  c := delta * gamma_j,
```

minimized near c = sqrt(5)/2 ~ 1.118, giving wall/lever ~ 0.57 * gamma_j.
At j = 1 (gamma_1 = 14.135) that is ~ 8 - a photo-finish decided by the
discreteness of the zeros; at j >= 2 the wall wins by a growing factor.
E-H3 is therefore the EXPECTED verdict, with j = 1 the only genuine fork
point. The run decides.

## 1. The engineered family (and why this one)

```text
  g~(s) = N(delta) * s (s - 1) * exp( (-delta^2 + i mu) * s (1 - s) )
  F = {0, 1}   (mainprop only needs {0,1} subset F, F finite disjoint from Z;
                the CC20 +-1/2 nodes are NOT needed at LEVEL-1)
  N(delta) = delta^2 * e        (max_t |g~(1/2+it)| = 1, closed form:
                |g~| = N Q e^{-delta^2 Q}, Q = t^2 + 1/4, max at Q = 1/delta^2)
```

Why symmetric: V(s) = s(s-1) and w(s) = s(1-s) are BOTH invariant under
s -> 1-s, so g~(1-s) = g~(s) EXACTLY (real coefficients give the conjugate).
Then

```text
  f~(s) = g~(s) g~(1-s)   (Mellin convolution theorem, 1070 s6.2)
  ON-LINE:  f~(1/2 + i g) = |g~(1/2+i g)|^2 >= 0  TERMWISE  (unchanged)
  TRIVIAL:  f~(1) = f~(0) = 0 EXACTLY                     (unchanged)
  OFF-LINE: f~(beta + i g) = g~(beta+i g)^2  and
            A_j = 4 Re[ g~(beta+i g_j)^2 ] = lever * cos(phi),
            phi = 2 arg g~(beta+i g_j)      <<<< FREE PHASE
```

The phase lever, explicitly (q = x + i y, x = beta(1-beta) + gamma^2,
y = gamma(1-2 beta)):

```text
  arg g~(beta+i g) = arg V(beta+i g) + mu x - delta^2 y
  =>  phi = 2( arg V + mu x - delta^2 y ),
  mu* := ( pi/2 - arg V(beta+i g) + delta^2 y ) / x    (sets phi = pi)
       ~ pi / (2 gamma^2)   at height gamma,
  magnitude cost: |e^{i mu q}| = e^{-mu y} = e^{mu gamma (1-2 beta)}
       = e^{O(1/gamma)} ~ 1   at mu = mu*   <<<< NO exponential suppression
```

This is the design the 1070 verdict demands: the Gaussian's phase
(2 beta - 1)(gamma delta^2 - 4/gamma) was LOCKED because its phase engine
lives in delta^2 Re(s) Im(s) with the SAME delta^2 that suppresses the
masses. Here the phase engine is mu * Re(s(1-s)) ~ mu gamma^2 - the
enormous REAL part of s(1-s) on the strip - while the magnitude feels only
the O(gamma) imaginary part. Phase-to-cost ratio improves from e^{-c gamma}
to e^{-c/gamma}. mu leaves the ON-LINE masses UNCHANGED (y = 0 on the
critical line), so margin and P_j are mu-independent - a hard internal gate.

Honesty ledger (mirrors 1070 s2): (gap-1) g~ is entire Gaussian-type, NOT
C_c^inf - the class caveat carries over verbatim. (gap-2) full Weil
functional, no semilocal restriction. (gap-3) the ANCHOR GATE (section 2)
validates the sign chain before any fork data; the family change does not
touch it (it runs on the B-spline and CC20 tests, family-independent).

## 2. Gates (hard asserts, unchanged from 1070 unless listed)

```text
  ANCHOR-A: explicit-formula identity on the C_c 6-fold B-spline test;
            two independent W_R implementations must agree <= 1e-8 and the
            identity must close <= 1e-6 relative.           [verbatim 1070]
  ANCHOR-B: CC20's own example test has W_inf < 0.          [verbatim 1070]
  DICT:     f~(1) = f~(0) = 0 exactly (<= 1e-25).           [verbatim 1070]
  SYM (new): g~(1-s) = g~(s) <= 1e-25 at sample points off the fixed set.
  MU-INV (new): margin(mu=0) = margin(mu=mu*) <= 1e-20 relative at every
            scanned (j, delta) - the phase lever must not touch the sums.
  PHASE (new): measured xphase at mu* within 1e-6 of pi (mod 2 pi).
  A-symmetry gate [verbatim 1070].
```

## 3. Measured quantities

```text
  Scan: j in {1, 2, 3, 5, 10, 20, 30} (mpmath zetazero, dps 30);
  delta in {0.3, 0.6, 1.0, 2.0} / gamma_j   (the c-lattice around the
  predicted optimum c ~ 1.118);
  beta grid {0.05, 0.10, 0.15, 0.20, 0.30, 0.40, 0.45}   [as 1070];
  mu in {0, mu*(beta)}  (mu = 0 is the no-phase control row);
  per row: margin, P_j, A at every beta, lever, wall = margin - P_j,
  wall/lever, xphase, tail bound (same envelope quadrature as 1070 with
  |g~(1/2+it)|^2 = N^2 Q^2 e^{-2 delta^2 Q}).
  Zero cache: |gamma| <= min(5/delta_min, 6000) (the wall is made of
  background, so the cache reaches deeper than 1070; rows whose window
  exceeds the cache carry printed tail bounds and are judged accordingly).
```

## 4. Acceptance

mpmath dps 30; all gates hard asserts; acceptance = flushed Linux-side log
(zero error/traceback/FAIL; all gate lines green), never exit codes. The
verdict is written into section 5 by hand from the table.

## 5. Post-run addendum (filled after execution)

Run: one deterministic WSL run (zero error/traceback/FAIL; 392/392 fork
rows = 7 j x 4 delta x 7 beta x {mu=0, mu*}; all anchor/family gates green:
ANCHOR-A identity, ANCHOR-B sign, symmetry 4.3e-31, dictionary exact 0,
phase gate exact +-pi at every mu* row, mu-invariance <= 1e-20 at every
scanned row).  Every scanned cutoff fit inside the 1272-zero cache
(largest cutoff 1689 < 1729), so no row needed its tail-bound escape.

### 5.1 The measured fork table (per j: best row over the delta/beta grid)

```text
  j | gamma_j | min wall/lever (mu*) | best flip (any mu)
  1 |  14.135 |        0.0000        |  -2.562152  FLIP
  2 |  21.016 |        1.3190        |  +1.150546  no flip
  3 |  25.011 |        1.9680        |  +2.137980  no flip
  5 |  32.936 |        3.3760        |  +4.172392  no flip
 10 |  49.774 |        6.7610        |  +9.265919  no flip
 20 |  77.144 |       13.0520        | +19.161391  no flip
 30 | 101.317 |       19.1750        | +29.055215  no flip
```

The j = 1 flips (all seven beta at delta = 1/gamma_1, six at
delta = 2/gamma_1): margin 3.180, P = 2.000, wall 1.180, lever 2.20-3.74,
flip = -1.02 .. -2.56 (wall/lever 0.31-0.54), xphase = +-pi exactly,
tail < 2.3e-18 - an O(1)-scale certificate sink by both clauses of the
pre-registered scale check (lever AND wall >= e^{-2}).

### 5.2 VERDICT: E-H1 fired at j = 1; the j >= 2 obstruction is LINEAR

Per the pre-stated fork: an O(1)-scale flip occurs at j = 1 (the branch's
own clause "at least at j = 1").  The G path is LIVE with zero-engineered
tests, at the first zero's height, with the recipe below.  The scan also
measured the obstruction law the fork's E-H3 branch was probing:

```text
  min wall/lever ~ 0.66 * gamma_j   (j >= 2; measured ratios 0.64-0.68)
```

a LINEAR hunting obstruction - five-plus orders of magnitude better than
1070's exponential law poly(gamma) e^{-1.74 gamma_j} at every scanned
height (at gamma_30: e^{-176} vs 19).  The phase lever bought the whole
difference, exactly as the family design intended.

### 5.3 The mechanism and the recipe

```text
  WHY j = 1: the first zero is spectrally ISOLATED - gamma_2 - gamma_1 =
     6.88 is a full detector band width at delta = 2/gamma_1, so the
     background vanishes into the envelope (measured wall 2.4e-5 against
     P = 0.0787) while the phase lever 4|g~(beta+i gamma_1)|^2 cos(phi)
     survives at O(1).  At j >= 2 the spacing 2 pi/log gamma shrinks, the
     neighbours crowd into every band, and the wall accumulates: the
     linear law 0.66 gamma_j IS zero crowding.
  RECIPE (recorded per E-H1): family E with F = {0,1};
     delta ~ 1/gamma_1 (the c = 1 row; c = 2 also flips with the wall
     vanished); mu = mu*(beta, gamma) = (pi/2 - arg V_F(beta+i gamma)
     + delta^2 y)/x per the s1 formula - the phase gate confirmed
     xphase = +-pi to < 1e-5 at EVERY mu* row (392-row grid); any
     beta in {0.05..0.45} flips at j = 1.
```

### 5.4 Consequences for the G path

```text
  1. 1070's consequence 4 is DISCHARGED: there exists an explicit
     engineered family that hunts at O(1) scale - the smooth-family
     verdict was a property of the family, not of LEVEL-1 hunting.
  2. The single-detector reach of THIS family is the lowest zeros only
     (wall/lever < 1 needs gamma_j <~ 1.5): zero crowding, not
     suppression, is the binding constraint.  Two escape directions are
     now the design levers: (a) multi-bump / combined tests, (b)
     support-location freedom (prime-local / semilocal tests) - the
     latter is again the 1070 gap-2 SCOPE wall, now with a measured
     price tag.
  3. Per-detector certificates (1050) absorb a LINEAR law as a schedule:
     detector #j must overcome ~gamma_j background - polynomial cost,
     not the exponential budget 1070 forced on A.
  4. Next slice options: (a) fine c-lattice at j = 2 (wall/lever 1.32 -
     one constant away from flipping; worth one narrow scan), (b) the
     multi-bump family, (c) hand the recipe to the Lean-facing detector
     design as the first CONSTRUCTIVE hunting datum.
```

### 5.5 Caveats (honesty ledger)

```text
  - The pre-registered mechanism prediction (s0) EXPECTED E-H3 with
    wall/lever ~ 0.57 gamma_j ~ 8 at j = 1; the measurement at the c = 1
    row gave 0.31-0.54 - the continuum estimate was right about the LINEAR
    form (measured coefficient 0.66) and wrong about the j = 1 constant
    (the isolation effect above).  The fork decided on data, as designed.
  - Run history: the first launch crashed at its own PHASE gate - the
    gate formula measured distance-to-zero instead of distance-to-pi;
    one mu=0 control row (j=1, delta=0.3/gamma_1: wall/lever 130) was
    flushed before the crash.  Gate formula fixed, zero cache persisted
    Linux-side, full grid re-run; no verdict data was read before the
    corrected run completed.
  - The delta lattice is coarse (c in {0.3, 0.6, 1, 2}): the true optimum
    and the exact flip boundary in (c, beta) are unresolved; j = 2's
    1.32 is an upper bound over this lattice.
  - The class caveats of 1070 s2 carry over (Gaussian-type entire g~,
    not C_c^inf; full Weil functional, no semilocal restriction).
```
