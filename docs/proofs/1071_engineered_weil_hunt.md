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

PENDING.
