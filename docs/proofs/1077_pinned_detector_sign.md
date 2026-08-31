# 1077 - Consumer #2 pinning: explicit triple-vanishing detector + field #4 sign

Date: 2026-09-01. Follows 1075 (F-A fired: the {0,1}-killing engineered symmetric
family flips zero #2 at O(1) scale with a THIN sink; single-detector reach = zeros
#1 AND #2). This record pre-registers the pinning slice BEFORE any run.

## 0. What this advances (and why it is allowed under the freeze boundary)

Record 1076 names four allowed consumers. This record advances **consumer #2**:

> a genuine compact-log detector with explicit support radius and finite
> visible-prime set;

by producing, for one pinned off-line zero rho_2 = beta + i gamma_2, an EXPLICIT
named test g with a closed form and a named support window - not the classical
existence theorem (CC20 `exists_residualWindow_correction`, fixed-window surjectivity)
that the route already carries.  Per the user's "both in one record" mandate it
simultaneously measures **field #4** of the healthy detector data at zero #2, i.e.
the sign that 1076/Lean reduce on a prime-free square to

    weilSquareSumPositive(g)  <=>  archimedeanTerm(g^box) > 0,
    and, for a root-supported triple-vanishing g,   qw(g) = -archimedeanTerm(g^box).

So "field #4 holds at zero #2" is exactly the numerical statement `qw(g_3) < 0`
on the pinned detector.  RH remains unclaimed; this is a numerical pinning + sign
measurement, not yet a Lean route payment (that is the follow-on slice).

## 1. The pinned detector (the explicit construction - deliverable (a))

The 1075 family kills only {0,1}; it is NOT triple-vanishing, so its measured flip
is not yet the clean field #4 statement (which requires vanishing at the whole node
set {0, 1/2, 1}).  We add ONE completion factor:

    g_3(s) = N' * s(1-s) * (s - 1/2)^2 * exp((-d^2 + i mu) * s(1-s)).

What it is / why it works:
- `s(1-s)` vanishes at {0,1}; `(s - 1/2)^2` vanishes at 1/2.  The product therefore
  kills the WHOLE triple {0, 1/2, 1} EXACTLY by construction - no interpolation, no
  residual-window existence lemma is needed for the vanishing clause.
- Symmetric under s -> 1-s (each factor individually symmetric), so on the orbit
  f_3~(s) = g_3(s)^2 and the off-line cross term is A = 4 Re g_3(rho)^2, exactly as
  in 1071/1075.
- Support window: root support lies in Icc(-log 2 / 2, log 2 / 2) in log coordinate
  (= x in [2^(-1/2), 2^(1/2)]); on that window the square is prime-free (visible
  primes = empty set, since no p^k with k>=1 falls in (1/2, 2)).  That finite
  visible-prime set (the EMPTY set here) IS consumer #2's second deliverable.

Phase retuning: keeping arg g_3(rho)^2 = pi requires absorbing the fixed phase of the
extra factor, so mu only gains one term relative to 1075's recipe:

    mu_3*(d, beta, gamma) = [pi/2 - arg V_F(rho) - 2 arg(rho - 1/2) + d^2 y] / x,
        q = s(1-s)|_rho = x + i y.

With the (s-1/2)^2 factor removed this reduces EXACTLY to 1075's mu*.  The probe
asserts that reduction as a gate so a sign slip in the correction cannot hide.

Normalization: the on-line peak of |g_3(1/2+it)| is mu-independent (q = t^2 + 1/4 is
real on the line), so N' is set by a one-shot on-line grid to make that peak exactly
1 - the same O(1)-scale convention as 1075, keeping wall / lever comparable and the
e^{-2} clause meaningful.

## 2. Fork (stated BEFORE the run)

The completion changes the RELATIVE size of the background (margin) versus the pinned
zero's own term (Pj): on-line every mass gains a factor t^4 while the off-line target
A sees |(rho-1/2)|^2, not gamma_2^2.  So killing s=1/2 has a real price, and the fork
is exactly whether that price is affordable at zero #2.

    F-A (PINNED / field #4 holds):
       exists a row at j = 2 with fl < 0 AND both O(1)-scale clauses pass
       (wall >= e^{-2} AND lever >= e^{-2}) AND the triple-vanishing + symmetry +
       phase gates all green.
       => the explicit detector g_3 has qw(g_3) < 0 <=> archimedeanTerm > 0 at zero #2;
          hrootDetector's sign clause is numerically satisfiable for zero #2 with a
          NAMED closed-form g and an EMPTY visible-prime set. Consumer #2 -> #3 advanced.

    F-B (SIGN-COST / completion too dear):
       min fl >= 0 at j = 2 over the re-scan even after beta is pushed past the
       1075 edge => killing s=1/2 costs more than the thin 1.5% sink found in 1075;
          triple-vanishing needs support-location or multi-bump freedom beyond a single
          symmetric completion factor. Record the measured margin as the price tag.

    F-C (ANOMALY, not expected):
       the triple-vanishing gate fails, OR symmetry / phase / mu-invariance breaks, OR
       the tail is uncontrolled => coordinate or construction issue; fix before any sign
       claim. Checked first because every other reading presumes a sound chain.

Scale check (carried from 1075): a flip counts as O(1)-scale only if lever AND wall are
both >= e^{-2} at the row.

## 3. Grids and cost

    j in {2, 3}                       (j = 2 is the pinned target; j = 3 is a control:
                                      its wall should still hold, confirming single-
                                      detector reach is not an artifact)
    cd in {1.00, ..., 1.40} step .05  (9 points straddling the 1075 valley cd* = 1.20)
    beta in {0.38, ..., 0.48} step .02(6 points; extends PAST the 1075 edge 0.46 to test
                                        the recorded caveat that deeper flips may exist,
                                        staying < 1/2 so rho remains genuinely off-line)
    mu in {0, mu_3*(beta, gamma)}     (mu = 0 control kept on every row)
    cutoff = max(3 gamma_j, 5/delta); the persisted zero cache covers it.
    Rows: 2 x 9 x 6 x 2 = 216 fork rows; margins computed once per (j, cd).

## 4. Gates and acceptance

- ANCHOR-A / ANCHOR-B imported VERBATIM from the committed 1071 probe
  (family-independent sign chain; identity residual <= 1e-6, W_inf < 0).
- Family gates: SYM (g_3(1-s)=g_3(s) rel <= 1e-25), TRIPLE-VANISHING
  (|g_3(0)|, |g_3(1/2)|, |g_3(1)| < 1e-25 - the new clause vs 1071's {0,1} only),
  DICTIONARY (trivial side of f_3~ vanishes), CONFIRM-REDUCTION
  (mu_3* + 2 arg(rho-1/2)/x == mu_1075*, resid <= 1e-25), PHASE (arg g_3(rho)^2 = pi,
  err < 1e-5 at every mu* row), MU-INV (mu leaves the on-line masses unchanged, rel
  < 1e-20).
- Acceptance: flushed Linux-side log, zero error/traceback/FAIL, all gate lines green;
  verdict hand-written into section 5 from the per-j best-flip rows.

## 5. What is NOT here

No Lean change yet (the follow-on slice lands g_3 as a named `CompactLogTest` and wires
field #4); GATE 1 mainline untouched; RH unclaimed. The multi-bump family and the
support-location direction remain separate future slices (they are F-B's escape routes).

## 6. Post-run addendum

**Verdict: F-A FIRED (field #4 holds at zero #2) - GOOD.**  The explicit pinned
detector g_3 gives `qw(g_3) < 0` <=> archimedeanTerm(g_3^box) > 0 numerically at
zero #2, with a DEEP sink and every gate green. RH remains unclaimed (numerical
pinning + sign measurement; the Lean route payment is the follow-on slice).

### 6.1 The result table (extended grid: cd in {1.30..1.80}, beta in {0.42,0.46,0.48,0.49})

j=2 wall/lever profile at mu* (the interior valley is now fully resolved):

```text
  cd      | 1.30   | 1.40   | 1.50   | 1.60   | 1.70   | 1.80
  beta=0.46| 1.052  | 0.786  | 0.662  | 0.639  | 0.708  | 0.884   <- min wall/lever
  flip     | +0.193 | -0.844 | -1.297 | -1.249 | -0.848 | -0.264    (sink depth)
```

- **min wall/lever = 0.633** at (cd=1.60, beta=0.49); rises to 1.052 on the low-cd
  side and 0.884 on the high-cd side => a clean INTERIOR valley, not an edge effect.
- **deepest sink = flip -1.331** at (cd=1.50, beta=0.49) = 34.4 percent of lever;
  margin 4.486, P 1.943, A -3.874, wall 2.543, lever 3.874 (all O(1), tail < 3e-16).
- Both O(1)-scale clauses pass on every flip row: wall AND lever >= e^{-2}.
- **j=3 control: no flip anywhere** in the extended grid (min wall/lever = 1.079 at
  cd=1.6) => selectivity preserved; single-detector reach of this family stays
  zeros #1 AND #2, not accidentally extended to #3 by a global rescaling.

### 6.2 Gates (all green, final authoritative log)

```text
  ANCHOR-A RESID = 1.655e-10   (identical to committed 1071 => imported verbatim)
  ANCHOR-B W_inf = -26.9858 < 0 (paper sign); inv-Fourier err <= 3e-16
  symmetry    rel = 1.22e-31   (<= 1e-25)
  triple-vanishing  g_3(0) = g_3(1/2) = g_3(1) = EXACTLY 0.0
  dictionary    f~3(0) = f~3(1) = exactly 0.0
  confirm-reduction  mu_3* + 2 arg(rho-1/2)/x == mu_1075*, resid = 0.0 (<= 1e-25)
  phase gate    xphase = +-pi exact on every mu* row; MU-INV rel < 1e-20
```

No error / traceback / FAIL in the log; zero cache (1272 zeros) reused, all cutoffs
inside, tails <= 6.2e-15.

### 6.3 What the completion did to the sink (why F-B's "sign-cost" worry was unfounded)

Killing s=1/2 with the symmetric factor (s-1/2)^2 does NOT merely preserve the flip;
it DEEPENS it sharply at zero #2:

```text
  family                      | min wall/lever @ j=2 | best sink % of lever
  {0,1}-killing (1075)        |      0.9850          |       ~1.5%   (thin)
  + (s-1/2)^2 = g_3 (this rec)|      0.633           |      ~34%     (deep)
```

Mechanism: the completion multiplies the off-line target term A by |(rho-1/2)^2| while
the on-line background is t^4-weighted; for zero #2 this raises |A| relative to the
wall so the negative cross-term overwhelms the background with room to spare.  The
price of adding a third vanishing node that F-B feared did not materialize in a single
symmetric completion factor - support-location / multi-bump freedom is still owed for
j>=3, but NOT (yet) for j=2.

### 6.4 Honest bookkeeping (two code fixes found by the run)

Run-1 used the section-3 pre-registered grids (cd to 1.40); it already fired F-A but
with two defects this addendum corrects in place, then re-ran on an extended grid:

1. `normalize_family3` dropped the |vf0| = q factor from the on-line peak magnitude,
   so every quantity was inflated ~q^2 (~1e5) and the e^{-2} clause passed vacuously.
   The flip SIGN and wall/lever ratio were unaffected (common scale => invariant), but
   the absolute O(1)-scale reading was not meaningful until fixed.  Now peak |g_3| = 1
   on-line and all values are genuine O(1) as tabulated above.
2. The `BEST` summary compared `fl < cur[1]` where the stored tuple is
   `(flip, cd, beta, ...)`, so it latched the LAST flip row instead of the most-negative;
   fixed to `cur[0]`.  Verdict never depended on this line (hand-written from raw rows).

The extended grid (cd to 1.80, beta to 0.49) was motivated by run-1's best sitting at the
cd=1.40 corner; it located the interior valley cleanly.  Section 3 is left untouched as
the pre-registration.

### 6.5 What this advances / what stays open

- ADVANCED (consumer #2 -> #3 for zero #2): hrootDetector's field-#4 sign clause is
  numerically satisfiable at zero #2 with a NAMED closed-form g_3 and an EMPTY visible-
  prime set on the root window [2^{-1/2}, 2^{1/2}].
- STILL OPEN: (i) land g_3 as a named `CompactLogTest` in Lean and wire field #4 into
  `HealthyYoshidaDetectorData` for zero #2 (the route-payment slice); (ii) j>=3 still
  needs multi-bump / support-location freedom; (iii) beta* = 0.49 sits near the on-line
  edge - a further narrow sweep past it is a cheap next step if one wants the absolute
  minimum sink, though F-A does not depend on it.
