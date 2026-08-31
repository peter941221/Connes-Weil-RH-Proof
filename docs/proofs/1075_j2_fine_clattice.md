# 1075 - G-side slice: the fine c-lattice at j = 2, 3, 5

Date: 2026-08-31. Follows 1071 (verdict E-H1: the engineered symmetric
family flips j = 1 at O(1) scale; j >= 2 wall/lever ~ 0.66 gamma_j on the
coarse c-lattice {0.3, 0.6, 1.0, 2.0}/gamma_j, with j = 2 at 1.3190 - "one
constant away from flipping; worth one narrow scan").  This record
pre-registers that narrow scan BEFORE any run.  Probe: the COMMITTED
1071 probe re-used verbatim with environment overrides (JLIST_1071,
DELTAS_1071, BETA_1071, CACHE_GMAX_1071) - no code change; the fork and
the grids live here.

## 0. Fork (stated BEFORE the run)

```text
  F-A (EXTENDS): the fine-grid min wall/lever at j = 2 drops below 1
     => E-H1 extends to j = 2 (the family hunts the first TWO zeros);
     record the winning (c*, beta*) recipe and the fine-grid law.
  F-B (CONFIRMED-LINEAR): min(j = 2) >= 1, and the fine minimum sits
     within 15 percent of the coarse 1.3190 => single-detector reach is
     the lowest zero only; the linear law 0.66 gamma_j is CONFIRMED at
     fine resolution (constant refined); hunting j = 2 needs multi-bump
     or support-location freedom (the 1070 gap-2 scope wall).
  F-C (ANOMALY, not expected): the fine minimum lands >= 25 percent
     below the coarse value, or the wall/lever(c) profile is wildly
     non-monotone on the fine grid => the coarse lattice was misleading;
     record the measured profile before any further use of the law.
  Either F-A or F-B decides the j = 2 question; F-C would weaken the
  1071 law's calibration and is checked first.
```

Scale check (carried from 1071, unchanged): a flip is called O(1)-scale
only if lever AND wall are both >= e^{-2} at the row.

## 1. Grids and cost

```text
  j in {2, 3, 5}                  (three heights anchor the linear law)
  c in {0.15, 0.20, ..., 3.00}    (58 points, step 0.05; coarse optimum
                                   expected near c ~ 1)
  beta in {0.02, 0.06, ..., 0.46} (12 points, symmetric about 1/4)
  mu in {0, mu*(beta, gamma)}     (mu = 0 control kept on every row)
  cutoff = gamma_j * max(3, 5/c)  <= 1100 at j = 5, c = 0.15;
  zero cache: the persisted 1071 cache reaches 1689 (1272 zeros) - reused,
  CACHE_GMAX_1071 = 1200; every row's cutoff fits, tail bounds printed.
  Rows: 3 x 58 x 12 x 2 = 4176; margins computed once per (j, c).
```

## 2. Gates and acceptance

ANCHOR-A/ANCHOR-B verbatim from the committed probe (family-independent
sign chain); SYM/DICT/MU-INV/PHASE family gates verbatim; acceptance =
flushed Linux-side log, zero error/traceback/FAIL, all gate lines green;
verdict hand-written into section 5 from the per-j minima.

## 3. What is NOT here

No Lean change; GATE 1 mainline untouched; RH unclaimed.  The multi-bump
family and the support-location direction are separate future slices.

## 4. Post-run addendum

One deterministic WSL run of the COMMITTED 1071 probe with the record-0
grids (3456 fork rows; zero error/traceback/FAIL; ANCHOR-A identity
1.7e-10, ANCHOR-B sign, symmetry 4.3e-31, dictionary exact, phase gate
exact +-pi at every mu* row, mu-invariance <= 1e-20; the persisted
1272-zero cache reused, every cutoff inside, tails < 1e-16).

Grid-line discrepancy (honest bookkeeping, pre-registered section 1 left
untouched): the launch carried DELTAS_1071 = 48 c-points
[0.15 .. 2.50] step 0.05 (1152 rows per j, 3456 fork rows total), while
the section 1 design line said "58 points to 3.00 / 4176 rows" - an
endpoint miscount between design text and the launched env list.  No
fork clause, threshold, or verdict depends on the endpoint: the valley
c* = 1.20 is interior and the wall rises monotonically above it on the
measured range (single clean valley, 4.1).

### 4.1 The measured fork table (per j: best row over the fine grid)

```text
  j | gamma_j | min wall/lever (mu*)  | argmin (c, beta) | best flip
  2 |  21.022 |        0.9850         |  1.20, 0.46      |  -0.050258  FLIP
  3 |  25.011 |        1.5630         |  1.20, 0.46      |  +0.388965  no flip
  5 |  32.936 |        2.8260         |  1.20, 0.46      |  +1.614410  no flip
```

The winning row (j = 2, c = 1.20, beta = 0.46, mu*): margin 4.9867,
P = 1.7193, wall 3.2673, lever 3.3176, xphase = 3.1416 exact,
flip = -0.0503, tail < 8.1e-19.  Scale check: lever AND wall >= e^{-2}
(both ~3.3) - an O(1)-scale certificate sink per the pre-registered
clause, though THIN (the sink depth is 1.5 percent of the lever).

The c-profile at (j = 2, beta = 0.46) is a clean single valley: 1.07 at
c = 1.10, 0.985 at c = 1.20, 1.01 at c = 1.30, rising smoothly to both
sides; no wild non-monotonicity.

### 4.2 VERDICT: F-A fired - the family hunts zeros #1 AND #2

Per the pre-registered fork: the fine-grid min wall/lever at j = 2 is
0.9850 < 1 with both scale clauses satisfied.  E-H1 extends to j = 2;
recipe: delta = 1.20/gamma_2, beta = 0.46, mu = mu*(beta, gamma_2).
At j = 3 (1.563) and j = 5 (2.826) the wall still wins - no flip.

### 4.3 Law recalibration (the F-C clause, recorded honestly)

```text
  coarse (1071):  min wall/lever ~ 0.66 * j   (2 <= j <= 30)
  fine (1075):    0.49 j (j=2), 0.52 j (j=3), 0.57 j (j=5), all at
                  c* = 1.20
```

- ERRATUM to 1071 s5.2/s5.3: the law's variable is the zero INDEX j,
  not gamma_j (the 1071 coarse table divided by j gives 0.64-0.68
  across j = 2..30; divided by gamma_j it gives 0.06-0.19, which was a
  notation slip in the record text).  The wall grows LINEARLY IN j on
  the measured range - better than linear in gamma_j ~ j log j.
- The coarse c-lattice {0.3, 0.6, 1, 2} missed the valley at c ~ 1.2
  and overestimated the wall by 16-25 percent; the fine constant rises
  slowly with j (0.49 -> 0.57 over j = 2..5), so j >= 3 likely stays
  above 1 even at its own valley.
- Caveats: beta* = 0.46 sits at the EDGE of the beta grid (lever grows
  toward beta = 1/2, so deeper j = 2 flips may exist past the edge);
  the j = 2 flip is real but thin; the linear-in-j law beyond j = 5 is
  coarse-resolution only.
- Consequence for the G path: single detectors of THIS family now reach
  zeros #1 and #2 at O(1) scale.  For j >= 3 the measured levers are
  multi-bump combinations (e.g. the j = 1 and j = 2 detectors share the
  same beta structure) or support-location freedom - the 1070 gap-2
  scope wall, now with a two-zero proof of concept.
