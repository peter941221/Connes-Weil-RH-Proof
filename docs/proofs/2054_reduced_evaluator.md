# 2054 — Route A link L2: the reduced-evaluator re-price at m = 1600

Verdict: **REDUCED-L2-GRAY** at the registered owner (one-copy G8-H,
ρ = 0.6 + 40.9187190121475i, scale 0.88, K = 30, support 9.504).  The
window node of the L2 architecture, re-priced on the m = 1600 object that
record 2053 registered, lands at

```
total = 7.564715e+11 (aggregate remainder, h = 0.001)
      + 1.307804e+07 (L1 nodal input)
      + 9.287269e+11 (archimedean projection)
      = 1.685212e+12  =  0.4948 x the re-based ideal budget (3.406050e+12)
                      =  4.948  x the 10% bar          (3.406050e+11)
```

so the window is NOT certified at the 10% bar, and IS priced inside the
budget — with the addend ranking turned over: the **archimedean projection
is now the leading term** (55.1% of the total; 2.73x the 10% bar by
itself), the aggregate remainder second (44.9%; 2.22x the bar), the nodal
input negligible (7.8e-06 of the total — rigor on that addend is free at
the reduced evaluator).  The comparison to the m = 400 era is the record's
structural content: the budget collapsed by 3.26e+07 (1.1112e+20 ->
3.4060e+12) while the charge collapsed by only 7.85e+05 (5.939e+17 ->
7.565e+11), so the same architecture's relative standing degrades from
0.0633x (record 2051/2052, on the committed m = 400 object) to 0.4948x on
the object a certificate actually needs.

Probe: `scripts/routea_reduced_evaluator_2054.py` (md5
`c1fe8db81ef005cf069efc4ccd0dc10d`, WSL ext4 mirror run, 676.0 s),
artifact `results/2054_reduced_evaluator.json` (md5
`8d26f110b84ad713087a5276d40167d9`).  The L4 kill of record 2053 is NOT
re-run and is NOT affected: those bounds describe the ideal object's own
full-line tail from landed Gevrey rungs, are evaluator-independent, and
stand (`T_bnd(40) = 6.515715e+41`).  This record prices the window node
only, exactly as records 2048-2052 did.

## 1. Frozen rules, controls, and anchors

Header-frozen rules (script lines 26-115, verbatim in substance):

- **Object (tier A)**: the committed 2037-class float pipeline with
  `xw1600_j = r59.phi_weights(a_j, panels = 6, m = 1600)` (9600
  nodes/family) and everything else committed — base/corr from
  `r37.setup` (eigh/min-h1 on the m = 400 nodal matrix), kernel, window
  [-40, 40].  Scope as 2051/2052: stored floats exact, L5 not touched.
- **Budget**: `BUDGET3 = |Q_1600| = 3.4060498718812666e+12` (the 2053
  frozen window value); `BAR10 = 0.1 BUDGET3`.
- **Verdict**: ANCHOR-FAIL if any gate misses; else REDUCED-L2-VIABLE iff
  total < BAR10, GRAY iff total < BUDGET3, FAIL otherwise.
- **Gates**: C1/C2 window controls vs the 2053 frozen values (rel <= 1e-6,
  sign negative); C3 setup cross-reads (families 17, book 1647, support
  9.504, C_book, C1_book, rel <= 1e-9; book identical at m = 400/1600);
  C4 span-parallel instrument equivalence (<= 1e-12, bitwise expected);
  C5 full-instrument m = 400 cross-read vs the 2051 frozen charges (rel
  <= 1e-9); C6 arch width_mean vs 569.087 (tol 2%); A1 pipeline
  (max |model g - committed g| <= 1e-9 gmax); A2a enclosure violations
  == 0; A3 bundle-vs-iv containment; A6 jet algebra selftest; B1 nodal
  containment (dps 40); B4 positivity; B5 forward-calculus selftest.
- **Re-scoped vs 2051/2052 (disclosed)**: A4 (agg <= L3) and A7 are
  REPORTED structure, not gates — at the reduced evaluator the L3-vs-agg
  ranking is data the verdict consumes.  A2b (commit-vs-model fd gap) is
  booked, not gated, as in 2051.

## 2. Controls read

```
+----+------------------------------------------------------------------+
| C1 | Q_400 = -1.1111757839943652e+20 vs frozen -1.1111757839943646e+20|
|    | rel 6.661e-16, sign_ok  -> PASS                                 |
| C2 | Q_1600 = -3406049871881.275 vs frozen -3406049871881.2666,       |
|    | rel 2.442e-15, sign_ok  -> PASS                                 |
| C3 | fam 17, book 1647, support 9.504, C_book 458.0475860314685,      |
|    | C1_book 21898.85724574201, 9600 nodes/fam, m400-identical        |
|    | -> PASS (exact)                                                 |
| C4 | worker-vs-parent 0.0, ParModel-vs-Model 0.0  -> PASS (bitwise)  |
| C5 | charge_L3 5.657706991143483e+18, charge_agg 2.7512365454404613e18|
|    | vs 2051 frozen: rel 0.000e+00 both  -> PASS (bitwise)           |
| C6 | width_mean 569.0867771360982 vs 569.087, rel 4.0e-07 -> PASS    |
+----+------------------------------------------------------------------+
```

C1/C2 reproduce both 2053-adjudicated window values at 1e-15 — the two
records are anchored to each other.  C5 is stronger than frozen-tolerance:
the m = 400 control row is **bitwise identical to the 2051 artifact on
every field**, not just the two charges — a1_abs_max 143360.0,
a2_violations 0 / worst 0.9987316442, a2_commit_violations 38 / worst
1.5227008444, a2_gap_charge 5096438.294695504, sum_U
1.235178868676494e+25, U/stencil 1.1096622445, tight median
12874481.75895616, p95 245367864.30337763 — the parallel/spanned
machinery, driven with run_rung's own outer chunk = 2048 at m = 400,
reproduces the 2051 sequential run exactly.  C4 extends that statement
to the m = 1600 path: worker-executed jets and the span-wrapped
`ParModel.g_jet` are bitwise identical to the in-parent sequential call
(0.0 on every component, including the K4 slot and all constant error
slots).  Span-batching at the jet chunk size is therefore a measured
no-op, not an assumption.

## 3. The window price at m = 1600

Fine grid: dxi = 0.00025, 320001 points, committed-pipeline gmax
`2.556148e+14` (the m = 400 counterpart is the alias-scale `3.790610e+19`
of 2051 — at m = 1600 the object has no alias mass).  Rungs
(`chunk = whole rung`, jets span-parallel at 4096):

```
+--------+----------+----------------+----------------+---------+----------------+---------+
| h      | panels   | charge_L3      | charge_agg     | agg/L3  | sum U          | U/st    |
+--------+----------+----------------+----------------+---------+----------------+---------+
| 0.01   |   8000   | 4.835546e+14   | 3.837446e+14   | 0.7936  | 8.445491e+18   | 2.6347  |
| 0.005  |  16000   | 5.570126e+13   | 3.318516e+13   | 0.5958  | 7.782773e+18   | 1.3045  |
| 0.002  |  40000   | 6.904699e+12   | 3.418537e+12   | 0.4951  | 1.507419e+19   | 1.0635  |
| 0.001  |  80000   | 1.633533e+12   | 7.564715e+11   | 0.4631  | 2.853036e+19   | 1.0250  |
+--------+----------+----------------+----------------+---------+----------------+---------+
```

The aggregate beats the crude L3 enclosure at every rung (agg/L3 falls
0.79 -> 0.46), and the best rung is h = 0.001 with
`min(L3, agg) = 7.564715e+11 = 0.2221 BUDGET3`.  Enclosure validity holds
everywhere: A2a violations 0 (worst sampled ratio 0.962 / 0.991 / 0.999 /
0.9997 — the bound sits at its own ceiling, as designed); A2b booked gap
charges 0 / 0 / 5.096e+06 / 5.841e+05 (four and ten panels of fd-stencil
excess, booked, four orders below the total); A1 `max |model g - committed
g|` = 3.125 (3.125, 3.125, 4.0 by rung) against the gate `1e-9 gmax =
2.556e+05` — node-representation-level agreement with ~4.8 orders of
margin.  The enclosure tightness `U/stencil` converges to 1.025 at
h = 0.001: at the reduced evaluator the certified sup|g''| is essentially
the measured stencil wherever mass lives.

## 4. The addends

**L1 nodal (2052 calculus at m = 1600)**, h* = 0.001, 80001 nodes:
Coef1 23323.213147 (sum-of-nodes rel 1.0e-15), C_max 2.556148e+14,
e_g max 71791.79, e_g median 3.937e-19, charge_nodal 1.307178e+07,
echo 6259.85, charge_L1 1.307804e+07 = 1.9e-06 of the 2051 L1 charge
(1.884216e+13).  B1 containment 7/7 on the frozen pick set including the
2053-measured mass-hump maximum at xi = -7.03 (C = g_exact =
2.3619265336460666e+14, abs_diff 0.0, e_g 54551.7) and xi = -6.68
(worst ratio 2.274e-05).  Rigor on the nodal input costs 7.8e-06 of the
verdict total.

**Archimedean projection**, rebuilt at m = 1600 with the 2048 A1
convention verbatim (0.05 panels, iv.dps 20, w_arch = widths of
`r43.sigma_arch_iv`): width_mean 569.0867771360982 (C6 pass), gmax on the
anchor grid 2.555399e+14, `arch_proj = 9.287269e+11`.  This is the
verdict's leading term.  It is also the term that scaled worst: 2051-era
arch 3.917065e+16 -> 9.287269e+11 is a 4.22e+04 collapse, against the
budget's 3.26e+07 — panel refinement cannot move it (the interval width
of sigma over a panel is `~ |sigma'| dxi`, so the projection is a fixed
functional `int |sigma'| |g|` up to method constants); reaching the bar
requires a better archimedean pricing, not a finer grid.

**Tier-B diagnostic** (base/corr re-solved on the m = 1600 nodal matrix,
`a_mat1600`): d_base 2.151e-09, d_corr 2.481e-09 relative; Q_1600 moves
from -3406049871881.275 to -3406049837242.479, shift 1.017e-08 relative
= |dQ| ~ 3.5e+04 absolute — four orders below BAR10.  Reading: the
eigh/min-h1 + nodal-matrix component of L5, the part this diagnostic
touches, is NOT a binding obstacle at this owner (not an enclosure; a
diagnostic).

**A7 structure** (48 panels, h = 0.002, reported): loss_vs_crude median
115.7 (mass-carrying 2.686), rigorous_over_measured median 3.46e+07
(mass-carrying 1.340, max 1.377), recovered factor 2.00,
worst_k_measured_over_bound 0.645.  The 2048-era cancellation blindness
(57.47x headline) does not appear at the reduced evaluator: every sampled
panel's measured remainder stays below the crude bound (<= 0.645), and on
mass-carrying panels the rigorous aggregate charge is only 1.34x the
measured remainder — close to 2051's m = 400 reading (1.317x).

**B3** (ladder node vs nearest fine-grid coordinate): max abs diff 0.0 —
at h = 0.001 the ladder nodes lie exactly on the 0.00025 grid and the
committed path is bitwise-reproducible across the two evaluations.

## 5. Assembly

```
+---------------------------+----------------+------------+-----------+
| addend                    | value          | / BUDGET3  | / BAR10   |
+---------------------------+----------------+------------+-----------+
| aggregate remainder (L2)  | 7.564715e+11   | 0.2221     | 2.221     |
| L1 nodal (2052 calculus)  | 1.307804e+07   | 3.84e-06   | 3.84e-05  |
| archimedean projection    | 9.287269e+11   | 0.2727     | 2.727     |
+---------------------------+----------------+------------+-----------+
| total                     | 1.685212e+12   | 0.4948     | 4.948     |
+---------------------------+----------------+------------+-----------+
```

All 13 gates pass; verdict REDUCED-L2-GRAY by the frozen rules.  The
2051/2052 claim (`6.330553e+17 = 0.0633x` of 1e19 on the committed m = 400
DAG) stands untouched as a claim about that DAG; on the object a
certificate actually targets, the same architecture now reads 0.4948x.
The 2053-registered follow-up (re-run the chain at m = 1600) is hereby
read and closed.

## 6. Consequence and next items

- To reach BAR10 from here the total must fall 4.948x.  The two live
  levers are the archimedean pricing (2.727x the bar alone; needs a
  method change, not a grid change) and the aggregate remainder (2.221x
  the bar; the 2051-era lever was the aggregate split, already applied;
  remaining slack is the enclosure constant C_book-class overhead at the
  mass-free panels, where U/stencil ~ 2.6e+06 at h = 0.01 and the
  tightness only converges where mass lives).
- The L4 kill of 2053 bounds the ideal object's own tail and is NOT
  relieved by anything here: even a VIABLE window node leaves the
  full-line certificate dead until an L4-class rescue lands.
- The tier-B reading promotes the L5 eigh/min-h1 component from "unknown"
  to "measured at ~3.5e+04 absolute": whoever prices L5 next should
  expect the eigh/min-h1 part to be cheap at this owner and look for the
  binding part elsewhere (F construction, phi rule residual, sigma).

## 7. Incident chain (all instrument; no physics adjudicated)

Four defects were caught pre-verdict, in order:

1. C4's comparator assumed the jet container was a `(real, imag)` pair;
   `g_jet` returns a REAL jet `[c0, c1, c2, c3, K4]` with slots 0-3
   bundles and slot 4 a bare array.  Caught as an IndexError in the first
   smoke; both the comparator and the span-concat were fixed with a
   slot-type-aware flattener.  The same class of indexing ambiguity as
   the 2051 K4-slot incident — the container convention is now written
   into both helpers.
2. `controls_c4` was defined but never called (the gate would have read
   False forever); caught in pre-sync self-review.
3. `pmap` was missing its pooled branch (returned None under a live
   pool); caught as a numpy dispatcher TypeError in smoke run 3.  The
   parallel jet path had masked it by calling `_POOL.map` directly.
4. The smoke ladder/dxi pair was inconsistent (h = 0.002 with
   dxi = 0.0025 -> step = 1 stencil reshaping); caught as a reshape
   ValueError in smoke run 3.  Smoke now uses h = 0.02 with
   dxi = 0.002 (step 10).

Determinism evidence beyond the gates: smoke and full runs produce
identical C1/C2 (rel 6.661e-16 / 2.442e-15), identical tier-B readings,
identical C4 zeroes; C5 ties the plumbing to the 2051 artifact bitwise.
No verdict-affecting nondeterminism was observed.

## 8. Scope and nonclaims

- L5 (F construction, phi quadrature, eigh/min-h1, sigma) remains
  registered, not touched: the bound starts from the stored floats as
  exact; the tier-B reading is a diagnostic, not an enclosure.
- L4 (full-line tail) separate and standing (2053).
- The echo term is the disclosed 2052 proxy at 1e-15 of the nodal max.
- The m = 1600 rule's own residual error (2053: m = 6400 cross-read rel
  4.3e-12) is not charged.
- The verdict is about the window node of this architecture at this
  owner; it is not a producer theorem and not RH.