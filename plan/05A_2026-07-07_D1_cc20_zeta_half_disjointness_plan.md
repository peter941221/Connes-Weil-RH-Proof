# 05A D1 CC20 Zeta-Half Disjointness Plan

Date: 2026-07-07

Status:
  Single canonical 05A document.  Do not create or update separate `05A1`,
  `05A2`, `05A3`, or `05A4` plan files.  Add every 05A tree split, execution
  note, rejection, and acceptance gate here.


## 1. Result First

Current result:
  Partial-good.  Lean now proves both the full unshifted half-period `cosZeta`
  power-series Abel limit to the ordered eta value:

    Source.tendsto_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt_ordered

  and the lower ordered-real eta continuity / safe-domain agreement bricks:

    Source.tendsto_orderedEtaValue_sigma_nhdsGT_half
    Source.dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_one_lt

  This is not 05A closure.  The remaining theorem is still the half-point
  analytic-continuation identification:

    HurwitzZeta.cosZeta (ZMod.toAddCircle (1 : ZMod 2)) (1 / 2 : C)
      =
    -(dirichletEtaRealHalfOrdered : C)

  Equivalently:

    dirichletEtaAnalytic (1 / 2 : C) =
      (dirichletEtaRealHalfOrdered : C)

  The safe-domain theorem proves equality only for real `sigma > 1`; it does
  not by itself transport the identity through the critical strip to
  `sigma = 1 / 2`.

Hard completion gate:

```text
Good:
  05A is shard-good only.  It does not close Plan 05 or
  `normalizedCoreCC20RHExitObjectPackageFromTheorems` until 05D and 05E also
  pass their own gates.

  Lean proves, without `sorryAx` or project-local axioms:

    Source.riemannZeta_half_ne_zero :
      riemannZeta (1 / 2 : C) != 0

    Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros :
      SourceFiniteSetDisjointFromNontrivialZeros
        RHDefinitionBridge.standard
        cc20TripleFiniteVanishingSet

Partial:
  Lean proves only conditional infrastructure, for example:

    Tendsto ... (-HurwitzZeta.cosZeta ... (1 / 2 : C)) ->
    Source.RiemannZetaHalfNonvanishing

Rejected:
  The proof introduces or consumes `sorry`, `admit`, `axiom`, `constant`,
  `opaque`, `unsafe`, an accepted-source theorem, a raw field, `True`,
  `Set.univ`, or a renamed theorem that states the target.

  The proof uses unordered `tsum`, `Summable`, `HasSum`, `LSeries`, or
  `dirichletEtaComplex (1 / 2)` as the active half-point owner.
```


## 2. One-Document Rule

Keep 05A documentation in this file.

```text
Allowed:
  plan/05A_2026-07-07_D1_cc20_zeta_half_disjointness_plan.md

Removed / do not recreate:
  plan/05A1_2026-07-07_D1_dirichlet_eta_base_layer_plan.md
  plan/05A2_2026-07-07_D1_eta_zeta_identity_plan.md
  plan/05A3_2026-07-07_D1_eta_half_positivity_plan.md
  plan/05A4_2026-07-07_D1_zeta_half_to_cc20_disjointness_plan.md
```

Reason:
  05A now has one active mathematical blocker.  Separate subplan files made the
  state look wider than the proof tree.  One file keeps the hard gate, the
  current tree, and the rejected routes in the same place.


## 3. File Ownership

Allowed Lean files for 05A:

```text
ConnesWeilRH/Source/DirichletEta.lean
ConnesWeilRH/Source/ZetaHalfNonvanishing.lean
ConnesWeilRH/Source/CC20RHExit.lean
```

`CC20RHExit.lean` may be edited only after the final unconditional disjointness
theorem exists and needs export from the CC20 RH-exit surface.

Do not edit from this lane:

```text
ConnesWeilRH/Source/CC20TestSpace.lean
ConnesWeilRH/Source/CC20YoshidaCriterion.lean
ConnesWeilRH/Source/CC20PropositionC1.lean
ConnesWeilRH/Dev/UnconditionalSkeleton.lean
ConnesWeilRH/Route/*.lean
```


## 4. Current Proof Tree

```text
05A shard-good
|
+-- final theorem:
|     Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros
|   |
|   +-- blocked until:
|       Source.riemannZeta_half_ne_zero
|
+-- Source.riemannZeta_half_ne_zero
    |
    +-- ordered eta owner
    |   |
    |   +-- done:
    |       etaHalfTerm
    |       etaHalfPartialSum
    |       dirichletEtaRealHalfOrdered
    |       dirichletEtaRealHalfOrdered_tendsto
    |
    +-- ordered eta positivity
    |   |
    |   +-- done:
    |       etaHalfTerm_nonneg
    |       etaHalfTerm_antitone
    |       etaHalfTerm_tendsto_zero
    |       dirichletEtaRealHalfOrdered_lower_bound
    |       dirichletEtaRealHalfOrdered_pos
    |
    +-- eta/zeta factor identity at s = 1/2
    |   |
    |   +-- done:
    |   |   dirichletEtaAnalytic_eq_factor_mul_riemannZeta_of_one_lt_re
    |   |   dirichletEtaAnalytic_eq_etaZetaFactorMul_riemannZeta_update
    |   |   dirichletEtaAnalytic_half_eq_factor_mul_riemannZeta
    |   |
    |   +-- still missing:
    |       dirichletEtaAnalytic (1 / 2 : C) =
    |         (dirichletEtaRealHalfOrdered : C)
    |
    +-- route-facing conditional bridge
        |
        +-- done:
            riemannZeta_half_ne_zero_of_dirichletEtaAnalytic_half_eq_ordered
            cc20_triple_disjoint_of_dirichletEtaAnalytic_half_eq_ordered
            dirichletEtaRealHalfOrdered_eq_factor_mul_riemannZeta_half_of_cosZeta_abel
            riemannZeta_half_ne_zero_of_neg_cosZeta_half_period_abel_limit
            cc20_triple_disjoint_of_neg_cosZeta_half_period_abel_limit
```


## 5. Active Hard Leaf

The first open leaf is the half-period `cosZeta` Abel-boundary theorem:

```lean
theorem tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries :
    Tendsto
      (fun x : R =>
        ((sum' n, ((-1 : R) ^ n * etaHalfTerm n) * x ^ n : R) : C))
      (nhdsWithin 1 (Iio 1))
      (nhds
        (-HurwitzZeta.cosZeta (ZMod.toAddCircle (1 : ZMod 2))
          (1 / 2 : C)))
```

Once Lean proves that theorem, the remaining 05A chain is mechanical:

```text
tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries
|
+-- dirichletEtaAnalytic_half_eq_ordered
|   |
|   +-- by uniqueness of limits:
|       tendsto_etaHalfPowerSeries_complex_nhdsWithin_lt
|       same Abel limit to `-cosZeta`
|
+-- dirichletEtaRealHalfOrdered_eq_factor_mul_riemannZeta_half
|   |
|   +-- combine with:
|       dirichletEtaAnalytic_half_eq_factor_mul_riemannZeta
|
+-- riemannZeta_half_ne_zero
|   |
|   +-- contradiction:
|       eta ordered value is positive but factor * zeta would be zero
|
+-- cc20_triple_disjoint_from_standard_source_nontrivial_zeros
    |
    +-- apply the existing conditional CC20 bridge
```


## 6. Why the Current Leaf Is Correct

The analytic eta owner is:

```lean
noncomputable def dirichletEtaAnalytic (s : C) : C :=
  ZMod.LFunction etaZModTwoCoeff s
```

The ordered half-point owner is:

```lean
noncomputable def dirichletEtaRealHalfOrdered : R :=
  Classical.choose etaHalfTerm_alternating_tendsto
```

The proof already has both sides of the intended limit comparison:

```text
ordered side:
  tendsto_etaHalfPowerSeries_complex_nhdsWithin_lt
    proves the Abel power series tends to
    `(dirichletEtaRealHalfOrdered : C)`.

analytic side:
  dirichletEtaAnalytic_half_eq_neg_cosZeta_half
    rewrites the analytic eta value at `1 / 2` as
    `-HurwitzZeta.cosZeta (ZMod.toAddCircle 1) (1 / 2)`.
```

The missing theorem must identify that analytic `cosZeta` value with the same
Abel boundary.  Proving another safe-domain identity or another wrapper around
`RiemannZetaHalfNonvanishing` does not move this leaf.

Current 05A-D refinement:

```text
05A-D. Ordered Abel boundary at the half point
|
+-- done: mod-2 eta coefficient matches the ordered eta sign
|     etaZModTwoCoeff_natCast_succ_eq_neg_one_pow
|
+-- done: mod-2 LSeries item at n+1 matches the ordered eta term
|     lseries_etaZModTwoCoeff_half_term_nat_succ_eq_etaHalfCoeff
|
+-- done: half-period cosZeta LSeries item at n+1, after negation,
|         matches the ordered eta term
|     neg_lseries_cosZeta_half_period_term_nat_succ_eq_etaHalfCoeff
|
+-- done: ordered eta power series is the negative shifted half-period
|         cosZeta LSeries-term power series
|     etaHalfPowerSeries_eq_neg_lseries_cosZeta_half_period_powerSeries
|
+-- done: the shifted LSeries-term Abel boundary implies the original
|         05A-D open theorem
|     tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries_of_lseries_term_abel
|
+-- done: shifted series equals negative full series divided by x
|     neg_shifted_lseries_cosZeta_half_period_powerSeries_eq_neg_full_div
|
+-- done: the full unshifted series is eventually summable near x = 1
|         from the left
|     norm_lseries_cosZeta_half_period_term_le_one
|     summable_lseries_cosZeta_half_period_powerSeries_of_norm_lt_one
|     eventually_summable_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt
|
+-- done: full unshifted Abel boundary implies the shifted Abel boundary
|     tendsto_neg_shifted_lseries_cosZeta_half_period_abel_of_full_lseries_term_abel
|
+-- done: full unshifted half-period LSeries-term Abel boundary to the
|         ordered eta value
|     tendsto_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt_ordered
|
+-- still open: identify the Mathlib analytic `cosZeta` value with that
|         ordered Abel boundary
      |
      +-- open analytic leaf:
          HurwitzZeta.cosZeta
              (ZMod.toAddCircle (1 : ZMod 2))
              (1 / 2 : C)
            =
          -(dirichletEtaRealHalfOrdered : C)

+-- final theorem after the shifted socket is proved:
      tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries
```

Why this matters:
  The remaining blocker is no longer an indexing or coefficient problem.  Lean
  now knows that the `ZMod 2` eta coefficient and the half-period `cosZeta`
  Dirichlet item both reduce to the same ordered eta coefficient after the
  `n + 1` reindexing.  Lean also knows that the ordered eta power series is
  exactly the negative shifted `cosZeta` item power series, proves the nearby
  summability needed for the quotient/reindex bridge, and proves the full
  unshifted `cosZeta` power series tends to `-dirichletEtaRealHalfOrdered`.
  The only missing mathematical content is the theorem that identifies the
  analytic `cosZeta` continuation value at `s = 1 / 2` with that same ordered
  Abel boundary.


## 6A. Direction And Tactic Decision

Direction:
  Keep 05A on the `cosZeta` Abel-boundary route.  Do not switch back to
  unordered `LSeries`, `tsum`, or `dirichletEtaComplex` at `1 / 2`.

Tactic adjustment:
  Stop splitting 05A into separate plan documents.  Split the proof tree inside
  this file only.

Current best attack:

```text
05A-D current attack
|
+-- done:
|     eventual summability for the full unshifted `cosZeta` term power series
|     on a left neighborhood of x = 1
|
+-- done:
|     Abel boundary for the full unshifted half-period `cosZeta` term series
|     to `-dirichletEtaRealHalfOrdered`
|
+-- current target:
|     identify the Mathlib analytic `cosZeta` value at s = 1 / 2 with
|     `-dirichletEtaRealHalfOrdered`
|
+-- then:
      use the checked quotient/reindex bridge
      -> shifted socket
      -> ordered eta Abel socket
      -> zeta-half nonvanishing
      -> CC20 triple disjointness
```

Why this is the right adjustment:
  The coefficient and shift work is already checked in Lean.  More wrappers or
  more document files would only rename the same blocker.  The proof now has
  two different obligations:

```text
support / convergence leaf:
  done.
  Lean bounds each half-period `cosZeta` LSeries term by 1, then compares the
  powered series with the real geometric series `|x|^m` on `0 < x < 1`.

analytic-continuation leaf:
  the real hard theorem.
  It must identify `HurwitzZeta.cosZeta (ZMod.toAddCircle 1) (1 / 2 : C)`
  with the already-proved ordered Abel boundary
  `-(dirichletEtaRealHalfOrdered : C)`.
```

Acceptance rule for the next pass:
  If the analytic-continuation leaf has no current Mathlib owner, record that
  exact theorem as the first non-Mathlib black box in this file.  Do not
  replace it with a theorem over unordered half-point summation.


## 6B. Closed-Leaf Audit After Route Review

2026-07-07 route review result:
  Bad for full closure.  05A remains open.

The proof tree has now been narrowed to one live mathematical edge:

```text
05A target:
  Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros
  |
  +-- needs:
      Source.riemannZeta_half_ne_zero
      |
      +-- already reduced to:
          dirichletEtaAnalytic (1 / 2 : C)
            =
          (dirichletEtaRealHalfOrdered : C)
          |
          +-- analytic side:
          |     done:
          |       dirichletEtaAnalytic_half_eq_neg_cosZeta_half
          |     meaning:
          |       analytic eta at 1/2 is `-cosZeta` at the half period
          |
          +-- ordered side:
          |     done:
          |       tendsto_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt_ordered
          |     meaning:
          |       the full unshifted half-period item power series tends to
          |       `-(dirichletEtaRealHalfOrdered : C)`
          |
          +-- only open edge:
                HurwitzZeta.cosZeta
                    (ZMod.toAddCircle (1 : ZMod 2))
                    (1 / 2 : C)
                  =
                -(dirichletEtaRealHalfOrdered : C)
```

Equivalently, the remaining edge is:

```text
Mathlib analytic continuation value
  =
ordered Abel boundary of the same half-period Dirichlet items.
```

What is now ruled out as closure:

```text
CC20 outlet route
  rejected as closure:
    The active finite set has three points.  The existing proof already removes
    0 by `riemannZeta_zero` and 1 by the standard no-pole row.  The 1/2 point
    still needs `riemannZeta (1 / 2 : C) != 0`.

  evidence:
    ConnesWeilRH/Source/ZetaHalfNonvanishing.lean:
      cc20_triple_disjoint_from_standard_source_nontrivial_zeros_of_zeta_half_ne_zero

Mathlib `cosZeta` safe-domain route
  rejected as closure:
    Mathlib proves the Dirichlet-series identity only for `1 < re s`.
    It does not supply the half-point Abel-boundary theorem.

  evidence:
    .lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:
      hasSum_nat_cosZeta
      LSeriesHasSum_cos

ZMod function-equation route
  rejected as closure by itself:
    `ZMod.LFunction_one_sub` and completed-function equations rewrite analytic
    continuation objects.  They do not identify the radial Abel limit from
    `x < 1` with the value at `s = 1 / 2`.

  evidence:
    .lake/packages/mathlib/Mathlib/NumberTheory/LSeries/ZMod.lean:
      LFunction_one_sub
      completedLFunction_one_sub_even
      completedLFunction_one_sub_odd
```

The next non-wrapper theorem must therefore be one of these exact shapes:

```lean
theorem cosZeta_half_period_eq_neg_dirichletEtaRealHalfOrdered :
    HurwitzZeta.cosZeta
        (ZMod.toAddCircle (1 : ZMod 2))
        (1 / 2 : C)
      =
    -(dirichletEtaRealHalfOrdered : C)

theorem dirichletEtaAnalytic_half_eq_ordered :
    dirichletEtaAnalytic (1 / 2 : C) =
      (dirichletEtaRealHalfOrdered : C)
```

Accepted proof shape:

```text
lower analytic theorem
  -> half-period `cosZeta` Abel boundary at s = 1/2
  -> `dirichletEtaAnalytic_half_eq_ordered`
  -> `dirichletEtaRealHalfOrdered_eq_factor_mul_riemannZeta_half`
  -> `riemannZeta_half_ne_zero`
  -> `cc20_triple_disjoint_from_standard_source_nontrivial_zeros`
```

Rejected proof shape:

```text
conditional theorem
  -> same condition restated under a new name
  -> final theorem
```

This is a wrapper and does not close 05A.


## 6C. Next Lower Split: Ordered Eta Continuity Route

2026-07-07 lower-route search result:
  The direct Mathlib search did not find a theorem identifying the half-period
  `cosZeta` analytic value with the ordered Abel boundary.  The next viable
  non-wrapper route is to build the missing theorem below the eta side, not by
  adding another route-facing condition.

New split:

```text
cosZeta half-period equality
|
+-- already done:
|     dirichletEtaAnalytic (1 / 2)
|       =
|     -cosZeta half-period value
|
+-- enough to prove:
      dirichletEtaAnalytic (1 / 2)
        =
      orderedEtaValue (1 / 2)
      |
      +-- define or expose ordered eta for 0 < sigma:
      |     orderedEtaValue sigma =
      |       limit_N sum_{n < N} (-1)^n / (n+1)^sigma
      |
      +-- prove safe-domain agreement:
      |     for 1 < sigma:
      |       dirichletEtaAnalytic sigma =
      |       orderedEtaValue sigma
      |
      +-- prove right-half-plane continuity:
      |     orderedEtaValue sigma -> orderedEtaValue (1 / 2)
      |     as sigma -> 1/2, sigma > 0
      |
      +-- use analytic / continuity uniqueness:
            dirichletEtaAnalytic is continuous at 1/2
            and agrees with orderedEtaValue on a set accumulating at 1/2
```

Why this is lower than the current blocker:

```text
current blocker:
  Mathlib analytic `cosZeta` value = ordered Abel boundary

lower eta route:
  ZMod analytic eta value = ordered eta value
  then use the already-proved
  dirichletEtaAnalytic_half_eq_neg_cosZeta_half
```

Lean bricks found:

```text
Mathlib.Analysis.SpecificLimits.Normed:
  Antitone.tendsto_alternating_series_of_tendsto_zero
  Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded
  norm_sum_neg_one_pow_le

Mathlib.Analysis.Normed.Group.Tannery:
  tendsto_tsum_of_dominated_convergence

Mathlib.Analysis.Normed.Group.FunctionSeries:
  continuous_tsum
  continuousOn_tsum

Mathlib.NumberTheory.LSeries.ZMod:
  ZMod.LFunction_eq_LSeries
  ZMod.differentiable_LFunction_of_sum_zero

ConnesWeilRH/Source/DirichletEta.lean:
  dirichletEtaAnalytic_eq_LSeries_of_one_lt_re
  dirichletEtaAnalytic_half_eq_neg_cosZeta_half
  dirichletEtaRealHalfOrdered_tendsto
```

Important rejection inside this split:

```text
Do not use `continuous_tsum` / `continuousOn_tsum` as the half-point proof
unless the bound is genuinely summable and does not assert absolute
convergence of the half-point eta series.

Reason:
  `continuous_tsum` is an M-test API.  A direct bound around `sigma = 1/2`
  would need a summable majorant for `(n+1)^(-sigma)`, which is false near
  sigma = 1/2.  Using it directly would smuggle in the rejected absolute
  summability route.
```

Accepted proof shape for this split:

```text
uniform Dirichlet / alternating estimate on a right-neighborhood of 1/2
  -> ordered partial sums converge uniformly to orderedEtaValue
  -> orderedEtaValue is continuous at 1/2
  -> agreement with `dirichletEtaAnalytic` on `1 < sigma`
  -> extend the equality to the connected positive real half-line / half-plane
  -> specialize at 1/2
```

Smaller first theorem to attempt:

```lean
theorem tendsto_orderedEtaValue_sigma_nhdsWithin_half :
    Tendsto
      (fun sigma : R => orderedEtaValue sigma)
      (nhdsWithin (1 / 2 : R) (Ioi 0))
      (nhds dirichletEtaRealHalfOrdered)
```

If this theorem cannot be formalized without a new owner, introduce the owner
as real ordered partial-sum data, not as a theorem field stating the target.


## 7. Rejected Routes

Rejected half-point owner:

```text
dirichletEtaReal (1 / 2)
dirichletEtaComplex (1 / 2)
any theorem whose active proof treats the half-point eta series as unordered
`tsum`
```

Reason:
  The eta half-point alternating series is conditionally convergent.  Mathlib's
  `tsum` API over `Nat` is the unordered finite-set summation API.  The
  accepted owner is the ordered partial-sum limit
  `dirichletEtaRealHalfOrdered`.

Rejected `LSeries` route:

```text
LSeries etaZModTwoCoeff (1 / 2)
LSeriesSummable etaZModTwoCoeff (1 / 2)
Mathlib.NumberTheory.LSeries.SumCoeff as a direct half-point close
```

Evidence:

```text
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/Basic.lean
  LSeries f s := tsum (term f s)
  LSeriesSummable f s := Summable (term f s)
```

Rejected function-equation-only route:

```text
HurwitzZeta.cosZeta_one_sub
HurwitzZeta.expZeta_one_sub
```

Reason:
  These theorems rewrite analytic-continuation objects.  They do not by
  themselves prove the ordered Abel boundary:

```text
Abel power series from x < 1
  =
-cosZeta half-period value at s = 1/2
```


## 8. Work Breakdown Inside This File

Use these labels for future notes.  Do not create separate files for them.

```text
05A-A. Ordered eta owner
  Status: done.
  Output:
    dirichletEtaRealHalfOrdered
    dirichletEtaRealHalfOrdered_tendsto

05A-B. Ordered eta positivity
  Status: done.
  Output:
    dirichletEtaRealHalfOrdered_pos

05A-C. Analytic eta owner and safe-domain eta-zeta identity
  Status: done.
  Output:
    dirichletEtaAnalytic
    dirichletEtaAnalytic_eq_factor_mul_riemannZeta_of_one_lt_re
    dirichletEtaAnalytic_eq_etaZetaFactorMul_riemannZeta_update
    dirichletEtaAnalytic_half_eq_factor_mul_riemannZeta

05A-D. Ordered Abel boundary at the half point
  Status: partial-good; the item-level coefficient bridges, local summability
  leaf, quotient/reindex bridge, full unshifted Abel boundary to the ordered
  eta value, ordered-real right-continuity, and safe-domain agreement for
  real `sigma > 1` are done.  The Mathlib analytic-continuation value
  identification at `sigma = 1 / 2` remains open.
  New output:
    etaZModTwoCoeff_natCast_succ_eq_neg_one_pow
    lseries_etaZModTwoCoeff_half_term_nat_succ_eq_etaHalfCoeff
    neg_lseries_cosZeta_half_period_term_nat_succ_eq_etaHalfCoeff
    etaHalfPowerSeries_eq_neg_lseries_cosZeta_half_period_powerSeries
    tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries_of_lseries_term_abel
    neg_shifted_lseries_cosZeta_half_period_powerSeries_eq_neg_full_div
    norm_lseries_cosZeta_half_period_term_le_one
    summable_lseries_cosZeta_half_period_powerSeries_of_norm_lt_one
    eventually_summable_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt
    tendsto_neg_shifted_lseries_cosZeta_half_period_abel_of_full_lseries_term_abel
    tendsto_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt_ordered
    cosZeta_half_period_eq_neg_dirichletEtaRealHalfOrdered_of_full_lseries_abel_limit
    dirichletEtaAnalytic_half_eq_ordered_of_full_lseries_cosZeta_half_period_abel_limit
    orderedEtaValue_sub_etaSigmaPartialSum_abs_le
    orderedEtaValue_half_eq_dirichletEtaRealHalfOrdered
    tendsto_orderedEtaValue_sigma_nhdsGT_half
    orderedEtaValue_eq_tsum_of_summable
    summable_etaSigmaCoeff_of_one_lt
    lseries_etaZModTwoCoeff_ofReal_term_nat_succ_eq_etaSigmaCoeff
    dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_one_lt
  First open theorem:
    HurwitzZeta.cosZeta (ZMod.toAddCircle 1) (1 / 2 : C)
      =
    -(dirichletEtaRealHalfOrdered : C)

05A-E. Zeta-half nonvanishing and CC20 disjointness
  Status: conditional-good.
  Output:
    riemannZeta_half_ne_zero_of_neg_cosZeta_half_period_abel_limit
    cc20_triple_disjoint_of_neg_cosZeta_half_period_abel_limit
    riemannZeta_half_ne_zero_of_full_lseries_cosZeta_half_period_abel_limit
    cc20_triple_disjoint_of_full_lseries_cosZeta_half_period_abel_limit
```


## 8A. 2026-07-07 Full-Series Socket Execution

Result:
  Partial-good only.  05A is still open.

What changed:
  Lean now has the shortest checked conditional route from the full unshifted
  half-period `cosZeta` Abel boundary to the ordered eta identity:

```text
full half-period cosZeta Abel boundary to analytic cosZeta value
  -> cosZeta_half_period_eq_neg_dirichletEtaRealHalfOrdered_of_full_lseries_abel_limit
  -> dirichletEtaAnalytic_half_eq_ordered_of_full_lseries_cosZeta_half_period_abel_limit
  -> riemannZeta_half_ne_zero_of_full_lseries_cosZeta_half_period_abel_limit
  -> cc20_triple_disjoint_of_full_lseries_cosZeta_half_period_abel_limit
```

Why this matters:
  The earlier shifted socket is still valid, but it is no longer the fastest
  route-facing chain once the full Abel boundary is available.  The active
  blocker is now exactly the theorem that the full half-period `cosZeta` term
  power series tends to Mathlib's analytic `cosZeta` value at `s = 1 / 2`.

Rejected as closure:
  This execution does not prove the full Abel boundary theorem.  It only proves
  the downstream route from that theorem to 05A's zeta-half nonvanishing and
  CC20 triple disjointness sockets.

Verification:
  WSL Ubuntu-24.04 main ext4 mirror, under `/tmp/connes-weil-rh-lake.lock`:

```text
lake build ConnesWeilRH.Source.DirichletEta ConnesWeilRH.Source.ZetaHalfNonvanishing
```

  Result: pass.

  Focused import-facing axiom audit for the two new DirichletEta declarations
  and the two full-series ZetaHalfNonvanishing consumers returned:

```text
[propext, Classical.choice, Quot.sound]
```

Remaining hard leaf:

```lean
Tendsto
  (fun x : R =>
    sum' m : N,
      LSeries.term
        (fun k : N => (Real.cos (2 * pi * (1 / 2) * k) : C))
        (1 / 2 : C)
        m * (x : C) ^ m)
  (nhdsWithin 1 (Iio 1))
  (nhds
    (HurwitzZeta.cosZeta
      (ZMod.toAddCircle (1 : ZMod 2))
      (1 / 2 : C)))
```

Do not replace this leaf with `LSeriesSummable`, unordered half-point `tsum`,
or a theorem that restates this Tendsto as an input under a new name.


## 8B. 2026-07-07 Ordered-Eta Finite-Head Execution

Result:
  Partial-good only.  05A is still open.

What changed:
  Lean now has the finite-head half of the ordered real-parameter eta
  continuity route:

```text
etaSigmaPartialSum sigma n
  =
sum_{i < n} (-1)^i * etaSigmaTerm sigma i

continuous_etaSigmaPartialSum n
  proves finite-head continuity in sigma.

tendsto_etaSigmaPartialSum_nhdsGT_half n
  proves the finite head tends to the half-point ordered partial sum as
  sigma -> 1/2 from the positive side.
```

New declarations:

```text
etaSigmaPartialSum
etaSigmaPartialSum_eq
continuousAt_etaSigmaTerm
continuous_etaSigmaPartialSum
etaSigmaPartialSum_half_eq_etaHalfPartialSum
tendsto_etaSigmaPartialSum_nhdsGT_half
```

Why this matters:
  The accepted lower route for `orderedEtaValue` continuity splits into:

```text
finite head:
  done by this execution.

uniform alternating tail:
  still open.
```

Rejected as closure:
  These declarations do not prove
  `orderedEtaValue sigma -> dirichletEtaRealHalfOrdered`, do not identify
  `dirichletEtaAnalytic (1 / 2)` with the ordered value, and do not close
  `riemannZeta_half_ne_zero`.

Verification:
  WSL Ubuntu-24.04 main ext4 mirror, under `/tmp/connes-weil-rh-lake.lock`:

```text
lake build ConnesWeilRH.Source.DirichletEta
```

  Result: pass.

  Focused import-facing axiom audit for the finite-head declarations returned:

```text
[propext, Classical.choice, Quot.sound]
```

Follow-up status:
  The uniform alternating-tail estimate and right-continuity theorem below
  were completed in the next execution section.

```lean
theorem tendsto_orderedEtaValue_sigma_nhdsGT_half :
    Tendsto
      (fun sigma : R => orderedEtaValue sigma)
      (nhdsWithin (1 / 2 : R) (Ioi (1 / 2)))
      (nhds dirichletEtaRealHalfOrdered)
```

Do not prove this through `continuous_tsum`, `LSeriesSummable`, unordered
half-point `tsum`, or a raw theorem field stating the continuity target.


## 8C. 2026-07-07 Ordered-Eta Tail And Safe-Domain Execution

Result:
  Partial-good only.  05A is still open.

What changed:
  Lean now has the full ordered real-parameter eta continuity brick at the
  half point from the right, plus the safe-domain agreement between Mathlib's
  analytic eta owner and the ordered real eta owner for real `sigma > 1`.

New declarations:

```text
orderedEtaValue_sub_etaSigmaPartialSum_abs_le
orderedEtaValue_half_eq_dirichletEtaRealHalfOrdered
tendsto_orderedEtaValue_sigma_nhdsGT_half
orderedEtaValue_eq_tsum_of_summable
summable_etaSigmaCoeff_of_one_lt
lseries_etaZModTwoCoeff_ofReal_term_nat_succ_eq_etaSigmaCoeff
dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_one_lt
```

Proof shape:

```text
ordered partial sums at sigma
  + finite-head continuity at sigma = 1/2
  + alternating-series tail bound uniformly dominated by etaHalfTerm
  -> orderedEtaValue sigma -> dirichletEtaRealHalfOrdered from the right

sigma > 1
  + Real p-series absolute convergence
  + LSeries n+1 reindex
  + etaZModTwoCoeff sign identity
  -> dirichletEtaAnalytic (sigma : C) = orderedEtaValue sigma
```

Why this matters:
  This removes two lower technical blockers without changing the half-point
  semantic owner.  `Summable`, `tsum`, and `LSeries` are used only in the safe
  domain `sigma > 1`, where absolute convergence is valid.  The half-point
  owner remains `dirichletEtaRealHalfOrdered`.

Rejected as closure:
  This does not prove

```lean
dirichletEtaAnalytic (1 / 2 : C) =
  (dirichletEtaRealHalfOrdered : C)
```

  The safe-domain theorem is only for `1 < sigma`.  A later theorem still has
  to transport the analytic identity from the safe domain to the half point
  through an accepted analytic-continuation / Dirichlet-uniform-convergence
  route, not by restating the half-point equality as a raw field.

Verification:
  WSL Ubuntu-24.04 main ext4 mirror, under `/tmp/connes-weil-rh-lake.lock`:

```text
lake build ConnesWeilRH.Source.DirichletEta \
  ConnesWeilRH.Source.ZetaHalfNonvanishing
```

  Result: pass.

  Focused import-facing axiom audit for the seven new ordered-tail and
  safe-domain declarations returned:

```text
[propext, Classical.choice, Quot.sound]
```

  Rejection scan result:
    no `sorry`, `admit`, new `axiom`, `constant`, `opaque`, `unsafe`,
    `Set.univ`, `True`, accepted-source, or raw source-theorem close was found
    in the 05A source files.  The `Summable`, `tsum`, and `LSeries` hits are
    either safe-domain `sigma > 1` support or pre-existing conditional Abel
    sockets; they do not define the half-point owner.

Remaining hard leaf in the lower eta split:

```text
new active target:
  dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos

then:
  specialize sigma = 1 / 2
  + orderedEtaValue_half_eq_dirichletEtaRealHalfOrdered
  -> half-point equality

Missing accepted theorem shape:
  theorem dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos
      {sigma : R} (hsigma : 0 < sigma) :
      dirichletEtaAnalytic (sigma : C) = (orderedEtaValue sigma : C)
```


## 8D. 2026-07-07 Positive-Strip Ordered Eta Agreement Plan

Status:
  Active target, partially lowered.  This is the next bottom theorem for 05A.

Hard completion gate:

```lean
theorem dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos
    {sigma : R} (hsigma : 0 < sigma) :
    dirichletEtaAnalytic (sigma : C) =
      (orderedEtaValue sigma : C)
```

Why this is the right next theorem:

```text
existing safe-domain theorem:
  dirichletEtaAnalytic (sigma : C) = orderedEtaValue sigma
  only for 1 < sigma

existing ordered continuity:
  orderedEtaValue sigma -> orderedEtaValue (1/2)
  from the right

gap:
  (1, infinity) does not accumulate at 1/2.
  So continuity alone cannot transport the safe-domain theorem to the half
  point.

needed:
  prove analytic eta equals the ordered conditional eta series on the whole
  real positive strip.
```

Accepted proof shape:

```text
1. Prove conditional convergence / ordered-sum agreement for eta coefficients
   on every sigma > 0.

2. Connect that conditional ordered sum to Mathlib's analytic continuation
   owner:
     dirichletEtaAnalytic = ZMod.LFunction etaZModTwoCoeff

3. Use the new theorem at sigma = 1/2 plus
   orderedEtaValue_half_eq_dirichletEtaRealHalfOrdered.
```

Allowed tools:

```text
Allowed:
  Abel summation / Dirichlet test APIs.
  Bounded periodic partial sums for etaZModTwoCoeff.
  Integral representation of LSeries from bounded coefficient sums.
  Analytic-continuation uniqueness when both sides are genuine analytic
  functions on an open connected domain and agree on a set with an accumulation
  point inside that domain.

Rejected:
  Using unordered half-point tsum as the semantic owner.
  Using LSeriesSummable at sigma = 1/2 as closure.
  Adding a raw theorem field or accepted-source theorem stating the target.
  Reusing dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_one_lt as if
  it accumulated at 1/2.
```

Execution result, 2026-07-07:

```text
Closed bottom half:

  theorem tendsto_etaSigmaPowerSeries_nhdsWithin_lt
      {sigma : R} (hsigma : 0 < sigma) :
      Tendsto
        (fun x : R =>
          sum' n : N, ((-1 : R) ^ n * etaSigmaTerm sigma n) * x ^ n)
        (nhdsWithin 1 (Iio 1))
        (nhds (orderedEtaValue sigma))

  theorem tendsto_etaSigmaPowerSeries_complex_nhdsWithin_lt
      {sigma : R} (hsigma : 0 < sigma) :
      Tendsto
        (fun x : R =>
          ((sum' n : N,
            ((-1 : R) ^ n * etaSigmaTerm sigma n) * x ^ n : R) : C))
        (nhdsWithin 1 (Iio 1))
        (nhds (orderedEtaValue sigma : C))

Meaning:
  orderedEtaValue sigma is now formally the Abel boundary of the same
  alternating power series for every sigma > 0.

Still open:
  Prove that Mathlib's analytic continuation owner
    dirichletEtaAnalytic (sigma : C)
  has the same Abel boundary for every sigma > 0.

  Exact next theorem:

  theorem tendsto_etaSigmaPowerSeries_complex_nhdsWithin_lt_dirichletEtaAnalytic
      {sigma : R} (hsigma : 0 < sigma) :
      Tendsto
        (fun x : R =>
          ((sum' n : N,
            ((-1 : R) ^ n * etaSigmaTerm sigma n) * x ^ n : R) : C))
        (nhdsWithin 1 (Iio 1))
        (nhds (dirichletEtaAnalytic (sigma : C)))

  Once this is proved, `tendsto_nhds_unique` with
  `tendsto_etaSigmaPowerSeries_complex_nhdsWithin_lt` gives
  `dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos`.

Rejected as closure:
  The new Abel-boundary theorem alone does not prove
    dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos.
  It only proves the ordered-series side of that equality.
```

Current evidence:

```text
WSL Ubuntu-24.04 main ext4 mirror, under /tmp/connes-weil-rh-lake.lock:

  lake build ConnesWeilRH.Source.DirichletEta

Result:
  pass

Focused import-facing axiom audit for:
  tendsto_etaSigmaPowerSeries_nhdsWithin_lt
  tendsto_etaSigmaPowerSeries_complex_nhdsWithin_lt
  dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_one_lt

Result:
  [propext, Classical.choice, Quot.sound]
```

Smallest build:

```text
lake build ConnesWeilRH.Source.DirichletEta \
  ConnesWeilRH.Source.ZetaHalfNonvanishing
```

Focused axiom audit targets after execution:

```lean
#check ConnesWeilRH.Source.dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos
#print axioms ConnesWeilRH.Source.dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos

#check ConnesWeilRH.Source.dirichletEtaAnalytic_half_eq_ordered
#print axioms ConnesWeilRH.Source.dirichletEtaAnalytic_half_eq_ordered
```


## 8E. 2026-07-08 Ordered LSeries Item Partial-Sum Bridge

Result:
  Partial-good only.  05A is still open.

What changed:
  Lean now has a clean ordered partial-sum bridge between Mathlib's
  `LSeries.term` item notation for `etaZModTwoCoeff` and the project's
  ordered eta owner:

```text
etaZModTwoCoeff_ordered_partialSum_eq_etaSigmaPartialSum
  identifies finite sums of
    LSeries.term etaZModTwoCoeff (sigma : C) (i + 1)
  with
    etaSigmaPartialSum sigma n.

tendsto_etaZModTwoCoeff_ordered_partialSum_of_pos
  proves those ordered partial sums tend to
    orderedEtaValue sigma
  for every sigma > 0.

tendsto_etaZModTwoCoeff_half_ordered_partialSum
  specializes the same bridge at sigma = 1/2 and lands at
    dirichletEtaRealHalfOrdered.
```

Why this matters:
  This pins the ordered-series side directly to `LSeries.term` without using
  `LSeries`, `LSeriesSummable`, unordered half-point `tsum`, or a raw theorem
  field.  It is a lower item/partial-sum bridge, not an analytic continuation
  theorem.

Rejected as closure:
  These declarations do not prove

```lean
dirichletEtaAnalytic (1 / 2 : C) =
  (dirichletEtaRealHalfOrdered : C)
```

  and do not prove the full half-period `cosZeta` Abel boundary to Mathlib's
  analytic `cosZeta` value.

Verification:
  WSL Ubuntu main ext4 mirror was reset to Windows HEAD `667e6d5` on Peter's
  instruction that Windows is the only source of truth.  The smallest module
  build passed under `/tmp/connes-weil-rh-lake.lock`:

```text
lake build ConnesWeilRH.Source.DirichletEta
```

  Focused import-facing axiom audit for the three new declarations returned:

```text
[propext, Classical.choice, Quot.sound]
```

Remaining hard leaf:
  Prove the analytic Abel-continuation side, for example the exact existing
  full-series socket:

```lean
Tendsto
  (fun x : R =>
    sum' m : N,
      LSeries.term
        (fun k : N => (Real.cos (2 * pi * (1 / 2) * k) : C))
        (1 / 2 : C)
        m * (x : C) ^ m)
  (nhdsWithin 1 (Iio 1))
  (nhds
    (HurwitzZeta.cosZeta
      (ZMod.toAddCircle (1 : ZMod 2))
      (1 / 2 : C)))
```

  Equivalently, prove `dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos`
  without using unordered half-point `tsum` or `LSeriesSummable` as the active
  owner.


## 9. Required Final Declarations

```lean
theorem tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries :
    Tendsto
      (fun x : R =>
        ((sum' n, ((-1 : R) ^ n * etaHalfTerm n) * x ^ n : R) : C))
      (nhdsWithin 1 (Iio 1))
      (nhds
        (-HurwitzZeta.cosZeta (ZMod.toAddCircle (1 : ZMod 2))
          (1 / 2 : C)))

theorem dirichletEtaAnalytic_half_eq_ordered :
    dirichletEtaAnalytic (1 / 2 : C) =
      (dirichletEtaRealHalfOrdered : C)

theorem dirichletEtaRealHalfOrdered_eq_factor_mul_riemannZeta_half :
    (dirichletEtaRealHalfOrdered : C) =
      ((1 : C) - (2 : C) ^ (1 - (1 / 2 : C))) *
        riemannZeta (1 / 2 : C)

theorem riemannZeta_half_ne_zero :
    riemannZeta (1 / 2 : C) != 0

theorem cc20_triple_disjoint_from_standard_source_nontrivial_zeros :
    SourceFiniteSetDisjointFromNontrivialZeros
      RHDefinitionBridge.standard
      cc20TripleFiniteVanishingSet
```


## 10. Current Verified Socket

Current conditional theorem chain:

```lean
theorem dirichletEtaRealHalfOrdered_eq_factor_mul_riemannZeta_half_of_cosZeta_abel
    (habel :
      Tendsto
        (fun x : R =>
          ((sum' n, ((-1 : R) ^ n * etaHalfTerm n) * x ^ n : R) : C))
        (nhdsWithin 1 (Iio 1))
        (nhds
          (-HurwitzZeta.cosZeta (ZMod.toAddCircle (1 : ZMod 2))
            (1 / 2 : C)))) :
    (dirichletEtaRealHalfOrdered : C) =
      ((1 : C) - (2 : C) ^ (1 - (1 / 2 : C))) *
        riemannZeta (1 / 2 : C)

theorem riemannZeta_half_ne_zero_of_neg_cosZeta_half_period_abel_limit
    (habel : <same Abel-boundary theorem>) :
    RiemannZetaHalfNonvanishing

theorem cc20_triple_disjoint_of_neg_cosZeta_half_period_abel_limit
    (habel : <same Abel-boundary theorem>) :
    SourceFiniteSetDisjointFromNontrivialZeros
      RHDefinitionBridge.standard
      cc20TripleFiniteVanishingSet
```

Focused import-facing axiom audit for these socket declarations returned:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`.

2026-07-07 05A-D item-level bridge audit:

```lean
#check ConnesWeilRH.Source.etaZModTwoCoeff_natCast_succ_eq_neg_one_pow
#print axioms ConnesWeilRH.Source.etaZModTwoCoeff_natCast_succ_eq_neg_one_pow

#check ConnesWeilRH.Source.lseries_etaZModTwoCoeff_half_term_nat_succ_eq_etaHalfCoeff
#print axioms ConnesWeilRH.Source.lseries_etaZModTwoCoeff_half_term_nat_succ_eq_etaHalfCoeff

#check ConnesWeilRH.Source.neg_lseries_cosZeta_half_period_term_nat_succ_eq_etaHalfCoeff
#print axioms ConnesWeilRH.Source.neg_lseries_cosZeta_half_period_term_nat_succ_eq_etaHalfCoeff

#check ConnesWeilRH.Source.etaHalfPowerSeries_eq_neg_lseries_cosZeta_half_period_powerSeries
#print axioms ConnesWeilRH.Source.etaHalfPowerSeries_eq_neg_lseries_cosZeta_half_period_powerSeries

#check ConnesWeilRH.Source.tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries_of_lseries_term_abel
#print axioms ConnesWeilRH.Source.tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries_of_lseries_term_abel

#check ConnesWeilRH.Source.neg_shifted_lseries_cosZeta_half_period_powerSeries_eq_neg_full_div
#print axioms ConnesWeilRH.Source.neg_shifted_lseries_cosZeta_half_period_powerSeries_eq_neg_full_div

#check ConnesWeilRH.Source.norm_lseries_cosZeta_half_period_term_le_one
#print axioms ConnesWeilRH.Source.norm_lseries_cosZeta_half_period_term_le_one

#check ConnesWeilRH.Source.summable_lseries_cosZeta_half_period_powerSeries_of_norm_lt_one
#print axioms ConnesWeilRH.Source.summable_lseries_cosZeta_half_period_powerSeries_of_norm_lt_one

#check ConnesWeilRH.Source.eventually_summable_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt
#print axioms ConnesWeilRH.Source.eventually_summable_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt

#check ConnesWeilRH.Source.tendsto_neg_shifted_lseries_cosZeta_half_period_abel_of_full_lseries_term_abel
#print axioms ConnesWeilRH.Source.tendsto_neg_shifted_lseries_cosZeta_half_period_abel_of_full_lseries_term_abel

#check ConnesWeilRH.Source.tendsto_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt_ordered
#print axioms ConnesWeilRH.Source.tendsto_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt_ordered
```

Result:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`.  These declarations do not close the half-point by `LSeries` or
unordered summation.  They prove the item identities, the local geometric
summability needed for the quotient/reindex bridge, and the strengthened
shifted bridge.  The newest declaration proves the full unshifted Abel
boundary to `-dirichletEtaRealHalfOrdered`; it does not identify that value
with Mathlib's analytic `cosZeta`.


## 10E. 2026-07-08 Paired Eta Closure

Result:
  Good.  The 05A half-point bridge is closed without `sorryAx`.

New semantic owner:
  `Source.etaPairTermComplex`

Route:

```text
adjacent pair term
  etaPairTermComplex s n
    = (2*n+1 : C)^(-s) - (2*n+2 : C)^(-s)

local uniform summability on {s | 0 < s.re}
  via the derivative/MVT bound
    ||m^(-s) - (m+1)^(-s)|| <= B * m^(-(a+1))

analytic paired tsum
  Source.analyticOnNhd_etaPairTermComplex_tsum

safe-ray identity
  paired tsum at (sigma : C), 1 < sigma
    = orderedEtaValue sigma
    = dirichletEtaAnalytic (sigma : C)

analytic uniqueness
  equality on real points accumulating at 2
  -> equality on the connected right half-plane {s | 0 < s.re}

half-point specialization
  dirichletEtaAnalytic (1/2 : C)
    = (dirichletEtaRealHalfOrdered : C)
```

New closure declarations:

```lean
Source.etaPairTermComplex
Source.summableLocallyUniformlyOn_etaPairTermComplex
Source.analyticOnNhd_etaPairTermComplex_tsum
Source.etaPairTermComplex_tsum_eq_dirichletEtaAnalytic_on_re_pos
Source.dirichletEtaAnalytic_half_eq_ordered
Source.riemannZeta_half_ne_zero
Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros
```

Scratch verification before main mirror sync:

```text
cd /tmp/cwrh-05a-scratch
flock /tmp/connes-weil-rh-lake.lock lake build \
  ConnesWeilRH.Source.DirichletEta \
  ConnesWeilRH.Source.ZetaHalfNonvanishing

Result: passed.
```

Focused import-facing axiom audit:

```text
Source.etaPairTermComplex_tsum_eq_dirichletEtaAnalytic_on_re_pos
  [propext, Classical.choice, Quot.sound]

Source.dirichletEtaAnalytic_half_eq_ordered
  [propext, Classical.choice, Quot.sound]

Source.riemannZeta_half_ne_zero
  [propext, Classical.choice, Quot.sound]

Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros
  [propext, Classical.choice, Quot.sound]
```

Rejected-route status:
  The old `cosZeta` / Abel-boundary theorems remain compatibility sockets.
  They are no longer the active hard leaf for 05A.  The closure does not use
  unordered half-point `LSeriesSummable`, `dirichletEtaReal (1 / 2)`,
  accepted-source theorem fields, `True`, or `Set.univ`.


## 11. Build Gate

Use the main WSL ext4 mirror.  Do not run `lake` from Windows or `/mnt/c`.

Smallest build after 05A Lean edits:

```text
cd /home/peter/projects/Connes-Weil-RH-Proof
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
  ConnesWeilRH.Source.DirichletEta \
  ConnesWeilRH.Source.ZetaHalfNonvanishing
```

Include `ConnesWeilRH.Source.CC20RHExit` only after the final theorem is
exported there.


## 12. Focused Axiom Audit

Run this after the open leaf is proved:

```lean
import ConnesWeilRH.Source.DirichletEta
import ConnesWeilRH.Source.ZetaHalfNonvanishing

#check ConnesWeilRH.Source.tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries
#print axioms ConnesWeilRH.Source.tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries

#check ConnesWeilRH.Source.dirichletEtaAnalytic_half_eq_ordered
#print axioms ConnesWeilRH.Source.dirichletEtaAnalytic_half_eq_ordered

#check ConnesWeilRH.Source.dirichletEtaRealHalfOrdered_eq_factor_mul_riemannZeta_half
#print axioms ConnesWeilRH.Source.dirichletEtaRealHalfOrdered_eq_factor_mul_riemannZeta_half

#check ConnesWeilRH.Source.riemannZeta_half_ne_zero
#print axioms ConnesWeilRH.Source.riemannZeta_half_ne_zero

#check ConnesWeilRH.Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros
#print axioms ConnesWeilRH.Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros
```

Accepted output may include only Lean/Mathlib foundational axioms already
accepted nearby.  It must not include `sorryAx` or project-local axioms.


## 13. Rejection Scans

Run before acceptance:

```text
rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b|accepted|source theorem|Set\.univ|\bTrue\b" \
  ConnesWeilRH/Source/DirichletEta.lean \
  ConnesWeilRH/Source/ZetaHalfNonvanishing.lean \
  ConnesWeilRH/Source/CC20RHExit.lean

rg -n "dirichletEtaComplex.*1 / 2|dirichletEtaReal \(1 / 2\)|LSeries .*1 / 2|LSeriesSummable .*1 / 2|HasSum|Summable|tendsto_neg_cosZeta_half_period_abel|riemannZeta_half_ne_zero" \
  ConnesWeilRH/Source/DirichletEta.lean \
  ConnesWeilRH/Source/ZetaHalfNonvanishing.lean
```

Inspect every hit.  `HasSum`, `Summable`, and `tsum` may occur in safe-domain
or Mathlib-wrapper code, but they must not define or close the active
half-point owner.


## 14. Acceptance Text

```text
Result:
  Good / partial / rejected.

Shard scope:
  05A shard-good only.  Plan 05 remains partial until 05D and 05E pass.

Old weak path removed:
  CC20 triple disjointness no longer depends on a missing zeta-half theorem.

New declarations:
  <exact declarations>

Build:
  <command and result>

Focused axiom audit:
  <output>

Remaining Plan 05 dependency:
  CC20 Proposition C.1 route realization and Dev integration remain outside
  this shard.
```
