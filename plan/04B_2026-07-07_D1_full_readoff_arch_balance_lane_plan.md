# D1 04B Full Read-Off Arch Balance Lane

Date: 2026-07-07

Status: execution lane for one manual AI session.  This file is not Lean
progress.  Accepted progress requires the WSL build and focused axiom audit
below.

AI session start:

```text
owner: Codex main session
cwd: C:\Projects\Connes-Weil-RH-Proof
lane: D1 04B full read-off / selected archimedean balance
old weak path:
  selected QW_lambda = QW through Root 2/common-data scoped balance,
  TraceData readback, later restricted-to-full bridge, or raw read-off rows
files allowed:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean
  ConnesWeilRH/Route/Bridge.lean
  plan/04B_2026-07-07_D1_full_readoff_arch_balance_lane_plan.md
files forbidden:
  no sibling 04B plan
  no wrapper/raw Prop replacement
  no Windows lake
smallest WSL build:
  lake build ConnesWeilRH.Dev.UnconditionalSkeleton
focused axiom audit:
  selected QW_lambda restriction/equality/full-readoff chain
expected output:
  either close 04B cleanly, or drill to the first lower non-wrapper theorem
```


## 1. Result First

Current result:

```text
Partial-good, rejected as solved.
```

Reason:

```text
The active selected arch-balance row no longer directly imports Root 2 at the
selected row site.  It now factors through a clean no-defect/global-formula
bridge, and that formula is itself reduced to the exact selected scalar
restriction-row socket:

normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
  -> normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems
  -> normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
  -> source_archimedean_balance_rows_of_no_defect_global_formula
  -> normalizedSelectedSourceNoDefectGlobalFormulaFromTheorems
  -> source_no_defect_global_formula_of_scalar_equality
  -> normalizedSelectedQWLambdaEqualsQWFromTheorems
  -> source_qw_lambda_eq_qw_of_qw_lambda_restriction
  -> normalizedSelectedQWLambdaRestrictionRowsFromTheorems
  -> normalizedSelectedArchimedeanContributionMatchesForRestrictionFromTheorems
  -> normalizedSelectedScopedArchimedeanContributionMatchesForRestrictionFromTheorems
  -> sorryAx

This is progress, but not closure.  The remaining hard socket is now:

  selected scoped archimedean contribution balance:

    SourceScopedArchimedeanContributionMatchesForRestriction
      selected-inputs selected-g selected-lambda selected-pkg

It must be proved before TraceFrontEndData and without Root 2,
read-off-row fallback, raw scalar equality storage, a raw scopedBalance field,
or a later restricted-to-full bridge contract.
```

2026-07-07 continuation result:

```text
Bad for closure.  04B still does not close.

The direct active Lean leaf is now:

  ConnesWeilRH/Dev/UnconditionalSkeleton.lean
    normalizedSelectedQWLambdaRestrictionRowsFromTheorems := by sorry

The lowest non-wrapper theorem found by this pass is not another route bridge.
It is the actual selected scoped balance:

  Source.CCM25Concrete.Package.ScopedArchimedeanContributionBalance
    normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
    normalizedSourceBackedFixedSTestFromTheorems.weilTest
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceCCM25ArithmeticPackageFromTheorems

Equivalently:

  archimedeanTerm(convolutionStar g g)
    + polePairing(g)
    - restricted finite-prime evaluator scoped sum

  =

  poleFunctional(convolutionStar g g)
    - archimedeanTerm(convolutionStar g g)
    - global finite-prime evaluator scoped sum

The pass checked the following dependency layers and rejected them as closure:

  1. selected source common tuple
  2. selected restricted finite-prime support stabilization
  3. package exact finite-prime support
  4. package QW_lambda formula components
  5. package QW / Psi global formula components
  6. global/restricted certificate equality
  7. source evaluator sum read-off
  8. common-data scoped archimedean balance
  9. SourceObjectConcreteCommonData boundary balance
  10. CommonFinitePrimeArithmeticSourceData scoped balance field
  11. S2B1 no-bulk rows
  12. S2B1 no-hidden-finite-part rows
  13. normalized source no-defect restricted formula
  14. normalized source no-defect global formula
  15. later restricted-to-full threshold/current-cutoff path
  16. TraceFrontEndData readback path
  17. NormalizedSourceTraceReadOffEqualityRows raw full/restricted rows
  18. finite-prime support-only route
  19. SourceWeilFormData definitional route
  20. pole-normalization-only route

Why these are rejected:

  finite-prime support stabilization only compares finite-prime index/sum
  support.  It does not account for the archimedean contribution.  In
  SourceWeilFormData the definitions are:

    qwLambda = archimedeanTerm + poleFunctional - restricted finite sum
    qw       = poleFunctional - archimedeanTerm - global finite sum

  so even restricted = global would still leave the missing archimedean
  balance.  The current lower source files expose this balance only as a field
  on CommonFinitePrimeArithmeticSourceData / SourceObjectConcreteCommonData,
  not as a theorem derived from lower analytic data.
```

What moved:

```text
The pure algebraic sub-bridges are now clean:

selected scalar equality:
  SourceQWLambdaIsRestrictionOfQW selected-inputs selected-g selected-lambda selected-pkg

  -> source_qw_lambda_eq_qw_of_qw_lambda_restriction
  -> qwLambda lambda g g = qw g g

selected restriction rows:
  common tuple
  finite-prime stabilization
  package exact finite support
  archimedean pole stability
  selected scoped archimedean contribution balance

  -> source_qw_lambda_is_restriction_of_common_tuple
  -> SourceQWLambdaIsRestrictionOfQW selected-inputs selected-g selected-lambda selected-pkg

selected scalar equality to arch-balance:
  qwLambda lambda g g = qw g g

  -> source_scoped_archimedean_contribution_matches_of_scalar_equality
  -> source_archimedean_balance_rows_of_scalar_equality
  -> SourceArchimedeanContributionBalanceRows

selected source no-defect global formula:
  sourceNoDefectTrace a = qwLambda lambda g g
  qwLambda lambda g g = qw g g

  -> source_no_defect_global_formula_of_scalar_equality
  -> sourceNoDefectTrace a = scoped global formula

selected source no-defect global formula to scalar equality:
  sourceNoDefectTrace a = qwLambda lambda g g
  sourceNoDefectTrace a = scoped global formula

  -> source_scalar_equality_of_no_defect_global_formula
  -> source_archimedean_balance_rows_of_no_defect_global_formula
  -> SourceArchimedeanContributionBalanceRows

Evidence:
  ConnesWeilRH/Route/Bridge.lean
    source_scoped_archimedean_contribution_matches_of_scalar_equality
    source_archimedean_balance_rows_of_scalar_equality
    source_scalar_equality_of_no_defect_global_formula
    source_no_defect_global_formula_of_scalar_equality
    source_qw_lambda_eq_qw_of_qw_lambda_restriction
    source_archimedean_balance_rows_of_no_defect_global_formula

WSL build:
  lake build ConnesWeilRH.Dev.UnconditionalSkeleton
  passed.

Focused axiom audit:
  all Route bridge declarations return:
    [propext, Classical.choice, Quot.sound]

  active Dev declarations still return:
    [propext, sorryAx, Classical.choice, Quot.sound]

  The first 04B selected leaf with sorryAx is now:
    normalizedSelectedScopedArchimedeanContributionMatchesForRestrictionFromTheorems
```

Complete result required:

```text
normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
  must be proved from a pre-TraceData selected archimedean-balance owner that
  does not read Root 2, normalizedTraceDataFromTheorems, or a later
  restricted-to-full bridge contract.

Then:
  normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems
  normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull

must consume that owner.
```


## 2. What Counts As Solved

Hard completion gate:

```text
old weak path:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2632-2642
    normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
      calls Source.common_data_scoped_archimedean_contribution_balance
        normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems

new semantic owner/API:
  a selected pre-TraceData theorem or data owner proving:

    SourceArchimedeanContributionBalanceRows
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceBackedFixedSTestFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceCCM25ArithmeticPackageFromTheorems

  The accepted low-level shape may use:

    source_archimedean_balance_rows_of_scalar_equality
    source_archimedean_balance_rows_of_no_defect_global_formula
    source_no_defect_global_formula_of_scalar_equality

  only if the SourceQWLambdaIsRestrictionOfQW input is itself proved before
  TraceFrontEndData and its scoped archimedean contribution balance is proved
  before TraceFrontEndData and without Root 2 / read-off-row fallback.

real consumer rewired:
  normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
  normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems
  normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull

same-object alias / wrapper rejection scan:
  the new owner must not restate scopedBalance as a raw Prop field copied from
  Root 2 or from a later TraceFrontEnd / restricted-to-full package.

smallest WSL build:
  lake build ConnesWeilRH.Dev.UnconditionalSkeleton

focused axiom audit targets:
  normalizedSelectedScopedArchimedeanContributionMatchesForRestrictionFromTheorems
  normalizedSelectedArchimedeanContributionMatchesForRestrictionFromTheorems
  normalizedSelectedQWLambdaRestrictionRowsFromTheorems
  normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
  normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems
  normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
  normalizedTraceDataFromTheorems

semantic sufficiency for next route/RH step:
  Tree B can produce selected full read-off before TraceFrontEndData consumes
  the full and restricted read-off bridges.
```


## 3. What Does Not Count

Rejected:

```text
- using normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems;
- using normalizedCommonFinitePrimeArithmeticSourceDataFromTheorems;
- using normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems;
- using normalizedTraceDataFromTheorems as an input to the full equality;
- using normalizedRestrictedToFullQWFromTheorems;
- using normalizedRestrictedToFullAsymptoticRowsInputFromTheorems while its
  type or constructor consumes normalizedTraceDataFromTheorems;
- using normalizedRestrictedToFullCurrentCutoffBindingFromTheorems while it is
  built from normalizedTraceDataFromTheorems;
- using normalizedTraceReadOffEqualityRowsFromTheorems or
  NormalizedSourceTraceReadOffEqualityRows as the scalar-equality producer;
- using Source.common_data_scoped_archimedean_contribution_balance or
  normalized_seed_source_no_defect_trace_eq_global_formula_of_common_data as
  the no-defect/global-formula producer;
- copying scopedBalance as a raw field from a new wrapper.
```

Circular shape to reject:

```text
selected full equality
  -> selected full read-off bridge
  -> normalizedTraceDataFromTheorems
  -> normalizedRestrictedToFullAsymptoticRowsInputFromTheorems
  -> normalizedRestrictedToFullCurrentCutoffBindingFromTheorems
  -> restricted-to-full bridge/equality
```

Raw read-off-row shape to reject:

```text
selected scalar equality
  -> fullTraceReadOffEquality field
  -> restrictedTraceReadOffEquality field
  -> NormalizedSourceTraceReadOffEqualityRows
  -> theorem-base input / bridge read-off constructor

Reason:
  This replaces Root 2 balance with a raw pair of route-facing numeric rows.
  It is not a lower selected semantic owner.
```


## 4. Current Evidence

Lean source evidence:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2632-2642
  normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
  reads normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2657-2668
  normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems
  consumes the selected common tuple, selected finite-prime stabilization, and
  selected archimedean balance.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2670-2700
  normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
  consumes scalar_equality_from_scoped_witness_components.

ConnesWeilRH/Route/Bridge.lean:1115-1124
  SourceArchimedeanContributionBalanceRows stores the scoped balance row needed
  by this lane.

ConnesWeilRH/Route/Bridge.lean:1572-1594
  RestrictedToFullQWScalarRestrictionWitness consumes the archimedean
  contribution match.

ConnesWeilRH/Route/Bridge.lean:1828-1900
  RestrictedToFullAsymptoticRows can derive scalar restriction from support,
  prime-power stabilization, and archimedean balance, but the current Dev
  provider for it is later than TraceData and cannot close this lane.

ConnesWeilRH/Route/Bridge.lean:
  source_scoped_archimedean_contribution_matches_of_scalar_equality proves the
  algebraic direction:

    qwLambda = qw
      -> ScopedRestrictedArchimedeanFormula = ScopedGlobalArchimedeanFormula

  source_archimedean_balance_rows_of_scalar_equality packages that result as
  SourceArchimedeanContributionBalanceRows.

  source_scalar_equality_of_no_defect_global_formula proves the lower
  source-read-off direction:

    sourceNoDefectTrace = qwLambda
    sourceNoDefectTrace = scoped global formula
      -> qwLambda = qw

  source_archimedean_balance_rows_of_no_defect_global_formula packages that
  result as SourceArchimedeanContributionBalanceRows.

ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:2649-2664
  NormalizedSourceTraceReadOffEqualityRows stores the full and restricted
  read-off equalities as raw fields.  It can imply qwLambda = qw only by
  reading those fields, so it is rejected as a 04B producer.

ConnesWeilRH/Source/S2B1TraceScale.lean:1473-1531
  normalized_seed_source_no_defect_trace_eq_global_formula_of_scalar_identification
  still requires scoped balance, and
  normalized_seed_source_no_defect_trace_eq_global_formula_of_common_data
  supplies that balance from CommonFinitePrimeArithmeticSourceData.  Both are
  rejected as 04B closure producers.
```

Focused audit evidence:

```text
Current Tree B selected path:
  normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
  normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems
  normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
  normalizedTraceDataFromTheorems

  all return:
    [propext, sorryAx, Classical.choice, Quot.sound]

Clean comparison:
  normalizedTraceLambdaInputFromTheorems
    [propext, Classical.choice, Quot.sound]

New algebra bridge:
  source_scoped_archimedean_contribution_matches_of_scalar_equality
  source_archimedean_balance_rows_of_scalar_equality
  source_scalar_equality_of_no_defect_global_formula
  source_archimedean_balance_rows_of_no_defect_global_formula

  all return:
    [propext, Classical.choice, Quot.sound]
```


## 5. First-Principles Dependency Chain

The selected full read-off needs:

```text
sourceNoDefectTrace = supportSquareTrace
  -> supportSquareTrace = QW_lambda
  -> QW_lambda = QW
  -> FullTraceReadOffEquality
  -> selected full read-off bridge
  -> normalizedTraceDataFromTheorems
```

04B owns only the final scalar restriction:

```text
QW_lambda selected lambda selected fixed S-test selected fixed S-test

=

QW selected fixed S-test selected fixed S-test
```

The current proof gets this from:

```text
RestrictedToFullQWScalarRestrictionWitness
  -> SourceArchimedeanContributionBalanceRows
  -> Root 2 finite-prime source data
```

04B must replace the last arrow.


## 5A. Tree Split

Current bad tree:

```text
Tree B: selected full read-off
|
+-- sourceNoDefectTrace = supportSquareTrace
|     evidence: selected trace legality / archimedean trace square
|
+-- supportSquareTrace = QW_lambda
|     owner: 04A selected restricted evaluator lane
|
+-- QW_lambda = QW
|     current owner:
|       normalizedSelectedQWLambdaEqualsQWFromTheorems
|         -> source_qw_lambda_eq_qw_of_qw_lambda_restriction
|         -> normalizedSelectedQWLambdaRestrictionRowsFromTheorems
|         -> normalizedSelectedArchimedeanContributionMatchesForRestrictionFromTheorems
|         -> normalizedSelectedScopedArchimedeanContributionMatchesForRestrictionFromTheorems
|         -> sorryAx
|
|     rejected old owner:
|       normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems
|         -> normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
|         -> Source.common_data_scoped_archimedean_contribution_balance
|         -> normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems
|         -> Root 2
|
+-- FullTraceReadOffEquality
      current theorem:
        normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
```

Completed algebra sub-tree:

```text
Tree B0: scalar equality from selected restriction rows
|
+-- input now field-split:
|     selected SourceQWLambdaIsRestrictionOfQW rows:
|       restrictedDefinition: from selected common tuple
|       fullDefinition: from selected common tuple
|       finitePrimeStabilization: from selected finite-prime stabilization
|       exactFinitePrimeSupport: from package exact support
|       archimedeanPoleStability: from selected common tuple
|       archimedeanContributionMatches:
|         normalizedSelectedArchimedeanContributionMatchesForRestrictionFromTheorems
|           -> normalizedSelectedScopedArchimedeanContributionMatchesForRestrictionFromTheorems
|           -> sorryAx
|
+-- clean algebra bridge:
|     source_qw_lambda_eq_qw_of_qw_lambda_restriction
|
+-- output:
      QW_lambda selected-lambda selected-g selected-g
        =
      QW selected-g selected-g
```

Completed algebra sub-tree:

```text
Tree B2: balance from selected scalar equality
|
+-- input still missing:
|     selected hscalar:
|       QW_lambda selected-lambda selected-g selected-g
|         =
|       QW selected-g selected-g
|
+-- clean algebra bridge:
|     source_scoped_archimedean_contribution_matches_of_scalar_equality
|
+-- rows adapter:
|     source_archimedean_balance_rows_of_scalar_equality
|
+-- output:
      SourceArchimedeanContributionBalanceRows
```

Completed lower algebra sub-tree:

```text
Tree B1b: no-defect/global formula from selected scalar equality
|
+-- input already available on active selected tuple:
|     sourceNoDefectTrace selected-a = QW_lambda selected-lambda selected-g selected-g
|
+-- input still missing:
|     selected hscalar:
|       QW_lambda selected-lambda selected-g selected-g
|         =
|       QW selected-g selected-g
|
+-- clean bridge:
|     source_no_defect_global_formula_of_scalar_equality
|
+-- output:
      sourceNoDefectTrace selected-a =
        scoped global formula for selected-g and selected package
```

Completed reverse-check algebra sub-tree:

```text
Tree B1c: selected scalar equality from no-defect/global formula
|
+-- input available after Tree B1b:
|     sourceNoDefectTrace selected-a = QW_lambda selected-lambda selected-g selected-g
|
+-- input available after Tree B1b:
|     sourceNoDefectTrace selected-a =
|       scoped global formula for selected-g and selected package
|
+-- clean bridge:
|     source_scalar_equality_of_no_defect_global_formula
|
+-- rows adapter:
|     source_archimedean_balance_rows_of_no_defect_global_formula
|
+-- output:
      SourceArchimedeanContributionBalanceRows
```

Remaining unsolved producer tree:

```text
Tree B1: producer for selected hscalar
|
+-- accepted source:
|     lower selected semantics before TraceFrontEndData
|     no Root 2 finite-prime source data
|     no theorem-base raw full/restricted read-off row
|     no later restricted-to-full bridge
|
+-- rejected source A:
|     normalizedTraceReadOffEqualityRowsFromTheorems
|       -> NormalizedSourceTraceReadOffEqualityRows.fullTraceReadOffEquality
|       -> NormalizedSourceTraceReadOffEqualityRows.restrictedTraceReadOffEquality
|
+-- rejected source B:
|     normalizedRestrictedToFullQWFromTheorems
|       -> normalizedRestrictedToFullCurrentCutoffBindingFromTheorems
|       -> normalizedTraceDataFromTheorems
|
+-- rejected source C:
|     normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems
        -> normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems
+
+-- current lowest missing theorem:
      selected scoped balance:
        SourceScopedArchimedeanContributionMatchesForRestriction
          selected-inputs selected-g selected-lambda selected-pkg

      This theorem must not be proved through:
        Source.common_data_scoped_archimedean_contribution_balance
        normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems
        NormalizedSourceTraceReadOffEqualityRows
        normalizedTraceDataFromTheorems
        normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
        normalizedSelectedQWLambdaRestrictionRowsFromTheorems
        normalizedSelectedQWLambdaEqualsQWFromTheorems as a raw Prop wrapper
```

Accepted final tree:

```text
selected lower scoped archimedean contribution balance
  -> normalizedSelectedScopedArchimedeanContributionMatchesForRestrictionFromTheorems
  -> normalizedSelectedArchimedeanContributionMatchesForRestrictionFromTheorems
  -> source_qw_lambda_is_restriction_of_common_tuple
  -> normalizedSelectedQWLambdaRestrictionRowsFromTheorems
  -> source_qw_lambda_eq_qw_of_qw_lambda_restriction
  -> normalizedSelectedQWLambdaEqualsQWFromTheorems
  -> source_no_defect_global_formula_of_scalar_equality
  -> normalizedSelectedSourceNoDefectGlobalFormulaFromTheorems
  -> source_archimedean_balance_rows_of_no_defect_global_formula
  -> normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
  -> normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems
  -> scalar_equality_from_scoped_witness_components
  -> normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
  -> normalizedTraceDataFromTheorems
```

Verification tree:

```text
static scan
  -> no Root 2 in normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
  -> no TraceData readback in selected full equality
  -> no raw NormalizedSourceTraceReadOffEqualityRows producer

WSL build
  -> lake build ConnesWeilRH.Dev.UnconditionalSkeleton

focused axiom audit
  -> normalizedSelectedQWLambdaEqualsQWFromTheorems
  -> normalizedSelectedSourceNoDefectGlobalFormulaFromTheorems
  -> normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
  -> normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems
  -> normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
  -> normalizedTraceDataFromTheorems
```


## 6. Implementation Route

Work in this order:

```text
1. Search for a pre-TraceData scalar equality or archimedean-balance theorem
   for the active selected package, fixed S-test, lambda, and arithmetic
   package.

2. Prefer the lower no-defect/global-formula shape:
     source_archimedean_balance_rows_of_no_defect_global_formula.

3. If the theorem proves scalar equality directly:
     use source_archimedean_balance_rows_of_scalar_equality.

4. If the theorem proves balance directly:
     use it only if it is not a raw scopedBalance wrapper and not Root 2.

5. Reject any theorem whose type mentions normalizedTraceDataFromTheorems or a
   route package built after normalizedTraceDataFromTheorems.

6. If a lower theorem exists, rewire:
     normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems

7. If the lower theorem needs support and atom stabilization rows, keep those as
   explicit selected prerequisites.  Do not hide them inside a generic wrapper.

8. If no theorem exists, report the missing pre-TraceData selected
   source-no-defect/global-formula owner or propose an API split that constructs
   full read-off before TraceFrontEndData.
```

Current execution result for steps 1-3:

```text
Found and proved:
  scalar-equality-to-balance algebra bridge
  no-defect/global-formula-to-balance algebra bridge
  scalar-equality-to-no-defect/global-formula algebra bridge
  restriction-rows-to-scalar-equality algebra bridge
  restriction-row constructor from selected common tuple, selected
    finite-prime stabilization, package exact support, pole stability, and
    selected archimedeanContributionMatches
  archimedeanContributionMatches wrapper from the scoped balance Prop

Did not find an accepted pre-TraceData selected scoped archimedean contribution
balance producer.

Rejected producers found in the current tree:
  NormalizedSourceTraceReadOffEqualityRows
  normalizedRestrictedToFullQWFromTheorems
  normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems
  normalized_seed_source_no_defect_trace_eq_global_formula_of_common_data

Current exact socket:
  normalizedSelectedScopedArchimedeanContributionMatchesForRestrictionFromTheorems

Current active reduction:
  normalizedSelectedSourceNoDefectGlobalFormulaFromTheorems
    -> source_no_defect_global_formula_of_scalar_equality
    -> normalizedSelectedQWLambdaEqualsQWFromTheorems
    -> source_qw_lambda_eq_qw_of_qw_lambda_restriction
    -> normalizedSelectedQWLambdaRestrictionRowsFromTheorems
    -> normalizedSelectedArchimedeanContributionMatchesForRestrictionFromTheorems
    -> normalizedSelectedScopedArchimedeanContributionMatchesForRestrictionFromTheorems
```

2026-07-07 drilldown handoff after "do not build":

```text
AI session handoff:
  status: rejected as closure / analysis-only

  files changed:
    MEMORY.md
    plan/04B_2026-07-07_D1_full_readoff_arch_balance_lane_plan.md

  declarations changed:
    none in this pass

  current tempting but rejected path:
    normalizedSelectedQWLambdaRestrictionRowsFromTheorems
      -> Source.SourceObjectConcreteCommonData.restricted_formula_eq_global_formula_of_concrete_common
      -> normalizedConcreteCommonFromTheorems
      -> SourceObjectConcreteCommonData.commonFinitePrimeArithmeticSourceData_scopedArchimedeanContributionBalance
      -> CommonFinitePrimeArithmeticSourceData.scopedArchimedeanContributionBalance
      -> Root 2/common finite-prime source-data field

  why rejected:
    restricted_formula_eq_global_formula_of_concrete_common is not a lower
    proof of selected archimedean balance.  It reads the same scoped balance
    field from SourceObjectConcreteCommonData, and that field is supplied by
    CommonFinitePrimeArithmeticSourceData rather than derived from support,
    atoms, no-bulk, or finite-part normal form.

  first-principles shape:
    ScopedArchimedeanContributionBalance expands to:

      archimedeanTerm(convolutionStar g g)
        + polePairing(g)
        - restricted finite-prime evaluator

      =

      poleFunctional(convolutionStar g g)
        - archimedeanTerm(convolutionStar g g)
        - global finite-prime evaluator

    With pole normalization this is equivalent to:

      restrictedFinite - globalFinite = 2 * archimedeanTerm

    Finite-prime support stabilization by itself cannot supply this; it does
    not account for the archimedean correction.

  rejected branches checked in this drilldown:
    - Package.lean qwLambda = qw theorems: all still require an archimedean
      contribution balance input.
    - S2B1 no-bulk rows: store no-extra-bulk Props, not this numeric balance.
    - S2B1 finite-part normal form: proves actualFinitePart = normalizedFinitePart
      and subtractedFinitePart = 0 for scalar slots, but does not connect those
      slots to restrictedFinite - globalFinite = 2 * archimedeanTerm.
    - RestrictedToFullAsymptoticRows: stores archimedeanContributionAtLarge as
      an input row, so using it here is a later-route loop.
    - TraceFrontEndData/read-off rows: downstream and circular for 04B.

  remaining blocker:
    prove a real lower selected theorem:

      restricted finite-prime contribution - global finite-prime contribution
        =
      2 * selected archimedean contribution

    or repair the route API so the selected full read-off consumes a more
    precise selected owner and does not demand generic selected qwLambda = qw.

  WSL build:
    not run; Peter explicitly said to stop building and drill to closure first.

  focused axiom audit:
    not run for the same reason.

  next safe action:
    Do not keep the concrete-common readback as accepted 04B progress.  Either
    revert/isolate that proof path back to an explicit missing socket, or add a
    real lower theorem/API that owns the archimedean correction before
    TraceFrontEndData and without Root 2/common finite-prime source-data fields.
```

Original search route kept for reference:

```text
1. Search for a pre-TraceData archimedean-balance theorem for the active
   selected package, fixed S-test, lambda, and arithmetic package.

2. Reject any theorem whose type mentions normalizedTraceDataFromTheorems or a
   route package built after normalizedTraceDataFromTheorems.

3. If a lower theorem exists, rewire:
     normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems

4. If the lower theorem needs support and atom stabilization rows, keep those as
   explicit selected prerequisites.  Do not hide them inside a generic wrapper.

5. If no theorem exists, report the missing pre-TraceData arch-balance owner or
   propose an API split that constructs full read-off before TraceFrontEndData.
```

Allowed files for this lane:

```text
Read/write:
  ConnesWeilRH/Route/Bridge.lean
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean
  plan/04B_2026-07-07_D1_full_readoff_arch_balance_lane_plan.md

Read-only unless the coordinator approves:
  ConnesWeilRH/Source/S2B1TraceScale.lean
  ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean
  ConnesWeilRH/Source/CCM25Concrete/Package.lean
  ConnesWeilRH/Route/TraceFrontEnd.lean
```

Forbidden files for this lane:

```text
plan/04A_2026-07-07_D1_selected_restricted_evaluator_lane_plan.md
ConnesWeilRH/Route/RouteTheorem.lean
```


## 7. Static Rejection Scans

Run before claiming progress:

```text
rg -n "normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems|normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems|normalizedCommonFinitePrimeArithmeticSourceDataFromTheorems|normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems|normalizedRestrictedToFullQWFromTheorems|normalizedRestrictedToFullAsymptoticRowsInputFromTheorems|normalizedRestrictedToFullCurrentCutoffBindingFromTheorems|normalizedTraceDataFromTheorems" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route/Bridge.lean

rg -n "source_archimedean_balance_rows_of_scalar_equality|source_scoped_archimedean_contribution_matches_of_scalar_equality|NormalizedSourceTraceReadOffEqualityRows|normalizedTraceReadOffEqualityRowsFromTheorems|scalarEquality" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route/Bridge.lean ConnesWeilRH/Source/ObjectTheoremBasePackage.lean

rg -n "source_archimedean_balance_rows_of_no_defect_global_formula|source_scalar_equality_of_no_defect_global_formula|normalized_seed_source_no_defect_trace_eq_global_formula|common_data_scoped_archimedean_contribution_balance" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route/Bridge.lean ConnesWeilRH/Source/S2B1TraceScale.lean

rg -n "scopedBalance\\s*:=|Set\\.univ|\\bTrue\\b|by sorry|\\bsorry\\b" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route/Bridge.lean ConnesWeilRH/Source/CCM25Concrete -g "*.lean"
```

The scan rejects obvious regressions.  Source review still decides whether a
candidate theorem is pre-TraceData.


## 8. WSL Build Gate

Run from Windows PowerShell:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Dev.UnconditionalSkeleton'
```


## 9. Focused Axiom Audit

Use a scratch file:

```lean
import ConnesWeilRH.Dev.UnconditionalSkeleton

#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedQWLambdaRestrictionRowsFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedArchimedeanContributionMatchesForRestrictionFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedScopedArchimedeanContributionMatchesForRestrictionFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedQWLambdaEqualsQWFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedSourceNoDefectGlobalFormulaFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceDataFromTheorems
```

Also audit the new algebra bridge:

```lean
import ConnesWeilRH.Route.Bridge

#print axioms ConnesWeilRH.Route.source_scoped_archimedean_contribution_matches_of_scalar_equality
#print axioms ConnesWeilRH.Route.source_archimedean_balance_rows_of_scalar_equality
#print axioms ConnesWeilRH.Route.source_scalar_equality_of_no_defect_global_formula
#print axioms ConnesWeilRH.Route.source_no_defect_global_formula_of_scalar_equality
#print axioms ConnesWeilRH.Route.source_qw_lambda_eq_qw_of_qw_lambda_restriction
#print axioms ConnesWeilRH.Route.source_archimedean_balance_rows_of_no_defect_global_formula
```

Accepted output:

```text
[propext, Classical.choice, Quot.sound]
```

Rejected output:

```text
sorryAx
project-local axiom
Root 2 finite-prime source data
TraceData readback
later restricted-to-full bridge contract
raw scopedBalance wrapper
```


## 10. Final Acceptance Text

Use this shape:

```text
AI session handoff:
  status: accepted / partial / blocked / rejected / analysis-only
  files changed:
  declarations changed:
  old paths removed:
    normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems no longer
    reads normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems.
  remaining blockers:
  WSL build:
  focused axiom audit:
  next safe action:
```


## 11. 2026-07-07 Active-Path Root Exposure

Result:

```text
Build-good, audit-bad for proof closure.
```

Code change:

```text
normalizedSelectedQWLambdaRestrictionRowsFromTheorems no longer calls:
  Source.SourceObjectConcreteCommonData.restricted_formula_eq_global_formula_of_concrete_common

The selected 04B path now factors through:
  normalizedSelectedScopedArchimedeanBalanceInputFromTheorems
    -> normalizedSelectedScopedArchimedeanContributionMatchesForRestrictionFromTheorems
    -> normalizedSelectedArchimedeanContributionMatchesForRestrictionFromTheorems
    -> normalizedSelectedQWLambdaRestrictionRowsFromTheorems
    -> normalizedSelectedQWLambdaEqualsQWFromTheorems
```

This is not proof closure.  The remaining selected scoped-balance root is:

```text
normalizedSelectedScopedArchimedeanBalanceInputFromTheorems
```

The theorem still to prove is:

```text
SourceScopedArchimedeanContributionMatchesForRestriction
  (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
  normalizedSourceBackedFixedSTestFromTheorems
  normalizedTraceLambdaInputFromTheorems.lambda
  normalizedTraceCCM25ArithmeticPackageFromTheorems
```

WSL build:

```text
lake build ConnesWeilRH.Dev.UnconditionalSkeleton ConnesWeilRH.Route.RouteTheorem
passed under /tmp/connes-weil-rh-lake.lock.
```

Focused axiom audit:

```text
normalizedSelectedScopedArchimedeanBalanceInputFromTheorems
normalizedSelectedScopedArchimedeanContributionMatchesForRestrictionFromTheorems
normalizedSelectedArchimedeanContributionMatchesForRestrictionFromTheorems
normalizedSelectedQWLambdaRestrictionRowsFromTheorems
normalizedSelectedQWLambdaEqualsQWFromTheorems
normalizedSelectedSourceNoDefectGlobalFormulaFromTheorems
normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems
normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
normalizedTraceDataFromTheorems
normalizedRouteCertificateFromTheorems

all return:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

Rejected as closure:

```text
Do not prove the new selected scoped-balance root from:
  Source.common_data_scoped_archimedean_contribution_balance
  CommonFinitePrimeArithmeticSourceData.scopedArchimedeanContributionBalance
  Root 2 finite-prime source data
  TraceData readback
  later restricted-to-full contracts
  a raw scopedBalance field
```
