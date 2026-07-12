# D1 04C Selected Scoped Balance API Repair Plan

Date: 2026-07-07

Status: documentation-first execution plan. This file is not Lean progress.

AI session start:

```text
owner: Codex main session
cwd: C:\Projects\Connes-Weil-RH-Proof
lane: D1 04C selected scoped archimedean balance API repair
old weak path:
  selected QW_lambda = QW through concrete-common scoped balance,
  CommonFinitePrimeArithmeticSourceData.scopedArchimedeanContributionBalance,
  Root 2 finite-prime source data, TraceData readback, or later restricted-to-full
  bridge contracts
files allowed:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean
  ConnesWeilRH/Route/Bridge.lean
  ConnesWeilRH/Route/RouteTheorem.lean
  ConnesWeilRH/Route/TraceFrontEnd.lean
  plan/04C_2026-07-07_D1_selected_scoped_balance_api_repair_plan.md
files forbidden:
  no sibling 04C plan
  no wrapper that claims scoped balance as solved
  no Windows lake
smallest WSL build:
  lake build ConnesWeilRH.Dev.UnconditionalSkeleton ConnesWeilRH.Route.RouteTheorem
focused axiom audit:
  selected scoped-balance obligation, selected QW_lambda restriction/equality,
  selected full-read-off path, normalizedTraceDataFromTheorems
expected output:
  expose the selected scoped archimedean balance as an explicit route-facing
  obligation, or reject the API repair if it still hides Root 2
```


## 1. Result First

Current result:

```text
04C is needed. 04B found a real route/API factoring problem.
```

04C does not prove the selected scoped archimedean balance. It names that
balance as the next explicit lower obligation and removes the hidden Root 2
readback from the active selected route path.


## 2. What Counts As Solved

Solved for 04C means:

```text
old weak path removed or demoted:
  normalizedSelectedQWLambdaRestrictionRowsFromTheorems
    -> Source.SourceObjectConcreteCommonData.restricted_formula_eq_global_formula_of_concrete_common
    -> SourceObjectConcreteCommonData.commonFinitePrimeArithmeticSourceData_scopedArchimedeanContributionBalance
    -> CommonFinitePrimeArithmeticSourceData.scopedArchimedeanContributionBalance
    -> Root 2 / common finite-prime source-data field

new semantic owner/API:
  an explicitly named selected scoped-balance obligation, for example:
    NormalizedSelectedScopedArchimedeanBalanceInput
      scopedBalance :
        SourceScopedArchimedeanContributionMatchesForRestriction
          selectedInputs selectedG selectedLambda selectedPkg

real consumer rewired:
  normalizedSelectedQWLambdaRestrictionRowsFromTheorems
    -> selected scoped-balance obligation
    -> normalizedSelectedQWLambdaEqualsQWFromTheorems
    -> normalizedSelectedSourceNoDefectGlobalFormulaFromTheorems
    -> normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
    -> normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
    -> normalizedTraceDataFromTheorems

smallest WSL build:
  lake build ConnesWeilRH.Dev.UnconditionalSkeleton ConnesWeilRH.Route.RouteTheorem

focused axiom audit:
  no hidden Root 2 in the selected 04C path
  any remaining sorryAx is on the named selected scoped-balance obligation

semantic sufficiency:
  the route now asks for the actual selected balance it needs, instead of hiding
  that balance inside common finite-prime source data
```

04C success is API cleanup. It is not 04B mathematical closure.


## 3. What Does Not Count

These do not count as 04C success:

```text
- proving the selected balance from
  Source.SourceObjectConcreteCommonData.restricted_formula_eq_global_formula_of_concrete_common
- proving the selected balance from
  Source.common_data_scoped_archimedean_contribution_balance
- reading
  CommonFinitePrimeArithmeticSourceData.scopedArchimedeanContributionBalance
- reading Root 2:
  normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems
  normalizedCommonFinitePrimeArithmeticSourceDataFromTheorems
  normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems
- reading TraceData or read-off rows:
  normalizedTraceDataFromTheorems
  NormalizedSourceTraceReadOffEqualityRows
  normalizedTraceReadOffEqualityRowsFromTheorems
- using a later restricted-to-full/current-cutoff/asymptotic bridge to create
  the selected full-read-off equality that builds TraceFrontEndData
- naming a raw scopedBalance field as solved rather than as the remaining
  selected obligation
```


## 4. Current Evidence

Lean source evidence:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2691-2712
  normalizedSelectedQWLambdaRestrictionRowsFromTheorems currently fills the
  selected archimedean contribution match through:

    Source.SourceObjectConcreteCommonData.restricted_formula_eq_global_formula_of_concrete_common

ConnesWeilRH/Source/ObjectExpandedRows.lean:1998-2031
  restricted_formula_eq_global_formula_of_concrete_common proves the balance by
  reading:

    data.commonFinitePrimeArithmeticSourceData_scopedArchimedeanContributionBalance

ConnesWeilRH/Source/ObjectExpandedRows.lean:86-98
  SourceObjectConcreteCommonData stores that row as a field.

ConnesWeilRH/Source/ObjectExpandedRows.lean:208-217
  ofCanonicalFinitePrimeOwner passes:

    commonFinitePrimeArithmeticSourceData.scopedArchimedeanContributionBalance

ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean:438-455
  CommonFinitePrimeArithmeticSourceData stores:

    scopedArchimedeanContributionBalance

  as an input field.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:610-613
  normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems is a sorry
  root, so the current concrete-common path still reaches an old black box.
```

Route evidence:

```text
ConnesWeilRH/Route/Bridge.lean:1082-1090
  SourceScopedArchimedeanContributionMatchesForRestriction is exactly the
  selected scoped balance 04B needs.

ConnesWeilRH/Route/Bridge.lean:1469-1487
  SourceQWLambdaRestrictionRows already isolates archimedeanContributionMatches
  as one field beside finite-prime stabilization and exact support.

ConnesWeilRH/Route/Bridge.lean:1668-1697
  source_qw_lambda_eq_qw_of_qw_lambda_restriction is a clean algebraic bridge.

ConnesWeilRH/Route/RouteTheorem.lean:128-147
  normalizedScalarFullTraceArchimedeanBalanceOfQWLambdaRestriction consumes
  SourceQWLambdaIsRestrictionOfQW and derives the route-facing balance.
```


## 5. First-Principles Dependency Chain

The selected 04B equality expands to:

```text
archimedeanTerm(convolutionStar g g)
  + polePairing(g)
  - restrictedFinitePrimeScopedSum

=

poleFunctional(convolutionStar g g)
  - archimedeanTerm(convolutionStar g g)
  - globalFinitePrimeScopedSum
```

With pole normalization, this demands:

```text
restrictedFinitePrimeScopedSum - globalFinitePrimeScopedSum
  =
2 * archimedeanTerm(convolutionStar g g)
```

Finite-prime support stabilization can compare finite-prime supports and sums.
It does not provide the archimedean correction term. A proof that only uses
finite-prime support data cannot close this balance unless another theorem
supplies the archimedean contribution.


## 6. Implementation Route

Recommended fastest route:

```text
1. Introduce one selected obligation record in Dev or Route-facing Dev glue.

   Proposed name:
     NormalizedSelectedScopedArchimedeanBalanceInput

   Proposed field:
     scopedBalance :
       SourceScopedArchimedeanContributionMatchesForRestriction
         (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
         normalizedSourceBackedFixedSTestFromTheorems
         normalizedTraceLambdaInputFromTheorems.lambda
         normalizedTraceCCM25ArithmeticPackageFromTheorems

2. Add:

     normalizedSelectedScopedArchimedeanBalanceInputFromTheorems

   This may remain the named 04C obligation. Do not call it closure.

3. Rewire:

     normalizedSelectedQWLambdaRestrictionRowsFromTheorems

   so its `archimedeanContributionMatches` input comes from the selected
   obligation, not from `restricted_formula_eq_global_formula_of_concrete_common`.

4. Keep the existing algebraic downstream chain:

     source_qw_lambda_eq_qw_of_qw_lambda_restriction
       -> normalizedSelectedQWLambdaEqualsQWFromTheorems
       -> source_no_defect_global_formula_of_scalar_equality
       -> normalizedSelectedSourceNoDefectGlobalFormulaFromTheorems
       -> source_archimedean_balance_rows_of_no_defect_global_formula
       -> normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
       -> normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull

5. Static-scan the selected path for old weak producers.

6. Run the smallest WSL build and focused import-based axiom audit.
```


## 7. Static Rejection Scans

Run after implementation:

```text
rg -n "normalizedSelectedQWLambdaRestrictionRowsFromTheorems|restricted_formula_eq_global_formula_of_concrete_common|common_data_scoped_archimedean_contribution_balance|normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems|normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems|normalizedTraceDataFromTheorems|normalizedRestrictedToFullQWFromTheorems" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route/Bridge.lean ConnesWeilRH/Route/RouteTheorem.lean ConnesWeilRH/Route/TraceFrontEnd.lean
```

Expected result:

```text
normalizedSelectedQWLambdaRestrictionRowsFromTheorems must not call:
  restricted_formula_eq_global_formula_of_concrete_common
  common_data_scoped_archimedean_contribution_balance
  normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems
  normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems
  normalizedTraceDataFromTheorems
  normalizedRestrictedToFullQWFromTheorems
```


## 8. WSL Build Gate

Use the main WSL ext4 mirror and the shared lock:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Dev.UnconditionalSkeleton ConnesWeilRH.Route.RouteTheorem'
```

Do not run `lake` on Windows or from `/mnt/c`.


## 9. Focused Axiom Audit

Use an import-based scratch file, not direct file elaboration:

```lean
import ConnesWeilRH.Dev.UnconditionalSkeleton
import ConnesWeilRH.Route.RouteTheorem

#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedQWLambdaRestrictionRowsFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedQWLambdaEqualsQWFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedSourceNoDefectGlobalFormulaFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceDataFromTheorems
```

Expected result for 04C:

```text
The selected path may still contain sorryAx.

The remaining sorryAx must point to the named selected scoped-balance obligation,
not to Root 2, common finite-prime source data, TraceData readback, or a later
restricted-to-full bridge.
```


## 10. Final Acceptance Text

Use this wording if 04C lands:

```text
04C repaired the selected full-read-off API shape. The active selected
QW_lambda = QW route no longer hides the scoped archimedean balance inside
concrete-common finite-prime source data or Root 2.

This does not close 04B mathematically. The remaining lower obligation is the
selected scoped archimedean contribution balance:

  SourceScopedArchimedeanContributionMatchesForRestriction
    selectedInputs selectedG selectedLambda selectedPkg

Future work must prove that obligation from lower analytic data or change the
route theorem statement. Do not count the selected obligation record itself as
proof of the balance.
```

## 11. Route API Cut Execution Update

Date: 2026-07-07

```text
Result:
  Good for active route closure.  04C's selected scoped-balance obligation no
  longer blocks normalizedRouteCertificateFromTheorems because the active final
  certificate no longer requires TraceFrontEndData, SourceTraceReadOffData, or
  a restricted-to-full QW bridge.

New route-facing API:
  SourceRouteTraceData

  It carries only the final route trace facts:
    archimedeanTest
    hilbertSchmidtGate
    lambda / oneLtLambda
    ccm25ArithmeticPackage
    testAndQuotientCompatibility
    fixedSSupportSquareTransport
    positiveTraceNonnegative

Active consumer:
  normalizedRouteCertificateFromTheorems

  The printed body is:
    route_bridge_certificate_of_sign_defect_classification
      normalizedRouteTraceDataFromTheorems
      normalizedSignDefectClassificationForRouteFromTheorems
      normalizedRouteFinalSignNonpositiveFromTheorems

Old 04C / restricted-to-full paths demoted:
  normalizedTraceDataFromTheorems
  normalizedSelectedSourceCoreTraceQWLambdaCalibrationInputFromTheorems
  normalizedSelectedFinitePrimeIndexDifferenceInputFromTheorems
  normalizedRestrictedToFullFinitePrimeIndexDifferenceRowsFromTheorems
  normalizedRestrictedToFullAsymptoticRowsInputFromTheorems
  normalizedRestrictedToFullQWFromTheorems

Build:
  WSL Ubuntu-24.04 ext4 mirror, under /tmp/connes-weil-rh-lake.lock:
    lake build ConnesWeilRH.Route.Theorem1 \
      ConnesWeilRH.Route.Exhaustion \
      ConnesWeilRH.Route.Bridge \
      ConnesWeilRH.Route.RouteTheorem \
      ConnesWeilRH.Dev.UnconditionalSkeleton
  passed.

Focused audit:
  normalizedRouteCertificateFromTheorems still has:
    [propext, sorryAx, Classical.choice, Quot.sound]

  This is expected from upstream source/package/fixed-test/arithmetic roots.
  It is not evidence that 04C still blocks the active route.

Acceptance interpretation:
  The selected scoped-balance obligation remains a compatibility/local selected
  trace-data obligation.  It is not on the active final route certificate path.
```
