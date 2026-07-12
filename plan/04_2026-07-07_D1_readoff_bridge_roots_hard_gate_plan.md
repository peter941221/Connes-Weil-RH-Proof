# D1 Read-Off And Bridge Roots Hard Gate Plan

Date: 2026-07-07

Status: executable plan only.  This file is not Lean progress.  The lane counts
as solved only after the implementation passes the build and axiom gates below.


## 1. Result First

Current result:

```text
Good for the active route API cut.  Not a global no-sorry RH proof.
```

Route API execution correction, 2026-07-07:

```text
Result:
  Good for the active route API cut.  Not a global no-sorry RH proof.

What changed:
  The active normalized route certificate no longer consumes
  TraceFrontEndData / SourceTraceReadOffData as its route-facing trace carrier.
  It now consumes the slim route-only carrier:

    SourceRouteTraceData

  SourceRouteTraceData keeps only the fields used by the final route:
    archimedean test
    Hilbert-Schmidt gate
    lambda and 1 < lambda
    selected CCM25 arithmetic package
    quotient compatibility
    fixed-S support-square transport
    positive trace nonnegativity

  It deliberately does not store:
    FullTraceReadOffBridgeContract
    RestrictedTraceReadOffBridgeContract
    RestrictedToFullQWBridgeContract

Active consumer rewired:
  normalizedRouteCertificateFromTheorems now prints as:

    sourceBackedTest := normalizedSourceBackedFixedSTestFromTheorems
    ledgers := normalizedRouteLedgersForRouteFromTheorems
    bridge :=
      route_bridge_certificate_of_sign_defect_classification
        normalizedRouteTraceDataFromTheorems
        normalizedSignDefectClassificationForRouteFromTheorems
        normalizedRouteFinalSignNonpositiveFromTheorems

  It no longer calls:
    route_certificate_of_normalized_certificate_boundary_rows_ledger_package_source_backed_cutoff
    normalizedTraceDataFromTheorems
    normalizedRestrictedToFullAsymptoticRowsInputFromTheorems
    normalizedTraceFullReadOffBridgeInputFromTheorems
    normalizedTraceRestrictedReadOffBridgeInputFromTheorems
    normalizedSelectedSourceCoreTraceQWLambdaCalibrationInputFromTheorems
    normalizedSelectedFinitePrimeIndexDifferenceInputFromTheorems
    normalizedRestrictedToFullFinitePrimeIndexDifferenceRowsFromTheorems

Route API changed:
  RouteBridgeCertificate.sourceTraceReadOff :
    SourceRouteTraceData inputs g

  RouteBridgeCertificate no longer has:
    restrictedToFullQWBridge

  final_connes_weil_rh no longer reads:
    restricted_to_full_qw_bridge_of_route_bridge_certificate

Build:
  WSL Ubuntu-24.04 ext4 mirror, under /tmp/connes-weil-rh-lake.lock:

    lake build ConnesWeilRH.Route.Theorem1 \
      ConnesWeilRH.Route.Exhaustion \
      ConnesWeilRH.Route.Bridge \
      ConnesWeilRH.Route.RouteTheorem \
      ConnesWeilRH.Dev.UnconditionalSkeleton

  passed.

  Unified build:

    lake build ConnesWeilRH

  passed.

Focused audit:
  Import-facing #print axioms still returns:
    [propext, sorryAx, Classical.choice, Quot.sound]

  for normalizedRouteCertificateFromTheorems and final no-argument RH outlets.
  The remaining sorryAx comes from upstream source/package/fixed-test/arithmetic
  roots such as normalizedSourceObjectPackageFromTheorems,
  normalizedSourceBackedFixedSTestFromTheorems,
  normalizedTraceCCM25ArithmeticPackageFromTheorems,
  normalizedTraceQuotientCompatibilityInputFromTheorems, and
  normalizedTraceSupportSquareTransportInputFromTheorems.  It is not accepted
  as final RH closure.

Acceptance interpretation:
  04 read-off / restricted-to-full bridge roots are no longer on the active
  normalizedRouteCertificateFromTheorems consumer chain.  They remain as
  compatibility/audit declarations only.

  Do not later reintroduce TraceFrontEndData, SourceTraceReadOffData,
  FullTraceReadOffBridgeContract, RestrictedTraceReadOffBridgeContract, or
  RestrictedToFullQWBridgeContract as required inputs to the active final route
  certificate unless the route theorem itself semantically consumes those
  proofs.
```

Historical rejected reason before this correction:

```text
The current active path still lets D1 read-off / bridge roots stop at:
  - `sorry`;
  - forall row providers;
  - primitive Prop bridge fields;
  - circular readbacks from data built with the same equality being proved.
```

Complete result required by this plan:

```text
Good only if all four read-off / bridge slice roots below are removed from the
active RH route:

  Slice root A, S2B1 trace-package remainders:
    normalizedCoreS2B1TracePackageRemaindersFromTheorems

  Slice root B, S2B1 actual scalar identification:
    normalizedCoreS2B1ActualScalarIdentificationFromTheorems

  Slice root C, source-object bridge read-off rows:
    normalizedSourceObjectBridgeReadOffRowsInputFromTheorems

  Slice root D, scalar common-test bridge rows:
    normalizedSourceObjectScalarCommonTestBridgeRowsProviderFromTheorems

and the active route certificate consumes selected package / fixed front end /
trace data / lambda evidence, not a forall source-object row family.
```

This plan is a reliable RH step only in this sense:

```text
_root_.RiemannHypothesis
  <- normalizedRouteCertificateFromTheorems
  <- selected TraceFrontEndData for the normalized source package
  <- selected full/restricted read-off bridges and scalar identification
  <- selected no-bulk, restricted-to-full, and fixed-tuple owners
  <- no active fallback to Root 1 / Root 2 or theorem-base scalar readback
```

It is not a final RH plan.  It closes this read-off / bridge slice so later D1
roots cannot hide behind the same row-provider black boxes.

Root 1 and Root 2 are not to be proved in this plan.  They are rejected
fallback paths for 04:

```text
04 D1 read-off / bridge bypass
|
+-- A. selected route-facing path that must stay active
|   |
|   +-- selected full read-off equality
|   +-- selected restricted read-off equality
|   +-- TraceFrontEndData.TraceScaleNoExtraBulkScalarData
|   +-- RouteLedgerClearingData
|
+-- B. paths that must not re-enter the active consumer chain
|   |
|   +-- theorem-base scalar readback
|   |   |
|   |   +-- normalizedActualScalarIdentificationFromTheoremBasePackage
|   |   +-- Source.normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage
|   |   +-- base.s2b1NormalizedSeedSupportSquareMainTermEqualsQWLambda
|   |
|   +-- Root 1
|   |   |
|   |   +-- normalizedCoreSourceWeilFormDataFromTheorems
|   |
|   +-- Root 2
|       |
|       +-- normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems
|
+-- C. current 04 code cut
|   |
|   +-- base/common data read from NormalizedSourceObjectCoreTheoremBaseData
|   +-- selected objects read from NormalizedSourceObjectObjectData
|   +-- selected equality now factors through:
|   |   |
|   |   +-- normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
|   |   +-- Source.normalizedSeedSupportSquareQWLambdaReadOffOfScalarIdentification
|   |   +-- normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
|   |
|   +-- compatibility theorem-base input remains non-authoritative
|
+-- D. hard gate
    |
    +-- WSL build under /tmp/connes-weil-rh-lake.lock
    +-- focused selected-path #print axioms
    +-- old-path rejection scan
```

Execution update, 2026-07-07:

```text
Partial only.

Build-good:
  lake build ConnesWeilRH.Route.RouteTheorem
    ConnesWeilRH.Dev.UnconditionalSkeleton
  passed in the WSL ext4 mirror under /tmp/connes-weil-rh-lake.lock.

Route API progress:
  route_certificate_of_normalized_certificate_boundary_rows_current_cutoff_binding
  now consumes the incoming selected TraceFrontEndData directly and takes an
  explicit selected trace-scale ownership proof.  Its focused axiom audit is:
    [propext, Classical.choice, Quot.sound]

Still rejected as solved:
  normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
    -> normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
    -> normalizedActualScalarIdentificationFromTheoremBasePackage
    -> Source.normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage

  Therefore the selected TraceFrontEndData used by
  normalizedRouteCertificateFromTheorems still reaches theorem-base scalar
  readback.  Root 1 / Root 2 are not closed and are not supposed to be proved
  here; the remaining 04 cut is the selected equality producer.
```

Post-correction rerun, 2026-07-07:

```text
Peter correction applied:
  Root 1 / Root 2 are bypass targets for 04, not proof targets.

WSL build:
  lake build ConnesWeilRH.Route.RouteTheorem
    ConnesWeilRH.Dev.UnconditionalSkeleton
  passed under /tmp/connes-weil-rh-lake.lock.

Focused axiom audit:
  route_certificate_of_normalized_certificate_boundary_rows_current_cutoff_binding
    [propext, Classical.choice, Quot.sound]

  normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
  normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
  normalizedTraceDataFromTheorems
  normalizedRouteCertificateFromTheorems
    [propext, sorryAx, Classical.choice, Quot.sound]

Static rejection scan:
  The active selected restricted equality still reaches:
    normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
      -> normalizedActualScalarIdentificationFromTheoremBasePackage
      -> Source.normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage

  Existing alternatives are rejected for 04 closure:
    - SourceObjectTheoremBasePackage support-square/QW-lambda accessors
      are theorem-base accessors.
    - TraceScaleNoMissingBulkData / NoDefectQWLambdaTheoremData can read
      restricted equality back from SourceTraceReadOffData, but that is
      circular for proving the selected equality.
    - Root 1 / Root 2 are forbidden fallback paths for this plan.

Conclusion:
  Current code is build-good but 04 remains unsolved.  The next real cut is a
  non-circular selected support-square/QW-lambda equality owner/API for:
    selected source trace test
    selected fixed S-test
    selected lambda
  and it must not be built from theorem-base scalar readback, Root 1, Root 2,
  or SourceTraceReadOffData readback.
```

Selected restricted-evaluator cut, 2026-07-07:

```text
Partial progress, not closure.

Code change:
  normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems no
  longer calls:
    normalizedActualScalarIdentificationFromTheoremBasePackage
    Source.normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage

  The active selected row now factors through the exact lower obligation:
    normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
      : Source.NormalizedSeedRestrictedEvaluatorScalarIdentification ...

  Then it builds the selected support-square/QW-lambda source data with:
    Source.normalizedSeedSupportSquareQWLambdaReadOffOfScalarIdentification

  The selected full equality was also changed to derive:
    sourceNoDefectTrace = supportSquareTrace
      -> supportSquareTrace = QW_lambda
      -> QW_lambda = QW
  instead of calling the theorem-base no-defect/QW-lambda readback.

WSL build:
  lake build ConnesWeilRH.Dev.UnconditionalSkeleton
  passed under /tmp/connes-weil-rh-lake.lock.

Focused axiom audit:
  normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
  normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
  normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
  normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
  normalizedTraceDataFromTheorems
  normalizedRouteCertificateFromTheorems
    [propext, sorryAx, Classical.choice, Quot.sound]

Rejection scan:
  In the active selected row neighborhood, the old theorem-base scalar readback
  and Root 1 / Root 2 paths are no longer present.

Remaining blocker:
  The first 04 lower root is now explicit:
    normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems

  This must be proved from lower selected evaluator semantics.  Filling it from
  theorem-base scalar readback, Root 1, Root 2, or SourceTraceReadOffData
  readback is rejected.
```

Selected restricted-evaluator execution split, 2026-07-07:

```text
04 selected restricted evaluator
|
+-- closed locally in this split
|   |
|   +-- normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
|       |
|       +-- CC20 support-square read-off:
|       |     Source.normalizedSeedSupportSquareCC20ReadOffData
|       |
|       +-- selected fixed-tuple support-square/QW-lambda row:
|       |     normalizedS2B1FixedTupleSupportSquareQWLambdaRowFromTheorems
|       |
|       +-- CCM25 evaluator read-off:
|             Source.normalized_seed_ccm25_qw_lambda_source_evaluator_read_off
|
+-- explicitly not used
|   |
|   +-- Root 1:
|   |     normalizedCoreSourceWeilFormDataFromTheorems
|   |
|   +-- Root 2:
|   |     normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems
|   |
|   +-- theorem-base scalar readback:
|   |     normalizedActualScalarIdentificationFromTheoremBasePackage
|   |     Source.normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage
|   |
|   +-- circular TraceFrontEndData readback:
|         normalizedTraceDataFromTheorems
|         full_trace_read_off_of_source_trace_data
|         restricted_trace_read_off_of_source_trace_data
|
+-- still not full 04 closure until audited
    |
    +-- upstream source of:
          normalizedS2B1FixedTupleSupportSquareQWLambdaRowFromTheorems

Result meaning:
  This split removes the selected restricted-evaluator declaration's local
  `sorry` and keeps Root 1 / Root 2 bypassed.  It does not by itself prove full
  04 completion because the fixed-tuple support-square/QW-lambda row still has
  to be audited as an accepted selected producer rather than a disguised
  theorem-base row.
```

Decomposition tree for the next execution split, 2026-07-07:

```text
04 route-facing read-off bridge
|
+-- Tree A: selected restricted read-off equality
|   |
|   +-- current active proof:
|   |     normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
|   |       -> normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
|   |       -> normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
|   |       -> normalizedS2B1FixedTupleSupportSquareQWLambdaRowFromTheorems
|   |       -> normalizedBaseFromTheorems
|   |       -> normalizedSourceObjectCoreTheoremBaseDataFromTheorems
|   |
|   +-- what is already good:
|   |     normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
|   |       no longer calls theorem-base scalar readback directly.
|   |
|   +-- remaining rejected leaf:
|         normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
|           still proves the evaluator identity by importing the old fixed-tuple
|           support-square/QW-lambda row.
|
+-- Tree B: selected full read-off equality
|   |
|   +-- current active proof:
|   |     normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
|   |       -> selected sourceNoDefect/supportSquare equality
|   |       -> normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
|   |       -> Source.common_data_scoped_archimedean_contribution_balance
|   |       -> normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems
|   |       -> normalizedSourceObjectCoreTheoremBaseDataFromTheorems.finitePrimeExact
|   |
|   +-- tempting but circular path:
|   |     normalizedRestrictedToFullQWFromTheorems
|   |       -> normalizedRestrictedToFullCurrentCutoffBindingFromTheorems
|   |       -> normalizedTraceDataFromTheorems
|   |       -> selected full/restricted read-off bridges
|   |
|   +-- remaining rejected leaf:
|         a pre-TraceData restricted-to-full / archimedean-balance owner is
|         needed.  The later `RestrictedToFullQWBridgeContract` cannot be used
|         to build the read-off equality that constructs the same TraceData.
|
+-- Tree C: scalar/common-test bridge
|   |
|   +-- current active improvement:
|   |     normalizedScalarSourceObjectCC20CommonTestBridgeInputFromTheorems
|   |       now builds the selected CC20/common-test bridge from the selected
|   |       scalar source-object package fields.
|   |
|   +-- old row provider to keep out of the active chain:
|         normalizedScalarSourceObjectCC20CommonTestBridgeRowsInputFromTheorems
|         normalizedSourceObjectScalarCommonTestBridgeRowsProviderFromTheorems
|
+-- Tree D: route consumer
    |
    +-- current active proof:
          normalizedRouteCertificateFromTheorems
            -> route_certificate_of_normalized_certificate_boundary_rows_ledger_package_source_backed_cutoff
            -> normalizedTraceDataFromTheorems

    +-- invariant:
          route certificate must keep consuming selected TraceFrontEndData.
          Do not widen it back to forall source-object bridge/read-off rows.
```

Execution rule from this tree:

```text
Do Tree A and Tree B as separate cuts.

Tree A target:
  replace the fixed-tuple/base-row dependency under
  normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems with a
  selected evaluator-scalar owner.

Tree B target:
  introduce a pre-TraceData restricted-to-full scalar equality owner, or prove
  that the current API is misfactored and must be split before full read-off can
  be non-circular.

Do not use:
  normalizedRestrictedToFullQWFromTheorems as the producer of
  normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull, because it is
  built after normalizedTraceDataFromTheorems.
```

Focused axiom audit after this split:

```text
WSL Ubuntu-24.04 ext4 mirror, under /tmp/connes-weil-rh-lake.lock:
  lake env lean /tmp/plan04_axioms.lean

Targets:
  normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
  normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
  normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
  normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
  normalizedTraceDataFromTheorems
  normalizedRouteCertificateFromTheorems

Result:
  [propext, sorryAx, Classical.choice, Quot.sound]

Meaning:
  rejected as solved.  Tree A and Tree B remain active.  The audit does not
  distinguish every upstream `sorry` by itself; use the source tree above to
  drive the next targeted cuts.
```

Tree B pre-TraceData witness cut, 2026-07-07:

```text
Build-good, not solved.

Code change:
  normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull no longer
  proves `QW_lambda = QW` by directly calling:

    Source.CCM25Concrete.Package.qw_lambda_eq_qw_of_scoped_archimedean_contribution
    Source.common_data_scoped_archimedean_contribution_balance

  Instead it now factors through a selected pre-TraceData witness:

    normalizedSelectedSourceCommonTestTupleFromTheorems
      -> normalizedSelectedRestrictedFinitePrimeSupportStabilizesFromTheorems
      -> normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems
      -> normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems
      -> scalar_equality_from_scoped_witness_components
      -> normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull

Why this matters:
  The selected full read-off equality is now produced before
  normalizedTraceDataFromTheorems.  It does not use the later
  normalizedRestrictedToFullQWFromTheorems contract, which would be circular.

WSL build:
  lake build ConnesWeilRH.Dev.UnconditionalSkeleton
  passed in the WSL ext4 mirror under /tmp/connes-weil-rh-lake.lock.

Focused axiom audit:
  normalizedSelectedSourceCommonTestTupleFromTheorems
  normalizedSelectedRestrictedFinitePrimeSupportStabilizesFromTheorems
  normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems
  normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
  normalizedTraceDataFromTheorems
  normalizedRouteCertificateFromTheorems

  all still return:
    [propext, sorryAx, Classical.choice, Quot.sound]

Remaining blocker:
  Tree B is no longer circular through TraceData, but it still inherits Dev
  `sorryAx` through its source package / finite-prime / fixed-test inputs.
  Tree A remains blocked by the selected evaluator-scalar owner.
```

Leaf audit / rejected alternatives, 2026-07-07:

```text
Rejected as solved.

New focused audit:
  normalizedCoreSourceWeilFormDataFromTheorems
  normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems
  normalizedSourceObjectCoreTheoremBaseDataFromTheorems
  normalizedBaseFromTheorems
  normalizedSourceObjectPackageFromTheorems
  normalizedFixedFrontEndFromTheorems
  normalizedSourceBackedFixedSTestFromTheorems
  normalizedTraceCCM25ArithmeticPackageFromTheorems
  normalizedTraceSelectedLegalityDataFromTheorems
  normalizedSelectedSourceCommonTestTupleFromTheorems
  normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems

  all return:
    [propext, sorryAx, Classical.choice, Quot.sound]

Clean comparison target:
  normalizedTraceLambdaInputFromTheorems
    [propext, Classical.choice, Quot.sound]

Meaning:
  04 is not blocked only by one local equality.  The selected route path still
  imports sorryAx through the large source package / fixed front end /
  arithmetic-package construction.  A local proof that merely avoids naming
  Root 1 / Root 2 in the final equality is insufficient if the selected object
  being consumed was built from those roots.

Tree A rejected alternative:
  Source.normalizedSeedMatchedRestrictedEvaluatorScalarIdentification is not an
  accepted replacement for
  normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems.
  It proves the evaluator identity for:

    normalizedSeedMatchedToCCM25Evaluator base W weilTest ccm25

  not for the active route seed:

    normalizedSeedFromTheorems

  Using it would change the selected route object/seed instead of proving the
  active selected equality.  That is an API/semantic-object replacement, not a
  local 04 cut.

Tree B rejected alternative:
  normalizedRestrictedToFullAsymptoticRowsInputFromTheorems and
  normalizedRestrictedToFullCurrentCutoffBindingFromTheorems are not allowed as
  producers for normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
  while their types or constructors consume normalizedTraceDataFromTheorems.

  Current circular shape:
    selected full equality
      -> selected full read-off bridge
      -> normalizedTraceDataFromTheorems
      -> normalizedRestrictedToFullAsymptoticRowsInputFromTheorems
      -> normalizedRestrictedToFullCurrentCutoffBindingFromTheorems
      -> restricted-to-full bridge/equality

Next valid split:
  04A:
    prove or reject a lower selected evaluator-scalar owner for the active
    normalizedSeedFromTheorems / selected source trace test / selected fixed
    S-test / selected lambda tuple.

  04B:
    prove or reject a pre-TraceData archimedean-balance owner that does not read
    normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems, Root 2,
    normalizedTraceDataFromTheorems, or a later RestrictedToFullQWBridgeContract.

  04C:
    if 04A/04B cannot be proved without changing selected objects, write the API
    split explicitly: the route currently requires a package whose construction
    is too broad for the selected equality being audited.
```


## 2. What Counts As Solved

Hard completion gate:

```text
old weak path:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1015-1023
    normalizedCoreS2B1RemainderRowsOutsideNoBulkFromTheorems := by sorry
    normalizedCoreS2B1TracePackageRemaindersFromTheorems := by sorry

  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1025-1076
    normalizedCoreS2B1ActualScalarIdentificationFromTheorems
      -> normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems
      -> normalizedCoreS2B1ActualScalarIdentificationFromTheorems

  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1568-1610
    normalizedSourceObjectBridgeReadOffRowsInputFromTheorems
      -> commonTestBridgeRows
      -> traceReadOffEqualityRows
      -> toBridgeReadOffData

  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1635-1646
    normalizedSourceObjectScalarCommonTestBridgeRowsProviderFromTheorems

  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2499-2583
    normalizedTraceReadOffEqualityRowsFromTheorems
      -> normalizedTraceFullReadOffEqualityInputFromTheorems
      -> normalizedTraceRestrictedReadOffEqualityInputFromTheorems

  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:3553-3569
    normalizedScalarSourceObjectCC20CommonTestBridgeRowsInputFromTheorems
      -> normalizedScalarSourceObjectCC20CommonTestBridgeInputFromTheorems

new semantic owner/API:
  Slice root A, S2B1 trace-package remainders:
    plan 03 accepted selected no-bulk / fixed-tuple source rows, used only
    after plan 03 passes its own build and axiom gate.

  Slice root B, S2B1 actual scalar identification:
    selected scalar / trace front-end API that proves only the selected
    route-facing equality needed by TraceFrontEndData.

    Root 1, Root 2, and
    Source.normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage
    are forbidden as active 04 producers.  They may remain only as
    compatibility or diagnostic declarations.

  Slice root C, source-object bridge read-off rows:
    selected route-facing read-off API:

      NormalizedSelectedSourceTraceReadOffEqualityInput
      normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
      normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple

    These declarations live in
      ConnesWeilRH/Dev/UnconditionalSkeleton.lean
    unless import cycles force the non-Dev theorem into
      ConnesWeilRH/Route/TraceFrontEnd.lean.

  Slice root D, scalar common-test bridge rows:
    selected scalar route-facing bridge API:

      NormalizedSelectedScalarCC20CommonTestBridgeInput
      normalizedSelectedScalarCC20TraceTestEqCommonTest
      normalizedScalarSourceObjectCrossObjectBridgeInputFromSelectedRows

    These declarations must be built from the selected scalar seed,
    normalized scalar remainders, and selected common test.  They must not read
    NormalizedScalarCC20CommonTestBridgeRows.

real consumer rewired:
  normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems
  normalizedCoreS2B1SupportSquareQWLambdaReadOffSourceDataFromTheorems
  normalizedTraceFullReadOffEqualityInputFromTheorems
  normalizedTraceRestrictedReadOffEqualityInputFromTheorems
  normalizedTraceFullReadOffBridgeInputFromTheorems
  normalizedTraceRestrictedReadOffBridgeInputFromTheorems
  normalizedTraceSourceReadOffDataFromParts
  normalizedTraceDataFromTheorems
  normalizedScalarSourceObjectCC20CommonTestBridgeInputFromTheorems
  normalizedScalarSourceObjectCrossObjectBridgeInputFromTheorems
  normalizedScalarSourceObjectPackageFromTheorems
  normalizedRouteCertificateFromTheorems

same-object alias / wrapper rejection scan:
  rg -n "normalizedCoreS2B1ActualScalarIdentificationFromTheorems|using normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems|normalizedSourceObjectBridgeReadOffRowsInputFromTheorems|normalizedSourceObjectScalarCommonTestBridgeRowsProviderFromTheorems|normalizedTraceReadOffEqualityRowsFromTheorems|normalizedScalarSourceObjectCC20CommonTestBridgeRowsInputFromTheorems|sourceTraceTestCompatibility\\s*:=|traceLegIsCommonTest\\s*:=|mellinLegIsCommonTest\\s*:=|fullTraceReadOffEquality\\s*:=\\s*normalizedTraceReadOffEqualityRowsFromTheorems|restrictedTraceReadOffEquality\\s*:=\\s*normalizedTraceReadOffEqualityRowsFromTheorems|full_trace_read_off_of_source_trace_data|restricted_trace_read_off_of_source_trace_data|Set\\.univ|\\bTrue\\b" ConnesWeilRH -g "*.lean"

smallest WSL build:
  lake build ConnesWeilRH.Source.S2B1TraceScale ConnesWeilRH.Source.ObjectExpandedRows
  lake build ConnesWeilRH.Route.TraceFrontEnd ConnesWeilRH.Route.RouteTheorem
  lake build ConnesWeilRH.Dev.UnconditionalSkeleton

focused axiom audit targets:
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreS2B1TracePackageRemaindersFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreS2B1ActualScalarIdentificationFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreS2B1SupportSquareQWLambdaReadOffSourceDataFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceFullReadOffEqualityInputFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceRestrictedReadOffEqualityInputFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceDataFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedScalarCC20TraceTestEqCommonTest
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedScalarSourceObjectCrossObjectBridgeInputFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedScalarSourceObjectPackageFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteCertificateFromTheorems

semantic sufficiency for next route/RH step:
  ConnesWeilRH/Route/RouteTheorem.lean:3177-3232 shows the active route
  certificate consumes one selected TraceFrontEndData for one selected package
  and fixed front end.  It does not need a forall source-object row provider.

  ConnesWeilRH/Route/TraceFrontEnd.lean:303-334 shows TraceFrontEndData needs
  one selected full read-off bridge and one selected restricted read-off
  bridge at one selected lambda.

  Closing this plan preserves the selected common test, source trace test,
  scalar seed, remainders, lambda, and CCM25 Weil symbols that flow into
  normalizedRouteCertificateFromTheorems.
```

Solved means all of the following are true:

```text
1. Slice root A is filled only after plan 03 supplies accepted no-bulk /
   fixed-tuple source rows.
2. Slice root B is producer-to-consumer.  The active selected proof does not
   call normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems, Root 1,
   Root 2, or the theorem-base scalar readback path.
3. Slice root C is no longer active.  Selected full/restricted read-off
   equality theorems feed the selected bridge inputs directly.
4. Slice root D is no longer active.  The scalar package path builds the
   selected CC20/common-test bridge from selected scalar objects, not from
   forall rows.
5. The old forall row providers may remain only as compatibility declarations.
6. The focused axiom audit for the selected path contains no sorryAx.
```


## 3. What Does Not Count

Rejected:

```text
- filling any root with `True`, `Set.univ`, a copied endpoint package, or a
  renamed raw Prop;
- proving slice root B from normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems;
- proving selected full/restricted read-off equality by first building
  normalizedTraceSourceReadOffDataFromParts and then reading back
  full_trace_read_off_of_source_trace_data or
  restricted_trace_read_off_of_source_trace_data;
- treating NormalizedSourceObjectBridgeReadOffConstructorInput,
  NormalizedSourceObjectBridgeReadOffData, NormalizedSourceTraceReadOffEqualityRows,
  or NormalizedScalarCC20CommonTestBridgeRows as lower semantic owners;
- copying sourceTraceTestCompatibility, traceLegIsCommonTest,
  mellinLegIsCommonTest, fullTraceReadOffEquality, or
  restrictedTraceReadOffEquality out of old row providers;
- leaving normalizedRouteCertificateFromTheorems on a path that reaches
  normalizedSourceObjectBridgeReadOffRowsInputFromTheorems or
  normalizedSourceObjectScalarCommonTestBridgeRowsProviderFromTheorems.
```

The dangerous circular shape is:

```text
equality needed to build TraceFrontEndData
  -> bridge built from that equality
  -> TraceFrontEndData built from the bridge
  -> equality read back from TraceFrontEndData
```

This plan accepts only:

```text
lower selected theorem
  -> selected equality
  -> selected bridge
  -> TraceFrontEndData
  -> route certificate
```


## 4. Current Evidence

Source evidence:

```text
ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:2513-2521
  NormalizedScalarCC20CommonTestBridgeRows stores three primitive Props.

ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:2571-2586
  NormalizedSourceTraceReadOffEqualityRows stores the full and restricted
  equalities directly as fields.

ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:2718-2768
  NormalizedSourceObjectBridgeReadOffData and
  NormalizedSourceObjectBridgeReadOffConstructorInput are forall row
  containers.  toBridgeReadOffData only projects fields.

ConnesWeilRH/Source/Objects.lean:143-146
  CommonTestInvolutionBridge stores primitive Props.

ConnesWeilRH/Source/Objects.lean:176-182
  CCM24CommonTestBridge stores primitive Props.

ConnesWeilRH/Source/Objects.lean:248-257
  CC20CommonTestBridge stores primitive Props plus half-density compatibility.

ConnesWeilRH/Source/ObjectExpandedRows.lean:2381-2403
  SourceObjectCrossObjectBridges still carries those bridge records into
  sourceObjectPackageOfData.
```

Dev evidence:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1025-1076
  Slice root B and its downstream read-off theorem currently call each other.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1568-1610
  Slice root C is the active source-object bridge/read-off row provider.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1731-1737
  normalizedSourceObjectTheoremBaseInputFromTheorems currently imports
  bridgeReadOff from normalizedSourceObjectBridgeReadOffDataFromTheorems.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2499-2583
  selected trace full/restricted equality inputs currently read old
  NormalizedSourceTraceReadOffEqualityRows.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:3553-3569
  scalar CC20/common-test bridge currently copies three primitive row fields.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4816-4830
  normalizedRouteCertificateFromTheorems consumes selected traceData and the
  selected normalized package path.
```

Positive producer evidence:

```text
ConnesWeilRH/Source/S2B1TraceScale.lean:973-993
  Source.normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage
  proves scalar identification from theorem-base support-square/QW rows.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2100-2113
  normalizedActualScalarIdentificationFromTheoremBasePackage already uses that
  producer direction on the source-object path.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2718-2736
  normalizedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems already derives
  the selected restricted QW lambda row from the selected theorem-base scalar
  identification path.
```

Route evidence:

```text
ConnesWeilRH/Route/TraceFrontEnd.lean:303-334
  TraceFrontEndData is selected data, not a forall row provider.

ConnesWeilRH/Route/TraceFrontEnd.lean:499-539
  sourceTraceReadOffDataOfTraceFrontParts builds selected source trace data
  from selected trace-front parts.

ConnesWeilRH/Route/TraceFrontEnd.lean:7153-7294
  normalized_scalar_trace_front_full_trace_equality_from_balance proves a full
  trace equality from restricted-to-full / archimedean balance, which is the
  required proof shape for selected full read-off equality.

ConnesWeilRH/Route/RouteTheorem.lean:3177-3232
  route_certificate_of_normalized_certificate_boundary_rows_ledger_package_source_backed_cutoff
  takes selected traceData, boundary, ledger, and current-cutoff/asymptotic rows.
```


## 5. First-Principles Dependency Chain

The active RH route needs one selected object chain:

```text
normalizedBaseFromTheorems
  -> normalizedCommonFromTheorems
  -> normalizedSeedFromTheorems
  -> normalizedRemaindersFromTheorems
  -> normalizedSourceObjectPackageFromTheorems
  -> normalizedFixedFrontEndFromTheorems
  -> normalizedTraceDataFromTheorems
  -> normalizedRouteCertificateFromTheorems
  -> cc20_source_rh_of_route_certificate
  -> _root_.RiemannHypothesis
```

The active proof does not need:

```text
forall commonTest
forall cc20Trace
forall scalarSeed
forall lambda
```

The route needs this selected tuple:

```text
commonTest:
  normalizedCommonFromTheorems.commonTest

cc20 trace test:
  normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest

scalar seed:
  normalizedScalarSeedFromTheorems

remainders:
  normalizedRemaindersFromTheorems
  normalizedScalarRemaindersFromTheorems

lambda:
  normalizedTraceLambdaInputFromTheorems.lambda
  normalizedTraceDataFromTheorems.lambda

Weil symbols:
  normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
```

So the implementation should narrow the active API to selected route objects:

```text
selected tuple
  -> selected theorem
  -> selected bridge / read-off data
  -> selected TraceFrontEndData
  -> route certificate
```


## 6. Implementation Route

### Phase 0: lock the prerequisite from plan 03

Before editing slice root A, verify plan 03 has accepted these declarations:

```text
normalizedCoreS2B1RemainderRowsOutsideNoBulkFromTheorems
normalizedS2B1NoBulkRowsFromTheorems
normalizedTraceFixedTupleRemainingRowsPackageFromTheorems
```

If plan 03 has not passed, slice root A remains blocked.  Do not fill
`normalizedCoreS2B1TracePackageRemaindersFromTheorems` from raw outside-no-bulk
rows.


### Phase 1: fix the selected restricted-evaluator owner

The current selected restricted equality has the right shape but the wrong
upstream source:

```text
normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
  -> normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
  -> normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
  -> normalizedS2B1FixedTupleSupportSquareQWLambdaRowFromTheorems
  -> normalizedBaseFromTheorems
  -> normalizedSourceObjectCoreTheoremBaseDataFromTheorems
```

Replace only the last three arrows.  The accepted producer must prove:

```text
Source.NormalizedSeedRestrictedEvaluatorScalarIdentification
  normalizedSeedFromTheorems
  (RouteInputs.ofExpandedSourcePackage
    normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
  normalizedRemaindersFromTheorems
  normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
  (normalizedSourceBackedFixedSTestFromTheorems).weilTest
  normalizedTraceCCM25ArithmeticPackageFromTheorems
```

It must not be produced from:

```text
normalizedS2B1FixedTupleSupportSquareQWLambdaRowFromTheorems
normalizedBaseFromTheorems.s2b1NormalizedSeedSupportSquareQWLambdaRow
Source.normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage
normalizedActualScalarIdentificationFromTheoremBasePackage
Root 1 / Root 2
SourceTraceReadOffData readback
Source.normalizedSeedMatchedRestrictedEvaluatorScalarIdentification
```

Reason for rejecting the matched-seed producer:

```text
normalizedSeedMatchedRestrictedEvaluatorScalarIdentification proves a theorem
for normalizedSeedMatchedToCCM25Evaluator ..., not for the active route seed
normalizedSeedFromTheorems.
```

If no such selected producer exists, record Tree A as blocked by a missing
lower selected evaluator-scalar theorem.  Do not replace it with a theorem-base
compatibility wrapper.


### Phase 2: fill trace package remainder only from accepted no-bulk rows

After plan 03 passes, build:

```text
normalizedCoreS2B1TracePackageRemaindersFromTheorems
```

from:

```text
normalizedCoreS2B1RemainderRowsOutsideNoBulkFromTheorems
accepted no-bulk row owner from plan 03
lambda := 2
hlambda := by norm_num
selected source trace test
selected common/weil test
```

The accepted shape is the same shape already used at
`ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2091-2099`, but with plan 03's
non-raw no-bulk owner behind the constructor.


### Phase 3: introduce selected read-off equality API

Add one selected input:

```lean
structure NormalizedSelectedSourceTraceReadOffEqualityInput where
  fullTraceReadOffEquality :
    FullTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      normalizedSourceBackedFixedSTestFromTheorems
  restrictedTraceReadOffEquality :
    RestrictedTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      normalizedSourceBackedFixedSTestFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda
```

Add two lower theorems:

```text
normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
  proves the restricted equality from:
    normalizedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems

normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
  proves the full equality from:
    normalizedRestrictedToFullCurrentCutoffBindingFromTheorems
    normalizedRestrictedToFullQWFromTheorems
    normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
    the selected archimedean / scalar balance rows used by
    normalized_scalar_trace_front_full_trace_equality_from_balance
```

These theorems must not call:

```text
normalizedTraceReadOffEqualityRowsFromTheorems
normalizedTraceSourceReadOffDataFromParts
full_trace_read_off_of_source_trace_data
restricted_trace_read_off_of_source_trace_data
```

Then rewire:

```text
normalizedTraceFullReadOffEqualityInputFromTheorems
normalizedTraceRestrictedReadOffEqualityInputFromTheorems
```

to read `NormalizedSelectedSourceTraceReadOffEqualityInput`.


### Phase 4: demote slice root C forall bridge/read-off rows

Keep old declarations only as compatibility, or delete them if no imported file
uses them:

```text
normalizedSourceObjectBridgeReadOffRowsInputFromTheorems
normalizedSourceObjectCommonTestBridgeRowsProviderFromTheorems
normalizedSourceTraceReadOffEqualityRowsProviderFromTheorems
normalizedSourceObjectBridgeReadOffConstructorInputFromTheorems
normalizedSourceObjectBridgeReadOffDataFromTheorems
```

The active route path must not use them.

If `normalizedSourceObjectTheoremBaseInputFromTheorems` still requires
`bridgeReadOff`, replace that field in the source API with a compatibility
option:

```text
Option A, preferred:
  split NormalizedSourceObjectTheoremBaseInput so the active route constructor
  does not require bridgeReadOff.

Option B, compatibility only:
  keep bridgeReadOff in a separate compatibility constructor that is not used
  by normalizedBaseFromTheorems, normalizedTraceDataFromTheorems, or
  normalizedRouteCertificateFromTheorems.
```

This is an API migration.  It is accepted because the current field is a
forall Prop row provider and the route needs only selected trace data.


### Phase 5: introduce selected scalar/common-test bridge API

Add:

```lean
structure NormalizedSelectedScalarCC20CommonTestBridgeInput where
  cc20TraceTest_eq_commonTest :
    Source.SourceObject.CC20CommonTestBridge
      (Source.SourceObjectExpandedRows.ccm25
        normalizedScalarSourceObjectBridgeRowsFromTheorems).weilSymbols
      normalizedCommonFromTheorems.commonTest
      normalizedScalarSourceObjectBridgeRowsFromTheorems.cc20Trace
```

Then prove:

```text
normalizedSelectedScalarCC20TraceTestEqCommonTest
```

from the selected scalar route objects:

```text
normalizedCommonFromTheorems.commonTest
normalizedScalarSeedFromTheorems
normalizedScalarRemaindersFromTheorems
normalizedScalarSourceObjectBridgeRowsFromTheorems.cc20Trace
normalizedScalarSourceObjectPackageFromTheorems
```

If this proof still needs primitive bridge rows, do not store them in a new
record.  Drill one layer lower and add the exact selected equality theorem
needed for `sourceTraceTestCompatibility`, `traceLegIsCommonTest`, and
`mellinLegIsCommonTest`.

Rewire:

```text
normalizedScalarSourceObjectCC20CommonTestBridgeInputFromTheorems
normalizedScalarSourceObjectCrossObjectBridgeInputFromTheorems
normalizedScalarBridgesFromTheorems
normalizedScalarSourceObjectPackageFromTheorems
```

so they no longer read:

```text
normalizedScalarSourceObjectCC20CommonTestBridgeRowsInputFromTheorems
normalizedSourceObjectScalarCommonTestBridgeRowsProviderFromTheorems
NormalizedScalarCC20CommonTestBridgeRows
```


### Phase 6: route integration

After phases 1-5, `normalizedTraceDataFromTheorems` must still be the selected
trace data consumed by:

```text
normalizedRouteCertificateFromTheorems
```

The route certificate call at
`ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4816-4830` should remain selected:

```text
normalizedBaseFromTheorems
normalizedConcreteCommonFromTheorems
normalizedCCM24FromTheorems
normalizedSeedFromTheorems
normalizedRemaindersFromTheorems
normalizedRhExitFromTheorems
normalizedBridgesFromTheorems
normalizedFixedDataFromTheorems
normalizedTraceDataFromTheorems
normalizedNoExtraBulkContractFromTheorems
normalizedRouteLedgerClearingInputDataFromTheorems
normalizedRestrictedToFullAsymptoticRowsInputFromTheorems
```

The only allowed bridge/read-off dependencies in that chain are selected
theorems from phases 3 and 5.


## 7. Static Rejection Scans

Run before acceptance:

```text
rg -n "\\bsorry\\b|\\badmit\\b|^\\s*(axiom|constant|opaque|unsafe)\\b" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

rg -n "normalizedCoreS2B1ActualScalarIdentificationFromTheorems|using normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems|normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems.*normalizedCoreS2B1ActualScalarIdentificationFromTheorems" ConnesWeilRH/Dev/UnconditionalSkeleton.lean

rg -n "normalizedTraceFullReadOffEqualityInputFromTheorems|normalizedTraceRestrictedReadOffEqualityInputFromTheorems|normalizedTraceReadOffEqualityRowsFromTheorems|full_trace_read_off_of_source_trace_data|restricted_trace_read_off_of_source_trace_data" ConnesWeilRH/Dev/UnconditionalSkeleton.lean

rg -n "normalizedSourceObjectBridgeReadOffRowsInputFromTheorems|normalizedSourceObjectScalarCommonTestBridgeRowsProviderFromTheorems|normalizedScalarSourceObjectCC20CommonTestBridgeRowsInputFromTheorems|sourceObjectCommonTestBridgeRows|sourceTraceReadOffEqualityRows|scalarCC20CommonTestBridgeRows|toBridgeReadOffData" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Source -g "*.lean"

rg -n "sourceTraceTestCompatibility\\s*:=\\s*(normalized.*rows|.*Rows)|traceLegIsCommonTest\\s*:=\\s*(normalized.*rows|.*Rows)|mellinLegIsCommonTest\\s*:=\\s*(normalized.*rows|.*Rows)|fullTraceReadOffEquality\\s*:=\\s*normalizedTraceReadOffEqualityRowsFromTheorems|restrictedTraceReadOffEquality\\s*:=\\s*normalizedTraceReadOffEqualityRowsFromTheorems|Set\\.univ|\\bTrue\\b" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

rg -n "normalizedRouteCertificateFromTheorems|route_certificate_of_normalized_certificate_boundary_rows_ledger_package_source_backed_cutoff|normalizedTraceDataFromTheorems|normalizedScalarSourceObjectCrossObjectBridgeInputFromTheorems" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route -g "*.lean"
```

The scans are rejection aids.  Acceptance still requires source review that
the selected theorems do not read the old row providers through another name.


## 8. WSL Build Gate

Run in WSL:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.S2B1TraceScale ConnesWeilRH.Source.ObjectExpandedRows'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Route.TraceFrontEnd ConnesWeilRH.Route.RouteTheorem'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Dev.UnconditionalSkeleton'
```

The route build is mandatory because this plan changes route-facing selected
trace data and scalar package construction.


## 9. Focused Axiom Audit

Use a temporary scratch file:

```lean
import ConnesWeilRH.Dev.UnconditionalSkeleton

#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreS2B1TracePackageRemaindersFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreS2B1ActualScalarIdentificationFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreS2B1SupportSquareQWLambdaReadOffSourceDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceFullReadOffEqualityInputFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceRestrictedReadOffEqualityInputFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedScalarCC20TraceTestEqCommonTest
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedScalarSourceObjectCrossObjectBridgeInputFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedScalarSourceObjectPackageFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteCertificateFromTheorems
```

Accepted output:

```text
[propext, Classical.choice, Quot.sound]
```

Rejected output:

```text
sorryAx
project-local axiom
old row-provider root used as semantic source
circular readback from selected trace data built with the same bridge
endpoint package projection used as semantic source
```


## 10. Final Acceptance Text

Use this exact acceptance shape after implementation:

```text
Result:
  Good / partial / rejected.

Old weak paths removed:
  normalizedCoreS2B1TracePackageRemaindersFromTheorems no longer uses raw
  outside-no-bulk rows.

  normalizedCoreS2B1ActualScalarIdentificationFromTheorems no longer calls
  normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems.

  normalizedTraceFullReadOffEqualityInputFromTheorems and
  normalizedTraceRestrictedReadOffEqualityInputFromTheorems no longer read
  normalizedTraceReadOffEqualityRowsFromTheorems.

  normalizedScalarSourceObjectCrossObjectBridgeInputFromTheorems no longer
  reads normalizedSourceObjectScalarCommonTestBridgeRowsProviderFromTheorems
  or NormalizedScalarCC20CommonTestBridgeRows.

New semantic/API path:
  selected restricted-evaluator scalar owner for the active route tuple;
  plan 03 accepted no-bulk/fixed-tuple row owner;
  selected restricted read-off equality from fixed-tuple QW lambda row;
  selected full read-off equality from restricted-to-full / archimedean balance;
  selected scalar CC20/common-test bridge from selected scalar objects.

Consumer rewires:
  normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems
  normalizedTraceFullReadOffBridgeInputFromTheorems
  normalizedTraceRestrictedReadOffBridgeInputFromTheorems
  normalizedTraceDataFromTheorems
  normalizedScalarSourceObjectCrossObjectBridgeInputFromTheorems
  normalizedScalarSourceObjectPackageFromTheorems
  normalizedRouteCertificateFromTheorems

Semantic sufficiency:
  The route certificate still receives the same selected package, fixed front
  end, trace data, lambda, source trace test, common test, scalar seed,
  remainders, and CCM25 Weil symbols.  The proof source is now selected lower
  data instead of forall row providers.

Build:
  Source, TraceFrontEnd, RouteTheorem, and Dev build gates pass in WSL.

Focused axiom audit:
  All targets in section 9 return only:
    [propext, Classical.choice, Quot.sound]

Remaining black box:
  None inside the four slice roots covered by this plan.  Any remaining
  CommonTestInvolutionBridge, CCM24CommonTestBridge, CC20CommonTestBridge,
  NormalizedSourceTraceReadOffEqualityRows, or
  NormalizedScalarCC20CommonTestBridgeRows declaration is compatibility-only
  and absent from the active normalizedRouteCertificateFromTheorems path.
```
