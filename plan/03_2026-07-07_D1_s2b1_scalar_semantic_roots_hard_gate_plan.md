# D1 S2B1 Scalar Semantic Roots Hard Gate Plan

Date: 2026-07-07

Status: execution plan.  No Lean progress is accepted until the build and
focused axiom gates in this file pass in the main WSL mirror.


## 1. Result First

This lane is not solved in the current tree.

Current code still lets the route certificate receive S2B1/scalar facts through
free Prop rows:

```text
Source fixed-tuple rows
  -> Dev NormalizedTrace*Input Prop records
  -> Route.TraceScaleNoExtraBulkSourceTermData Prop fields
  -> Route.TraceScaleNoExtraBulkContract
  -> normalizedRouteCertificateFromTheorems

Source NormalizedRouteLedgerRows Prop records
  -> Dev NormalizedRouteLedgerSourceInput
  -> RouteLedgerSemanticData
  -> normalizedRouteCertificateFromTheorems
```

That path cannot be a reliable step toward `_root_.RiemannHypothesis`, because
the proof route can still import the target S2B1 rows as caller-supplied Props.


## 2. Hard Completion Gate

The lane is solved only if all gates below pass.

```text
old weak path:
  Source.S2B1TraceScaleAnalyticExclusionConstructorInput.noExtraBulkConstructorInput
  Source.S2B1TraceScaleAnalyticExclusionConstructorInput.rankZeroModeConstructorInput
  Source.S2B1TraceScaleAnalyticExclusionConstructorInput.noStripRankPoleConstructorInput
  Source.S2B1TraceScaleAnalyticExclusionConstructorInput.endpointStripCdefConstructorInput
  Source.NormalizedRouteLedgerRows
  Route.TraceScaleNoExtraBulkSourceTermData.noBulkScaleTermOutsideLedger
  Route.TraceScaleNoExtraBulkSourceTermData.noHiddenFinitePartSubtraction
  Route.TraceScaleNoExtraBulkContract.noExtraBulkScaleTerm
  Route.S2B1RouteLedgerSemanticInput.rankKilled
  Route.S2B1RouteLedgerSemanticInput.poleKilled
  Route.S2B1RouteLedgerSemanticInput.cdefExhausts
  Dev normalizedCoreS2B1RemainingConstructorInputsFromTheorems
  Dev normalizedTracePositiveTraceDecompositionInputFromTheorems
  Dev normalizedTraceNoExtraBulkTermInputFromTheorems
  Dev normalizedTraceNoHiddenFinitePartInputFromTheorems
  Dev normalizedTraceNoExtraBulkScaleTermInputFromTheorems
  Dev normalizedRouteLedgerRowsInputFromTheorems
  Dev normalizedRouteLedgerSourceInputFromTheorems

new semantic owner/API:
  Source.CC20SelectedTraceLegalityData
  Source.CC20SelectedTraceReadOffData
  Source.S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
  Source.S2B1FinitePartSourceNormalFormData
  Route.TraceScalePositiveQWLambdaDecompositionData
  Route.TraceScaleBulkResidualData
  Route.TraceScaleFinitePartResidualData
  Route.TraceScaleNoExtraBulkScalarData
  Route.RouteLedgerClearingData

real consumer rewired:
  Source.SourceObjectTheoremBaseConstructorInput
  Source.SourceObjectTheoremBasePackage
  Source.SourceObjectTheoremBasePackage.s2b1SupportSquareQWLambdaReadOffSourceData
  Source.SourceObjectTheoremBasePackage.s2b1FinitePartSourceNormalFormData
  Route.TraceFrontEndData.no_extra_bulk_contract_of_source_term_data
  Route.TraceFrontEndData.no_extra_bulk_contract_of_trace_scale_no_missing_bulk
  Route.TraceFrontEndData.no_extra_bulk_contract_of_parts
  Route.SignDefect.route_ledger_semantic_data_of_source_backed_ledgers
  Route.SignDefect.S2B1RouteLedgerSemanticInput.toRouteLedgerSemanticData
  Dev normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems
  Dev normalizedNoExtraBulkSourceTermsFromTheorems
  Dev normalizedNoExtraBulkContractFromTheorems
  Dev normalizedRouteLedgerSemanticDataFromTheorems
  Dev normalizedRouteCertificateFromTheorems

old path removed or compatibility-only:
  Source package constructors no longer expose active fixed-tuple rank/pole/Cdef/no-bulk inputs.
  Route no-bulk constructors no longer accept noBulkScaleTermOutsideLedger : Prop.
  Route no-bulk constructors no longer accept noHiddenFinitePartSubtraction : Prop.
  Route ledger constructors no longer accept rankKilled/poleKilled/cdefExhausts from callers.
  Dev roots no longer copy NormalizedTrace*Input Prop rows into Route data.
  Dev roots no longer copy NormalizedRouteLedgerRows into RouteLedgers.

smallest WSL build:
  lake build ConnesWeilRH.Source.CC20Concrete.TraceScale ConnesWeilRH.Source.ObjectTheoremBasePackage
  lake build ConnesWeilRH.Source.ObjectExpandedRows ConnesWeilRH.Source.S2B1TraceScale
  lake build ConnesWeilRH.Route.TraceFrontEnd ConnesWeilRH.Route.SignDefect ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem
  lake build ConnesWeilRH.Dev.UnconditionalSkeleton

focused axiom audit targets:
  Source.CC20SelectedTraceLegalityData.selectedTraceClass
  Source.CC20SelectedTraceLegalityData.selectedCyclicLegal
  Source.CC20SelectedTraceReadOffData.positiveTrace_eq_qwLambda
  Source.SourceObjectTheoremBasePackage.s2b1SupportSquareQWLambdaReadOffSourceData
  Source.SourceObjectTheoremBasePackage.s2b1FinitePartSourceNormalFormData
  Route.TraceScalePositiveQWLambdaDecompositionData.positiveTrace_eq_qwLambda
  Route.TraceScaleBulkResidualData.residual_eq_zero
  Route.TraceScaleFinitePartResidualData.hidden_residual_eq_zero
  Route.TraceScaleNoExtraBulkScalarData.toSourceTermData
  Route.RouteLedgerClearingData.ofSourceBacked
  Route.RouteLedgerClearingData.toRouteLedgerSemanticData
  Dev normalizedTraceScalePositiveQWLambdaDecompositionDataFromTheorems
  Dev normalizedTraceScaleBulkResidualDataFromTheorems
  Dev normalizedTraceScaleFinitePartResidualDataFromTheorems
  Dev normalizedTraceScaleNoExtraBulkScalarDataFromTheorems
  Dev normalizedRouteLedgerClearingDataFromTheorems
  Dev normalizedNoExtraBulkContractFromTheorems
  Dev normalizedRouteLedgerSemanticDataFromTheorems
  Dev normalizedRouteCertificateFromTheorems

semantic sufficiency for next route/RH step:
  The route certificate must read a proof that the selected positive trace
  equals the selected QW_lambda term, plus zero proofs for the residual bulk and
  hidden finite-part terms, plus typed route ledger clearing.  A Prop named
  noExtraBulkScaleTerm does not prove those statements.  This lane closes only
  when the active certificate path consumes those typed owners.
```


## 3. Current Evidence

Use these source facts as the baseline.

```text
ConnesWeilRH/Basic.lean:150
  ArchimedeanTraceSymbols.TraceClassTemplateStatement is:
    hilbertSchmidtGate g -> traceClass g /\ cyclicLegal g

  It cannot prove hilbertSchmidtGate g from traceClass g and cyclicLegal g.
  Any plan or implementation that uses this implication backward is rejected.

ConnesWeilRH/Route/TraceFrontEnd.lean:873
  TraceScaleNoExtraBulkSourceTermData stores:
    positiveTraceDecomposesIntoQWLambdaRankPoleCdef : Prop
    noBulkScaleTermOutsideLedger : Prop
    noHiddenFinitePartSubtraction : Prop

ConnesWeilRH/Route/TraceFrontEnd.lean:944
  no_extra_bulk_contract_of_parts accepts noExtraBulkScaleTerm : Prop and
  copies it into all no-bulk fields.

ConnesWeilRH/Route/SignDefect.lean:521
  RouteLedgerSemanticData is a semantic-looking record, but it still indexes
  over caller-owned RouteLedgers.

ConnesWeilRH/Route/SignDefect.lean:608
  S2B1RouteLedgerSemanticInput stores:
    rankKilled : L.rankKilled
    poleKilled : L.poleKilled
    cdefExhausts : L.cdefExhausts

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1215
  normalizedCoreS2B1RemainingConstructorInputsFromTheorems is still a sorry
  root for rank/pole/Cdef/no-bulk constructor inputs.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:3922
  normalizedNoExtraBulkSourceTermsFromTheorems currently fills Route
  no-bulk fields from NormalizedTrace*Input Props.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4186
  normalizedRouteLedgerSemanticDataFromTheorems currently reaches ledger
  semantic data through the source ledger Prop path.

ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:2466
  SourceObjectTheoremBaseConstructorInput still stores
  S2B1TraceScaleAnalyticExclusionConstructorInput.

ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:3144
  s2b1NoExtraBulkConstructorInput still exports the old no-bulk constructor
  input from the Source theorem-base package.
```


## 4. RH Dependency Chain

The active route needs one scalar equality and two absence statements:

```text
selected positive trace
  = selected QW_lambda
    + rank contribution
    + pole contribution
    + endpoint Cdef contribution
    + bulk residual
    + hidden finite-part residual
```

The old path hides the last two residuals behind Prop names.

The executable path must expose the objects:

```text
selected source trace test
        |
        v
selected CC20 read-off
        |
        v
support-square / QW_lambda source scalar
        |
        v
positiveTrace = QW_lambda
        |
        +-----------------------------+
        |                             |
        v                             v
bulk residual = 0             hidden finite-part residual = 0
        |                             |
        +-------------+---------------+
                      |
                      v
TraceScaleNoExtraBulkScalarData
                      |
                      v
TraceScaleNoExtraBulkSourceTermData adapter
                      |
                      v
normalizedRouteCertificateFromTheorems
                      |
                      v
_root_.RiemannHypothesis route chain
```


## 5. Required Source API

Add `Source.CC20SelectedTraceLegalityData`.

Required fields:

```lean
structure CC20SelectedTraceLegalityData
    (A : ArchimedeanTraceSymbols) (archimedeanTest : A.Test) where
  selectedHilbertSchmidtGate : A.hilbertSchmidtGate archimedeanTest
  selectedTraceClass : A.traceClass archimedeanTest
  selectedCyclicLegal : A.cyclicLegal archimedeanTest
  selectedTraceClass_from_gate :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement A ->
      A.traceClass archimedeanTest
  selectedCyclicLegal_from_gate :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement A ->
      A.cyclicLegal archimedeanTest
```

Reason:

```text
TraceClassTemplateStatement only proves:
  hilbertSchmidtGate -> traceClass /\ cyclicLegal

The selected legality owner must either store selectedHilbertSchmidtGate or
come from a concrete seed where hilbertSchmidtGate is definitionally
traceClass /\ cyclicLegal.  It must not derive Hilbert gate from traceClass and
cyclicLegal.
```

Add `Source.CC20SelectedTraceReadOffData`.

Required fields:

```lean
structure CC20SelectedTraceReadOffData
    (A : ArchimedeanTraceSymbols) (W : WeilFormSymbols)
    (lambda : ℝ) (archimedeanTest : A.Test) (weilTest : TestFunction) where
  legality : CC20SelectedTraceLegalityData A archimedeanTest
  positiveTrace_eq_supportSquare :
    A.positiveTrace archimedeanTest = A.supportSquareTrace archimedeanTest
  supportSquare_qwLambda :
    S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
      A W lambda archimedeanTest weilTest
  positiveTrace_eq_qwLambda :
    A.positiveTrace archimedeanTest = W.qwLambda lambda weilTest weilTest
```

`positiveTrace_eq_qwLambda` must be proved by transitivity:

```text
positiveTrace = supportSquare
supportSquare = sourceRestrictedTraceScalar
sourceRestrictedTraceScalar = QW_lambda
```

It must not be a stored free Prop.


## 6. Required Source Package Migration

Change `SourceObjectTheoremBaseConstructorInput`.

Active fields after this plan:

```text
ccm24Model
ccm25Model
cc20TraceModel
s2b1NormalizedSeed
s2b1NormalizedSeedArchimedeanSymbolsEq
selectedTraceLegalityData
selectedTraceReadOffData
s2b1SupportSquareQWLambdaReadOffSourceData
s2b1FinitePartSourceNormalFormData
rhDefinitionBridge
cc20RHExitObjectPackage
```

Compatibility-only fields after migration:

```text
s2b1RemainderRowsOutsideNoBulk
s2b1TraceScaleAnalyticExclusionConstructorInput
```

Delete or demote these active accessors:

```text
SourceObjectTheoremBasePackage.s2b1RankZeroModeConstructorInput
SourceObjectTheoremBasePackage.s2b1NoStripRankPoleConstructorInput
SourceObjectTheoremBasePackage.s2b1EndpointStripCdefConstructorInput
SourceObjectTheoremBasePackage.s2b1NoExtraBulkConstructorInput
SourceObjectTheoremBasePackage.s2b1TraceScaleNoBulkRows
SourceObjectTheoremBasePackage.s2b1TraceScaleNoBulkStatement
```

If any active Dev or Route declaration still calls those accessors, reject the
batch.


## 7. Required Route Scalar Owners

Add `Route.TraceScalePositiveQWLambdaDecompositionData`.

Required content:

```lean
structure TraceScalePositiveQWLambdaDecompositionData
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (lambda : ℝ) where
  selectedReadOff :
    Source.CC20SelectedTraceReadOffData
      pkg.cc20Trace.archimedeanSymbols
      pkg.ccm25.weilSymbols
      lambda pkg.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest
  positiveTrace_eq_qwLambda :
    pkg.cc20Trace.archimedeanSymbols.positiveTrace
        pkg.cc20Trace.sourceTraceTest =
      pkg.ccm25.weilSymbols.qwLambda lambda
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest
```

Add `Route.TraceScaleBulkResidualData`.

The residual must be a real expression:

```lean
def TraceScaleBulkResidualExpression
    (positiveTrace qwlambda : ℝ) : ℝ :=
  positiveTrace - qwlambda
```

Required theorem:

```lean
theorem TraceScaleBulkResidualData.residual_eq_zero :
  bulkScaleResidual = 0
```

The proof must use `positiveTrace_eq_qwLambda` and `sub_self`.  It must not set
`bulkScaleResidual := 0` without an expression tying it to positive trace and
QW_lambda.

Add `Route.TraceScaleFinitePartResidualData`.

The residual must read:

```lean
sourceNormalForm.sourceScalars.sourceSubtractedFinitePartTerm
```

Required theorem:

```lean
theorem TraceScaleFinitePartResidualData.hidden_residual_eq_zero :
  hiddenFinitePartResidual = 0
```

The proof must use:

```text
Source.S2B1FinitePartSourceNormalFormData.noSubtractedFinitePartTermHolds
```

Add `Route.TraceScaleNoExtraBulkScalarData`.

It must store:

```text
same pkg
same fixedFront
same lambda
same sourceTraceTest
same weilTest
same selected read-off data
same finite-part source-normal-form data
bulk residual data
hidden finite-part residual data
```

Adapter:

```lean
def TraceScaleNoExtraBulkScalarData.toSourceTermData :
  TraceScaleNoExtraBulkSourceTermData pkg fixedFront lambda ccm25ArithmeticPackage
```

The adapter may fill old Prop fields only with:

```text
positiveTrace_eq_qwLambda
bulk residual = 0
hidden finite-part residual = 0
```

It must not accept any Prop argument.


## 8. Required Route Ledger Owner

Add concrete route statements:

```lean
def RouteRankKilledStatement
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  SourceRemainderNoStripProjectionSplit inputs g lambda ∧
    SourceNoExtraNoStripChannel inputs g lambda

def RoutePoleKilledStatement
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  SourceRemainderNoStripProjectionSplit inputs g lambda ∧
    SourceNoExtraNoStripChannel inputs g lambda

def RouteCdefExhaustsStatement
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  SourceProjectionOrderEndpointStripNormalForm inputs g lambda ∧
    WindowSupportContainment inputs g lambda ∧
      PostQSeriesTailBoundedComparison inputs g lambda
```

Add owner:

```lean
structure RouteLedgerClearingData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) where
  oneLtLambda : 1 < lambda
  sourcePositiveTraceRemainderOwnership :
    SourcePositiveTraceRemainderOwnership inputs g lambda
  rankKilledHolds :
    RouteRankKilledStatement inputs g lambda
  poleKilledHolds :
    RoutePoleKilledStatement inputs g lambda
  cdefExhaustsHolds :
    RouteCdefExhaustsStatement inputs g lambda
  postQBoundedComparison :
    SourceBackedPostQBoundedComparisonData inputs g lambda
```

Required producer:

```lean
def RouteLedgerClearingData.ofSourceBacked
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs)
    {lambda : ℝ} (hlambda : 1 < lambda) :
    RouteLedgerClearingData inputs g lambda
```

It must use existing lower route theorems:

```text
source_positive_trace_remainder_ownership_of_source_backed
source_remainder_no_strip_projection_split_of_source_backed
source_projection_order_endpoint_strip_normal_form_of_source_backed
window_support_containment_of_source_backed
post_q_series_tail_bounded_comparison_of_source_backed_data
```

Adapters:

```lean
def RouteLedgerClearingData.toRouteLedgers : RouteLedgers
def RouteLedgerClearingData.toRouteLedgerSemanticData :
  RouteLedgerSemanticData inputs g lambda data.toRouteLedgers
```

These adapters must not take `L.rankKilled`, `L.poleKilled`, or
`L.cdefExhausts` as inputs.


## 9. Required Dev Rewire

Delete or demote these roots from the active route path:

```text
normalizedCoreS2B1RemainingConstructorInputsFromTheorems
normalizedTracePositiveTraceDecompositionInputFromTheorems
normalizedTraceNoExtraBulkTermInputFromTheorems
normalizedTraceNoHiddenFinitePartInputFromTheorems
normalizedTraceNoExtraBulkScaleTermInputFromTheorems
normalizedRouteLedgerRowsInputFromTheorems
normalizedRouteLedgerSourceInputFromTheorems
```

Add source-order roots:

```text
normalizedCoreCC20SelectedTraceLegalityDataFromTheorems
normalizedCoreCC20SelectedTraceReadOffDataFromTheorems
normalizedCoreS2B1SupportSquareQWLambdaReadOffSourceDataFromTheorems
normalizedCoreS2B1FinitePartSourceNormalFormDataFromTheorems
normalizedSourceObjectScalarSelectedTraceReadOffDataFromTheorems
normalizedSourceObjectScalarFinitePartSourceNormalFormDataFromTheorems
```

Add route-order roots:

```text
normalizedTraceScalePositiveQWLambdaDecompositionDataFromTheorems
normalizedTraceScaleBulkResidualDataFromTheorems
normalizedTraceScaleFinitePartResidualDataFromTheorems
normalizedTraceScaleNoExtraBulkScalarDataFromTheorems
normalizedRouteLedgerClearingDataFromTheorems
```

Rewrite these declarations:

```text
normalizedNoExtraBulkSourceTermsFromTheorems
normalizedNoExtraBulkContractFromTheorems
normalizedRouteLedgerSemanticDataFromTheorems
normalizedRouteCertificateFromTheorems
```

They must call the new route-order roots.  They must not read:

```text
normalizedTraceFixedTupleRemainingRowsPackageFromTheorems
normalizedRouteLedgerRowsInputFromTheorems
normalizedRouteLedgerSourceInputFromTheorems
normalizedCoreS2B1RemainingConstructorInputsFromTheorems.noExtraBulkConstructorInput
```


## 10. Execution Order

Use this order.  Do not start with Dev skeleton rewiring.

```text
1. Add source selected-legality/read-off data.
   Build:
     lake build ConnesWeilRH.Source.CC20Concrete.TraceScale ConnesWeilRH.Source.ObjectTheoremBasePackage

2. Migrate SourceObjectTheoremBaseConstructorInput so active Source package
   fields expose only selected read-off, support-square/QW_lambda source data,
   and finite-part source-normal-form data.
   Build:
     lake build ConnesWeilRH.Source.ObjectTheoremBasePackage ConnesWeilRH.Source.ObjectExpandedRows

3. Add route scalar residual owners and adapters.
   Build:
     lake build ConnesWeilRH.Route.TraceFrontEnd

4. Add route ledger clearing owner and adapters.
   Build:
     lake build ConnesWeilRH.Route.SignDefect

5. Rewire Dev no-bulk and ledger roots to the new route-order roots.
   Build:
     lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem
     lake build ConnesWeilRH.Dev.UnconditionalSkeleton

6. Run the focused axiom audit in section 12.
```


## 11. Static Rejection Scans

Run before acceptance.

```text
rg -n "selectedHilbertSchmidtGate_of_traceClass_cyclicLegal|\\.mpr\\s*\\n\\s*⟨.*traceClass|TraceClassTemplateStatement.*mpr" ConnesWeilRH -g "*.lean"

rg -n "normalizedTraceFixedTupleRemainingRowsPackageFromTheorems|normalizedRouteLedgerRowsInputFromTheorems|normalizedRouteLedgerSourceInputFromTheorems|normalizedCoreS2B1RemainingConstructorInputsFromTheorems\\.noExtraBulkConstructorInput" ConnesWeilRH/Dev/UnconditionalSkeleton.lean

rg -n "noBulkScaleTermOutsideLedger\\s*:\\s*Prop|noHiddenFinitePartSubtraction\\s*:\\s*Prop|noExtraBulkScaleTerm\\s*:\\s*Prop|rankKilled\\s*:\\s*[^\\n]*L\\.rankKilled|poleKilled\\s*:\\s*[^\\n]*L\\.poleKilled|cdefExhausts\\s*:\\s*[^\\n]*L\\.cdefExhausts" ConnesWeilRH/Route ConnesWeilRH/Dev -g "*.lean"

rg -n "s2b1RankZeroModeConstructorInput|s2b1NoStripRankPoleConstructorInput|s2b1EndpointStripCdefConstructorInput|s2b1NoExtraBulkConstructorInput|s2b1TraceScaleNoBulkRows|s2b1TraceScaleNoBulkStatement" ConnesWeilRH/Source ConnesWeilRH/Route ConnesWeilRH/Dev -g "*.lean"

rg -n "Set\\.univ|\\bTrue\\b|sourceActualFinitePart\\s*:=\\s*0|sourceNormalizedFinitePart\\s*:=\\s*0|sourceSubtractedFinitePartTerm\\s*:=\\s*0|:=\\s*rfl" ConnesWeilRH/Source ConnesWeilRH/Route ConnesWeilRH/Dev -g "*.lean"

rg -n "\\bsorry\\b|\\badmit\\b|^\\s*(axiom|constant|opaque|unsafe)\\b" ConnesWeilRH/Source/ObjectTheoremBasePackage.lean ConnesWeilRH/Route/TraceFrontEnd.lean ConnesWeilRH/Route/SignDefect.lean ConnesWeilRH/Dev/UnconditionalSkeleton.lean
```

Expected result:

```text
Old names may remain only in compatibility declarations with no active Dev or
Route consumer.  The active path into normalizedRouteCertificateFromTheorems
must not call the old Prop roots.
```


## 12. Focused Axiom Audit

Use a temporary scratch file:

```lean
import ConnesWeilRH.Dev.UnconditionalSkeleton

#print axioms Source.CC20SelectedTraceLegalityData.selectedTraceClass
#print axioms Source.CC20SelectedTraceLegalityData.selectedCyclicLegal
#print axioms Source.CC20SelectedTraceReadOffData.positiveTrace_eq_qwLambda
#print axioms Source.SourceObjectTheoremBasePackage.s2b1SupportSquareQWLambdaReadOffSourceData
#print axioms Source.SourceObjectTheoremBasePackage.s2b1FinitePartSourceNormalFormData

#print axioms Route.TraceScalePositiveQWLambdaDecompositionData.positiveTrace_eq_qwLambda
#print axioms Route.TraceScaleBulkResidualData.residual_eq_zero
#print axioms Route.TraceScaleFinitePartResidualData.hidden_residual_eq_zero
#print axioms Route.TraceScaleNoExtraBulkScalarData.toSourceTermData
#print axioms Route.RouteLedgerClearingData.ofSourceBacked
#print axioms Route.RouteLedgerClearingData.toRouteLedgerSemanticData

#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceScalePositiveQWLambdaDecompositionDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceScaleBulkResidualDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceScaleFinitePartResidualDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceScaleNoExtraBulkScalarDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteLedgerClearingDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedNoExtraBulkContractFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteLedgerSemanticDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteCertificateFromTheorems
```

Accepted output for plan-owned declarations:

```text
[propext, Classical.choice, Quot.sound]
```

`normalizedRouteCertificateFromTheorems` may still show `sorryAx` only from D1
roots outside this plan.  Reject the batch if `sorryAx` enters through:

```text
selected trace legality/read-off
support-square/QW_lambda read-off
finite-part source-normal-form
bulk residual data
hidden finite-part residual data
no-extra-bulk scalar adapter
route ledger clearing data
route ledger semantic adapter
```


## 13. What Counts As彻底解决

This lane is completely solved only when the final acceptance text can state:

```text
Result:
  Good.  Plan 03 is solved for the active D1 S2B1/scalar route path.

Old weak paths removed:
  <exact declarations and grep evidence>

New source-order owners:
  <exact declarations and files>

New typed route owners:
  <exact declarations and files>

Consumer rewires:
  <exact Source / Route / Dev declarations>

Semantic preservation:
  same source object:
  same normalized seed:
  same selected sourceTraceTest:
  same lambda:
  same archimedeanTest:
  same weilTest:
  same SourceBackedFixedSTest:
  same finite-part source-normal-form data:
  same bounded-comparison owner:
  no route package back-projection into Source roots:

Build:
  <exact WSL commands and results>

Focused axiom audit:
  <target list and output>

Remaining D1 roots outside this plan:
  <exact declarations and why they are outside Plan 03>
```

If any old Prop row still feeds `normalizedRouteCertificateFromTheorems`, the
lane is not solved.


## 14. Rejection Rules

Reject the implementation if any item occurs.

```text
1. A new owner stores old primitive Prop fields under new names.
2. A proof uses TraceClassTemplateStatement backward to infer hilbertSchmidtGate.
3. A residual owner sets a residual to 0 by construction instead of proving a
   selected expression equals 0.
4. RouteLedgerClearingData accepts L.rankKilled, L.poleKilled, or
   L.cdefExhausts from a caller.
5. A Source package still exports fixed-tuple rank/pole/Cdef/no-bulk accessors
   on the active route-certificate path.
6. A Dev root constructs old records directly from NormalizedTrace*Input or
   NormalizedRouteLedgerRows.
7. Scalar rows and finite-part rows come from different source objects.
8. Any plan-owned focused audit target contains sorryAx.
9. The implementation uses True, Set.univ, x = x, rfl over the target row,
   zero scalar defaults, copied package rows, or endpoint package projections.
```


## 15. Why This Advances RH

The final RH proof cannot depend on a route certificate that imports the S2B1
scalar cancellation as a named Prop.  That only renames the missing theorem.

This plan advances the unconditional route because it changes the active
certificate input from:

```text
caller supplies noExtraBulkScaleTerm
```

to:

```text
selected trace read-off
  + support-square/QW_lambda equality
  + finite-part normal form
  + source-backed post-Q comparison
  + route ledger clearing
  -> no-extra-bulk source-term adapter
  -> route certificate
```

After this lane closes, any remaining `sorryAx` in
`normalizedRouteCertificateFromTheorems` must come from other D1 roots, not from
S2B1 scalar/no-bulk or route-ledger clearance.


## 16. 2026-07-08 Post-04 Handling Result

Result:
  Partial-good / route-active-good after 04.  The original Plan 03 hard gate is
  not fully satisfied as written, because the Dev-level Plan 03 declarations
  still inherit `sorryAx` from broader skeleton roots.  However, after the
  accepted 04 route API cut, the active final route certificate no longer goes
  through the old Plan 03 no-bulk/read-off/restricted-to-full Prop path.

What is good:
  The lower Source and Route semantic owners named by Plan 03 are present and
  focused-audit clean:

```text
ConnesWeilRH.Source.CC20SelectedTraceLegalityData.selectedTraceClass
ConnesWeilRH.Source.CC20SelectedTraceLegalityData.selectedCyclicLegal
ConnesWeilRH.Source.CC20SelectedTraceReadOffData.positiveTrace_eq_qwLambda
ConnesWeilRH.Source.SourceObjectTheoremBasePackage.s2b1SupportSquareQWLambdaReadOffSourceData
ConnesWeilRH.Source.SourceObjectTheoremBasePackage.s2b1FinitePartSourceNormalFormData
ConnesWeilRH.Route.TraceFrontEndData.TraceScalePositiveQWLambdaDecompositionData.positiveTrace_eq_qwLambda
ConnesWeilRH.Route.TraceFrontEndData.TraceScaleBulkResidualData.residual_eq_zero
ConnesWeilRH.Route.TraceFrontEndData.TraceScaleFinitePartResidualData.hidden_residual_eq_zero
ConnesWeilRH.Route.TraceFrontEndData.TraceScaleNoExtraBulkScalarData.toSourceTermData
ConnesWeilRH.Route.RouteLedgerClearingData.ofSourceBacked
ConnesWeilRH.Route.RouteLedgerClearingData.toRouteLedgerSemanticData
```

Focused axiom audit for those declarations returned only:

```text
[propext, Classical.choice, Quot.sound]
```

Active route-certificate print:

```text
normalizedRouteCertificateFromTheorems :=
  { sourceBackedTest := normalizedSourceBackedFixedSTestFromTheorems
    ledgers := normalizedRouteLedgersForRouteFromTheorems
    bridge :=
      route_bridge_certificate_of_sign_defect_classification
        normalizedRouteTraceDataFromTheorems
        normalizedSignDefectClassificationForRouteFromTheorems
        normalizedRouteFinalSignNonpositiveFromTheorems }
```

Old-path scan of that print was empty for:

```text
normalizedTraceDataFromTheorems
normalizedNoExtraBulk
normalizedTraceScale
normalizedTraceFixedTupleRemainingRowsPackageFromTheorems
normalizedRouteLedgerRowsInputFromTheorems
normalizedRouteLedgerSourceInputFromTheorems
normalizedCoreS2B1RemainingConstructorInputsFromTheorems
route_certificate_of_normalized_certificate_boundary_rows_ledger_package_source_backed_cutoff
normalizedTraceReadOff
normalizedRestrictedToFull
```

What remains not good:
  The Dev-level Plan 03 assembly declarations still return `sorryAx`:

```text
normalizedTraceScalePositiveQWLambdaDecompositionDataFromTheorems
normalizedTraceScaleBulkResidualDataFromTheorems
normalizedTraceScaleFinitePartResidualDataFromTheorems
normalizedTraceScaleNoExtraBulkScalarDataFromTheorems
normalizedRouteLedgerClearingDataFromTheorems
normalizedNoExtraBulkContractFromTheorems
normalizedRouteLedgerSemanticDataFromTheorems
normalizedRouteCertificateFromTheorems
```

Down-drill:
  The remaining `sorryAx` is inherited from broader Dev skeleton objects such
  as `normalizedSourceObjectPackageFromTheorems`,
  `normalizedSourceBackedFixedSTestFromTheorems`,
  `normalizedTraceCCM25ArithmeticPackageFromTheorems`, route trace data,
  sign-defect classification, and final sign nonpositivity.  Do not count this
  as a clean no-sorry Plan 03 closure.

Post-04 interpretation:
  Treat Plan 03 as handled for the active final route certificate path only.
  Do not reopen the route certificate through
  `normalizedNoExtraBulkContractFromTheorems`, `normalizedTraceDataFromTheorems`,
  old fixed-tuple no-bulk rows, or old route-ledger Prop-row inputs.  If future
  work needs the Dev helper declarations themselves to be no-sorry, that is a
  separate upstream skeleton-root task, not a reason to undo the 04 route API
  cut.

Build evidence:
  WSL Ubuntu-24.04 ext4 verification copy at HEAD `667e6d5`, under
  `/tmp/connes-weil-rh-lake.lock`:

```text
lake build ConnesWeilRH.Source.CC20Concrete.TraceScale ConnesWeilRH.Source.ObjectTheoremBasePackage
lake build ConnesWeilRH.Source.ObjectExpandedRows ConnesWeilRH.Source.S2B1TraceScale
lake build ConnesWeilRH.Route.TraceFrontEnd ConnesWeilRH.Route.SignDefect ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem
lake build ConnesWeilRH.Dev.UnconditionalSkeleton
```

All passed.  `Dev/UnconditionalSkeleton.lean` still emitted existing `sorry`
warnings and the known Lean compiler PANIC backtrace while exiting 0 with
`Build completed successfully`.
