# Top-Down RH Source And Route Map

This file is a map, not a progress ledger.

Use it to choose the next semantic lane from the final RH obligation down to
the source owner that must change. Put batch results, dates, build transcripts,
axiom audits, open/closed status, and current frontier notes in `MEMORY.md`.


## 1. How To Read This Map

```text
final theorem
  -> route obligation
  -> source responsibility
  -> semantic lane
  -> owner/API
  -> consumer rewiring
  -> Lean build and axiom audit
```

Each lane must answer one question before editing:

```text
What stronger statement removes a real dependency from the route toward
_root_.RiemannHypothesis?
```

Do not start from a nearby theorem that looks easy to prove.


## 2. World Map

```text
_root_.RiemannHypothesis
|
+-- route/final bridge
|   |
|   +-- restricted-to-full bridge
|   +-- sign-defect bridge
|   +-- route ledger semantics
|   +-- lower-bound evidence
|
+-- scoped restricted scalar formula
|   |
|   +-- ScopedRestrictedArchimedeanFormula
|   +-- ScopedArchimedeanContributionBalance
|   +-- ScopedGlobalArchimedeanFormula
|
+-- source responsibilities
    |
    +-- CCM24 fixed-S / semilocal source model
    +-- CCM25 finite-prime arithmetic source model
    +-- S2-B1 trace-scale analytic exclusion package
```


## 3. Three-Source Lane Tree

This tree lists coarse semantic lanes. It does not say which lanes are open or
closed. Check `MEMORY.md` for current status.

```text
source responsibilities
|
+-- [A] CCM24 source / window / model
|   |
|   +-- A1. support/window raw kernel
|   |       |
|   |       +-- SourceFixedWindowCoordinateRows
|   |       +-- SourceSupportClosedWindowZeroKernelModel
|   |       +-- rawSupportKernel
|   |       +-- supportFootprint
|   |       +-- SourceSemilocalRows consumer
|   |
|   +-- A2. support carrier / window / lambda geometry
|   |       |
|   |       +-- supportCarrier
|   |       +-- windowCarrier
|   |       +-- lambdaCarrier
|   |       +-- coordinate lower / upper rows
|   |       +-- logScale = 0 rows
|   |
|   +-- A3. Fourier-support transform / involution
|   |       |
|   |       +-- fourierSupportCarrier
|   |       +-- supportCarrier (A.involution sourceTest)
|   |       +-- sourceFourierSupportCarrier_eq_involutionSupport
|   |       +-- support geometry of the transformed source test
|   |
|   +-- A4. Fourier transform / grading semantics
|   |       |
|   |       +-- SourceFourierCoordinateGradingData
|   |       +-- coordinateFourierEquiv
|   |       +-- coordinateFourier_preserves_grade
|   |       +-- concrete Fourier / involution semantics owner
|   |       +-- identity-is-real-Fourier theorem, if identity is intended
|   |
|   +-- A5. scaling action semantics
|   |       |
|   |       +-- SourceScalingCoordinateActionData
|   |       +-- SourceScalarCoordinateScalingData
|   |       +-- multiplicative scaling law
|   |       +-- arbitrary-place compatibility
|   |
|   +-- A6. bounded comparison semantics
|           |
|           +-- SourceBoundedComparisonData
|           +-- SourceBoundedComparisonEquivData
|           +-- SourceSignedCoordinateComparisonData
|           +-- comparisonMap / comparisonInverse
|           +-- inverse-law and operator-meaning owner
|
+-- [B] CCM25 / S2-B1 arithmetic source
|   |
|   +-- B1. visible finite-prime arithmetic data
|   |       |
|   |       +-- SourceVisibleFinitePrimeArithmeticData.atVisibleIndex
|   |       +-- SourceEvaluationVisibleFinitePrimeBoundary
|   |       +-- FixedLambdaArithmeticCertificateSourceTestData consumer
|   |
|   +-- B2. global exact finite-prime coverage
|   |       |
|   |       +-- SourcePrimePowerArithmeticSupportSkeletonAtLambda.globalExact
|   |       +-- CCM25SourceModel.global_prime_index_coverage
|   |       +-- routeVisibleGlobalIndex
|   |
|   +-- B3. restricted exact finite-prime coverage
|   |       |
|   |       +-- SourcePrimePowerArithmeticSupportSkeletonAtLambda.restrictedExact
|   |       +-- CCM25SourceModel.restricted_prime_index_coverage
|   |       +-- routeVisibleRestrictedIndex
|   |
|   +-- B4. visible atoms in lambda cutoff
|   |       |
|   |       +-- visibleAtomsInLambdaCut
|   |       +-- source-visible / route-visible bridge
|   |       +-- lambda cutoff membership
|   |
|   +-- B5. trace-scale / source-term arithmetic rows
|           |
|           +-- SourceWeilFormData.archimedeanTerm
|           +-- SourceEvaluationData.valueAt
|           +-- ScopedRestrictedArchimedeanFormula source term
|           +-- normalized source no-defect formula consumer
|
+-- [C] route / ledger / final bridge
    |
    +-- C1. route ledger semantic data
    |       |
    |       +-- RouteLedgerSemanticData
    |       +-- rank/pole ledger rows
    |       +-- RouteLedgers.cdefExhausts
    |
    +-- C2. restricted-to-full bridge
    |       |
    |       +-- current cutoff binding
    |       +-- threshold bridge package
    |       +-- lower-bound evidence
    |
    +-- C3. source-backed route consumers
    |       |
    |       +-- fixed-S CCM24 facts
    |       +-- CCM25 finite-prime source facts
    |       +-- S2-B1 source facts
    |       +-- route theorem consumers
    |
    +-- C4. final RH bridge
            |
            +-- source-backed route theorem
            +-- restricted-to-full theorem
            +-- sign-defect theorem
            +-- no-argument _root_.RiemannHypothesis
```


## 4. CCM24 Country Map

```text
CCM24 fixed-S / semilocal source model
|
+-- SourceSupportWindowData
|   |
|   +-- supportCarrier
|   +-- fourierSupportCarrier
|   +-- windowCarrier
|   +-- lambdaCarrier
|   +-- scalingActionImplemented
|   +-- fourierGradingCompatible
|   +-- boundedComparisonMap
|   +-- boundedComparisonInverse
|
+-- SourceFixedWindowCoordinateRows
|   |
|   +-- sourceSupportClosedWindowZeroKernelModel
|   +-- sourceSupportCarrierSemantics
|   +-- sourceSupportCarrierGeometry
|   +-- sourceFourierSupportCarrierGeometry
|   +-- sourceFourierSupportInvolutionBridge
|   +-- fixedWindowExhaustionCompatible
|
+-- place/model data
|   |
|   +-- SourcePlaceCarrierData
|   +-- SourceCanonicalHilbertModelData
|   +-- SourceScalingCoordinateActionData
|   +-- SourceFourierCoordinateGradingData
|   +-- SourceBoundedComparisonData
|
+-- consumer boundary
    |
    +-- SourceSemilocalRows
    +-- CCM24SourceModel
    +-- SourceObject.CCM24SemilocalObjectPackage.sourceModel
    +-- RouteInputs.ccm24
    +-- SourceBackedFixedSTest
```

CCM24 lane acceptance shape:

```text
old source/model input
  -> stronger concrete owner/API
  -> SourceSemilocalRows or CCM24SourceModel rewired
  -> old package/Prop path deleted or demoted to compatibility
```


## 5. CCM25 / S2-B1 Country Map

```text
CCM25 finite-prime arithmetic source model
|
+-- source-test and common-test objects
|   |
|   +-- CommonTestObject
|   +-- ConcreteCommonSourceTest
|   +-- FixedLambdaArithmeticCertificateSourceTestData
|
+-- finite-prime support skeleton
|   |
|   +-- SourcePrimePowerArithmeticSupportSkeletonAtLambda
|   +-- SourceVisibleFinitePrimeArithmeticData
|   +-- SourceFinitePrimeArithmeticIndexData
|   +-- SourceFinitePrimeArithmeticPairingData
|   +-- SourceFinitePrimeArithmeticFormulaData
|
+-- source evaluation and Weil-form data
|   |
|   +-- SourceEvaluationData
|   +-- SourceWeilFormData
|   +-- SourceEvaluationVisibleFinitePrimeBoundary
|
+-- package and object consumers
    |
    +-- FinitePrimeSourceData
    +-- FinitePrimeSourceDataBridge
    +-- CCM25SourceModel
    +-- SourceObjectConcreteCommonData
    +-- ObjectExpandedRows
```

S2-B1 trace-scale lane shape:

```text
S2-B1 trace-scale analytic exclusion package
  -> normalized seed rows
  -> scalar finite-part source normal form
  -> no-extra-bulk rows
  -> rank-zero rows
  -> endpoint-strip Cdef rows
  -> analytic exclusion constructor
```


## 6. Route Country Map

```text
route/final bridge
|
+-- Route SourceBackedFixedSTest
|   |
|   +-- fixed test admissibility
|   +-- triple vanishing
|   +-- finite-prime visibility
|   +-- trace read-off
|
+-- RouteLedgerSemanticData
|   |
|   +-- rank/pole ledger data
|   +-- RouteLedgers.cdefExhausts
|   +-- current cutoff binding
|   +-- threshold bridge package
|   +-- lower-bound evidence
|
+-- restricted-to-full layer
|   |
|   +-- normalized restricted scalar formula
|   +-- scoped restricted formula
|   +-- global archimedean balance
|
+-- final theorem layer
    |
    +-- source-backed theorem
    +-- restricted-to-full theorem
    +-- sign-defect theorem
    +-- _root_.RiemannHypothesis
```


## 7. Province Template

Use this template before editing a lane.

```text
parent world node:
parent country node:
province / lane:

route obligation:
current weak statement:
why the current statement is insufficient:

old path to remove:
real consumer to rewire:
new owner/API:
expected lower brick:

forbidden shortcuts:
  True
  Set.univ
  renamed free Prop
  package endpoint alias
  compatibility wrapper only

smallest owning build:
focused axiom audit targets:
```


## 8. Acceptance Gate

```text
candidate change
|
+-- Does it remove or lower a real old path?
|     |
|     +-- no  -> prep-only
|     +-- yes -> continue
|
+-- Does a real consumer use the stronger statement?
|     |
|     +-- no  -> prep-only
|     +-- yes -> continue
|
+-- Does the statement preserve or strengthen the needed semantics?
|     |
|     +-- no  -> reject or redesign
|     +-- yes -> continue
|
+-- Does the proof path bottom in Lean/Mathlib without project-local axioms?
      |
      +-- no  -> project-bottom/API boundary only
      +-- yes -> Mathlib-bottom for that lane
```

`#print axioms` is an audit of proof dependencies. It does not prove statement
sufficiency. A clean axiom list over a weak statement still fails the semantic
gate.


## 9. Maintenance Rule

```text
map file
  -> stable ownership layers
  -> stable dependency directions
  -> lane taxonomy
  -> consumer boundaries
  -> province templates

MEMORY.md
  -> batch results
  -> current frontier status
  -> open/closed lane notes
  -> build transcripts
  -> axiom audit results
  -> dated lessons
```

Do not add current batch progress to this map. Update this file only when the
ownership structure, dependency direction, lane taxonomy, or province template
changes.
