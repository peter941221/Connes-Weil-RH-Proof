# 10A Post-09AB Single-Lane Strategy

Date: 2026-07-09

Status:
  Coordinator plan.  This does not prove RH, close 08A, or touch 09F.


## Result First

Current result:

```text
Good direction change.
Not an unconditional RH proof.
Not 08A closure.
```

After the 09A-E coordinator pass and the 09AB constructor-provenance guard,
the best strategy is no longer to keep widening the package-source split in
parallel.

The current constructor path should be treated as a rejected lower-producer
candidate unless the API is later redesigned so the package rows are built from
the same source-data owner.


## Evidence

Production Lean evidence:

```text
ConnesWeilRH/Route/CC20RouteRealization.lean

09A:
  sourceBackedFixedSTestWithNormalizedYoshidaDetectorSquare_commonTestRow_iff_inputOwner

09B:
  normalizedRouteBackedYoshidaDetectorArchimedeanTraceRealization_packageCertificateFamily_eq_inputRows
  normalizedRouteBackedYoshidaDetectorArchimedeanTraceRealization_packageSourceDataRows_iff_inputs

09A-E:
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageSourceDataRowsCalibration_iff_commonTest_certificateFamily
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermMassRowsCalibration_iff_routePoleCollapseCalibrations
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageSplitSourceDataAtomRowsCalibration_iff_components

10A-B:
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormSourceDataCertificateSourceTestReadOff_of_commonTestRows
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormVisibleAtomSourceDataRowsCalibration_of_sourceDataCertificateVisibleReadOff
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormSourceAtoms_forced_eq_sourceDataCertificateAtoms
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormSourceDataCertificateAtomVisibleReadOff_iff_direct
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageSplitSourceDataDirectCertificateRowsCalibration_iff_components
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormSourceDataCertificateVisibleArithmeticReadOff_of_visibleArithmeticDataReadOff
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageSplitSourceDataDirectCertificateDataRowsCalibration_iff_components

ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceDataBridge.lean

10A-B source constructor guards:
  FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleData_visibleArithmeticData
  FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleData_atoms
  FixedLambdaArithmeticCertificateSourceTestData.ofSourceWeilFormVisibleData_visibleArithmeticData
  FixedLambdaArithmeticCertificateSourceTestData.ofSourceWeilFormVisibleData_atoms
```

Verified gate:

```text
lake build ConnesWeilRH.Route.CC20RouteRealization

focused import-facing #check / #print axioms:
  only [propext, Classical.choice, Quot.sound]
  no sorryAx
```


## Current Shape

```text
08A source-Weil-form finite-prime package route
|
+-- split source-data atom owner
    |
    +-- SourceWeilFormCarrier
    |
    +-- VisibleAtomForSourceTestNormalization
    |
    +-- VisibleAtomSourceDataRows
    |
    +-- PackageSourceDataCommonTestRows
    |     |
    |     +-- 09A guard:
    |           not constructor-internal;
    |           equals caller-supplied sourceDataOwner same-test row
    |
    +-- PackageSourceDataCertificateFamilyRows
    |     |
    |     +-- 09B guard:
    |           not constructor-internal;
    |           equals caller-supplied rows/sourceDataOwner binding
    |
    +-- DirectTermMassRows
          |
          +-- 09D guard:
                equivalent to route restricted-QW pole collapse
                + route psi-pole collapse
```

What this means:

```text
The combined 09A-E owner is not a new arithmetic source.
It is a packaging of:
  - same-object carrier/atom rows,
  - external AB input binding,
  - route pole-collapse calibrations.
```


## Decision

Recommended route:

```text
Do not continue 09A-E as parallel lower producers.

Do not immediately redesign the constructor API.

Instead:
  reject the current constructor path as a lower producer,
  then attack the remaining component with the best chance of real descent.
```

Why not redesign the API now:

```text
Current constructor:
  sourceDataOwner : external input
  rows            : independent external input

09A/09B need:
  sourceDataOwner.commonTestFunction = route test
  rows.finitePrimeArithmeticCertificates =
    fixedLambdaArithmeticSourceTestCertificatesForAllTests sourceDataOwner

Changing the constructor now would move this equality into the API boundary.
That may be useful later, but it would not by itself prove the missing
mathematical provenance.
```


## 10A Main Tree

```text
10A main lane
|
+-- A. Record rejection of current constructor path
|   |
|   +-- A1. Keep 09AB guards as production evidence
|   |
|   +-- A2. Add no new constructor-only AB closure claims
|   |
|   +-- A3. Treat current package-source constructor path as non-lower
|
+-- B. Attack local semantic atom alignment first
|   |
|   +-- B1. Target:
|   |     NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormVisibleAtomSourceDataRowsCalibration
|   |
|   +-- B2. Result after first 10A-B pass:
|   |     VisibleAtomSourceDataRows is not a free wrapper over arbitrary
|   |     sourceAtoms.  It forces sourceAtoms.toNormalization to equal the
|   |     source-data certificate atom normalization.
|   |
|   +-- B3. Lowered leaves:
|   |     SourceDataCertificateSourceTestReadOff
|   |       generated by PackageSourceDataCommonTestRows
|   |
|   |     SourceDataCertificateVisibleReadOff
|   |       lowered by 10A-B4 into the two rows below
|   |
|   +-- B4. Result after source-data certificate visible split:
|         SourceDataCertificateAtomVisibleReadOff
|           source-data certificate atoms
|           =
|           source-data certificate visibleArithmeticData
|           lowered by 10A-B5 into the direct row below
|
|         SourceDataCertificateVisibleArithmeticReadOff
|           source-data certificate visibleArithmeticData
|           =
|           source-Weil-form visible arithmetic data
|
|   +-- B5. Current active 10A-B bottom:
|         SourceDataCertificateDirectAtomVisibleReadOff
|           source-data certificate atoms.atIndex n
|           =
|           source-data certificate visibleArithmeticData.atVisibleIndex n
|
|         SourceDataCertificateVisibleArithmeticReadOff
|           lowered by 10A-B6 into the whole-function row below
|
|   +-- B6. Result after direct certificate data-row pass:
|         Source constructor projections show:
|           ofSourceWeilFormVisibleData.visibleArithmeticData
|             = source-Weil-form visible arithmetic data
|           ofSourceWeilFormVisibleData.atoms
|             = caller-supplied atoms
|
|         So source-Weil-form visible construction closes only the visible
|         data projection; it does not close atom-vs-visible equality.
|
|   +-- B7. Current active 10A-B bottom:
|         SourceDataCertificateDirectAtomVisibleReadOff
|           direct same-certificate atom/visible arithmetic equality
|
|         SourceDataCertificateVisibleArithmeticDataReadOff
|           whole visible-arithmetic function equality between the
|           source-data certificate and the source-Weil-form carrier
|
|   +-- B8. Next question:
|         Can the certificate constructor/API force atoms from
|         visibleArithmeticData, or is the direct atom-vs-visible row a real
|         same-certificate selection row?
|
+-- C. If B is a wrapper, move to SourceWeilFormCarrier
|   |
|   +-- C1. Target:
|   |     NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration
|   |
|   +-- C2. Question:
|   |     Does the route already carry same-symbol SourceWeilFormData,
|   |     or is this another external carrier existence assumption?
|   |
|   +-- C3. Desired output:
|         produce the carrier from route inputs,
|         or guard it as a genuine external source-Weil-form existence row.
|
+-- D. If B/C do not descend, classify pole-collapse
    |
    +-- D1. Use existing 09D theorem:
    |     DirectTermMassRows iff route pole-collapse calibrations
    |
    +-- D2. Question:
    |     Are these pole-collapse calibrations RH-level / no-off-line-source-zero
    |     rather than lower arithmetic producers?
    |
    +-- D3. Desired output:
          named Lean guard rejecting pole-collapse as lower,
          or a genuinely lower source theorem.
```


## Strict Non-Scope

```text
Do not work on 09F here.
Peter is handling 09F separately.

Do not create a new 09F plan.
Do not edit plan/09F_2026-07-09_half_point_abel_boundary.md.
Do not touch ConnesWeilRH/Dev/Parallel09F_HalfPointAbelBoundary.lean.
```


## Next Action

Start with 10A-B:

```text
Current active target:
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormSourceDataCertificateDirectAtomVisibleReadOff

  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormSourceDataCertificateVisibleArithmeticDataReadOff

Read:
  FixedLambdaArithmeticCertificateSourceTestData.atoms
  FixedLambdaArithmeticCertificateSourceTestData.visibleArithmeticData
  FixedLambdaArithmeticCertificateSourceTestData.ofSourceWeilFormVisibleData
  FixedLambdaSourceWeilFormVisibleArithmeticData.toSourceEvaluationVisibleArithmeticData

Then prove one of:
  - direct atom-visible equality from a stronger certificate construction; or
  - an iff/guard showing certificate atoms and visibleArithmeticData are
    independently selected fields and must remain a named same-certificate row;
    then
  - whole visible-arithmetic data equality from a data-bearing source-data
    constructor/read-off row, or a guard showing the route source-data owner is
    still selected independently from the source-Weil-form carrier.
```

Acceptance gate:

```text
1. Production Lean theorem in ConnesWeilRH/Route/CC20RouteRealization.lean.
2. lake build ConnesWeilRH.Route.CC20RouteRealization under WSL lock.
3. Focused import-facing #check / #print axioms.
4. No sorryAx in the new declarations.
```

## 2026-07-09 Update: Canonical Constructor Provenance Bottom

Result:
  Bottom classification.  Not an RH proof and not 08A closure.  No build was
  run by request.

New production guard:

```text
sourceBackedFixedSTestWithNormalizedYoshidaDetectorSquare_certificateDataCanonicalRow_iff_inputOwner
normalizedRouteBackedYoshidaDetectorSquareTraceRealization_of_archimedean_sourceDataOwner_eq_input
normalizedRouteBackedYoshidaDetectorSquareRouteRealization_of_trace_realization_sourceDataOwner_eq_input
normalizedRouteBackedCC20SquareRestrictedTest_of_yoshida_square_route_realization_sourceDataOwner_eq_input
```

Meaning:

```text
square source-backed constructor
  |
  +-- finitePrimeSourceDataOwner := sourceDataOwner
  |
  +-- canonical certificate row on route certificateData
        iff
      canonical certificate row on caller-supplied sourceDataOwner

trace / route / square-restricted carrier conversions
  |
  +-- preserve the same finitePrimeSourceDataOwner by rfl
```

This proves the current constructor path does not generate the canonical
certificate row internally.  `SourceDataCertificateCanonicalSourceEvaluationDataReadOff`
is now a data-bearing provenance bottom: closing it requires a source-data
owner/API whose `certificateData` is built by
`ofSourceEvaluationVisibleCanonicalData`, not a witness assembled from route
`certificateData.atoms`.

Next action:
  Either introduce that stronger data-bearing source-data owner/API, or reject
  this constructor path as an external finite-prime atom-selection requirement
  for 08A.

## 2026-07-09 Update: Source-Weil-Form Carrier Provenance Bottom

Result:
  `SourceWeilFormCarrier` is classified as external per-route provenance for
  the current route API.  Not an RH proof and not 08A closure.  No build was
  run.

New production names:

```text
NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormExternalCarrierProvenance
NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration_of_externalCarrierProvenance
NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormExternalCarrierProvenance_of_carrierCalibration
```

Meaning:

```text
RouteInputs
  |
  +-- ccm25 : CCM25Interface
        |
        +-- weilSymbols : WeilFormSymbols

missing:
  SourceWeilFormData A
  equality ccm25.weilSymbols = sourceWeilForm.toWeilFormSymbols
```

So the source-Weil-form branch is not a lower finite-prime arithmetic producer
unless a stronger upstream route/source API supplies this carrier.  The active
next lane should move to the pole-collapse pair:

```text
DirectTermMassRows
  iff
RestrictedQWPoleCollapseCalibration
+ PsiPoleCollapseCalibration
```


## 09D Pole-Collapse Guard Update

Current result:

```text
DirectTermMassRows is rejected as a lower finite-prime arithmetic producer.
```

New production evidence:

```text
normalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonSplitNonPoleMassCoverage_of_routeFrontNonPoleMassCalibrations
normalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonSplitPsiPoleCoverage_of_routeFrontPsiPoleCalibrations
normalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonSplitQWPoleCoverage_of_routeFrontQWPoleCalibrations
normalizedCC20_no_offline_source_zero_of_square_restricted_traceFrontComparisonSplitNonPoleMassCalibrations
normalizedCC20_no_offline_source_zero_of_square_restricted_traceFrontComparisonSplitPsiPoleCalibrations
normalizedCC20_no_offline_source_zero_of_square_restricted_traceFrontComparisonSplitQWPoleCalibrations
normalizedCC20_no_offline_source_zero_of_square_restricted_routePoleCollapseCalibrations
normalizedCC20_no_offline_source_zero_of_square_restricted_sourceWeilFormDirectTermMassRowsCalibration
```

What the guard says:

```text
route-front rows
  B1 pole-pairing transport
  B2 trace-front split rows
  B3a index balance
  detector coverage
  Yoshida detector existence

+ PsiPoleCollapseCalibration
  |
  v
detector-family split psi-pole coverage
  |
  v
no-off-line source-zero
```

So the psi half of:

```text
DirectTermMassRows
  iff
RestrictedQWPoleCollapseCalibration
+ PsiPoleCollapseCalibration
```

is RH-level once placed back into the route-front context where it is used.

The stronger direct guard is now:

```text
SourceWeilFormCarrier
+ DirectTermMassRows
+ B1/B2/B3a route-front rows
+ detector coverage
+ Yoshida detector existence
  |
  v
no-off-line source-zero
```

The remaining restricted-QW half should not be treated as an independent
bottom by default.  Existing route code already has:

```text
NormalizedRouteBackedCC20SquareRestrictedRestrictedQWPoleCollapseCalibration_of_scopedBalance_globalMassCalibrations
```

which generates it from scoped finite-prime balance plus global mass
cancellation.

B1/B2/B3a audit:

```text
B1 exact pole transport alone      -> not enough
B2 trace-front split rows alone    -> not enough
B3a index balance alone            -> not enough

B1 + B2 + B3a + NonPoleMass closing row -> no-off-line source-zero
B1 + B2 + B3a + PsiPole closing row     -> no-off-line source-zero
B1 + B2 + B3a + QWPole closing row      -> no-off-line source-zero
```

Conclusion:

```text
Do not keep attacking DirectTermMassRows, PsiPoleCollapse, or
RestrictedQWPoleCollapse as lower finite-prime arithmetic.

The remaining plausible exit is not pole-collapse.  It is a genuinely
data-bearing route/source provenance API, especially:
  - same-symbol SourceWeilFormCarrier provenance;
  - source-data certificate canonical constructor provenance.
```
