# 08A Restricted-Test CC20 Sufficiency Plan

Result:
  Active execution plan.  Not accepted proof progress until the build and
  focused axiom gates below pass.

Execution update, 2026-07-09, split package source-data rows lowering:

```text
Result:
  Good five-milestone 08A package-source lowering.  Not an unconditional RH
  proof and not 08A closure.

Hard gate moved:
  old active package-source shape:
    SourceWeilFormCarrier
    + VisibleAtomForSourceTestNormalization
    + PackageSourceDataRows
        sourceBackedTest.finitePrimeSourceDataOwner.commonTestFunction =
          route weilTest
        package.rows.finitePrimeArithmeticCertificates =
          fixedLambdaArithmeticSourceTestCertificatesForAllTests
            sourceBackedTest.finitePrimeSourceDataOwner
    + VisibleAtomSourceDataRows
    + DirectTermMassRows

  new active package-source shape:
    SourceWeilFormCarrier
    + VisibleAtomForSourceTestNormalization
    + PackageSourceDataCommonTestRows
        sourceBackedTest.finitePrimeSourceDataOwner.commonTestFunction =
          route weilTest
    + PackageSourceDataCertificateFamilyRows
        package.rows.finitePrimeArithmeticCertificates =
          fixedLambdaArithmeticSourceTestCertificatesForAllTests
            sourceBackedTest.finitePrimeSourceDataOwner
    + VisibleAtomSourceDataRows
        sourceAtoms.atomsWithSourceTest.toNormalization =
          source-data certificate atomsWithSourceTest.toNormalization
    + DirectTermMassRows

New route-facing declarations:
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageSourceDataCommonTestRowsCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageSourceDataCertificateFamilyRowsCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageSourceDataRowsCalibration_of_splitRows`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageSourceTestReadOffCalibration_of_splitPackageSourceDataRows`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageAtomsWithSourceTestReadOffCalibration_of_splitPackageSourceDataRows`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageSplitSourceDataAtomRowsCalibration`
  - bridges from the split owner back to the source-data atom rows owner and
    older compatibility owners
  - three trace-front route consumers for the lower split owner
  - three matching SourceRH exits for the lower split owner

Verification:
  WSL persistent mirror:
    `lake env lean ConnesWeilRH/Route/CC20RouteRealization.lean`
    `lake build ConnesWeilRH.Route.CC20RouteRealization`

  Focused import-facing audit passed for the two split leaves, split-to-owner
  bridge, representative trace-front consumer, and representative SourceRH
  exit.  The audit output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound

Rejected as solved:
  This does not prove either package source-data split leaf.  It only exposes
  common-test selection and certificate-family provenance as independent
  active bottoms.

Next safe action:
  Attack `PackageSourceDataCommonTestRows` and
  `PackageSourceDataCertificateFamilyRows` separately.  If either is false for
  the current route constructors, reject the package-source path with concrete
  Lean evidence instead of hiding the failure inside a combined owner.
```

Execution update, 2026-07-09, package source-data atom rows lowering:

```text
Result:
  Good three-milestone 08A package-source lowering.  Not an unconditional RH
  proof and not 08A closure.

Hard gate moved:
  old active package-source shape:
    SourceWeilFormCarrier
    + VisibleAtomForSourceTestNormalization
    + PackageSourceDataRows
        sourceBackedTest.finitePrimeSourceDataOwner.commonTestFunction =
          route weilTest
        package.rows.finitePrimeArithmeticCertificates =
          fixedLambdaArithmeticSourceTestCertificatesForAllTests
            sourceBackedTest.finitePrimeSourceDataOwner
    + PackageAtomsWithSourceTestReadOff
        commonCertificate.atomsWithSourceTest.toNormalization =
          visible source atoms
    + DirectTermMassRows

  new active package-source shape:
    SourceWeilFormCarrier
    + VisibleAtomForSourceTestNormalization
    + PackageSourceDataRows
        sourceBackedTest.finitePrimeSourceDataOwner.commonTestFunction =
          route weilTest
        package.rows.finitePrimeArithmeticCertificates =
          fixedLambdaArithmeticSourceTestCertificatesForAllTests
            sourceBackedTest.finitePrimeSourceDataOwner
    + VisibleAtomSourceDataRows
        sourceAtoms.atomsWithSourceTest.toNormalization =
          source-data certificate atomsWithSourceTest.toNormalization
    + DirectTermMassRows

New route-facing declarations:
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormVisibleAtomSourceDataRowsCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageAtomsWithSourceTestReadOffCalibration_of_packageSourceDataRows`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageSourceDataAtomRowsCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageSourceDataRowsCalibration_of_packageSourceDataAtomRowsCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageSourceRowsCalibration_of_packageSourceDataAtomRowsCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageRowsCalibration_of_packageSourceDataAtomRowsCalibration`
  - three trace-front route consumers for the lower source-data atom rows owner
  - three matching SourceRH exits for the lower source-data atom rows owner

Verification:
  WSL persistent mirror build passed:
    `lake build ConnesWeilRH.Route.CC20RouteRealization`

  Focused import-facing audit passed for the new source-data rows owner,
  visible atom source-data rows owner, lower bridges, representative
  trace-front consumer, and representative SourceRH exit.  The audit output
  contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound

Rejected as solved:
  This does not prove source-data certificate-family alignment, visible atom
  source-data alignment, the source-Weil-form carrier, or direct term mass
  rows.  It only shows that the former package source-test and package atom
  wrapper rows are consequences of this lower source-data atom owner.

Next safe action:
  Attack or reject `PackageSourceDataRows` and `VisibleAtomSourceDataRows`.
  The critical audit is whether the route package and visible atom owner are
  both produced from `sourceBackedTest.finitePrimeSourceDataOwner`.
```

Execution update, 2026-07-09, package source-data rows lowering:

```text
Result:
  Good 08A package source-test lowering.  Not an unconditional RH proof and
  not 08A closure.

Hard gate moved:
  old active package-source shape:
    SourceWeilFormCarrier
    + VisibleAtomForSourceTestNormalization
    + PackageSourceTestReadOff
        source_test_of_package package =
          concrete common source test interface
    + PackageAtomsWithSourceTestReadOff
    + DirectTermMassRows

  new active package-source shape:
    SourceWeilFormCarrier
    + VisibleAtomForSourceTestNormalization
    + PackageSourceDataRows
        sourceBackedTest.finitePrimeSourceDataOwner.commonTestFunction =
          route weilTest
        package.rows.finitePrimeArithmeticCertificates =
          fixedLambdaArithmeticSourceTestCertificatesForAllTests
            sourceBackedTest.finitePrimeSourceDataOwner
    + PackageAtomsWithSourceTestReadOff
        commonCertificate.atomsWithSourceTest.toNormalization =
          visible source atoms
    + DirectTermMassRows

New route-facing declarations:
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageSourceDataRowsCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageSourceTestReadOffCalibration_of_packageSourceDataRows`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageSourceDataRowsCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageSourceRowsCalibration_of_packageSourceDataRowsCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageRowsCalibration_of_packageSourceDataRowsCalibration`
  - three trace-front route consumers for the lower package source-data rows owner
  - three matching SourceRH exits for the lower package source-data rows owner

Verification:
  WSL ext4 verification copy with preserved `.lake` cache:
    `lake env lean ConnesWeilRH/Route/CC20RouteRealization.lean`

  The Lean file check passed.  It reported only existing warnings.

Rejected as solved:
  This does not prove source-data rows alignment, package atom read-off, the
  source-Weil-form carrier, visible atoms, or direct term mass rows.  It only
  proves that source-data rows alignment generates the package source-test
  read-off.

Next safe action:
  Attack or reject `PackageSourceDataRows`.  The critical audit is whether
  the route package's `rows.finitePrimeArithmeticCertificates` is exactly the
  family generated by `sourceBackedTest.finitePrimeSourceDataOwner`, and
  whether that owner has `commonTestFunction = sourceBackedTest.weilTest`.
```

Execution update, 2026-07-09, package source-test atom read-off split:

```text
Result:
  Good 08A package-source finite-prime lowering.  Not an unconditional RH
  proof and not 08A closure.

Hard gate moved:
  old active package-source shape:
    SourceWeilFormCarrier
    + VisibleAtomForSourceTestNormalization
    + PackageAtomForSourceTestNormalization
        - commonCertificate.support.sourceTest =
          concrete common source test interface
        - commonCertificate.atomsWithSourceTest.toNormalization =
          visible source atoms
    + DirectTermMassRows

  new active package-source shape:
    SourceWeilFormCarrier
    + VisibleAtomForSourceTestNormalization
    + PackageSourceTestReadOff
        source_test_of_package package =
          concrete common source test interface
    + PackageAtomsWithSourceTestReadOff
        commonCertificate.atomsWithSourceTest.toNormalization =
          visible source atoms
    + DirectTermMassRows

New route-facing declarations:
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageSourceTestReadOffCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageAtomsWithSourceTestReadOffCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageAtomForSourceTestNormalizationCalibration_of_packageSourceRows`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageSourceRowsCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageRowsCalibration_of_packageSourceRowsCalibration`
  - three trace-front route consumers for the lower package-source rows owner
  - three matching SourceRH exits for the lower package-source rows owner

Verification:
  WSL ext4 verification copy with preserved `.lake` cache:
    `lake env lean ConnesWeilRH/Route/CC20RouteRealization.lean`

  The Lean file check passed.  It reported only existing warnings.

Rejected as solved:
  This does not prove either package-source leaf.  It only exposes the package
  source-test selector as a named target.  Do not treat
  `PackageAtomForSourceTestNormalizationCalibration` as the active bottom when
  `DirectTermForSourceTestAtomPackageSourceRowsCalibration` is available.

Next safe action:
  Attack or reject `PackageSourceTestReadOff` by tracing the package
  `ConcreteCCM25ArithmeticPackage.rows.finitePrimeArithmeticCertificates`
  selector.  If the route/source package never states that this selector is
  the concrete common source test, this remains a real open package-source
  leaf, not a definitional equality.
```

Execution update, 2026-07-09, source-Weil-form direct mass owner:

```text
Result:
  Good 08A finite-prime owner consolidation.  Not an unconditional RH proof
  and not 08A closure.

Three milestone groups landed:
  1. The two source-Weil-form direct mass leaves are grouped under one
     same-carrier mass owner:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectMassRowsCalibration

     Fields:
       - direct restricted mass on `sourceWeilForm.evaluation`;
       - direct global mass on `sourceWeilForm.evaluation`.

  2. The route now has a direct arithmetic rows owner that carries the carrier,
     both atom read-off rows, and the grouped mass owner:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectArithmeticRowsCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectRowsCalibration_of_directArithmeticRowsCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataArithmeticSumRowsCalibration_of_sourceWeilFormDirectArithmeticRowsCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataLowerRowsCalibration_of_sourceWeilFormDirectArithmeticRowsCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataRowsCalibration_of_sourceWeilFormDirectArithmeticRowsCalibration

  3. The non-pole, psi-pole, and QW-pole trace-front route consumers, plus the
     corresponding SourceRH exits, now accept the direct arithmetic rows owner:

       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceWeilFormDirectArithmeticRowsCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceWeilFormDirectArithmeticRowsCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceWeilFormDirectArithmeticRowsCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceWeilFormDirectArithmeticRowsNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceWeilFormDirectArithmeticRowsPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceWeilFormDirectArithmeticRowsQWPoleCalibrations

Current finite-prime bottom:
  `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectArithmeticRowsCalibration`
  is the active grouped owner when using direct source-Weil-form mass rows.
  Its open fields are:
    - same-symbol source-Weil-form carrier;
    - source-Weil-form restricted atom read-off;
    - source-Weil-form global atom read-off;
    - grouped direct mass rows on `sourceWeilForm.evaluation`.

Rejected as solved:
  This does not prove any field.  It only prevents the two direct mass rows
  from being passed as unrelated top-level route arguments.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the direct mass owner, direct
  arithmetic rows owner, lower bridges, three route consumers, and three
  SourceRH exits.  The audit output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound

  Static forbidden scan over the diff found no new `sorry`, `admit`, `axiom`,
  `constant`, `opaque`, `unsafe`, `True`, or `Set.univ`.
```

Execution update, 2026-07-09, source-Weil-form direct mass rows:

```text
Result:
  Good 08A finite-prime bottom lowering.  Not an unconditional RH proof and
  not 08A closure.

Three milestone groups landed:
  1. The route now has direct source-Weil-form finite-prime mass leaves:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectRestrictedMassCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectGlobalMassCalibration

     These rows are stated on the actual `sourceWeilForm.evaluation` selected
     by the same-symbol carrier, not on an `E` recovered later through
     `Classical.choose`.

  2. A lower direct rows owner now constructs the source-evaluation
     arithmetic-sum witness directly:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectRowsCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataArithmeticSumRowsCalibration_of_sourceWeilFormDirectRowsCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataLowerRowsCalibration_of_sourceWeilFormDirectRowsCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataRowsCalibration_of_sourceWeilFormDirectRowsCalibration

     The witness is `(A, sourceWeilForm.evaluation)`, so the bridge does not
     need to prove that `Classical.choose` selected the same `E`.

  3. The non-pole, psi-pole, and QW-pole trace-front route consumers, plus the
     corresponding SourceRH exits, now accept the direct rows owner:

       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceWeilFormDirectRowsCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceWeilFormDirectRowsCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceWeilFormDirectRowsCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceWeilFormDirectRowsNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceWeilFormDirectRowsPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceWeilFormDirectRowsQWPoleCalibrations

Current finite-prime bottom:
  `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectRowsCalibration`
  is the lower owner when the route can supply source-Weil-form mass rows
  directly.  Its open fields are:
    - same-symbol source-Weil-form carrier;
    - source-Weil-form restricted atom read-off;
    - source-Weil-form global atom read-off;
    - direct restricted mass on `sourceWeilForm.evaluation`;
    - direct global mass on `sourceWeilForm.evaluation`.

Rejected as solved:
  This does not prove any of the five direct rows.  It only lowers the mass
  statement below the old existential arithmetic calibration.  Do not claim a
  direct mass bridge through the old `SourceWeilFormRestrictedMassCalibration`
  or `SourceWeilFormGlobalMassCalibration` unless the API is changed to expose
  the chosen `E` as data.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the direct mass leaves, direct rows
  owner, lower bridges, three route consumers, and three SourceRH exits.  The
  audit output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound

  Static forbidden scan over the diff found no new `sorry`, `admit`, `axiom`,
  `constant`, `opaque`, `unsafe`, `True`, or `Set.univ`.
```

Execution update, 2026-07-09, source-Weil-form rows lower-route unification:

```text
Result:
  Good 08A route-level finite-prime API unification.  Not an unconditional RH
  proof and not 08A closure.

Three milestone groups landed:
  1. The source-Weil-form rows owner now has explicit exits into the older
     lower source-evaluation finite-prime route:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataArithmeticSumRowsCalibration_of_sourceWeilFormRowsCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataLowerRowsCalibration_of_sourceWeilFormRowsCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataRowsCalibration_of_sourceWeilFormRowsCalibration

  2. The non-pole trace-front source-Weil-form rows consumer now goes through
     the arithmetic-sum finite-prime API instead of manually expanding the five
     source-Weil-form row fields.

       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceWeilFormRowsCalibrations

  3. The psi-pole and QW-pole trace-front source-Weil-form rows consumers now
     use the same lower finite-prime API bridge.

       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceWeilFormRowsCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceWeilFormRowsCalibrations

Current finite-prime bottom:
  `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormRowsCalibration`
  remains open.  Its fields are still:
    - same-symbol source-Weil-form carrier;
    - source-Weil-form restricted atom read-off;
    - source-Weil-form global atom read-off;
    - source-Weil-form-scoped restricted E-mass;
    - source-Weil-form-scoped global E-mass.

Rejected as solved:
  This update does not prove any of the five fields.  It removes a parallel
  bypass by making the rows owner feed the established `ArithmeticSumRows` /
  `LowerRows` finite-prime route API.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the three new lower bridges, three
  rewired trace-front consumers, and three SourceRH exits.  The audit output
  contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound

  Static forbidden scan over the diff found no new `sorry`, `admit`, `axiom`,
  `constant`, `opaque`, `unsafe`, `True`, or `Set.univ`.
```

Execution update, 2026-07-09, source-Weil-form finite-prime rows owner:

```text
Result:
  Good 08A route-level owner consolidation.  Not an unconditional RH proof.

Three milestone groups landed:
  1. The five source-Weil-form finite-prime leaves are now grouped under one
     data-bearing route boundary:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormRowsCalibration

     Fields:
       - same-symbol source-Weil-form carrier
       - source-Weil-form restricted atom read-off
       - source-Weil-form global atom read-off
       - source-Weil-form-scoped restricted E-mass
       - source-Weil-form-scoped global E-mass

  2. The non-pole trace-front consumer now accepts that single source-Weil-form
     rows owner:

       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceWeilFormRowsCalibrations

  3. The psi-pole and QW-pole trace-front consumers now accept the same owner:

       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceWeilFormRowsCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceWeilFormRowsCalibrations

Current finite-prime bottom:
  `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormRowsCalibration`
  remains open.  Its fields are the current hard leaves; the update prevents
  route consumers from accepting them as unrelated arguments.

Rejected as solved:
  This does not prove the source-Weil-form carrier, either atom read-off row,
  or either mass row.  It is a route-boundary consolidation that preserves the
  same-object invariant across all five fields.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the rows owner and three route
  consumers.  The audit output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound
```

Execution update, 2026-07-09, source-Weil-form scoped E-mass lowering:

```text
Result:
  Good 08A route-level finite-prime API lowering batch.  Not an unconditional
  RH proof.

Three milestone groups landed:
  1. The source-Weil-form arithmetic boundary is now named explicitly:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormArithmeticRowsCalibration

     It packages the same-symbol source-Weil-form carrier with the two
     source-Weil-form atom read-off leaves, then derives the older arithmetic
     rows calibration.

  2. The restricted/global E-mass leaves have source-Weil-form-scoped names:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormRestrictedMassCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormGlobalMassCalibration

     These are tied to the E selected by the source-Weil-form arithmetic-row
     calibration.  They are not direct claims about `hweil r`'s
     `sourceWeilForm.evaluation`.

  3. The route-facing non-pole, psi-pole, and QW-pole trace-front consumers now
     accept source-Weil-form read-off plus source-Weil-form-scoped mass rows:

       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceWeilFormReadOffSourceWeilFormMassCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceWeilFormReadOffSourceWeilFormMassCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceWeilFormReadOffSourceWeilFormMassCalibrations

Current finite-prime bottom:
  for every square restricted carrier:
    - same-symbol source-Weil-form carrier;
    - source-Weil-form restricted atom read-off;
    - source-Weil-form global atom read-off;
    - source-Weil-form-scoped restricted E-mass;
    - source-Weil-form-scoped global E-mass.

Rejected as solved:
  A direct mass bridge from `hweil r`'s `sourceWeilForm.evaluation` to the
  legacy `ArithmeticRowsCalibration` does not type-check because the legacy
  boundary is an existential Prop and downstream calibrations read E via
  `Classical.choose`.  Do not claim direct source-Weil-form evaluation mass
  closure unless the API is changed to carry the selected source-Weil-form data
  through the route boundary.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the source-Weil-form arithmetic rows,
  the two source-Weil-form mass leaves, two mass bridges, and three route
  consumers.  The audit output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound
```

Execution update, 2026-07-09, source-Weil-form atom read-off lowering:

```text
Result:
  Good 08A route-level finite-prime lowering milestone batch.  Not an
  unconditional RH proof.

Three milestone groups landed:
  1. The restricted and global package-atom read-off leaves are lowered below
     the same-symbol source-Weil-form carrier:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormRestrictedAtomReadOffCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormGlobalAtomReadOffCalibration

     These leaves no longer ask separately for support data or visible
     arithmetic data; those are generated by the same source-Weil-form carrier.
     The remaining atom condition is the real equality:

       route package certificate atom = source-Weil-form visible arithmetic atom

  2. The source-Weil-form atom leaves now bridge to the older carrier-level
     compatibility boundary:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataCarrierRestrictedAtomReadOffCalibration_of_sourceWeilFormRestrictedAtomReadOff
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataCarrierGlobalAtomReadOffCalibration_of_sourceWeilFormGlobalAtomReadOff

     The old carrier read-off names are no longer the active finite-prime
     bottom when the source-Weil-form carrier route is used.

  3. The non-pole, psi-pole, and QW-pole trace-front consumers now accept the
     lower source-Weil-form read-off API:

       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceWeilFormReadOffMassCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceWeilFormReadOffMassCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceWeilFormReadOffMassCalibrations

Current finite-prime bottom:
  for every square restricted carrier:
    - same-symbol source-Weil-form carrier;
    - source-Weil-form restricted atom read-off;
    - source-Weil-form global atom read-off;
    - restricted E-mass = archimedean;
    - global E-mass = -archimedean.

Rejected as solved:
  This update does not prove the source-Weil-form carrier, either atom read-off
  equality, or either E-mass row.  It only removes support data, visible
  arithmetic data, and carrier-level atom read-off from the active bottom once
  the same-symbol source-Weil-form carrier path is selected.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the two source-Weil-form atom
  read-off leaves, two carrier compatibility bridges, and three route
  consumers.  The audit output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound
```

Execution update, 2026-07-09, arithmetic/sum finite-prime split:

```text
Result:
  Good 08A route-level finite-prime dependency split.  Not an unconditional RH
  proof.

Three milestone groups landed:
  1. The lower finite-prime source-evaluation owner is split into arithmetic
     alignment and sum rows:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataArithmeticRows
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataSumRows
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataArithmeticSumRows

     `ArithmeticRows` contains support data, visible arithmetic data, and both
     package-atom alignment rows.  `SumRows` contains only the two E-written
     finite-prime sums.

  2. The unified E rows calibration now accepts arithmetic-sum rows:

       Route.normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataReadOff_of_arithmeticRows
       Route.normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataRows_of_arithmeticSumRows
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataArithmeticSumRowsCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataRowsCalibration_of_arithmeticSumRowsCalibration

  3. The route consumers and SourceRH exits now consume arithmetic-sum rows:

       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceEvaluationDataArithmeticSumRowsCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceEvaluationDataArithmeticSumRowsCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceEvaluationDataArithmeticSumRowsCalibrations

       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceEvaluationDataArithmeticSumRowsNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceEvaluationDataArithmeticSumRowsPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceEvaluationDataArithmeticSumRowsQWPoleCalibrations

Current combined bottom:
  for every square restricted carrier:
    - stored-route pole-pairing transport;
    - source-side TraceFrontEnd B2 comparison rows;
    - support-square scalar same-carrier alignment;
    - restricted QW_lambda scalar same-carrier alignment;
    - finite-prime arithmetic alignment rows;
    - E-written finite-prime sum rows.

Rejected as solved:
  This split does not prove the two E-written sum rows.  It proves that
  package-atom arithmetic alignment is a separate lower obligation from the
  finite-prime sum identities.  Do not merge the fields back into one anonymous
  existential or count the compatibility `LowerRows` name as a new bottom.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the arithmetic read-off bridge,
  arithmetic-sum rows bridge, calibration bridge, three trace-front consumers,
  and three SourceRH exits.  The audit output contained no `sorryAx`; it listed
  only:
    propext
    Classical.choice
    Quot.sound
```

Execution update, 2026-07-09, lower source-evaluation-data finite-prime rows:

```text
Result:
  Good 08A route-level finite-prime lowering milestone batch.  Not an
  unconditional RH proof.

Three milestone groups landed:
  1. The unified source-evaluation-data finite-prime rows owner is now
     generated from a lower support/visible-arithmetic/alignment owner:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataLowerRows
       Route.normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataRows_of_lowerRows

     The lower owner carries:

       - FixedLambdaCommonFinitePrimeSupportData
       - FixedLambdaSourceEvaluationVisibleArithmeticData
       - restricted package atom = visible arithmetic atom
       - global package atom = visible arithmetic atom
       - E-written scoped finite-prime balance
       - E-written global finite-prime mass cancellation

  2. The calibration boundary now accepts the lower rows directly:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataLowerRowsCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataRowsCalibration_of_lowerRowsCalibration

  3. The trace-front source-alignment consumers and SourceRH exits now consume
     lower finite-prime rows calibration:

       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceEvaluationDataLowerRowsCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceEvaluationDataLowerRowsCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceEvaluationDataLowerRowsCalibrations

       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceEvaluationDataLowerRowsNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceEvaluationDataLowerRowsPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceEvaluationDataLowerRowsQWPoleCalibrations

Current combined bottom:
  for every square restricted carrier:
    - stored-route pole-pairing transport;
    - source-side TraceFrontEnd B2 comparison rows;
    - support-square scalar same-carrier alignment;
    - restricted QW_lambda scalar same-carrier alignment;
    - one lower finite-prime owner containing support data, visible arithmetic,
      package-atom alignment, E-written scoped balance, and E-written global
      mass cancellation.

Rejected as solved:
  Support data plus visible arithmetic alone is not enough because it does not
  identify the route package atoms with the visible arithmetic atoms.  The
  restricted/global package-atom alignment rows are mandatory.  This update
  still does not prove the two E-written finite-prime sums.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the lower-row bridge, calibration
  bridge, three trace-front consumers, and three SourceRH exits.  The audit
  output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound
```

Execution update, 2026-07-09, unified source-evaluation-data finite-prime rows:

```text
Result:
  Good 08A route-level finite-prime lowering milestone batch.  Not an
  unconditional RH proof.

Three milestone groups landed:
  1. The common/evaluator-value finite-prime balance is now generated from a
     stronger same-carrier source-evaluation-data rows owner:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataRows
       Route.normalizedRouteBackedCC20SquareRestrictedCommonScopedFinitePrimeEvaluatorValueBalance_of_sourceEvaluationDataRows

     This owner does not restate the old evaluator-value balance.  It stores a
     single source-evaluation `E`, atom-to-E read-off for restricted and global
     atoms, and the balance sum written directly with `E.legacyValueAt`.

  2. The common global evaluator-value mass cancellation is generated from the
     same source-evaluation-data rows owner:

       Route.normalizedRouteBackedCC20SquareRestrictedCommonGlobalFinitePrimeEvaluatorValueMassCancellation_of_sourceEvaluationDataRows
       Route.normalizedRouteBackedCC20SquareRestrictedGlobalFinitePrimeMassCancellation_of_sourceEvaluationDataRows

     The old B3c evaluator-value mass row is now a derived compatibility layer
     when this same-carrier rows owner is available.

  3. The trace-front source-alignment route consumers and SourceRH exits now
     consume the unified finite-prime rows calibration:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataRowsCalibration
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceEvaluationDataFinitePrimeRowsCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceEvaluationDataFinitePrimeRowsCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceEvaluationDataFinitePrimeRowsCalibrations

       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceEvaluationDataFinitePrimeRowsNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceEvaluationDataFinitePrimeRowsPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceEvaluationDataFinitePrimeRowsQWPoleCalibrations

Current combined bottom:
  for every square restricted carrier:
    - stored-route pole-pairing transport;
    - source-side TraceFrontEnd B2 comparison rows;
    - support-square scalar same-carrier alignment;
    - restricted QW_lambda scalar same-carrier alignment;
    - one same-carrier source-evaluation-data finite-prime rows owner whose
      atom read-off feeds both:
        * common scoped finite-prime balance;
        * common global finite-prime mass cancellation.

Rejected as solved:
  This does not prove the source-evaluation-data finite-prime sums.  It only
  proves the previous two evaluator-value leaves are consequences of a single
  stronger same-carrier source-evaluation owner plus atom-to-E read-off.  Do
  not replace this with a raw Prop wrapper that restates evaluator-value
  balance/global mass, detector-only coverage, SourceRH, no-off-line
  source-zero, `True`, `Set.univ`, stored Mellin rows, or stored determinant
  rows.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the source-evaluation-data rows
  bridges, finite-prime calibration bridges, three trace-front consumers, and
  three SourceRH exits.  The audit output contained no `sorryAx`; it listed
  only:
    propext
    Classical.choice
    Quot.sound
```

Execution update, 2026-07-09, B3c common-global mass lowering:

```text
Result:
  Good 08A route-level B3c lowering milestone batch.  Not an unconditional RH
  proof.

Three milestone groups landed:
  1. The explicit route global finite-prime mass row was lowered to common
     global finite-prime arithmetic:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonGlobalFinitePrimeMassCancellation
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonGlobalFinitePrimeMathlibMassCancellation
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonGlobalFinitePrimeFilterMassCancellation
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonGlobalFinitePrimeSourceEvaluationMassCancellation
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonGlobalFinitePrimeEvaluatorValueMassCancellation

     The bridge uses the package common-atom global read-off:

       Source.CCM25Concrete.Package.global_finite_prime_sum_common_atoms_of_package

  2. The B3c calibration boundary now accepts the lower common global
     evaluator-value mass row:

       Route.NormalizedRouteBackedCC20SquareRestrictedGlobalFinitePrimeMassCancellationCalibration_of_evaluatorValueMassCalibration

     Higher compatibility bridges also exist for common, Mathlib, filter, and
     source-evaluation mass spellings.

  3. The source-alignment trace-front route consumers and SourceRH exits moved
     to the lower B3c socket:

       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentScopedBalanceEvaluatorValueGlobalMassCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentScopedBalanceEvaluatorValueGlobalMassCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentScopedBalanceEvaluatorValueGlobalMassCalibrations

       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentScopedBalanceEvaluatorValueGlobalMassNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentScopedBalanceEvaluatorValueGlobalMassPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentScopedBalanceEvaluatorValueGlobalMassQWPoleCalibrations

Current combined bottom:
  for every square restricted carrier:
    - stored-route pole-pairing transport;
    - source-side TraceFrontEnd B2 comparison rows;
    - support-square scalar same-carrier alignment;
    - restricted QW_lambda scalar same-carrier alignment;
    - scoped/common finite-prime balance, already lowerable to evaluator-value
      finite-prime balance;
    - common global finite-prime evaluator-value mass cancellation.

Rejected as solved:
  This does not prove B3c.  It only removes the route-symbol global `Finset.sum`
  as the active B3c bottom.  The new active B3c leaf is the common global
  evaluator-value mass cancellation row.  Detector-only coverage, SourceRH,
  no-off-line source-zero, `True`, `Set.univ`, stored Mellin rows, and stored
  determinant rows remain rejected as producers.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the new B3c common-global mass ladder,
  calibration bridges, three trace-front consumers, and three SourceRH exits.
  The audit output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound

  Static forbidden scan over the new diff found no new `sorry`, `admit`,
  `axiom`, `constant`, `opaque`, `unsafe`, `True`, or `Set.univ`.
```

Execution update, 2026-07-09, scoped/common finite-prime balance lowering:

```text
Result:
  Good 08A route-level finite-prime lowering milestone batch.  Not an
  unconditional RH proof.

Three milestone groups landed:
  1. The restricted finite-prime mass row is no longer the active route
     spelling once B3c global mass is also present.  The new route bridge is:

       Route.NormalizedRouteBackedCC20SquareRestrictedScopedFinitePrimeArchimedeanBalanceCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeArchimedeanCancellationCalibration_of_scopedBalance_globalMassCalibrations
       Route.NormalizedRouteBackedCC20SquareRestrictedRestrictedQWPoleCollapseCalibration_of_scopedBalance_globalMassCalibrations
       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeIndexDifferenceCalibration_of_scopedBalance_globalMassCalibrations

     Logic:

       scoped finite-prime balance:
         restricted_scoped_sum - global_scoped_sum = 2 * archimedean

       global mass:
         global_sum = -archimedean

       package scoped/full sum equality:
         restricted_sum = archimedean

       package QW_lambda formula:
         restricted QW_lambda = polePairing

  2. The source-alignment trace-front consumers moved to the lower combined
     B3a/B3c socket:

       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentScopedBalanceGlobalMassCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentScopedBalanceGlobalMassCalibrations
       Route.normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentScopedBalanceGlobalMassCalibrations

     and the route now has SourceRH exits from the same socket:

       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentScopedBalanceGlobalMassNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentScopedBalanceGlobalMassPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentScopedBalanceGlobalMassQWPoleCalibrations

  3. The scoped finite-prime balance itself was lowered to the existing common
     finite-prime arithmetic ladder:

       Route.NormalizedRouteBackedCC20SquareRestrictedCommonScopedFinitePrimeArchimedeanBalanceCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonScopedFinitePrimeMathlibBalanceCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonScopedFinitePrimeFilterBalanceCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonScopedFinitePrimeSourceEvaluationBalanceCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedCommonScopedFinitePrimeEvaluatorValueBalanceCalibration

Current combined bottom:
  for every square restricted carrier:
    - stored-route pole-pairing transport;
    - source-side TraceFrontEnd B2 comparison rows;
    - support-square scalar same-carrier alignment;
    - restricted QW_lambda scalar same-carrier alignment;
    - common/evaluator-value finite-prime balance, or any higher equivalent
      in the common/mathlib/filter/source-evaluation ladder;
    - explicit global finite-prime mass cancellation.

Rejected as solved:
  This does not prove the common finite-prime balance or the global mass row.
  It only proves that the old restricted-mass / restricted-QW-pole leaf is
  generated by scoped finite-prime balance plus global mass.  Detector-only
  coverage, SourceRH, no-off-line source-zero, `True`, `Set.univ`, stored
  Mellin rows, and stored determinant rows remain rejected as producers.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the new common finite-prime ladder,
  scoped-balance calibration bridges, three trace-front consumers, and three
  SourceRH exits.  The audit output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound

  Static forbidden scan over the new diff found no new `sorry`, `admit`,
  `axiom`, `constant`, `opaque`, `unsafe`, `True`, or `Set.univ`.
```

Execution update, 2026-07-09, B3a restricted-mass plus global-mass lowering:

```text
Result:
  Good 08A route-level B3a lowering milestone batch.  Not an unconditional RH
  proof.

Three milestone groups landed:
  1. The outside-global B3a mass row is no longer an independent producer:

       Route.normalizedRouteBackedCC20SquareRestrictedFinitePrimeOutsideGlobalMass_of_restrictedArchimedean_globalMass

     The proof uses:
       - package exact support for `restricted ⊆ global`;
       - restricted finite-prime mass equals the archimedean term;
       - global finite-prime mass equals `- archimedean`;
       - finite-set algebra:

           global_sum = restricted_sum + outside_global_sum

     Therefore:

           outside_global_sum = -2 * archimedean

  2. The B3a calibration boundary moved from outside-mass-only to
     restricted-mass plus B3c global-mass:

       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeArchimedeanCancellationCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeOutsideGlobalMassOnlyCalibration_of_restrictedArchimedean_globalMassCalibrations
       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeOutsideGlobalMassCalibration_of_restrictedArchimedean_globalMassCalibrations
       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeIndexDifferenceCalibration_of_restrictedArchimedean_globalMassCalibrations

     The old outside-mass-only API is now compatibility above this split.

  3. The source-alignment combined route exits now consume the restricted-mass
     plus global-mass B3a/B3c split:

       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentRestrictedArchimedeanGlobalMassNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentRestrictedArchimedeanGlobalMassPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentRestrictedArchimedeanGlobalMassQWPoleCalibrations

Current combined bottom:
  for every square restricted carrier:
    - stored-route pole-pairing transport;
    - source-side TraceFrontEnd B2 comparison rows;
    - support-square scalar same-carrier alignment;
    - restricted QW_lambda scalar same-carrier alignment;
    - restricted finite-prime mass equals archimedean;
    - explicit global finite-prime mass cancellation.

Rejected as solved:
  This does not prove B3a or B3c.  It proves that the previous outside-global
  mass leaf is a consequence of the restricted/global mass split and package
  exact support.  The restricted finite-prime mass row and global finite-prime
  cancellation remain open semantic producers.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the outside-mass producer, calibration
  bridges, three trace-front consumers, and three SourceRH exits.  The audit
  output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound

  Static forbidden scan over the new diff found no new `sorry`, `admit`,
  `axiom`, `constant`, `opaque`, `unsafe`, `True`, or `Set.univ`.
```

Execution update, 2026-07-09, B3a exact-support outside-mass-only lowering:

```text
Result:
  Good 08A route-level B3a lowering milestone batch.  Not an unconditional RH
  proof.

Three milestone groups landed:
  1. The B3a restricted-subset row is no longer an open route leaf:

       Route.normalizedRouteBackedCC20SquareRestrictedFinitePrimeRestrictedSubsetGlobal_of_packageExactSupport

     The proof uses the route bridge's same-carrier
     `ConcreteCCM25ArithmeticPackage` exact-support API:

       Source.CCM25Concrete.Package.restricted_exact_of_package_exact_support
       Source.CCM25Concrete.Package.global_exact_of_package_exact_support

     In first-principles terms:

       restricted membership
         -> prime-power + visible atom + lambda cut
         -> prime-power + visible atom
         -> global membership

  2. The B3a calibration boundary moved from
     "subset + outside-global mass" to "outside-global mass only":

       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeOutsideGlobalMassOnlyCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeRestrictedSubsetOutsideGlobalMassCalibration_of_outsideGlobalMassOnlyCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeOutsideGlobalMassCalibration_of_outsideGlobalMassOnlyCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeIndexDifferenceCalibration_of_outsideGlobalMassOnlyCalibration

     The old restricted-subset calibration path remains compatibility, not the
     active B3a bottom.

  3. The source-alignment combined route exits now consume the outside-mass-only
     B3a boundary:

       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentOutsideMassOnlyNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentOutsideMassOnlyPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentOutsideMassOnlyQWPoleCalibrations

Current combined bottom:
  for every square restricted carrier:
    - stored-route pole-pairing transport;
    - source-side TraceFrontEnd B2 comparison rows;
    - support-square scalar same-carrier alignment;
    - restricted QW_lambda scalar same-carrier alignment;
    - outside-global finite-prime mass value;
    - explicit global finite-prime mass cancellation.

Rejected as solved:
  This does not prove B3a.  It proves that the restricted-subset and
  decomposition parts of B3a are consequences of the route package exact
  support.  The outside-global mass value remains the real B3a producer.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the exact-support subset producer,
  outside-mass-only calibration bridges, three trace-front calibration
  consumers, and three SourceRH exits.  The audit output contained no
  `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound

  Static forbidden scan over the new producer/route changes found no new
  `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `True`, or
  `Set.univ`.  Diff hits for detector / SourceRH / no-off-line are existing
  route exits or rejection guards, not new producers.
```

Execution update, 2026-07-09, B3a restricted-subset outside-mass lowering:

```text
Result:
  Good 08A route-level B3a lowering milestone batch.  Not an unconditional RH
  proof.

Three milestone groups landed:
  1. B3a decomposition is no longer a free finite-prime row once the support
     shape is known:

       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeRestrictedSubsetGlobal
       Route.normalizedRouteBackedCC20SquareRestrictedFinitePrimeIndexDifferenceDecomposition_of_restrictedSubsetGlobal

     The proof is finite-set algebra:

       restricted_sum - global_sum
         =
       - outside_global_sum

     using `Finset.union_sdiff_of_subset` and `Finset.sum_union`.

  2. The B3a calibration is lowered below decomposition:

       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeRestrictedSubsetOutsideGlobalMassCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeOutsideGlobalMassCalibration_of_restrictedSubsetOutsideMassCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeIndexDifferenceCalibration_of_restrictedSubsetOutsideMassCalibration

     The remaining B3a leaves are now:
       - restricted index set is a subset of the global index set;
       - outside-global finite-prime mass has value `-2 * archimedean`.

  3. The source-alignment combined route exits now consume the lower B3a
     boundary:

       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentRestrictedSubsetOutsideMassNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentRestrictedSubsetOutsideMassPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentRestrictedSubsetOutsideMassQWPoleCalibrations

Current combined bottom:
  for every square restricted carrier:
    - stored-route pole-pairing transport;
    - source-side TraceFrontEnd B2 comparison rows;
    - support-square scalar same-carrier alignment;
    - restricted QW_lambda scalar same-carrier alignment;
    - restricted finite-prime index set subset global finite-prime index set;
    - outside-global finite-prime mass value;
    - explicit global finite-prime mass cancellation.

Rejected as solved:
  This does not prove B3a.  It proves only that the old decomposition row is
  finite-set algebra once the support-subset row is available.  The subset row
  and the outside-global mass value remain real B3a producers.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the new B3a support-subset API,
  finite-set decomposition bridge, lowered B3a calibration bridge, three route
  calibration bridges, and three SourceRH exits.  The audit output contained no
  `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound

  Static forbidden scan over the new diff found no new `sorry`, `admit`,
  `axiom`, `constant`, `opaque`, `unsafe`, `True`, or `Set.univ`.
```

Execution update, 2026-07-09, source-alignment outside-global combined socket:

```text
Result:
  Good 08A route-level lowering milestone batch.  Not an unconditional RH proof.

Three milestone groups landed:
  1. B1 old concrete-owner input is now explicitly compatibility:

       Route.NormalizedRouteBackedCC20SquareRestrictedConcretePolePairingOwnerCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedRoutePolePairingTransportCalibration_of_concretePolePairingOwnerCalibration

     The active B1 bottom remains stored-route pole-pairing transport.

  2. B2 whole-carrier calibration is split into source rows plus two
     same-carrier scalar alignments:

       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonSourceRowsCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontSupportSquareAlignmentCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontQWLambdaAlignmentCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration_of_sourceAlignmentCalibrations

     The old bundled trace-front row package is compatibility through
     `Classical.choice`; it is not the new semantic bottom.

  3. The main route now has named exits from the fully split trace-front socket:

       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentOutsideGlobalMassSplitNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentOutsideGlobalMassSplitPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentOutsideGlobalMassSplitQWPoleCalibrations

Current combined bottom:
  for every square restricted carrier:
    - stored-route pole-pairing transport;
    - source-side TraceFrontEnd B2 comparison rows;
    - support-square scalar same-carrier alignment;
    - restricted QW_lambda scalar same-carrier alignment;
    - finite-prime index decomposition plus outside-global-mass value;
    - explicit global finite-prime mass cancellation.

Rejected as solved:
  This does not prove B1, B2, B3a, or B3c.  It exposes the combined
  whole-carrier socket and demotes the older concrete-owner / bundled-row paths
  to compatibility producers.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the new B1 compatibility guard, B2
  source/alignment calibration APIs, three source-alignment outside-global
  calibration bridges, and three SourceRH exits.  The audit output contained no
  `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound

  Static forbidden scan over the new diff found no new `sorry`, `admit`,
  `axiom`, `constant`, `opaque`, `unsafe`, `True`, or `Set.univ`.  SourceRH and
  detector hits are route exits / existing rejection guards, not new producers.
```

Execution update, 2026-07-09, B3c global finite-prime mass split:

```text
Result:
  Accepted 08A route-level B3c lowering milestone batch.  Not an
  unconditional RH proof.

Three milestone groups landed:
  1. B3c now has an explicit global finite-prime mass calibration:

       Route.NormalizedRouteBackedCC20SquareRestrictedGlobalFinitePrimeMassCancellationCalibration

     This is lower than the non-pole-mass spelling because the route input is
     the same-square global finite-prime mass identity:

       global finite-prime mass = - archimedean mass

     The non-pole mass row is recovered by:

       Route.NormalizedRouteBackedCC20SquareRestrictedNonPoleMassVanishesCalibration_of_globalFinitePrimeMassCancellationCalibration

  2. The package-level global finite-prime / archimedean cancellation is now a
     separate compatibility calibration:

       Route.NormalizedRouteBackedCC20SquareRestrictedGlobalFinitePrimeArchimedeanCancellationCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedGlobalFinitePrimeMassCancellationCalibration_of_globalFinitePrimeArchimedeanCancellationCalibration

     This keeps the package read-off visible instead of hiding it inside a
     B3c collapse.

  3. The split trace-front route exits now consume the lower B3c boundary in
     both spellings:

       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonGlobalMassSplitNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonGlobalMassSplitPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonGlobalMassSplitQWPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonGlobalArchimedeanSplitNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonGlobalArchimedeanSplitPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonGlobalArchimedeanSplitQWPoleCalibrations

Current trace-front whole-carrier bottom:
  for every square restricted carrier:
    - stored-route pole-pairing transport;
    - carrier-supplied decode-to-projected-square alignment;
    - source-side TraceFrontEnd B2 comparison plus two scalar alignments;
    - finite-prime index-difference / archimedean balance;
    - explicit global finite-prime mass cancellation.

Rejected as solved:
  B3c has not been proved.  The package-global cancellation route is
  compatibility unless its package read-off producer is supplied.  Detector-only
  targets remain RH-level and are not lower 08A producers.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the new B3c calibration APIs,
  compatibility bridges, six calibration bridges, six WeilCriterion exits, and
  six SourceRH exits.  The audit output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound

  Static forbidden scan over `CC20RouteRealization.lean` found no new
  `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `True`, or
  `Set.univ`.  Hits for `SourceRH`, detector, and no-off-line remain route
  exits / rejection guards, not new producers.
```

Execution update, 2026-07-09, square B1 stored-route pole-pairing split:

```text
Result:
  Accepted 08A route-level B1 lowering milestone batch.  Not an unconditional
  RH proof.

Three milestone groups landed:
  1. B1 was split below the old square pole-pairing transport row:

       Route.NormalizedRouteBackedCC20SquareRestrictedRouteTestDecodesToProjectedSquare
       Route.NormalizedRouteBackedCC20SquareRestrictedRoutePolePairingTransport

     The first row is supplied by the square carrier's `square_eq_routeTest`.
     The second row is the stored route-test pole-pairing transport.  Together
     they reconstruct:

       Route.NormalizedRouteBackedCC20SquareRestrictedPolePairingTransport

  2. The active B1 whole-carrier calibration now has a lower producer:

       Route.NormalizedRouteBackedCC20SquareRestrictedRoutePolePairingTransportCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedPolePairingTransportCalibration_of_routePolePairingTransportCalibration

     The old concrete-owner path is compatibility only for this lower B1
     route:

       Route.normalizedRouteBackedCC20SquareRestrictedRoutePolePairingTransport_of_concreteOwner

  3. The three trace-front split route exits now accept the lower B1 input:

       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonRoutePolePairingSplitNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonRoutePolePairingSplitPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonRoutePolePairingSplitQWPoleCalibrations

Current trace-front whole-carrier bottom:
  for every square restricted carrier:
    - stored-route pole-pairing transport;
    - carrier-supplied decode-to-projected-square alignment;
    - source-side TraceFrontEnd B2 comparison plus two scalar alignments;
    - finite-prime index-difference / archimedean balance;
    - one B3c collapse: non-pole mass vanishing, psi=pole, or QW=pole.

Rejected as solved:
  A global concrete pole-pairing owner is no longer the active B1 boundary for
  the split trace-front route.  It remains a compatibility producer for the
  lower stored-route transport.  Detector-only targets remain RH-level and are
  not 08A producers.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the lower B1 owner, compatibility
  bridge, three calibration bridges, three WeilCriterion exits, and three
  SourceRH exits.  The audit output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound

  Static forbidden scan over `CC20RouteRealization.lean` found no new
  `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `True`, or
  `Set.univ`.  Hits for `SourceRH`, detector, and no-off-line remain route
  exits / rejection guards, not new producers.
```

Execution update, 2026-07-09, TraceFrontEnd B2 source/alignment split:

```text
Result:
  Accepted 08A route-level B2 lowering milestone batch.  Not an unconditional
  RH proof.

Three milestone groups landed:
  1. The trace-front B2 socket was split below the old bundled row package:

       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonSourceRows
       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontSupportSquareAlignment
       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontQWLambdaAlignment
       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonSplitB2Rows

     The source-side owner is now separated from the same-carrier scalar
     alignments.

  2. The active whole-carrier B2 API now consumes split rows:

       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration

     The old bundled row package remains only as a compatibility producer:

       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration_of_traceFrontComparisonRowsCalibration

     The split-bottom route exits still pass through the lower B2 boundary:

       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSplitNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSplitPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSplitQWPoleCalibrations

  3. The split detector-only targets were updated to use the split B2 rows and
     remain rejected by the existing no-off-line guards:

       Route.NormalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonSplitNonPoleMassCoverage
       Route.NormalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonSplitPsiPoleCoverage
       Route.NormalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonSplitQWPoleCoverage

Current trace-front B2 bottom:
  for every square restricted carrier:
    - source-side normalized TraceFrontEnd support-square/QW_lambda comparison;
    - support-square scalar same-carrier alignment;
    - restricted QW_lambda scalar same-carrier alignment.

Rejected as solved:
  Detector-only split trace-front coverage remains RH-level even after this B2
  split.  Do not use it as an 08A lower producer.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the split B2 declaration group, route
  exits, and rejection guards.  The audit output contained no `sorryAx`; it
  listed only:
    propext
    Classical.choice
    Quot.sound
```

Execution update, 2026-07-09, TraceFrontEnd global-QW and split-bottom sockets:

```text
Result:
  Accepted 08A route-level lowering/rejection milestone batch.  Not an
  unconditional RH proof.

Three milestone groups landed:
  1. The trace-front comparison route now has the global-QW B3c spelling:

       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleRows
       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration
       Route.normalizedRouteBackedCC20SquareRestrictedWeilCriterion_of_traceFrontComparisonQWPoleCalibration
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonQWPoleCalibration

  2. The trace-front route now has a split-bottom whole-carrier API:

       Route.NormalizedRouteBackedCC20SquareRestrictedPolePairingTransportCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration
       Route.NormalizedRouteBackedCC20SquareRestrictedFinitePrimeIndexDifferenceCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedNonPoleMassVanishesCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedPsiPoleCollapseCalibration
       Route.NormalizedRouteBackedCC20SquareRestrictedGlobalQWPoleCollapseCalibration

     These combine into the existing trace-front non-pole, psi-pole, and
     QW-pole route consumers, and directly into the square restricted Weil
     criterion / SourceRH exits:

       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSplitNonPoleMassCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSplitPsiPoleCalibrations
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSplitQWPoleCalibrations

  3. The split detector-only targets are rejected by named guards:

       Route.normalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonSplitNonPoleMassCoverage_iff_no_offline_source_zero
       Route.normalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonSplitPsiPoleCoverage_iff_no_offline_source_zero
       Route.normalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonSplitQWPoleCoverage_iff_no_offline_source_zero

Current trace-front 08A bottom:
  for every square restricted carrier:
    - B1 exact pole-pairing transport;
    - B2 TraceFrontEnd support-square/QW_lambda comparison rows;
    - B3a finite-prime index-difference / archimedean balance;
    - B3c one of non-pole mass vanishing, psi=pole, or QW=pole.

Rejected as solved:
  Detector-only split trace-front coverage is RH-level.  Do not use it as an
  08A lower producer.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the global-QW and split-bottom
  declaration groups.  The audit output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound
```

Execution update, 2026-07-09, TraceFrontEnd comparison B2 route lowering:

```text
Result:
  Accepted 08A route-level lowering/rejection milestone batch.  Not an
  unconditional RH proof.

Six milestones landed:
  1. B2b now has a route-facing producer from
     `TraceFrontEndData.NormalizedSupportSquareQWLambdaSourceComparison` plus
     scalar same-carrier evaluation alignment:

       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows
       Route.normalizedRouteBackedCC20SquareRestrictedTraceReadOffEquality_of_traceFrontComparisonRows
       Route.NormalizedRouteBackedCC20SquareRestrictedTraceTransportB2EqualityRows.ofTraceFrontComparisonRows

  2. The whole-carrier non-pole transport API now accepts this trace-front B2b
     producer:

       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration
       Route.normalizedRouteBackedCC20SquareRestrictedWeilCriterion_of_traceFrontComparisonNonPoleMassCalibration
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonNonPoleMassCalibration

  3. The detector-only trace-front non-pole target is rejected by a named guard:

       Route.normalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonNonPoleMassCalibrationCoverage_iff_no_offline_source_zero

  4. The trace-front route also has a B3c `psi(square)=pole(square)` spelling:

       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleRows
       Route.NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration

  5. The trace-front psi-pole API is connected to the route consumers:

       Route.normalizedRouteBackedCC20SquareRestrictedWeilCriterion_of_traceFrontComparisonPsiPoleCalibration
       Route.normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonPsiPoleCalibration

  6. The detector-only trace-front psi-pole target is also rejected:

       Route.normalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonPsiPoleCalibrationCoverage_iff_no_offline_source_zero

Current 08A square bottom after this batch:
  - exact square pole-pairing transport;
  - route-trace-data B2a support-square/no-defect row;
  - TraceFrontEnd scalar comparison + scalar same-carrier alignment for B2b;
  - finite-prime index-difference / archimedean balance;
  - non-pole finite-prime mass vanishing or psi(square)=pole(square).

Rejected as solved:
  Detector-only trace-front comparison coverage is RH-level, in both non-pole
  and psi-pole B3c forms.  Do not count it as 08A closure.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for all six milestone groups.  The audit
  output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound
```

Execution update, 2026-07-08, B2 owner and trace-data rejection:

```text
Result:
  Accepted 08A route-level lowering/rejection milestone.  Not an unconditional
  RH proof.

Milestone 1:
  The concrete CC20 source layer now has the import-facing square Mellin
  scaling theorem:

    Source.normalizedCC20ConcreteEvaluationData_mellinAt_convolutionSquare

  This supports the square/star-convolution finite-vanishing closure used by
  the square-backed carrier.  The proof unfolds the concrete legacy test
  equivalence instead of treating the abstract `Test` as a function.

Milestone 2:
  B2 for the square-backed carrier is now owned by a same-carrier
  `SourceTraceReadOffData`, not by free scalar rows:

    Route.NormalizedRouteBackedCC20SquareRestrictedTraceReadOffDataRows
    Route.normalizedRouteBackedCC20SquareRestrictedSupportSquareNoDefectTrace_of_sourceTraceReadOffDataRows
    Route.normalizedRouteBackedCC20SquareRestrictedNoDefectTraceQWLambda_of_sourceTraceReadOffDataRows
    Route.normalizedRouteBackedCC20SquareRestrictedNoDefectTraceScopedFormula_of_sourceTraceReadOffDataRows

  The route-facing API is:

    Route.NormalizedRouteBackedCC20SquareRestrictedTraceDataScopedFormulaCalibration

  Because the rows carry a real trace-data object, the API is a Prop-level
  `Nonempty` owner rather than pretending the data record itself is Prop.

Milestone 3:
  Detector-only coverage remains rejected even after B2 is owned by trace data:

    Route.NormalizedRouteBackedCC20SquareRestrictedDetectorTraceDataScopedFormulaCalibrationCoverage
    Route.normalizedRouteBackedCC20SquareRestrictedDetectorTraceDataScopedFormulaCalibrationCoverage_iff_no_offline_source_zero

  Therefore the dangerous branch

    detector family + same-carrier trace-data rows

  is still not a lower producer.  It is equivalent to the no-off-line
  source-zero statement under the 05C Yoshida detector existence hypothesis.

Current hard leaves:
  Whole-carrier, non-detector-only producers for:

    concrete pole-pairing owner
    same-carrier SourceTraceReadOffData
    finite-prime index difference
    non-pole mass annihilation
    detector coverage as a separate route-coverage input

Verification:
  WSL persistent mirror build passed:

    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the new source square-Mellin theorem,
  B2 trace-data owner theorems, trace-data calibration bridge, and detector
  trace-data rejection guard.  The audit output contained no `sorryAx`; it
  listed only:

    propext
    Classical.choice
    Quot.sound

  Static forbidden scan over the edited Source/Route files found no `sorry`,
  `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `Set.univ`, or bare `True`.
  `git diff --check` reported only CRLF warnings.
```

Execution update, 2026-07-08, Route A square-backed split:

```text
Result:
  Accepted decomposition milestone.  Not an unconditional RH proof.

Lean declarations added:
  Route.NormalizedRouteBackedCC20RestrictedConcretePolePairingOwner
  Route.NormalizedRouteBackedCC20RestrictedPolePairingSquareLift
  Route.normalizedRouteBackedCC20RestrictedPolePairingSquareLift_of_transport_concreteOwner
  Route.NormalizedRouteBackedCC20RestrictedScopedFinitePrimeArchimedeanBalance
  Route.NormalizedRouteBackedCC20RestrictedGlobalFinitePrimeArchimedeanCancellation
  Route.normalizedRouteBackedCC20RestrictedFinitePrimeArchimedeanCancellation_of_scopedBalance_globalCancellation
  Route.NormalizedRouteBackedCC20SquareRestrictedTest
  Route.NormalizedRouteBackedCC20SquareRestrictedPolePairingTransport
  Route.normalizedRouteBackedCC20SquareRestrictedPolePairingTransport_of_concreteOwner
  Route.NormalizedRouteBackedCC20SquareRestrictedTraceCalibrationRows
  Route.normalizedRouteBackedCC20SquareRestrictedWeilCriterion_of_traceCalibration
  Route.NormalizedRouteBackedCC20SquareRestrictedDetectorCoverage
  Route.normalizedCC20_source_rh_of_square_restricted_route_criterion

Meaning:
  The raw restricted-test carrier now exposes its hidden B1 cost:
    polePairing(convolutionSquare g) = polePairing g.

  The guard
    normalizedRouteBackedCC20RestrictedPolePairingSquareLift_of_transport_concreteOwner
  proves that ordinary concrete-owner transport plus the raw B1 transport
  already implies this square-lift row.  Future work cannot hide that row
  behind a generic transport theorem.

  A cleaner square-backed carrier is available.  It stores the route
  source-backed test as:
    normalizedCC20TestSpace.toRouteTest (normalizedCC20TestSpace.starConvolution test).

  For that carrier, ordinary concrete pole-pairing ownership proves the B1
  transport without a square-lift theorem.

Verification:
  WSL persistent mirror build passed:
    lake build ConnesWeilRH.Route.CC20RouteRealization

  Focused import-facing audit passed for the new guard, B3 lowering, B1'
  transport, square-backed criterion, and square-backed SourceRH bridge.
  The audit output contained no `sorryAx`; it listed only:
    propext
    Classical.choice
    Quot.sound

Active hard leaves after this split:
  Raw carrier:
    prove a narrow square-lift row or reject the raw B1 route.

  Square-backed carrier:
    build detector coverage and route rows for the square test:
      source-backed fixed-S square carrier
      triple-vanishing fields
      finite-prime visibility
      route common tuple
      restricted trace read-off
      global finite-prime / archimedean cancellation
```

Execution update, 2026-07-08, no-build static lowering:

```text
Result:
  Partial Route A interface progress.  Not accepted proof progress because no
  build or focused axiom audit was run.

Lean declarations added:
  Route.NormalizedRouteBackedCC20RestrictedTest
  Route.normalizedRouteBackedCC20RestrictedTest_of_yoshida_route_realization
  Route.NormalizedRouteBackedCC20RestrictedWeilCriterion
  Route.NormalizedRouteBackedCC20RestrictedDetectorCoverage
  Route.normalizedRouteBackedCC20RestrictedDetectorCoverage_of_yoshida_route_realizer
  Route.normalizedCC20_source_rh_of_restricted_route_criterion

Meaning:
  The Route A shape is now a Lean API:
    restricted route-backed tests
      + restricted Weil criterion
      + detector coverage
      -> SourceRH.

  Existing detector-specific route realizers supply the coverage half through
  `normalizedRouteBackedCC20RestrictedDetectorCoverage_of_yoshida_route_realizer`.

Remaining hard leaf:
  `NormalizedRouteBackedCC20RestrictedWeilCriterion`.

Why this is still hard:
  A restricted test stores final-sign route data for the source-backed fixed-S
  witness.  The criterion must still prove
    CC20WeilNonpositive normalizedCC20TestSpace r.test
  for the projected normalized test.  That requires a same-test formula owner
  connecting the route final sign/read-off to the projected CC20 local sum,
  without falling back to the rejected same-test Mathlib-bottom or
  detector-wide pole-pairing nonnegativity sockets.

Verification:
  No build by instruction.  Static `git diff --check` only; it reported CRLF
  warnings and no whitespace errors.
```

Execution update, 2026-07-08, no-build read-off split:

```text
Result:
  Useful split plus rejection guard.  Not accepted proof progress because no
  build or focused axiom audit was run.

Lean declarations added:
  Route.NormalizedRouteBackedCC20RestrictedLocalSumReadOff
  Route.normalizedRouteBackedCC20RestrictedLocalSumReadOff_of_yoshida_route_realization
  Route.normalizedRouteBackedCC20RestrictedWeilCriterion_of_localSumReadOff
  Route.NormalizedRouteBackedCC20RestrictedDetectorReadOffCoverage
  Route.normalizedRouteBackedCC20RestrictedDetectorReadOffCoverage_of_yoshida_route_realizer
  Route.normalizedCC20_source_rh_of_restricted_route_readOff_coverage
  Route.normalizedRouteBackedCC20RestrictedDetectorReadOffCoverage_iff_no_offline_source_zero

Meaning:
  The old hard leaf
    NormalizedRouteBackedCC20RestrictedWeilCriterion
  is now split into:
    ∀ r, NormalizedRouteBackedCC20RestrictedLocalSumReadOff r
      -> NormalizedRouteBackedCC20RestrictedWeilCriterion.

  Existing detector route realizers can supply read-off coverage for the
  detector tests they represent.

Rejection guard:
  Detector-only read-off coverage is not a lower theorem.  With the 05C
  Yoshida detector existence theorem, it is equivalent to:
    ∀ rho, sourceNontrivialZero rho -> rho.re = 1 / 2.

  Therefore the route cannot close 08A by proving only:
    for every off-line-source-zero Yoshida detector,
    there exists a represented restricted test with read-off.

Active hard leaf after this split:
  A lower formula owner for `NormalizedRouteBackedCC20RestrictedLocalSumReadOff`
  that is not detector-only, not SourceRH/no-off-line, and not the rejected
  same-test Mathlib-bottom/local-sum calibration path.

Verification:
  No build by instruction.  Static `git diff --check` only; it reported CRLF
  warnings and no whitespace errors.
```

Execution update, 2026-07-08, no-build formula lowering:

```text
Result:
  Route A hard leaf is now more precise.  Not accepted proof progress because
  no build or focused axiom audit was run.

Lean declarations added:
  Route.NormalizedRouteBackedCC20RestrictedPolePairingTraceFormula
  Route.NormalizedRouteBackedCC20RestrictedPositiveTraceQWLambda
  Route.NormalizedRouteBackedCC20RestrictedFinitePrimeArchimedeanCancellation
  Route.NormalizedRouteBackedCC20RestrictedPolePairingTransport
  Route.NormalizedRouteBackedCC20RestrictedTraceCalibrationRows
  Route.normalizedRouteBackedCC20RestrictedPolePairingTraceFormula_of_qwLambda_cancellation
  Route.normalizedRouteBackedCC20RestrictedPolePairingTraceFormula_of_traceCalibrationRows
  Route.normalizedRouteBackedCC20RestrictedLocalSumReadOff_of_polePairingTraceFormula
  Route.normalizedRouteBackedCC20RestrictedLocalSumReadOff_of_traceCalibrationRows
  Route.NormalizedRouteBackedCC20RestrictedTraceCalibration
  Route.normalizedRouteBackedCC20RestrictedWeilCriterion_of_traceCalibration
  Route.NormalizedRouteBackedCC20RestrictedDetectorPolePairingTraceCoverage
  Route.normalizedRouteBackedCC20RestrictedDetectorReadOffCoverage_of_polePairingTraceCoverage
  Route.normalizedRouteBackedCC20RestrictedDetectorPolePairingTraceCoverage_iff_no_offline_source_zero

Evidence from source scan:
  `SourceQWEqualsNegCC20WeilSum` is not a scalar formula owner.  Its fields
  store common-test rows, psi/sign expansion, trace legality,
  positiveTraceNonnegative, sign conventions, and finite-prime sign ownership.
  It does not store:
    normalizedCC20TestSpace.weilLocalSum (starConvolution r.test)
      =
    -positiveTrace(...)

  The concrete CC20 owner gives:
    normalizedCC20TestSpace.weilLocalSum g = -polePairing g
    normalizedCC20TestSpace.starConvolution g = convolutionSquare g

  Therefore the lower formula behind restricted local-sum read-off is:
    polePairing(convolutionSquare r.test)
      =
    positiveTrace(r.bridge.sourceTraceReadOff.archimedeanTest).

  This formula splits into three lower rows:
    1. concrete-to-source pole-pairing transport:
         concrete polePairing(convolutionSquare r.test)
           =
         route W.polePairing r.sourceBackedTest.weilTest

    2. positive-trace/QW-lambda read-off:
         positiveTrace(archimedeanTest)
           =
         W.qwLambda lambda weilTest weilTest

    3. finite-prime/archimedean cancellation:
         source_restricted_finite_prime_evaluator_sum pkg
           =
         W.archimedeanTerm(convolutionStar weilTest weilTest)

  Then the package row
    W.qwLambda lambda f f =
      archimedeanTerm(convolutionStar f f) + W.polePairing f - restrictedSum
  gives:
    positiveTrace = W.polePairing f.

Rejection guard:
  Detector-only pole-pairing/trace coverage is also equivalent to no-off-line
  source-zero under 05C detector existence.  It cannot be used as the lower
  Route A producer.

Active hard leaf after this split:
  Find or build non-detector-only owners for the three rows above.  The
  final-sign package does not currently own them.  They must come from real
  CC20/CCM25 transport and trace-calibration theorems, not from SourceRH,
  no-off-line source-zero, detector existence, stored final-sign rows,
  same-test Mathlib-bottom, or the false forall-g criterion.

Current coverage scan:
  positiveTrace = qwLambda:
    lowered to the existing route vocabulary:
      Route.NormalizedRouteBackedCC20RestrictedTraceReadOffEquality
        -> Route.NormalizedRouteBackedCC20RestrictedSupportSquareQWLambda
        -> Route.NormalizedRouteBackedCC20RestrictedPositiveTraceQWLambda.

    The wrapper exists, but the current restricted carrier still stores only
    `SourceRouteTraceData`, not a `SourceTraceReadOffData` field containing
    `restrictedTraceReadOffBridge`.  A producer must supply the equality row
    for the same restricted test.

  restricted finite-prime sum = archimedean term:
    the previous one-row target
      source_restricted_finite_prime_evaluator_sum pkg = archimedeanTerm(...)
    is too strong as a bottom theorem.  The actual existing route/source rows
    expose:
      Route.NormalizedRouteBackedCC20RestrictedScopedFinitePrimeArchimedeanBalance
      Route.NormalizedRouteBackedCC20RestrictedGlobalFinitePrimeArchimedeanCancellation

    These two rows imply the old `R = A` cancellation row.  Existing
    `SourceScopedFinitePrimeArchimedeanBalance` supplies only
      R_scoped - G_scoped = 2A.
    To derive `R = A`, the route still needs the extra global row
      G = -A.

  concrete-to-source pole-pairing transport:
    split into:
      Route.NormalizedRouteBackedCC20RestrictedConcretePolePairingOwner
      Route.NormalizedRouteBackedCC20RestrictedRouteTestDecodesToProjectedTest
      Route.NormalizedRouteBackedCC20RestrictedSinglePolePairingTransport
      Route.NormalizedRouteBackedCC20RestrictedPolePairingSquareLift

    `r.test_eq_routeTest` proves only the decode row:
      decode sourceBackedTest.weilTest = r.test.

    Even with a concrete pole-pairing owner for the route `WeilFormSymbols`,
    that gives only:
      concrete polePairing r.test = W.polePairing sourceBackedTest.weilTest.

    The CC20 local sum needs:
      concrete polePairing (convolutionSquare r.test)
        =
      W.polePairing sourceBackedTest.weilTest.

    The remaining extra row is therefore the square-lift:
      concrete polePairing (convolutionSquare r.test)
        =
      concrete polePairing r.test.

    This row is mathematically suspicious as a general theorem.  The next
    attack must either prove a narrower source-backed square carrier where the
    stored `sourceBackedTest.weilTest` is the square test, or reject the current
    B1 formula path.

    Guard added:
      Route.normalizedRouteBackedCC20RestrictedPolePairingSquareLift_of_transport_concreteOwner
      Route.normalizedRouteBackedCC20RestrictedPolePairingSquareLift_of_traceCalibrationRows_concreteOwner

    Meaning:
      if a future proof combines B1 transport with the ordinary concrete
      pole-pairing owner, Lean exposes the hidden square-lift obligation.
```

## 1. What Counts As Solved

Hard completion gate:

```text
The lane is solved only if:

1. Old weak path is deleted or compatibility-only:
     Route.normalizedCC20FiniteVanishingWeilCriterionInput
     Source.CC20FiniteVanishingWeilCriterion
       Source.normalizedCC20TestSpace
       Source.cc20TripleFiniteVanishingSet
     Dev.normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreFromTheorems

2. New semantic owner/API supplies the active proof object:
     a restricted source-backed CC20 test universe C_route
     plus a sufficiency theorem saying C_route detects the Yoshida tests
     needed for the CC20 RH exit.

3. Named theorem proves route inequality on C_route:
     for every route-backed restricted test, the route read-off gives
     CC20WeilNonpositive for its projected normalized CC20 test.

4. Named theorem proves sufficiency:
     for every off-critical-line standard source zero rho,
     05C supplies a Yoshida detector whose test is represented in C_route,
     and the C_route inequality contradicts Yoshida positivity.

5. Real consumer rewired:
     Dev.normalizedSelectedRouteBackedSourceRHFromTheorems
     or its lower source uses the restricted-test sufficiency theorem,
     not the false forall-g criterion and not detector-wide pole-pairing
     nonnegativity.

6. Smallest WSL build passes:
     lake build ConnesWeilRH.Route.CC20RouteRealization
       ConnesWeilRH.Dev.UnconditionalSkeleton

7. Focused axiom audit passes for:
     Route.<restricted-test inequality theorem>
     Route.<restricted-test sufficiency theorem>
     Dev.normalizedSelectedRouteBackedSourceRHFromTheorems
     Dev.unconditional_rh_skeleton
```

## 2. What Does Not Count

Rejected as not solved:

```text
- Proving or assuming
  CC20FiniteVanishingWeilCriterion normalizedCC20TestSpace
    cc20TripleFiniteVanishingSet.

- Proving detector-wide pole-pairing nonnegativity.

- Proving a selected one-test inequality and naming it C_route sufficiency.

- Making C_route definitionally equal to normalizedCC20TestSpace.

- Using SourceRH, no-off-line source-zero, True, Set.univ, accepted-source
  fields, stored determinant rows, or stored Mellin rows as the proof object.

- Reintroducing same-test Mathlib-bottom, same-test local-sum calibration, or
  same-test half-density trace formula as a final-path producer.
```

## 3. Current Evidence

```text
False global target:
  Source.CC20YoshidaInterpolationNode.not_normalizedCC20FiniteVanishingWeilCriterion

Current false input:
  Route.normalizedCC20FiniteVanishingWeilCriterionInput

Current RH-equivalent socket:
  Route.normalizedRouteBackedSourceZeroYoshidaDetectorPolePairingNonnegativeRealizer_iff_no_offline_source_zero

Current route-backed selected data:
  Route.RouteBackedCC20ExitInputData
  Route.final_sign_nonpositive_of_route_backed_cc20_exit_input_data
```

## 4. First-Principles Dependency Chain

```text
Route A
|
+-- C_route universe
|   |
|   +-- element:
|   |     normalized CC20 test g
|   |     source-backed fixed-S witness
|   |     route bridge certificate/read-off rows for that same test
|   |
|   +-- projection:
|         g : normalizedCC20TestSpace.Test
|
+-- route inequality
|   |
|   +-- route bridge gives SourceQWNonnegativeToCC20Nonpositive
|   +-- final sign gives CC20WeilNonpositive for the projected g
|
+-- sufficiency
|   |
|   +-- assume source zero rho off-line
|   +-- 05C gives Yoshida detector D for rho
|   +-- prove D.test has a C_route witness
|   +-- route inequality gives nonpositive local sum
|   +-- Yoshida detector gives positive local sum
|   +-- contradiction
|
+-- SourceRH
    |
    +-- Mathlib RH bridge
```

Current Route A attack tree after scalar lowering:

```text
08A restricted-test CC20 sufficiency
|
+-- A. Restricted universe
|   |
|   +-- owner:
|   |     Route.NormalizedRouteBackedCC20RestrictedTest
|   |
|   +-- fields:
|         test : normalizedCC20TestSpace.Test
|         sourceBackedTest : SourceBackedFixedSTest inputs
|         bridge : RouteBridgeCertificate inputs sourceBackedTest ledgers
|         test_eq_routeTest :
|           normalizedCC20TestSpace.toRouteTest test =
|           sourceBackedTest.weilTest
|
+-- B. Restricted inequality
|   |
|   +-- target:
|   |     Route.NormalizedRouteBackedCC20RestrictedWeilCriterion
|   |
|   +-- lowered to:
|   |     Route.NormalizedRouteBackedCC20RestrictedTraceCalibration
|   |
|   +-- trace calibration rows:
|       |
|       +-- B1. pole-pairing transport
|       |     concrete polePairing(convolutionSquare test)
|       |       =
|       |     route W.polePairing sourceBackedTest.weilTest
|       |
|       |     lowered to:
|       |       B1a. concrete pole-pairing owner
|       |            W.polePairing f =
|       |              concrete polePairing(decode f)
|       |
|       |       B1b. route test decodes to projected test
|       |            decode sourceBackedTest.weilTest = test
|       |            supplied by test_eq_routeTest
|       |
|       |       B1c. single-test transport
|       |            concrete polePairing test =
|       |              W.polePairing sourceBackedTest.weilTest
|       |
|       |       B1d. square-lift gap
|       |            concrete polePairing(convolutionSquare test) =
|       |              concrete polePairing test
|       |
|       |     current judgment:
|       |       B1d is not a harmless transport row.  It may be false for the
|       |       current carrier.  If false, change the restricted carrier so it
|       |       stores the source-backed square test instead of forcing a
|       |       pole-pairing square-lift theorem.
|       |
|       |     alternate carrier branch:
|       |       B1'. square-backed restricted carrier
|       |          owner:
|       |            Route.NormalizedRouteBackedCC20SquareRestrictedTest
|       |
|       |          sourceBackedTest.weilTest =
|       |            normalizedCC20TestSpace.toRouteTest
|       |              (normalizedCC20TestSpace.starConvolution test)
|       |
|       |       then ordinary concrete owner gives:
|       |          concrete polePairing(convolutionSquare test) =
|       |            W.polePairing sourceBackedTest.weilTest
|       |
|       |       Lean split added:
|       |          Route.NormalizedRouteBackedCC20SquareRestrictedPolePairingTransport
|       |          Route.normalizedRouteBackedCC20SquareRestrictedPolePairingTransport_of_concreteOwner
|       |          Route.NormalizedRouteBackedCC20SquareRestrictedTraceCalibrationRows
|       |          Route.normalizedRouteBackedCC20SquareRestrictedWeilCriterion_of_traceCalibration
|       |          Route.NormalizedRouteBackedCC20SquareRestrictedDetectorCoverage
|       |          Route.normalizedCC20_source_rh_of_square_restricted_route_criterion
|       |
|       |       cost:
|       |          detector coverage and route realization constructors must
|       |          represent the square test, not the raw detector test.  This is
|       |          a real API migration, not a wrapper rename.
|       |
|       |       current judgment:
|       |          B1' is cleaner than proving square-lift.  Its hard leaf moves to
|       |          square-test coverage:
|       |            for every Yoshida detector test g, build a route witness whose
|       |            source-backed fixed-S test is `starConvolution g`, while the
|       |            public CC20 projection remains g.
|       |
|       |          This requires new producers for triple-vanishing, finite-prime
|       |          visibility, route common tuple, and trace read-off on the square
|       |          test.  The current helper
|       |            sourceBackedFixedSTestWithNormalizedYoshidaDetector
|       |          is raw-test only:
|       |            weilTest := normalizedCC20TestSpace.toRouteTest detector.test.
|       |
|       +-- B2. positive trace / QW-lambda
|       |     positiveTrace(bridge.sourceTraceReadOff.archimedeanTest)
|       |       =
|       |     W.qwLambda lambda sourceBackedTest.weilTest sourceBackedTest.weilTest
|       |
|       |     lowered to:
|       |       B2a. restricted trace read-off equality
|       |            supportSquareTrace(archimedeanTest) =
|       |              W.qwLambda lambda sourceBackedTest.weilTest sourceBackedTest.weilTest
|       |
|       |       B2b. ordinary trace support-square
|       |            positiveTrace(archimedeanTest) =
|       |              supportSquareTrace(archimedeanTest)
|       |
|       |     current judgment:
|       |       B2b comes from route trace legality plus
|       |       `ordinaryTraceSupportSquare`.  B2a still needs a same-test
|       |       producer because `SourceRouteTraceData` does not store
|       |       `restrictedTraceReadOffBridge`.
|       |
|       +-- B3. finite-prime / archimedean cancellation
|             source_restricted_finite_prime_evaluator_sum pkg
|               =
|             W.archimedeanTerm(convolutionStar sourceBackedTest.weilTest
|                                             sourceBackedTest.weilTest)
|
|             lowered to:
|               B3a. scoped restricted/global balance
|                    source_restricted_scoped_sum pkg
|                      - source_global_scoped_sum pkg
|                      =
|                    2 * archimedeanTerm(square)
|
|               B3b. scoped/full package conversion
|                    source_restricted_scoped_sum = source_restricted_sum
|                    source_global_scoped_sum = source_global_sum
|
|               B3c. global finite-prime / archimedean cancellation
|                    source_global_finite_prime_evaluator_sum pkg
|                      =
|                    -archimedeanTerm(square)
|
|             current judgment:
|               B3a and B3b match existing infrastructure.  B3c is the new
|               hard row.  Existing balance rows alone give `R - G = 2A`,
|               not `R = A`.
|
+-- C. Detector coverage
|   |
|   +-- ordinary coverage:
|   |     Route.NormalizedRouteBackedCC20RestrictedDetectorCoverage
|   |
|   +-- supplied by:
|   |     Route.NormalizedRouteBackedYoshidaDetectorRouteRealizer
|   |
|   +-- rejected lower shortcut:
|         detector-only read-off / polePairingTrace coverage
|           <=>
|         no-off-line source-zero
|
+-- D. SourceRH exit
    |
    +-- accepted shape:
          05C Yoshida detector existence
          + restricted inequality
          + detector coverage
          -> SourceRH
```

## 5. Implementation Route

```text
A0. Static owner scan
    Find where RouteBackedCC20ExitInputData currently converts selected route
    positivity into CC20PropositionC1InputData.

A1. Define a restricted-test record
    Suggested owner:
      ConnesWeilRH.Route.CC20RouteRealization

    Suggested shape:
      structure NormalizedRouteBackedCC20RestrictedTest where
        test : normalizedCC20TestSpace.Test
        inputs : RouteInputs
        sourceBackedTest : SourceBackedFixedSTest inputs
        ledgers : RouteLedgers
        bridge : RouteBridgeCertificate inputs sourceBackedTest ledgers
        test_eq_routeTest :
          normalizedCC20TestSpace.toRouteTest test =
            sourceBackedTest.weilTest
        exitInputData :
          RouteBackedCC20ExitInputData inputs sourceBackedTest ledgers bridge

A2. Define C_route as a CC20TestSpace-like restricted carrier
    Prefer a separate predicate/record first.  Do not immediately coerce it
    into CC20TestSpace if doing so erases the route witness.

A3. Prove restricted route inequality
    Target shape:
      ∀ r : NormalizedRouteBackedCC20RestrictedTest,
        normalizedCC20TestSpace.compactSupportSmooth r.test →
        CC20VanishesOn normalizedCC20TestSpace cc20TripleFiniteVanishingSet r.test →
        CC20WeilNonpositive normalizedCC20TestSpace r.test

    This may need strengthening because RouteBackedCC20ExitInputData currently
    stores input.fullWeilPositivity for the route input, not a theorem about an
    arbitrary projected normalized test.

    2026-07-08 status:
      This is now the active 08A hard leaf:
        Route.NormalizedRouteBackedCC20RestrictedWeilCriterion.

      Later split:
        Route.NormalizedRouteBackedCC20RestrictedLocalSumReadOff
          -> Route.NormalizedRouteBackedCC20RestrictedWeilCriterion.

      Formula lowering:
        Route.NormalizedRouteBackedCC20RestrictedPolePairingTraceFormula
      -> Route.NormalizedRouteBackedCC20RestrictedLocalSumReadOff.

        Route.NormalizedRouteBackedCC20RestrictedTraceCalibration
          -> Route.NormalizedRouteBackedCC20RestrictedWeilCriterion.

      Detector-only read-off coverage is rejected as a lower producer by:
        Route.normalizedRouteBackedCC20RestrictedDetectorReadOffCoverage_iff_no_offline_source_zero.

      Detector-only pole-pairing/trace coverage is rejected as a lower producer by:
        Route.normalizedRouteBackedCC20RestrictedDetectorPolePairingTraceCoverage_iff_no_offline_source_zero.

A4. Prove detector membership / sufficiency
    Target shape:
      ∀ {rho}, sourceNontrivialZero rho → rho.re != 1/2 →
        ∃ r : NormalizedRouteBackedCC20RestrictedTest,
          r.test = detector.test

    This is the real hard leaf.  If the only proof uses no-off-line
    source-zero, reject the route.

    2026-07-08 status:
      Lowered to existing detector route realizer:
        NormalizedRouteBackedYoshidaDetectorRouteRealizer
          -> NormalizedRouteBackedCC20RestrictedDetectorCoverage.
      This does not close A4 unconditionally because the active Dev root still
      needs a producer for the detector route realizer, but the API split is
      now explicit.

      Strengthened read-off coverage from detector route realizers is also
      available, but it is now classified as RH-level diagnostic evidence, not
      as an accepted lower proof source.

A5. Rewire Dev final root only after A3 and A4 are real.
```

## 6. Static Rejection Scans

Run before accepting any edit:

```text
rg -n "CC20FiniteVanishingWeilCriterion\\s+normalizedCC20TestSpace|normalizedCC20FiniteVanishingWeilCriterionInput|PolePairingNonnegativeCoreFromTheorems|NoOffLineSourceZeroFromTheorems|SourceRHFromTheorems|Set\\.univ|\\bTrue\\b" ConnesWeilRH -g "*.lean"

rg -n "sameTest|MathlibBottom|HalfDensityTraceFormula|LocalSumCalibration|PolePairingTraceCalibration" ConnesWeilRH/Dev ConnesWeilRH/Route -g "*.lean"
```

Accept only if these names remain as rejection evidence or compatibility, not
as active producers for the 08A final route.

## 7. WSL Build Gate

Do not run during the current no-build execution round.

Milestone build, when Peter allows:

```text
flock /tmp/connes-weil-rh-lake.lock -c \
  'lake build ConnesWeilRH.Route.CC20RouteRealization ConnesWeilRH.Dev.UnconditionalSkeleton'
```

Use the persistent WSL mirror:

```text
/home/peter/verify/Connes-Weil-RH-Proof
```

## 8. Focused Axiom Audit

Milestone audit targets:

```lean
#check ConnesWeilRH.Route.<restricted-test inequality theorem>
#print axioms ConnesWeilRH.Route.<restricted-test inequality theorem>

#check ConnesWeilRH.Route.<restricted-test sufficiency theorem>
#print axioms ConnesWeilRH.Route.<restricted-test sufficiency theorem>

#check ConnesWeilRH.Dev.normalizedSelectedRouteBackedSourceRHFromTheorems
#print axioms ConnesWeilRH.Dev.normalizedSelectedRouteBackedSourceRHFromTheorems

#check ConnesWeilRH.Dev.unconditional_rh_skeleton
#print axioms ConnesWeilRH.Dev.unconditional_rh_skeleton
```

Expected final result must not contain `sorryAx`.

## 9. Final Acceptance Text

```text
Result:
  Good / partial / rejected.

Old weak path:
  <which false/RH-equivalent route was removed>

New semantic owner/API:
  <restricted-test owner>

Real consumer rewired:
  <Dev/Route theorem now consuming restricted sufficiency>

Same-object alias / wrapper rejection scan:
  <scan result>

Smallest WSL build:
  <command and result>

Focused axiom audit:
  <targets and result>

Semantic sufficiency for next route/RH step:
  <why the theorem is lower than SourceRH and not false forall-g>
```

## 2026-07-08 Route A square-backed coverage lowering

Result:
  Good partial progress.  This does not prove RH and does not close Route A,
  but it removes one wrapper layer from the clean B1' branch.

What changed:
  The square-backed branch now has an explicit detector-to-route production
  tree:

```text
Route A / square-backed B1'
|
+-- public CC20 test
|     detector.test
|
+-- route-backed source test
|     sourceBackedFixedSTestWithNormalizedYoshidaDetectorSquare
|       weilTest :=
|         toRouteTest (starConvolution detector.test)
|
+-- square fixed-S obligations
|     NormalizedRouteBackedYoshidaDetectorSquareFixedSTestRows
|     |
|     +-- square compactness
|     |     compactSupportSmooth (starConvolution detector.test)
|     |
|     +-- square triple vanishing
|           CC20VanishesOn F (starConvolution detector.test)
|
+-- finite-prime visibility
|     normalizedRouteBackedCC20TestFinitePrimeVisibility
|       sourceDataOwner (starConvolution detector.test)
|
+-- square trace route witness
|     NormalizedRouteBackedYoshidaDetectorSquareTraceRealization
|       |
|       +-- base SourceBackedFixedSTest
|       +-- CommonFinitePrimeArithmeticSourceData
|       +-- square fixed-S rows above
|       +-- SourceRouteTraceData for the square source-backed test
|       +-- local-sum / positiveTrace read-off
|
+-- square route realization
|     NormalizedRouteBackedYoshidaDetectorSquareRouteRealization
|       |
|       +-- ledgers from RouteLedgerClearingData.ofSourceBacked
|       +-- sign-defect classification
|       +-- SourceCommonTestTupleContract
|       +-- squareMatchesRouteTest
|
+-- square restricted carrier
|     NormalizedRouteBackedCC20SquareRestrictedTest
|       square_eq_routeTest :=
|         toRouteTest (starConvolution detector.test) = sourceBackedTest.weilTest
|
+-- square detector coverage
      normalizedRouteBackedCC20SquareRestrictedDetectorCoverage_of_yoshida_square_trace_realizer
```

New declarations:
  - `Route.NormalizedRouteBackedYoshidaDetectorSquareFixedSTestRows`
  - `Route.sourceBackedFixedSTestWithNormalizedYoshidaDetectorSquare`
  - `Route.NormalizedRouteBackedYoshidaDetectorSquareTraceRealization`
  - `Route.NormalizedRouteBackedYoshidaDetectorSquareRouteRealization`
  - `Route.NormalizedRouteBackedYoshidaDetectorSquareTraceRealizer`
  - `Route.NormalizedRouteBackedYoshidaDetectorSquareRouteRealizer`
  - `Route.normalizedRouteBackedYoshidaDetectorSquareRouteRealization_of_trace_realization`
  - `Route.normalizedRouteBackedYoshidaDetectorSquareRouteRealizer_of_trace_realizer`
  - `Route.normalizedRouteBackedCC20SquareRestrictedTest_of_yoshida_square_route_realization`
  - `Route.normalizedRouteBackedCC20SquareRestrictedDetectorCoverage_of_yoshida_square_trace_realizer`

Rejected as solved:
  This still does not prove the square trace realizer.  The active leaves are
  now explicit:

```text
square trace realizer
|
+-- square compactness for starConvolution detector.test
+-- square triple vanishing at {0, 1/2, 1}
+-- SourceRouteTraceData for the square source-backed test
+-- B2 restricted trace read-off equality
+-- B3c global finite-prime / archimedean cancellation
```

Why this matters:
  The previous raw carrier needed a suspicious row:

```text
polePairing(convolutionSquare g) = polePairing g
```

The square-backed carrier no longer asks for that row.  Instead it requires
the route witness itself to be built on the square test.  That is a real lower
mathematical/API obligation, not a same-object alias.

Smallest WSL build:
  Persistent mirror:
    `/home/peter/verify/Connes-Weil-RH-Proof`

  Command:
    `flock /tmp/connes-weil-rh-lake.lock -c 'lake build ConnesWeilRH.Route.CC20RouteRealization'`

  Result:
    passed.

Focused axiom audit:
  Import-facing audit passed with no `sorryAx`; all audited declarations
  depend only on:

```text
[propext, Classical.choice, Quot.sound]
```

  Audited declarations:
  - `sourceBackedFixedSTestWithNormalizedYoshidaDetectorSquare`
  - `normalizedRouteBackedYoshidaDetectorSquareRouteRealization_of_trace_realization`
  - `normalizedRouteBackedYoshidaDetectorSquareRouteRealizer_of_trace_realizer`
  - `normalizedRouteBackedCC20SquareRestrictedTest_of_yoshida_square_route_realization`
  - `normalizedRouteBackedCC20SquareRestrictedDetectorCoverage_of_yoshida_square_trace_realizer`

Next safe action:
  Continue Route A by attacking the square trace realizer leaves above.  Do not
  revive the raw square-lift row, the false forall-`g` criterion, or same-test
  Mathlib-bottom calibration as producers.

## 2026-07-08 Route A square fixed-S leaves discharged

Result:
  Good partial progress.  No build was run under the project default
  no-build cadence.

What changed:
  The square-backed trace realizer no longer asks callers to supply square
  compactness or square triple vanishing.  Source-level concrete CC20 theorems
  now supply those rows from the detector itself.

New Source API:
  - `Source.normalizedCC20ConcreteEvaluationData_mellinAt_convolutionSquare`
  - `Source.normalizedCC20TestSpace_starConvolution_compactSupportSmooth`
  - `Source.normalizedCC20TestSpace_starConvolution_vanishesOn`

Route API moved:
  - `Route.normalizedRouteBackedYoshidaDetectorSquareFixedSTestRows_of_detector`

```text
old square trace realizer input
|
+-- caller supplied square compactness
+-- caller supplied square triple vanishing
+-- caller supplied SourceRouteTraceData
|
v
new square trace realizer input
|
+-- detector.compactSupportSmooth
|     |
|     v
|     normalizedCC20TestSpace_starConvolution_compactSupportSmooth
|
+-- detector.vanishesOnF
|     |
|     v
|     normalizedCC20TestSpace_starConvolution_vanishesOn
|
+-- caller supplied SourceRouteTraceData for the square source-backed test
```

Current 08A square branch:

```text
square trace realizer
|
+-- SourceRouteTraceData for:
|     sourceBackedFixedSTestWithNormalizedYoshidaDetectorSquare
|
+-- local-sum / positiveTrace read-off
|
v
square route realization
|
v
square restricted detector coverage
|
v
normalizedCC20_source_rh_of_square_restricted_route_criterion
```

Still open:

```text
Route A square trace realizer
|
+-- build SourceRouteTraceData for the square source-backed test
+-- B2 restricted trace read-off equality
+-- B3c global finite-prime / archimedean cancellation
```

Rejected as solved:
  Do not reopen square compactness or square triple vanishing as Route A
  blockers unless a later typecheck shows these Source theorems fail.  Do not
  revive raw square-lift, false forall-`g` finite-vanishing, same-test
  Mathlib-bottom calibration, `SourceRH`, `True`, `Set.univ`, stored Mellin
  rows, or stored determinant rows.

Evidence:
  Static scan over the edited Source/Route files found no
  `sorry`, `admit`, `axiom`, `constant`, `opaque`, `Set.univ`, or bare `True`.

Verification:
  Not run.  Peter set the default cadence to no build.

Next safe action:
  Attack `SourceRouteTraceData` for the square source-backed test, then split
  the remaining B2/B3c scalar rows.

## 2026-07-08 Route A square trace-data leaf lowered

Result:
  Good milestone-grade progress.  No build was run under the project default
  no-build cadence.

What changed:
  The square-backed branch no longer treats `SourceRouteTraceData` as a caller
  supplied leaf.  The new square archimedean realization owns the data needed
  to construct it:

```text
NormalizedRouteBackedYoshidaDetectorSquareArchimedeanTraceRealization
|
+-- inputs
+-- base SourceBackedFixedSTest
+-- CommonFinitePrimeArithmeticSourceData
+-- archimedeanTest
+-- hilbertSchmidtGate
+-- lambda, 1 < lambda
+-- CCM25 arithmetic package for:
|     toRouteTest (starConvolution detector.test)
+-- local-sum / positiveTrace read-off
|
v
normalizedRouteBackedYoshidaDetectorSquareRouteTraceData_of_archimedean
|
+-- SourceRouteTraceData for:
|     sourceBackedFixedSTestWithNormalizedYoshidaDetectorSquare
|
v
normalizedRouteBackedYoshidaDetectorSquareTraceRealization_of_archimedean
|
v
normalizedRouteBackedYoshidaDetectorSquareTraceRealizer
|
v
normalizedRouteBackedCC20SquareRestrictedDetectorCoverage
```

New declarations:
  - `Route.NormalizedRouteBackedYoshidaDetectorSquareArchimedeanTraceRealization`
  - `Route.normalizedRouteBackedYoshidaDetectorSquareRouteTraceData_of_archimedean`
  - `Route.normalizedRouteBackedYoshidaDetectorSquareTraceRealization_of_archimedean`
  - `Route.NormalizedRouteBackedYoshidaDetectorSquareArchimedeanTraceRealizer`
  - `Route.normalizedRouteBackedYoshidaDetectorSquareTraceRealizer_of_archimedean_trace_realizer`
  - `Route.normalizedRouteBackedCC20SquareRestrictedDetectorCoverage_of_yoshida_square_archimedean_trace_realizer`

Current 08A square branch after this cut:

```text
square archimedean trace realizer
|
+-- choose archimedean test with Hilbert-Schmidt gate
+-- choose lambda and square-test CCM25 arithmetic package
+-- prove local-sum / positiveTrace read-off
|
v
square trace realizer
|
v
square route realizer
|
v
square restricted detector coverage
|
v
normalizedCC20_source_rh_of_square_restricted_route_criterion
```

Still open:

```text
Route A square branch
|
+-- local-sum / positiveTrace read-off for each detector
+-- B2 restricted trace read-off equality for the square source-backed test
+-- B3c global finite-prime / archimedean cancellation for the square package
```

Semantic judgment:
  This cut is stronger than the previous one because the route no longer asks
  an arbitrary caller to provide a full `SourceRouteTraceData` object for the
  square test.  It now constructs that object from lower archimedean trace
  fields and the CCM25 arithmetic package for the square route test.

Rejected as solved:
  The square archimedean realization still contains the local-sum read-off.
  Do not count this as 08A closure.  Do not replace the read-off with
  no-off-line source-zero, `SourceRH`, raw square-lift, false forall-`g`
  finite-vanishing, same-test Mathlib-bottom calibration, `True`, `Set.univ`,
  stored Mellin rows, or stored determinant rows.

Evidence:
  Static scan over edited Source/Route files found no `sorry`, `admit`,
  `axiom`, `constant`, `opaque`, `Set.univ`, or bare `True`.

Verification:
  Not run.  Peter set the default cadence to no build.

Next safe action:
  Split the square archimedean local-sum read-off.  If it reduces to
  no-off-line source-zero, reject it as an RH-equivalent producer.  If it can
  be expressed through B2/B3c scalar rows for the square package, push those
  rows down next.

## 2026-07-08 Route A square detector-read-off branch rejected

Result:
  Major route-level milestone.  The detector-specific square read-off
  production path is rejected as a lower producer.  This is not an
  unconditional RH proof.

What changed:
  The square branch was pushed past helper-level API lowering and judged at
  the route level.  The following path is now diagnostic/rejected:

```text
square archimedean trace realizer
|
+-- routeBackedLocalSumReadOff:
|     weilLocalSum(starConvolution detector.test)
|       =
|     -positiveTrace archimedeanTest
+-- hilbertSchmidtGate
|     |
|     v
|     positiveTrace >= 0
|
v
square trace realizer
|
v
square route realizer
|
v
detector-only square read-off coverage
|
v
no-off-line source-zero / SourceRH
```

New rejection/equivalence guards:
  - `Route.NormalizedRouteBackedSourceZeroYoshidaDetectorSquareArchimedeanTraceRealizer`
  - `Route.normalizedRouteBackedSourceZeroYoshidaDetectorSquareArchimedeanTraceRealizer_iff_no_offline_source_zero`
  - `Route.normalizedRouteBackedSourceZeroYoshidaDetectorSquareTraceRealizer_iff_no_offline_source_zero`
  - `Route.normalizedRouteBackedSourceZeroYoshidaDetectorSquareRouteRealizer_iff_no_offline_source_zero`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedDetectorReadOffCoverage`
  - `Route.normalizedRouteBackedCC20SquareRestrictedDetectorReadOffCoverage_iff_no_offline_source_zero`

Meaning:
  The square carrier still fixes the raw B1 square-lift problem, but the
  detector-specific witness path cannot close Route A.  Once the witness stores
  the same local-sum/positiveTrace read-off for a Yoshida detector, Hilbert
  positivity turns it into a nonpositive CC20 local sum, contradicting Yoshida
  positivity for any off-line source zero.  Therefore this path is exactly
  no-off-line source-zero in different packaging.

Rejected as solved:
  Do not continue 08A by trying to prove any of:

```text
NormalizedRouteBackedYoshidaDetectorSquareArchimedeanTraceRealizer
NormalizedRouteBackedYoshidaDetectorSquareTraceRealizer
NormalizedRouteBackedYoshidaDetectorSquareRouteRealizer
NormalizedRouteBackedCC20SquareRestrictedDetectorReadOffCoverage
```

  as the lower producer.  These are now RH-equivalent when used over the
  off-line Yoshida detector family.

Remaining valid 08A tree:

```text
Route A square branch
|
+-- full restricted carrier criterion
|     NormalizedRouteBackedCC20SquareRestrictedWeilCriterion
|
+-- must be proved for every square restricted carrier r,
|   not only for detector witnesses
|
+-- lower scalar rows for arbitrary r:
|   |
|   +-- B1'. concrete pole-pairing owner / square transport
|   |
|   +-- B2. RestrictedTraceReadOffEquality
|   |     supportSquareTrace(archimedeanTest)
|   |       =
|   |     qwLambda lambda squareTest squareTest
|   |
|   +-- B3a. SourceScopedFinitePrimeArchimedeanBalance
|   |
|   +-- B3c. global finite-prime / archimedean cancellation
|         globalFinitePrimeSum(pkg)
|           =
|         -archimedeanTerm(square)
|
v
square restricted criterion
|
v
detector coverage without read-off
|
v
SourceRH
```

Next safe action:
  Attack B2/B3c as rows for the whole square restricted carrier, or reject
  one of those rows as another RH-equivalent/false bottom.  Do not re-enter
  the detector-only square read-off route.

## 2026-07-08 Route A B2/B3c scalar bottom exposed

Result:
  Major route-level scalar lowering.  This is not an unconditional RH proof.

What changed:
  B2 and B3c are no longer vague scalar fields on the square restricted
  carrier.  They have been exposed as two named bottom sockets:

```text
08A square restricted scalar rows
|
+-- B2. restricted trace read-off
|   |
|   +-- target:
|   |     RestrictedTraceReadOffEquality
|   |       supportSquareTrace archimedeanTest
|   |         =
|   |       qwLambda lambda squareTest squareTest
|   |
|   +-- narrow owner:
|   |     NormalizedRouteBackedCC20SquareRestrictedTraceReadOffBridgeRows
|   |       carries RestrictedTraceReadOffBridgeContract
|   |
|   +-- stronger owner:
|         NormalizedRouteBackedCC20SquareRestrictedTraceReadOffDataRows
|           carries SourceTraceReadOffData
|           plus same archimedeanTest / lambda alignment
|
+-- B3c. global finite-prime / archimedean cancellation
    |
    +-- old target:
    |     globalFinitePrimeSum(pkg) = -archimedeanTerm(square)
    |
    +-- equivalent exposed target:
          GlobalQWPoleCollapse:
            qw(square) = poleFunctional(square)
```

New declarations:
  - `Route.NormalizedRouteBackedCC20SquareRestrictedTraceReadOffDataRows`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedTraceReadOffBridgeRows`
  - `Route.normalizedRouteBackedCC20SquareRestrictedTraceReadOffEquality_of_traceReadOffBridgeRows`
  - `Route.normalizedRouteBackedCC20SquareRestrictedTraceReadOffEquality_of_sourceTraceReadOffDataRows`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedGlobalQWPoleCollapse`
  - `Route.normalizedRouteBackedCC20SquareRestrictedGlobalFinitePrimeArchimedeanCancellation_iff_qwPoleCollapse`

Meaning:
  `SourceRouteTraceData` is not a B2 owner.  It stores the archimedean test,
  lambda, package, support-square transport, and positive trace
  nonnegativity, but it intentionally does not store
  `RestrictedTraceReadOffBridgeContract`.  B2 requires either that bridge or a
  same-carrier `SourceTraceReadOffData` with alignment.

  B3c is not an ordinary finite-prime read-off.  By the package global QW
  formula,

```text
qw(square)
  =
poleFunctional(square)
  - archimedeanTerm(square)
  - globalFinitePrimeSum(pkg)
```

  so proving

```text
globalFinitePrimeSum(pkg) = -archimedeanTerm(square)
```

  is exactly proving:

```text
qw(square) = poleFunctional(square)
```

  This is a strong global QW-pole collapse socket and must not be hidden
  behind package plumbing.

Rejected as solved:
  Do not close B2 from `SourceRouteTraceData` alone.
  Do not close B2 by importing the selected fixed-tuple row unless the same
  square restricted carrier and same archimedean/lambda alignment are proved.
  Do not close B3c by saying the package has finite-prime read-off; the real
  content is the QW-pole collapse above.

Current valid next tree:

```text
08A
|
+-- B2 route:
|   prove same-carrier restricted trace bridge/comparison
|   or reject it as selected-only / RH-equivalent / false
|
+-- B3c route:
    prove global QW-pole collapse
    or reject it as too strong / equivalent to a forbidden final socket
```

Verification:
  Not run.  Current project cadence defaults to no build.

Static evidence:
  Forbidden scan over edited Source/Route files found no `sorry`, `admit`,
  `axiom`, `constant`, `opaque`, `Set.univ`, or bare `True`.
  `git diff --check` reported only existing CRLF warnings.

## 2026-07-08 Route A B3c QW-pole collapse boundary

Result:
  Major B3c judgment.  B3c alone is not yet proved false or RH-equivalent, but
  B3c used as a detector-family calibrated producer is rejected as
  no-off-line equivalent.  This is not an unconditional RH proof.

What changed:
  The B3c exposed form is:

```text
NormalizedRouteBackedCC20SquareRestrictedGlobalQWPoleCollapse r
:
  qw(square) = poleFunctional(square)
```

  New row bundle using this exposed B3c form:

```text
NormalizedRouteBackedCC20SquareRestrictedTraceReadOffQWPoleCalibrationRows r
|
+-- B1'. concrete pole-pairing owner
+-- B2. restricted trace read-off equality
+-- B3a. scoped finite-prime / archimedean balance
+-- B3c. global QW-pole collapse
```

  New detector-family guard:

```text
NormalizedRouteBackedCC20SquareRestrictedDetectorQWPoleCalibrationCoverage
  <=>
forall source nontrivial zeros rho, rho.re = 1 / 2
```

New declarations:
  - `Route.NormalizedRouteBackedCC20SquareRestrictedTraceReadOffQWPoleCalibrationRows`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedTraceReadOffBalancedCalibrationRows.ofQWPoleRows`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedTraceCalibrationRows.ofQWPoleRows`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedDetectorQWPoleCalibrationCoverage`
  - `Route.normalizedRouteBackedCC20SquareRestrictedDetectorReadOffCoverage_of_qwPoleCalibrationCoverage`
  - `Route.normalizedRouteBackedCC20SquareRestrictedDetectorQWPoleCalibrationCoverage_iff_no_offline_source_zero`

Meaning:
  B3c does not by itself give a sign contradiction.  The isolated equality

```text
qw(square) = poleFunctional(square)
```

  needs B1/B2/B3a before it becomes a CC20 local-sum read-off.  Therefore the
  isolated B3c socket remains a possible hard mathematical/API leaf.

  However, if a future proof uses B3c together with B1, B2, and B3a only to
  cover the off-line Yoshida detector family, that calibrated detector
  coverage is exactly no-off-line source-zero.  It is not a lower producer.

Rejected as solved:
  Do not close 08A by proving detector-only
  `NormalizedRouteBackedCC20SquareRestrictedDetectorQWPoleCalibrationCoverage`.
  Do not claim B3c is harmless once bundled with detector-specific B1/B2/B3a
  rows; that bundle is now guarded as no-off-line equivalent.

Current B3c status:

```text
B3c alone:
  open hard leaf
  exposed as qw(square) = poleFunctional(square)

B3c + B1 + B2 + B3a over detector family:
  rejected
  equivalent to no-off-line source-zero
```

Next safe action:
  Attack B2's same-carrier restricted trace comparison first, or attack B3c
  as a whole-carrier global QW-pole theorem.  Do not attack detector-only
  calibrated coverage.

## 2026-07-08 Route A B3c psi-pole bottom exposed

Result:
  Major B3c lowering.  This is not an unconditional RH proof.

What changed:
  B3c is no longer merely a package/global-sum socket or a `qw` socket.  The
  bottom form is now:

```text
NormalizedRouteBackedCC20SquareRestrictedPsiPoleCollapse r
:
  psi(square) = poleFunctional(square)
```

  The B3c equivalence class is now explicit:

```text
B3c for a square restricted carrier r
|
+-- package spelling:
|     globalFinitePrimeSum(pkg) = -archimedeanTerm(square)
|
+-- package-free mass spelling:
|     sum_{n in globalPrimeIndexSet} finitePrimeTerm n square
|       =
|     -archimedeanTerm(square)
|
+-- QW spelling:
|     qw(square) = poleFunctional(square)
|
+-- bottom psi spelling:
      psi(square) = poleFunctional(square)
```

New declarations:
  - `Route.NormalizedRouteBackedCC20SquareRestrictedPsiPoleCollapse`
  - `Route.normalizedRouteBackedCC20SquareRestrictedGlobalFinitePrimeArchimedeanCancellation_iff_psiPoleCollapse`
  - `Route.normalizedRouteBackedCC20SquareRestrictedGlobalFinitePrimeMassCancellation_iff_psiPoleCollapse`
  - `Route.normalizedRouteBackedCC20SquareRestrictedGlobalQWPoleCollapse_iff_psiPoleCollapse`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedTraceReadOffPsiPoleCalibrationRows`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedDetectorPsiPoleCalibrationCoverage`
  - `Route.normalizedRouteBackedCC20SquareRestrictedDetectorReadOffCoverage_of_psiPoleCalibrationCoverage`
  - `Route.normalizedRouteBackedCC20SquareRestrictedDetectorPsiPoleCalibrationCoverage_iff_no_offline_source_zero`

Evidence:
  `Source.SourceWeilFormData.psi` is defined as:

```text
psi(F) =
  poleFunctional(F)
    - archimedeanTerm(F)
    - sum global finitePrimeTerm(F)
```

  and `Source.SourceWeilFormData.qw f g = psi(convolutionStar f g)`.  Therefore
  B3c forces the non-pole part of the Weil distribution on the same square to
  vanish.  The route proof now names that as the bottom socket instead of
  hiding it behind arithmetic-package read-off.

Rejected as solved:
  Do not close B3c by proving detector-only
  `NormalizedRouteBackedCC20SquareRestrictedDetectorPsiPoleCalibrationCoverage`.
  With B1/B2/B3a bundled, that coverage is now guarded as equivalent to:

```text
forall source nontrivial zeros rho, rho.re = 1 / 2
```

Current B3c status:

```text
B3c alone:
  open hard leaf
  unique named bottom:
    psi(square) = poleFunctional(square)

B3c + B1 + B2 + B3a over detector family:
  rejected
  equivalent to no-off-line source-zero
```

Next safe action:
  Either attack B3c as a whole-carrier `psi(square)=pole(square)` theorem, or
  switch to B2 and prove/reject the same-carrier restricted trace comparison.
  Do not spend more time on package read-off, QW read-off, or detector-family
  calibrated coverage as producers.

## 2026-07-08 Route A B3c non-pole mass bottom exposed

Result:
  Major B3c lowering.  This is not an unconditional RH proof.

What changed:
  The B3c bottom has been lowered one more layer from the `psi` spelling to
  the literal non-pole mass annihilation:

```text
NormalizedRouteBackedCC20SquareRestrictedNonPoleMassVanishes r
:
  archimedeanTerm(square)
    +
  sum_{n in globalPrimeIndexSet} finitePrimeTerm n square
    =
  0
```

  The active B3c equivalence class is now:

```text
B3c
|
+-- package spelling:
|     globalFinitePrimeSum(pkg) = -archimedeanTerm(square)
|
+-- finite-prime mass spelling:
|     globalFinitePrimeMass(square) = -archimedeanTerm(square)
|
+-- QW spelling:
|     qw(square) = poleFunctional(square)
|
+-- psi spelling:
|     psi(square) = poleFunctional(square)
|
+-- bottom non-pole spelling:
      archimedeanTerm(square) + globalFinitePrimeMass(square) = 0
```

New declarations:
  - `Route.NormalizedRouteBackedCC20SquareRestrictedNonPoleMassVanishes`
  - `Route.normalizedRouteBackedCC20SquareRestrictedGlobalFinitePrimeMassCancellation_iff_nonPoleMassVanishes`
  - `Route.normalizedRouteBackedCC20SquareRestrictedNonPoleMassVanishes_iff_psiPoleCollapse`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedTraceReadOffNonPoleMassCalibrationRows`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedDetectorNonPoleMassCalibrationCoverage`
  - `Route.normalizedRouteBackedCC20SquareRestrictedDetectorReadOffCoverage_of_nonPoleMassCalibrationCoverage`
  - `Route.normalizedRouteBackedCC20SquareRestrictedDetectorNonPoleMassCalibrationCoverage_iff_no_offline_source_zero`

Meaning:
  B3c is now identified as an exact cancellation theorem between the
  archimedean contribution and the global finite-prime mass on the same
  square.  It is not a trace bridge, not a package read-off, not a QW
  definition, and not a detector coverage statement.

Rejected as solved:
  Do not try to close B3c by proving detector-only
  `NormalizedRouteBackedCC20SquareRestrictedDetectorNonPoleMassCalibrationCoverage`.
  Once B1/B2/B3a are included, that detector-family target is already
  equivalent to no-off-line source-zero.

Current B3c hard bottom:

```text
For every relevant square restricted carrier r:
  prove or reject:
    archimedeanTerm(square)
      +
    globalFinitePrimeMass(square)
      =
    0
```

Next safe action:
  Either attack this whole-carrier non-pole mass annihilation theorem directly,
  or move to B2's same-carrier restricted trace comparison.  Do not spend more
  time on package/QW/psi renamings or detector-family calibrated coverage.

## 2026-07-08 Route A fully atomized square scalar API

Result:
  Major Route A dependency split.  This is not an unconditional RH proof.

What changed:
  The square route consumer now has a fully atomized whole-carrier scalar API:

```text
NormalizedRouteBackedCC20SquareRestrictedAtomicTraceCalibration
|
+-- for every square restricted carrier r:
    |
    +-- B1. concrete pole-pairing owner
    |
    +-- B2a. support-square/no-defect trace
    |     supportSquareTrace(archimedeanTest)
    |       =
    |     sourceNoDefectTrace(archimedeanTest)
    |
    +-- B2b. no-defect/`QW_lambda` read-off
    |     sourceNoDefectTrace(archimedeanTest)
    |       =
    |     qwLambda(lambda, squareTest, squareTest)
    |
    +-- B3a. finite-prime index difference
    |     restrictedFinitePrimeMass(square)
    |       -
    |     globalFinitePrimeMass(square)
    |       =
    |     2 * archimedeanTerm(square)
    |
    +-- B3c. non-pole mass annihilation
          archimedeanTerm(square)
            +
          globalFinitePrimeMass(square)
            =
          0
```

New declarations:
  - `Route.NormalizedRouteBackedCC20SquareRestrictedSupportSquareNoDefectTrace`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedNoDefectTraceQWLambda`
  - `Route.normalizedRouteBackedCC20SquareRestrictedTraceReadOffEquality_of_noDefectTraceQWLambda`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedTraceReadOffAtomicRows`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedAtomicTraceCalibration`
  - `Route.normalizedRouteBackedCC20SquareRestrictedWeilCriterion_of_atomicTraceCalibration`
  - `Route.normalizedCC20_source_rh_of_square_restricted_atomicTraceCalibration`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedDetectorAtomicCalibrationCoverage`
  - `Route.normalizedRouteBackedCC20SquareRestrictedDetectorAtomicCalibrationCoverage_iff_no_offline_source_zero`

Meaning:
  B2 is no longer hidden behind `RestrictedTraceReadOffBridgeContract`.
  Its real mathematical/API split is:

```text
supportSquareTrace
  =
sourceNoDefectTrace
  =
qwLambda
```

  The valid Route A target is whole-carrier atomized calibration.  Proving the
  same atomized rows only for the off-line Yoshida detector family is rejected:
  that detector-only coverage is equivalent to no-off-line source-zero.

Current hard leaves:

```text
Whole-carrier 08A square route:
  B1  concrete pole owner
  B2a support-square/no-defect trace
  B2b no-defect/`QW_lambda`
  B3a finite-prime index difference
  B3c non-pole mass annihilation
  plus detector coverage without read-off
```

Next safe action:
  Attack these five rows as whole-carrier APIs, starting with whether B2a/B2b
  have existing source owners for arbitrary square restricted carriers.  Do not
  use selected fixed-tuple trace rows unless same carrier and same
  archimedean/lambda equality are proved.

## 2026-07-08 Route A B2b scoped-formula bottom exposed

Result:
  Major B2 lowering.  This is not an unconditional RH proof.

What changed:
  B2b is no longer exposed as a `QW_lambda` read-off.  It is lowered through
  the CCM25 package identity to the scoped restricted archimedean formula:

```text
NormalizedRouteBackedCC20SquareRestrictedNoDefectTraceScopedFormula r
:
  sourceNoDefectTrace(archimedeanTest)
    =
  ScopedRestrictedArchimedeanFormula(W, squareTest, lambda, package)
```

  The current whole-carrier scalar API is:

```text
NormalizedRouteBackedCC20SquareRestrictedScopedFormulaTraceCalibration
|
+-- for every square restricted carrier r:
    |
    +-- B1. concrete pole-pairing owner
    +-- B2a. supportSquareTrace = sourceNoDefectTrace
    +-- B2b. sourceNoDefectTrace = ScopedRestrictedArchimedeanFormula
    +-- B3a. restricted/global finite-prime index difference
    +-- B3c. archimedean + global finite-prime mass = 0
```

New declarations:
  - `Route.NormalizedRouteBackedCC20SquareRestrictedNoDefectTraceScopedFormula`
  - `Route.normalizedRouteBackedCC20SquareRestrictedNoDefectTraceQWLambda_iff_scopedFormula`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedTraceReadOffScopedFormulaRows`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedScopedFormulaTraceCalibration`
  - `Route.normalizedCC20_source_rh_of_square_restricted_scopedFormulaTraceCalibration`
  - `Route.NormalizedRouteBackedCC20SquareRestrictedDetectorScopedFormulaCalibrationCoverage`
  - `Route.normalizedRouteBackedCC20SquareRestrictedDetectorScopedFormulaCalibrationCoverage_iff_no_offline_source_zero`

Meaning:
  B2b is not a generic `QW_lambda` package read-off.  The remaining semantic
  row is no-defect trace equals the scoped restricted archimedean formula for
  the same square carrier, same cutoff, and same package.

Rejected as solved:
  Detector-only scoped-formula calibration coverage is still equivalent to
  no-off-line source-zero.  Do not close Route A by proving the scoped-formula
  rows only for the off-line Yoshida detector family.

Next safe action:
  Attack B2a/B2b as whole-carrier source-owner rows:
  support-square/no-defect and no-defect/scoped-formula.  Selected fixed-tuple
  rows remain unusable unless same square carrier and same archimedean/lambda
  alignment are proved.

## 2026-07-09 Finite-Prime Source-Evaluation Carrier Split

Result:
  Accepted route-level lowering batch.  This is not an RH proof and not full
  08A closure.

Hard gate moved:

```text
old finite-prime bottom:
  ArithmeticSumRowsCalibration
    = arithmetic alignment + scoped E-balance + global E-mass

new finite-prime bottom:
  ArithmeticCarrierCalibration
  + CarrierSupportCalibration
  + CarrierVisibleArithmeticCalibration
  + CarrierRestrictedAtomReadOffCalibration
  + CarrierGlobalAtomReadOffCalibration
  + RestrictedFinitePrimeSourceEvaluationDataMassCalibration
  + GlobalFinitePrimeSourceEvaluationDataMassCalibration
```

What it means:
  The route consumer no longer has to treat scoped balance as an opaque sum
  row.  It can now use:

```text
restricted E-sum = archimedean
global E-sum     = -archimedean
```

  These two rows imply the old scoped balance by pure algebra, while both rows
  stay tied to the same source-evaluation object selected by the arithmetic
  carrier.

New key declarations:
  - `NormalizedRouteBackedCC20SquareRestrictedCommonRestrictedFinitePrimeSourceEvaluationDataArchimedeanMass`
  - `normalizedRouteBackedCC20SquareRestrictedCommonScopedFinitePrimeSourceEvaluationDataBalance_of_restrictedMass_globalMass`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonRestrictedFinitePrimeSourceEvaluationDataMassCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonScopedFinitePrimeSourceEvaluationDataBalanceCalibration_of_restricted_global`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataArithmeticCarrierCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataCarrierSupportCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataCarrierVisibleArithmeticCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataCarrierRestrictedAtomReadOffCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataCarrierGlobalAtomReadOffCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataArithmeticRowsCalibration_of_carrierSupportVisibleAtomReadOffs`

Route consumers moved:
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceEvaluationDataArithmeticRestrictedGlobalCalibrations`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceEvaluationDataArithmeticRestrictedGlobalCalibrations`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceEvaluationDataArithmeticRestrictedGlobalCalibrations`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceEvaluationDataCarrierRestrictedGlobalCalibrations`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceEvaluationDataCarrierRestrictedGlobalCalibrations`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceEvaluationDataCarrierRestrictedGlobalCalibrations`

Rejected as solved:
  `ArithmeticSumRowsCalibration`, scoped E-balance, and arithmetic rows are now
  compatibility/bridge layers for this lane, not the active named bottom.
  Do not fill the new carrier with `True`; use the data-bearing
  `Σ A, SourceEvaluationData A` carrier and keep the proof rows as
  separate leaves.

Verification:
  Smallest WSL build:
    `lake build ConnesWeilRH.Route.CC20RouteRealization`
    passed in the persistent WSL mirror.

  Focused import-facing axiom audit for the new bridges and route consumers:
    only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

Next safe action:
  Attack or reject the seven new finite-prime leaves directly:
  arithmetic carrier, support data, visible arithmetic, restricted atom
  read-off, global atom read-off, restricted E-mass, and global E-mass.

## 2026-07-09 Source-Weil-Form Carrier Lowering

Result:
  Accepted finite-prime source-owner lowering.  This is not RH closure and not
  full 08A closure.

Hard gate moved:

```text
old active arithmetic-carrier leaves:
  ArithmeticCarrierCalibration
  CarrierSupportCalibration
  CarrierVisibleArithmeticCalibration
  CarrierRestrictedAtomReadOffCalibration
  CarrierGlobalAtomReadOffCalibration
  Restricted E-mass
  Global E-mass

new active finite-prime source-owner shape:
  SourceWeilFormCarrierCalibration
  CarrierRestrictedAtomReadOffCalibration
  CarrierGlobalAtomReadOffCalibration
  Restricted E-mass
  Global E-mass
```

What changed:
  `SourceWeilFormCarrierCalibration` carries the same-symbol equality:

```text
for each route carrier r:
  Σ A, { sourceWeilForm : SourceWeilFormData A //
         r.inputs.ccm25.weilSymbols =
           sourceWeilForm.toWeilFormSymbols }
```

  From this carrier, Lean now derives:

```text
ArithmeticCarrierCalibration
CarrierSupportCalibration
CarrierVisibleArithmeticCalibration
```

  The same-symbol equality is part of the API because support/visible data
  over a different `WeilFormSymbols` object would be a false route producer.

New declarations:
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataArithmeticCarrierCalibration_of_sourceWeilFormCarrier`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataCarrierSupportCalibration_of_sourceWeilFormCarrier`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataCarrierVisibleArithmeticCalibration_of_sourceWeilFormCarrier`

Route consumers moved:
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceWeilFormCarrierAtomReadOffMassCalibrations`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceWeilFormCarrierAtomReadOffMassCalibrations`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceWeilFormCarrierAtomReadOffMassCalibrations`

Rejected as solved:
  Support data and visible arithmetic are no longer active independent leaves
  once the source-Weil-form carrier is accepted.  They become active again only
  if that carrier is rejected.

Verification:
  Smallest WSL build:
    `lake build ConnesWeilRH.Route.CC20RouteRealization`
    passed in the persistent WSL mirror.

  Focused import-facing axiom audit:
    only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

Next safe action:
  Attack or reject the remaining five finite-prime leaves:
  source-Weil-form carrier, restricted atom read-off, global atom read-off,
  restricted E-mass, and global E-mass.

## 2026-07-09 Source-Weil-Form Package-Atom Lowering

Result:
  Accepted route-level finite-prime lowering batch.  This is not RH closure and
  not full 08A closure.

Hard gate moved:

```text
old active source-Weil-form finite-prime shape:
  SourceWeilFormCarrier
  + restricted package atom = visible arithmetic atom
  + global package atom = visible arithmetic atom
  + DirectMassRows

new active source-Weil-form finite-prime shape:
  SourceWeilFormCarrier
  + PackageAtomReadOffCalibration
      package.commonCertificate.atoms.atIndex n
        =
      sourceWeilForm visible arithmetic atom n
      for every source-visible atom n
  + DirectMassRows
```

What changed:
  The restricted/global atom read-off leaves now come from one common package
  certificate read-off:

```text
PackageAtomReadOffCalibration
  -> RestrictedAtomReadOffCalibration
  -> GlobalAtomReadOffCalibration
```

  The new `DirectPackageRowsCalibration` groups this common package atom row
  with the same-symbol source-Weil-form carrier and direct mass rows, then
  bridges to the previous `DirectArithmeticRowsCalibration`.

Route consumers moved:
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceWeilFormDirectPackageRowsCalibrations`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceWeilFormDirectPackageRowsCalibrations`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceWeilFormDirectPackageRowsCalibrations`
  - `normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceWeilFormDirectPackageRowsNonPoleMassCalibrations`
  - `normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceWeilFormDirectPackageRowsPsiPoleCalibrations`
  - `normalizedCC20_source_rh_of_square_restricted_traceFrontComparisonSourceAlignmentSourceWeilFormDirectPackageRowsQWPoleCalibrations`

Rejected as solved:
  `PackageAtomReadOffCalibration` is still an active finite-prime leaf.  It is
  stronger than the old two projection rows, but it does not prove that the
  route package common certificate is constructed from the source-Weil-form
  visible arithmetic data.  Do not count it as B3 closure.

Verification:
  Smallest WSL build:
    `lake build ConnesWeilRH.Route.CC20RouteRealization`
    passed in the persistent WSL mirror.

  Focused import-facing axiom audit:
    only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

Next safe action:
  Attack the remaining package-certificate source:
  prove or reject that the route `ccm25ArithmeticPackage.commonCertificate`
  is the same common source-visible arithmetic certificate generated from the
  same-symbol `SourceWeilFormData`.  The two direct mass rows remain separate
  analytic finite-prime leaves.

## 2026-07-09 update: finite-prime term-mass lowering

Result:
  Good route-level lowering.  This is not RH closure and not full 08A closure.

Hard gate moved:

```text
old active finite-prime shape:
  SourceWeilFormCarrier
  + PackageAtomReadOffCalibration
  + DirectMassRows
      restricted/global sums written with sourceWeilForm.evaluation.legacyValueAt

new active finite-prime shape:
  SourceWeilFormCarrier
  + PackageAtomReadOffCalibration
  + DirectTermMassRows
      restricted/global sums written with
      sourceWeilForm.toWeilFormSymbols.finitePrimeTerm
```

What changed:
  Added source-Weil-form finite-prime term mass rows and proved the bridge back
  to the previous direct E-mass rows by using
  `FixedLambdaSourceWeilFormVisibleArithmeticData.termReadOff`.

  The route consumer and selected SourceRH exits now accept
  `DirectTermPackageRowsCalibration` through:

```text
DirectTermPackageRows
  -> DirectPackageRows
  -> DirectArithmeticRows
  -> trace-front non-pole / psi-pole / QW-pole calibrations
  -> selected SourceRH exits
```

New route-facing declarations:
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectRestrictedTermMassCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectGlobalTermMassCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermMassRowsCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectMassRowsCalibration_of_directTermMassRowsCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermPackageRowsCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectPackageRowsCalibration_of_directTermPackageRowsCalibration`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceWeilFormDirectTermPackageRowsCalibrations`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceWeilFormDirectTermPackageRowsCalibrations`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceWeilFormDirectTermPackageRowsCalibrations`

Verification:
  Smallest WSL build:
    `lake build ConnesWeilRH.Route.CC20RouteRealization`
    passed in the persistent WSL mirror.

  Focused import-facing axiom audit:
    only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

  Static forbidden scan over the diff found no new `sorry`, `admit`, `axiom`,
  `constant`, `opaque`, `unsafe`, `True`, or `Set.univ`.

Rejected as solved:
  The finite-prime term rows lower the mass API, but they are still the active
  analytic leaves.  Do not claim these rows prove the restricted/global mass
  identities, and do not move the active bottom back to E-written
  `DirectMassRows`.

Next safe action:
  Attack the remaining active bottom:

```text
SourceWeilFormCarrier
+ PackageAtomReadOffCalibration
+ DirectTermMassRows
```

## 2026-07-09 update: package atom-normalization source split

Result:
  Good route-level lowering.  This is not RH closure and not full 08A closure.

Hard gate moved:

```text
old active finite-prime shape:
  SourceWeilFormCarrier
  + PackageAtomReadOffCalibration
  + DirectTermMassRows

new active finite-prime shape:
  SourceWeilFormCarrier
  + VisibleAtomNormalization
      sourceAtoms.atIndex n =
        sourceWeilForm visible arithmetic atom n
  + PackageAtomNormalization
      package.commonCertificate.atoms =
        sourceAtoms
  + DirectTermMassRows
```

What changed:
  The package atom read-off is no longer one opaque row.  It is derived from a
  named source atom normalization and a separate package certificate atom
  equality:

```text
VisibleAtomNormalization
+ PackageAtomNormalization
  -> PackageAtomReadOffCalibration
```

  The route consumer and selected SourceRH exits now accept
  `DirectTermAtomNormalizationPackageRowsCalibration` through:

```text
DirectTermAtomNormalizationPackageRows
  -> DirectTermPackageRows
  -> DirectPackageRows
  -> DirectArithmeticRows
  -> trace-front non-pole / psi-pole / QW-pole calibrations
  -> selected SourceRH exits
```

New route-facing declarations:
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormVisibleAtomNormalizationCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageAtomNormalizationCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageAtomReadOffCalibration_of_atomNormalization`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermAtomNormalizationPackageRowsCalibration`
  - `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermPackageRowsCalibration_of_directTermAtomNormalizationPackageRowsCalibration`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonNonPoleMassCalibration_of_sourceAlignmentSourceWeilFormDirectTermAtomNormalizationPackageRowsCalibrations`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonPsiPoleCalibration_of_sourceAlignmentSourceWeilFormDirectTermAtomNormalizationPackageRowsCalibrations`
  - `normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceWeilFormDirectTermAtomNormalizationPackageRowsCalibrations`

Verification:
  Smallest WSL build:
    `lake build ConnesWeilRH.Route.CC20RouteRealization`
    passed in the persistent WSL mirror.

  Focused import-facing axiom audit:
    only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

  Static forbidden scan over the diff found no new `sorry`, `admit`, `axiom`,
  `constant`, `opaque`, `unsafe`, `True`, or `Set.univ`.

Rejected as solved:
  The package atom-normalization equality is still an active package-source
  leaf.  Do not claim the package certificate is generated from the
  source-Weil-form visible atoms until that equality has a lower producer.

Next safe action:
  Attack the remaining active bottom:

```text
SourceWeilFormCarrier
+ VisibleAtomNormalization
+ PackageAtomNormalization
+ DirectTermMassRows
```
