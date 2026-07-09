/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM24
import ConnesWeilRH.Source.CCM24SourceModel
import ConnesWeilRH.Source.CCM25
import ConnesWeilRH.Source.CC20
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData

/-!
# Route definitions

Phase 1 keeps the analytic payload abstract. The point is to make every route
dependency explicit before replacing these predicates with richer objects.
-/

namespace ConnesWeilRH
namespace Route

structure FixedSTest where
  admissibleWindow : Prop
  tripleVanishing : Prop
  finitePrimesVisible : Prop

structure RouteLedgers where
  rankKilled : Prop
  poleKilled : Prop
  cdefExhausts : Prop

structure RouteInputs where
  ccm24 : SemilocalModelSymbols
  ccm25 : Source.CCM25Interface
  cc20 : Source.CC20Interface

/--
Route-facing CCM24 row owner for a source-backed fixed test.

The route layer keeps the compact `SourceBackedFixedSTest` bundle for API
stability, but active route consumers should read CCM24 rows through this
semantic owner instead of treating individual `g.<field>` projections as the
proof source.
-/
structure SourceBackedCCM24RouteConsumerRows
    (inputs : RouteInputs)
    (placeSet : inputs.ccm24.PlaceSet)
    (semilocalTest : inputs.ccm24.Test)
    (window : inputs.ccm24.Window) where
  canonicalModel :
    SemilocalModelSymbols.CanonicalSemilocalModelStatement inputs.ccm24
  canonicalHilbertModel :
    inputs.ccm24.canonicalHilbertModel placeSet
  supportTransport :
    SemilocalModelSymbols.SupportTransportStatement inputs.ccm24
  soninComparison :
    SemilocalModelSymbols.SoninComparisonStatement inputs.ccm24
  semilocalTest_eq_sourceTest :
    semilocalTest = inputs.ccm24.sourceTest
  soninSpaceComparison :
    inputs.ccm24.soninSpaceComparison window
  sourceSupportInWindow :
    inputs.ccm24.supportInWindow inputs.ccm24.sourceTest window
  sourceFourierSupportInWindow :
    inputs.ccm24.fourierSupportInWindow inputs.ccm24.sourceTest window
  fourierSupportGeometry :
    SemilocalModelSymbols.FourierSupportInvolutionGeometryData
      inputs.ccm24 window
  sourceConvolutionSupportTransported :
    inputs.ccm24.convolutionSupportTransported inputs.ccm24.sourceTest window
  boundedComparisonData : Type
  boundedComparisonDataWitness : boundedComparisonData
  boundedComparisonMap :
    boundedComparisonData → inputs.ccm24.boundedComparisonMap placeSet
  boundedComparisonInverse :
    boundedComparisonData → inputs.ccm24.boundedComparisonInverse placeSet
  windowContainedInLambda :
    ∀ lambda : ℝ,
      1 < lambda → inputs.ccm24.windowContainedInLambda window lambda
  lambdaCompatible :
    ∀ lambda : ℝ,
      1 < lambda → inputs.ccm24.lambdaCompatible window lambda

namespace SourceBackedCCM24RouteConsumerRows

theorem supportInWindow
    {inputs : RouteInputs}
    {placeSet : inputs.ccm24.PlaceSet}
    {semilocalTest : inputs.ccm24.Test}
    {window : inputs.ccm24.Window}
    (rows :
      SourceBackedCCM24RouteConsumerRows inputs placeSet semilocalTest window) :
    inputs.ccm24.supportInWindow semilocalTest window :=
  by
    rw [rows.semilocalTest_eq_sourceTest]
    exact rows.sourceSupportInWindow

theorem fourierSupportInWindow
    {inputs : RouteInputs}
    {placeSet : inputs.ccm24.PlaceSet}
    {semilocalTest : inputs.ccm24.Test}
    {window : inputs.ccm24.Window}
    (rows :
      SourceBackedCCM24RouteConsumerRows inputs placeSet semilocalTest window) :
    inputs.ccm24.fourierSupportInWindow semilocalTest window :=
  by
    rw [rows.semilocalTest_eq_sourceTest]
    exact rows.sourceFourierSupportInWindow

theorem convolutionSupportTransported
    {inputs : RouteInputs}
    {placeSet : inputs.ccm24.PlaceSet}
    {semilocalTest : inputs.ccm24.Test}
    {window : inputs.ccm24.Window}
    (rows :
      SourceBackedCCM24RouteConsumerRows inputs placeSet semilocalTest window) :
    inputs.ccm24.convolutionSupportTransported semilocalTest window :=
  by
    rw [rows.semilocalTest_eq_sourceTest]
    exact rows.sourceConvolutionSupportTransported

theorem canonicalModelCompatibility
    {inputs : RouteInputs}
    {placeSet : inputs.ccm24.PlaceSet}
    {semilocalTest : inputs.ccm24.Test}
    {window : inputs.ccm24.Window}
    (rows :
      SourceBackedCCM24RouteConsumerRows inputs placeSet semilocalTest window) :
    inputs.ccm24.scalingActionImplemented placeSet ∧
      inputs.ccm24.fourierGradingCompatible placeSet :=
  rows.canonicalModel placeSet rows.canonicalHilbertModel

theorem supportTransportRows
    {inputs : RouteInputs}
    {placeSet : inputs.ccm24.PlaceSet}
    {semilocalTest : inputs.ccm24.Test}
    {window : inputs.ccm24.Window}
    (rows :
      SourceBackedCCM24RouteConsumerRows inputs placeSet semilocalTest window) :
    inputs.ccm24.supportTransported semilocalTest window ∧
      inputs.ccm24.convolutionSupportTransported semilocalTest window :=
  rows.supportTransport semilocalTest window
    rows.supportInWindow rows.fourierSupportInWindow

theorem boundedComparisonRows
    {inputs : RouteInputs}
    {placeSet : inputs.ccm24.PlaceSet}
    {semilocalTest : inputs.ccm24.Test}
    {window : inputs.ccm24.Window}
    (rows :
      SourceBackedCCM24RouteConsumerRows inputs placeSet semilocalTest window) :
    inputs.ccm24.boundedComparisonMap placeSet ∧
      inputs.ccm24.boundedComparisonInverse placeSet :=
  ⟨rows.boundedComparisonMap rows.boundedComparisonDataWitness,
    rows.boundedComparisonInverse rows.boundedComparisonDataWitness⟩

theorem fixedWindowExhaustionCompatible
    {inputs : RouteInputs}
    {placeSet : inputs.ccm24.PlaceSet}
    {semilocalTest : inputs.ccm24.Test}
    {window : inputs.ccm24.Window}
    (rows :
      SourceBackedCCM24RouteConsumerRows inputs placeSet semilocalTest window) :
    inputs.ccm24.fixedWindowExhaustionCompatible window :=
  rows.soninComparison window rows.soninSpaceComparison

end SourceBackedCCM24RouteConsumerRows

/-- Route-facing owner for the fixed-test triple-vanishing row. -/
structure SourceBackedTripleVanishingRouteRows
    (test : FixedSTest) (tripleVanishingSymbols : TripleVanishingSymbols) where
  sourceTripleVanishing :
    TripleVanishingSymbols.TripleVanishingStatement tripleVanishingSymbols
  routeTripleVanishingBridge :
    TripleVanishingSymbols.TripleVanishingStatement
        tripleVanishingSymbols →
      test.tripleVanishing

namespace SourceBackedTripleVanishingRouteRows

theorem routeTripleVanishing
    {test : FixedSTest} {tripleVanishingSymbols : TripleVanishingSymbols}
    (rows :
      SourceBackedTripleVanishingRouteRows test tripleVanishingSymbols) :
    test.tripleVanishing :=
  rows.routeTripleVanishingBridge rows.sourceTripleVanishing

end SourceBackedTripleVanishingRouteRows

/-- Route-facing owner for finite-prime visibility on the fixed test. -/
structure SourceBackedFinitePrimeRouteRows
    (inputs : RouteInputs) (test : FixedSTest) (weilTest : TestFunction) where
  sourceDataOwner :
    Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      inputs.ccm25.weilSymbols
  visibilityStatement :
    WeilFormSymbols.FinitePrimeVisibilityStatement inputs.ccm25.weilSymbols
      weilTest weilTest
  finitePrimeVisibilityBridge :
    WeilFormSymbols.FinitePrimeVisibilityStatement inputs.ccm25.weilSymbols
        weilTest weilTest →
      test.finitePrimesVisible
  finitePrimeTermNormalization :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement
      inputs.ccm25.weilSymbols weilTest weilTest

namespace SourceBackedFinitePrimeRouteRows

theorem finitePrimesVisible
    {inputs : RouteInputs} {test : FixedSTest} {weilTest : TestFunction}
    (rows : SourceBackedFinitePrimeRouteRows inputs test weilTest) :
    test.finitePrimesVisible :=
  rows.finitePrimeVisibilityBridge rows.visibilityStatement

end SourceBackedFinitePrimeRouteRows

namespace RouteInputs

def ofExpandedSourcePackage
    (pkg : Source.SourceObject.SourceObjectPackage) : RouteInputs where
  ccm24 := Source.SourceObject.SourceObjectPackage.toSemilocalModelSymbols pkg
  ccm25 := Source.CCM25Interface.ofSourceObjectPackage pkg
  cc20 := Source.CC20Interface.ofSourceObjectPackage pkg

end RouteInputs

structure ExpandedSourceFixedSTestFrontEnd
    (pkg : Source.SourceObject.SourceObjectPackage) where
  test : FixedSTest
  tripleVanishingSymbols : TripleVanishingSymbols
  admissibleWindow : test.admissibleWindow
  tripleVanishingBridge :
    TripleVanishingSymbols.TripleVanishingStatement
        tripleVanishingSymbols →
      test.tripleVanishing
  tripleVanishingSourceHolds :
    TripleVanishingSymbols.TripleVanishingStatement tripleVanishingSymbols
  finitePrimeVisibilityStatement :
    WeilFormSymbols.FinitePrimeVisibilityStatement
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest pkg.commonTest.sourceTest
  finitePrimeVisibilityBridge :
    WeilFormSymbols.FinitePrimeVisibilityStatement
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest pkg.commonTest.sourceTest →
      test.finitePrimesVisible

/--
Goal 3A data for constructing the fixed-`S` test front end from an expanded
source package.

This record does not prove admissibility, triple vanishing, or finite-prime
visibility by itself.  It keeps those fixed-test obligations explicit while
pinning their CCM25 visibility statement to the package's common source test.
-/
structure FixedSTestFrontEndData
    (pkg : Source.SourceObject.SourceObjectPackage) where
  test : FixedSTest
  tripleVanishingSymbols : TripleVanishingSymbols
  admissibleWindow : test.admissibleWindow
  tripleVanishingBridge :
    TripleVanishingSymbols.TripleVanishingStatement
        tripleVanishingSymbols →
      test.tripleVanishing
  tripleVanishingSourceHolds :
    TripleVanishingSymbols.TripleVanishingStatement tripleVanishingSymbols
  finitePrimeVisibilityStatement :
    WeilFormSymbols.FinitePrimeVisibilityStatement
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest pkg.commonTest.sourceTest
  finitePrimeVisibilityBridge :
    WeilFormSymbols.FinitePrimeVisibilityStatement
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest pkg.commonTest.sourceTest →
      test.finitePrimesVisible

namespace FixedSTestFrontEndData

def toExpandedSourceFixedSTestFrontEnd
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestFrontEndData pkg) :
    ExpandedSourceFixedSTestFrontEnd pkg where
  test := data.test
  tripleVanishingSymbols := data.tripleVanishingSymbols
  admissibleWindow := data.admissibleWindow
  tripleVanishingBridge := data.tripleVanishingBridge
  tripleVanishingSourceHolds := data.tripleVanishingSourceHolds
  finitePrimeVisibilityStatement := data.finitePrimeVisibilityStatement
  finitePrimeVisibilityBridge := data.finitePrimeVisibilityBridge

theorem test_of_expanded_source_fixed_test_front_end
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestFrontEndData pkg) :
    (toExpandedSourceFixedSTestFrontEnd pkg data).test = data.test :=
  rfl

theorem triple_vanishing_symbols_of_expanded_source_fixed_test_front_end
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestFrontEndData pkg) :
    (toExpandedSourceFixedSTestFrontEnd pkg data).tripleVanishingSymbols =
      data.tripleVanishingSymbols :=
  rfl

theorem finite_prime_visibility_bridge_of_expanded_source_fixed_test_front_end
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestFrontEndData pkg) :
    (toExpandedSourceFixedSTestFrontEnd pkg data).finitePrimeVisibilityBridge =
      data.finitePrimeVisibilityBridge :=
  rfl

end FixedSTestFrontEndData

structure SourceBackedFixedSTest (inputs : RouteInputs) where
  test : FixedSTest
  placeSet : inputs.ccm24.PlaceSet
  window : inputs.ccm24.Window
  semilocalTest : inputs.ccm24.Test
  weilTest : TestFunction
  tripleVanishingSymbols : TripleVanishingSymbols
  scalingActionImplemented :
    inputs.ccm24.scalingActionImplemented placeSet
  fourierGradingCompatible :
    inputs.ccm24.fourierGradingCompatible placeSet
  supportInWindow :
    inputs.ccm24.supportInWindow semilocalTest window
  fourierSupportInWindow :
    inputs.ccm24.fourierSupportInWindow semilocalTest window
  supportTransported :
    inputs.ccm24.supportTransported semilocalTest window
  convolutionSupportTransported :
    inputs.ccm24.convolutionSupportTransported
      semilocalTest window
  soninSpaceComparison :
    inputs.ccm24.soninSpaceComparison window
  boundedComparisonMap :
    inputs.ccm24.boundedComparisonMap placeSet
  boundedComparisonInverse :
    inputs.ccm24.boundedComparisonInverse placeSet
  ccm24RouteConsumerRows :
    SourceBackedCCM24RouteConsumerRows inputs placeSet semilocalTest window
  sourceBackedBoundedComparisonData : Type
  sourceBackedBoundedComparisonDataWitness :
    sourceBackedBoundedComparisonData
  sourceBackedBoundedComparisonMap :
    sourceBackedBoundedComparisonData →
      inputs.ccm24.boundedComparisonMap placeSet
  sourceBackedBoundedComparisonInverse :
    sourceBackedBoundedComparisonData →
      inputs.ccm24.boundedComparisonInverse placeSet
  fixedWindowExhaustionCompatible :
    inputs.ccm24.fixedWindowExhaustionCompatible window
  windowContainedInLambda :
    ∀ lambda : ℝ,
      1 < lambda →
        inputs.ccm24.windowContainedInLambda window lambda
  lambdaCompatible :
    ∀ lambda : ℝ,
      1 < lambda →
        inputs.ccm24.lambdaCompatible window lambda
  admissibleWindow : test.admissibleWindow
  tripleVanishingBridge :
    TripleVanishingSymbols.TripleVanishingStatement
        tripleVanishingSymbols →
      test.tripleVanishing
  tripleVanishingSourceHolds :
    TripleVanishingSymbols.TripleVanishingStatement tripleVanishingSymbols
  tripleVanishingRouteRows :
    SourceBackedTripleVanishingRouteRows test tripleVanishingSymbols
  finitePrimeVisibilityBridge :
    WeilFormSymbols.FinitePrimeVisibilityStatement inputs.ccm25.weilSymbols
        weilTest weilTest →
      test.finitePrimesVisible
  finitePrimeVisibilityStatement :
    WeilFormSymbols.FinitePrimeVisibilityStatement inputs.ccm25.weilSymbols
      weilTest weilTest
  finitePrimeRouteRows :
    SourceBackedFinitePrimeRouteRows inputs test weilTest
  finitePrimeSourceDataOwner :
    Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      inputs.ccm25.weilSymbols
  finitePrimeTermNormalization :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement
      inputs.ccm25.weilSymbols weilTest weilTest

namespace SourceBackedFixedSTest

def ofExpandedSourcePackage
    (pkg : Source.SourceObject.SourceObjectPackage)
    (front : ExpandedSourceFixedSTestFrontEnd pkg) :
    SourceBackedFixedSTest (RouteInputs.ofExpandedSourcePackage pkg) where
  test := front.test
  placeSet := pkg.ccm24.semilocalSymbols.sourcePlaceSet
  window := pkg.ccm24.sourceSupportWindow
  semilocalTest := pkg.ccm24.semilocalSymbols.sourceTest
  weilTest := pkg.commonTest.sourceTest
  tripleVanishingSymbols := front.tripleVanishingSymbols
  scalingActionImplemented := by
    let hFixed :=
      pkg.ccm24.sourceModel.soninComparison pkg.ccm24.sourceSupportWindow
        pkg.ccm24.sourceSoninSpaceComparisonData
    exact hFixed.2.2.1 pkg.ccm24.semilocalSymbols.sourcePlaceSet hFixed.2.1
  fourierGradingCompatible := by
    let hFixed :=
      pkg.ccm24.sourceModel.soninComparison pkg.ccm24.sourceSupportWindow
        pkg.ccm24.sourceSoninSpaceComparisonData
    exact hFixed.2.2.2.1 pkg.ccm24.semilocalSymbols.sourcePlaceSet hFixed.2.1
  supportInWindow := pkg.ccm24.sourceSoninSpaceComparisonData.1
  fourierSupportInWindow :=
    pkg.ccm24.sourceFourierSupportInvolutionGeometryData.fourierSupportInWindow
  supportTransported :=
    SemilocalModelSymbols.supportTransported_of_supportInWindow
      pkg.ccm24.sourceSoninSpaceComparisonData.1
  convolutionSupportTransported :=
    pkg.ccm24.sourceFourierSupportInvolutionGeometryData.convolutionSupportTransported
  soninSpaceComparison :=
    pkg.ccm24.sourceSoninSpaceComparisonData
  boundedComparisonMap := by
    exact
      pkg.ccm24.sourceBackedBoundedComparisonMap
        pkg.ccm24.sourceBackedBoundedComparisonDataWitness
  boundedComparisonInverse := by
    exact
      pkg.ccm24.sourceBackedBoundedComparisonInverse
        pkg.ccm24.sourceBackedBoundedComparisonDataWitness
  ccm24RouteConsumerRows := by
    let hFixed :=
      pkg.ccm24.sourceModel.soninComparison pkg.ccm24.sourceSupportWindow
        pkg.ccm24.sourceSoninSpaceComparisonData
    exact
      { canonicalModel := pkg.ccm24.sourceModel.canonicalSemilocalModel
        canonicalHilbertModel := hFixed.2.1
        supportTransport := pkg.ccm24.sourceModel.supportTransport
        soninComparison := pkg.ccm24.sourceModel.soninComparison
        semilocalTest_eq_sourceTest := rfl
        soninSpaceComparison := pkg.ccm24.sourceSoninSpaceComparisonData
        sourceSupportInWindow := pkg.ccm24.sourceSoninSpaceComparisonData.1
        sourceFourierSupportInWindow :=
          pkg.ccm24.sourceFourierSupportInvolutionGeometryData.fourierSupportInWindow
        fourierSupportGeometry :=
          pkg.ccm24.sourceFourierSupportInvolutionGeometryData
        sourceConvolutionSupportTransported :=
          pkg.ccm24.sourceFourierSupportInvolutionGeometryData.convolutionSupportTransported
        boundedComparisonData :=
          pkg.ccm24.sourceBackedBoundedComparisonData
        boundedComparisonDataWitness :=
          pkg.ccm24.sourceBackedBoundedComparisonDataWitness
        boundedComparisonMap :=
          pkg.ccm24.sourceBackedBoundedComparisonMap
        boundedComparisonInverse :=
          pkg.ccm24.sourceBackedBoundedComparisonInverse
        windowContainedInLambda := fun lambda hlambda =>
          Source.ccm24_source_window_contained_in_lambda
            pkg.ccm24.sourceModel pkg.ccm24.sourceSupportWindow hlambda
        lambdaCompatible := fun lambda hlambda =>
          Source.ccm24_source_lambda_compatible
            pkg.ccm24.sourceModel pkg.ccm24.sourceSupportWindow hlambda }
  sourceBackedBoundedComparisonData :=
    pkg.ccm24.sourceBackedBoundedComparisonData
  sourceBackedBoundedComparisonDataWitness :=
    pkg.ccm24.sourceBackedBoundedComparisonDataWitness
  sourceBackedBoundedComparisonMap :=
    pkg.ccm24.sourceBackedBoundedComparisonMap
  sourceBackedBoundedComparisonInverse :=
    pkg.ccm24.sourceBackedBoundedComparisonInverse
  fixedWindowExhaustionCompatible := by
    exact
      pkg.ccm24.sourceModel.soninComparison pkg.ccm24.sourceSupportWindow
        pkg.ccm24.sourceSoninSpaceComparisonData
  windowContainedInLambda := fun lambda hlambda =>
    Source.ccm24_source_window_contained_in_lambda
      pkg.ccm24.sourceModel pkg.ccm24.sourceSupportWindow hlambda
  lambdaCompatible := fun lambda hlambda =>
    Source.ccm24_source_lambda_compatible
      pkg.ccm24.sourceModel pkg.ccm24.sourceSupportWindow hlambda
  admissibleWindow := front.admissibleWindow
  tripleVanishingBridge := front.tripleVanishingBridge
  tripleVanishingSourceHolds := front.tripleVanishingSourceHolds
  tripleVanishingRouteRows :=
    { sourceTripleVanishing := front.tripleVanishingSourceHolds
      routeTripleVanishingBridge := front.tripleVanishingBridge }
  finitePrimeVisibilityBridge := front.finitePrimeVisibilityBridge
  finitePrimeVisibilityStatement := front.finitePrimeVisibilityStatement
  finitePrimeRouteRows :=
    { sourceDataOwner := pkg.commonFinitePrimeArithmeticSourceDataOwner
      visibilityStatement := front.finitePrimeVisibilityStatement
      finitePrimeVisibilityBridge := front.finitePrimeVisibilityBridge
      finitePrimeTermNormalization :=
        front.finitePrimeVisibilityStatement.finitePrimeTermNormalization }
  finitePrimeSourceDataOwner := pkg.commonFinitePrimeArithmeticSourceDataOwner
  finitePrimeTermNormalization :=
    front.finitePrimeVisibilityStatement.finitePrimeTermNormalization

def ofExpandedSourcePackageWithCCM24Model
    (pkg : Source.SourceObject.SourceObjectPackage)
    (front : ExpandedSourceFixedSTestFrontEnd pkg)
    (model : Source.CCM24SourceModel)
    (hSymbols :
      model.semilocalSymbols =
        (RouteInputs.ofExpandedSourcePackage pkg).ccm24) :
    SourceBackedFixedSTest (RouteInputs.ofExpandedSourcePackage pkg) :=
  ofExpandedSourcePackage pkg front

theorem weil_test_of_expanded_source_package
    (pkg : Source.SourceObject.SourceObjectPackage)
    (front : ExpandedSourceFixedSTestFrontEnd pkg) :
    (ofExpandedSourcePackage pkg front).weilTest =
      pkg.commonTest.sourceTest :=
  rfl

theorem semilocal_window_of_expanded_source_package
    (pkg : Source.SourceObject.SourceObjectPackage)
    (front : ExpandedSourceFixedSTestFrontEnd pkg) :
    (ofExpandedSourcePackage pkg front).window =
      pkg.ccm24.sourceSupportWindow :=
  rfl

theorem weil_test_of_fixed_test_front_end_data
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestFrontEndData pkg) :
    (ofExpandedSourcePackage pkg
      (FixedSTestFrontEndData.toExpandedSourceFixedSTestFrontEnd
        pkg data)).weilTest =
      pkg.commonTest.sourceTest :=
  rfl

theorem semilocal_window_of_fixed_test_front_end_data
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestFrontEndData pkg) :
    (ofExpandedSourcePackage pkg
      (FixedSTestFrontEndData.toExpandedSourceFixedSTestFrontEnd
        pkg data)).window =
      pkg.ccm24.sourceSupportWindow :=
  rfl

theorem finite_prime_visibility_bridge_of_fixed_test_front_end_data
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestFrontEndData pkg) :
    (ofExpandedSourcePackage pkg
      (FixedSTestFrontEndData.toExpandedSourceFixedSTestFrontEnd
        pkg data)).finitePrimeVisibilityBridge =
      data.finitePrimeVisibilityBridge :=
  rfl

end SourceBackedFixedSTest

end Route
end ConnesWeilRH
