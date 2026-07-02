/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM24
import ConnesWeilRH.Source.CCM25
import ConnesWeilRH.Source.CC20

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
  ccm24 : Source.CCM24Interface
  ccm25 : Source.CCM25Interface
  cc20 : Source.CC20Interface

namespace RouteInputs

def ofExpandedSourcePackage
    (pkg : Source.SourceObject.SourceObjectPackage) : RouteInputs where
  ccm24 := Source.CCM24Interface.ofSourceObjectPackage pkg
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
  placeSet : inputs.ccm24.semilocalSymbols.PlaceSet
  window : inputs.ccm24.semilocalSymbols.Window
  semilocalTest : inputs.ccm24.semilocalSymbols.Test
  weilTest : TestFunction
  tripleVanishingSymbols : TripleVanishingSymbols
  canonicalModel :
    inputs.ccm24.semilocalSymbols.canonicalHilbertModel placeSet
  supportInWindow :
    inputs.ccm24.semilocalSymbols.supportInWindow semilocalTest window
  fourierSupportInWindow :
    inputs.ccm24.semilocalSymbols.fourierSupportInWindow semilocalTest window
  soninSpaceComparison :
    inputs.ccm24.semilocalSymbols.soninSpaceComparison window
  windowContainedInLambda :
    ∀ lambda : ℝ,
      1 < lambda →
        inputs.ccm24.semilocalSymbols.windowContainedInLambda window lambda
  lambdaCompatibilityBridge :
    ∀ lambda : ℝ,
      inputs.ccm24.semilocalSymbols.supportInWindow semilocalTest window →
        inputs.ccm24.semilocalSymbols.fourierSupportInWindow
            semilocalTest window →
          inputs.ccm24.semilocalSymbols.supportTransported semilocalTest
              window →
            inputs.ccm24.semilocalSymbols.convolutionSupportTransported
                semilocalTest window →
              inputs.ccm24.semilocalSymbols.fixedWindowExhaustionCompatible
                  window →
                inputs.ccm24.semilocalSymbols.windowContainedInLambda
                    window lambda →
                  inputs.ccm24.semilocalSymbols.lambdaCompatible
                    window lambda
  admissibleWindow : test.admissibleWindow
  tripleVanishingBridge :
    TripleVanishingSymbols.TripleVanishingStatement
        tripleVanishingSymbols →
      test.tripleVanishing
  tripleVanishingSourceHolds :
    TripleVanishingSymbols.TripleVanishingStatement tripleVanishingSymbols
  finitePrimeVisibilityBridge :
    WeilFormSymbols.FinitePrimeVisibilityStatement inputs.ccm25.weilSymbols
        weilTest weilTest →
      test.finitePrimesVisible
  finitePrimeTermNormalization :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement
      inputs.ccm25.weilSymbols weilTest weilTest

namespace SourceBackedFixedSTest

def ofExpandedSourcePackage
    (pkg : Source.SourceObject.SourceObjectPackage)
    (front : ExpandedSourceFixedSTestFrontEnd pkg) :
    SourceBackedFixedSTest (RouteInputs.ofExpandedSourcePackage pkg) where
  test := front.test
  placeSet := pkg.ccm24.sourcePlaceSet
  window := pkg.ccm24.sourceSupportWindow
  semilocalTest := pkg.ccm24.sourceTestLeg
  weilTest := pkg.commonTest.sourceTest
  tripleVanishingSymbols := front.tripleVanishingSymbols
  canonicalModel := pkg.ccm24.sourceCanonicalModelData
  supportInWindow := pkg.ccm24.sourceSupportInWindowData
  fourierSupportInWindow := pkg.ccm24.sourceFourierSupportInWindowData
  soninSpaceComparison := pkg.ccm24.sourceSoninSpaceComparisonData
  windowContainedInLambda := pkg.ccm24.sourceWindowContainedInLambdaData
  lambdaCompatibilityBridge := pkg.ccm24.sourceLambdaCompatibilityBridge
  admissibleWindow := front.admissibleWindow
  tripleVanishingBridge := front.tripleVanishingBridge
  tripleVanishingSourceHolds := front.tripleVanishingSourceHolds
  finitePrimeVisibilityBridge := front.finitePrimeVisibilityBridge
  finitePrimeTermNormalization :=
    Source.CCM25Interface.finite_prime_pointwise_term_of_source_object_package
      pkg pkg.commonTest.sourceTest pkg.commonTest.sourceTest

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
