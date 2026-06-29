/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.AdmissibleWindow
import ConnesWeilRH.Source.ObjectExpandedRows

/-!
# Fixed-test front-end staging

Goal 3 turns the expanded source package into the fixed-test front end consumed
by the route.  This module keeps the remaining fixed-test obligations explicit
while proving the definitional read-offs that prevent tuple drift.
-/

namespace ConnesWeilRH
namespace Route

/--
Goal 3B obligation data for the fixed-test front end.

The record carries the route test and its fixed-test obligations, plus read-off
equalities that keep the route test tied to the expanded source package's
common test, CCM24 source leg, CCM24 window, and CCM25 symbols.
-/
structure FixedSTestObligationData
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
  routeTest : TestFunction
  routeTest_eq_commonTest : routeTest = pkg.commonTest.sourceTest
  semilocalTest_eq_sourceLeg :
    pkg.ccm24.sourceTestLeg = pkg.ccm24.sourceTestLeg := rfl
  semilocalWindow_eq_sourceWindow :
    pkg.ccm24.sourceSupportWindow = pkg.ccm24.sourceSupportWindow := rfl
  ccm25Symbols_eq_package :
    (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols =
      pkg.ccm25.weilSymbols := rfl
  finitePrimeVisibilityBridge :
    WeilFormSymbols.FinitePrimeVisibilityStatement
        pkg.ccm25.weilSymbols pkg.commonTest.sourceTest
        pkg.commonTest.sourceTest →
      test.finitePrimesVisible

namespace FixedSTestObligationData

/--
Goal 3B constructor from fixed-test obligation data to the Goal 3A data
record.
-/
def toFixedSTestFrontEndData
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestObligationData pkg) :
    FixedSTestFrontEndData pkg where
  test := data.test
  tripleVanishingSymbols := data.tripleVanishingSymbols
  admissibleWindow := data.admissibleWindow
  tripleVanishingBridge := data.tripleVanishingBridge
  tripleVanishingSourceHolds := data.tripleVanishingSourceHolds
  finitePrimeVisibilityBridge := by
    rw [data.ccm25Symbols_eq_package]
    exact data.finitePrimeVisibilityBridge

def toExpandedSourceFixedSTestFrontEnd
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestObligationData pkg) :
    ExpandedSourceFixedSTestFrontEnd pkg :=
  (data.toFixedSTestFrontEndData pkg).toExpandedSourceFixedSTestFrontEnd pkg

theorem fixed_test_front_end_data_test
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestObligationData pkg) :
    (data.toFixedSTestFrontEndData pkg).test = data.test :=
  rfl

theorem fixed_test_front_end_data_triple_vanishing_symbols
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestObligationData pkg) :
    (data.toFixedSTestFrontEndData pkg).tripleVanishingSymbols =
      data.tripleVanishingSymbols :=
  rfl

theorem expanded_front_end_test
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestObligationData pkg) :
    (data.toExpandedSourceFixedSTestFrontEnd pkg).test = data.test :=
  rfl

theorem route_test_eq_common_test
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestObligationData pkg) :
    data.routeTest = pkg.commonTest.sourceTest :=
  data.routeTest_eq_commonTest

theorem source_backed_weil_test_eq_common_test
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestObligationData pkg) :
    (SourceBackedFixedSTest.ofExpandedSourcePackage pkg
      (data.toExpandedSourceFixedSTestFrontEnd pkg)).weilTest =
      pkg.commonTest.sourceTest :=
  rfl

theorem source_backed_semilocal_test_eq_source_leg
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestObligationData pkg) :
    (SourceBackedFixedSTest.ofExpandedSourcePackage pkg
      (data.toExpandedSourceFixedSTestFrontEnd pkg)).semilocalTest =
      pkg.ccm24.sourceTestLeg :=
  rfl

theorem source_backed_window_eq_source_window
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestObligationData pkg) :
    (SourceBackedFixedSTest.ofExpandedSourcePackage pkg
      (data.toExpandedSourceFixedSTestFrontEnd pkg)).window =
      pkg.ccm24.sourceSupportWindow :=
  rfl

theorem source_backed_ccm25_symbols_eq_package
    (pkg : Source.SourceObject.SourceObjectPackage)
    (_data : FixedSTestObligationData pkg) :
    (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols =
      pkg.ccm25.weilSymbols :=
  rfl

/--
Goal 3C bridge: the fixed-test finite-prime visibility statement comes from
the concrete CCM25 arithmetic rows attached to the same package common test.
-/
theorem finite_prime_visibility_statement_of_concrete_arithmetic_rows
    (pkg : Source.SourceObject.SourceObjectPackage) :
    WeilFormSymbols.FinitePrimeVisibilityStatement
      pkg.ccm25.weilSymbols pkg.commonTest.sourceTest
      pkg.commonTest.sourceTest :=
  Source.CCM25Concrete.Interface.finite_prime_visibility_of_arithmetic_rows
    pkg.ccm25.concreteArithmeticRows pkg.commonTest.sourceTest
    pkg.commonTest.sourceTest

theorem finite_primes_visible_of_concrete_arithmetic_rows
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestObligationData pkg) :
    data.test.finitePrimesVisible :=
  data.finitePrimeVisibilityBridge
    (finite_prime_visibility_statement_of_concrete_arithmetic_rows pkg)

/--
Goal 3D bridge: source triple-vanishing symbols feed the route test without
changing the fixed-test tuple.
-/
theorem triple_vanishing_of_obligation_data
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestObligationData pkg) :
    data.test.tripleVanishing :=
  data.tripleVanishingBridge data.tripleVanishingSourceHolds

theorem admissible_for_theorem1_of_obligation_data
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestObligationData pkg) :
    AdmissibleForTheorem1 data.test :=
  ⟨data.admissibleWindow,
    finite_primes_visible_of_concrete_arithmetic_rows pkg data⟩

theorem source_backed_triple_vanishing_of_obligation_data
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestObligationData pkg) :
    (SourceBackedFixedSTest.ofExpandedSourcePackage pkg
      (data.toExpandedSourceFixedSTestFrontEnd pkg)).test.tripleVanishing :=
  triple_vanishing_of_obligation_data pkg data

theorem source_backed_admissible_for_theorem1_of_obligation_data
    (pkg : Source.SourceObject.SourceObjectPackage)
    (data : FixedSTestObligationData pkg) :
    AdmissibleForTheorem1
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg
      (data.toExpandedSourceFixedSTestFrontEnd pkg)).test :=
  admissible_for_theorem1_of_obligation_data pkg data

/--
Goal 3 package-constructor specialization: build the fixed-test front end from
the exact `sourceObjectPackageOfData` output produced by Goal 2D.
-/
def toExpandedSourceFixedSTestFrontEndOfPackageData
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (rows : Source.SourceObjectExpandedRows base common)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges : Source.SourceObjectCrossObjectBridges base common rows rhExit)
    (data :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfData base common rows rhExit bridges)) :
    ExpandedSourceFixedSTestFrontEnd
      (Source.sourceObjectPackageOfData base common rows rhExit bridges) :=
  data.toExpandedSourceFixedSTestFrontEnd
    (Source.sourceObjectPackageOfData base common rows rhExit bridges)

theorem package_data_source_backed_weil_test_eq_common
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (rows : Source.SourceObjectExpandedRows base common)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges : Source.SourceObjectCrossObjectBridges base common rows rhExit)
    (data :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfData base common rows rhExit bridges)) :
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfData base common rows rhExit bridges)
      (toExpandedSourceFixedSTestFrontEndOfPackageData
        base common rows rhExit bridges data)).weilTest =
      common.commonTest.sourceTest :=
  rfl

theorem package_data_source_backed_window_eq_source_window
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (rows : Source.SourceObjectExpandedRows base common)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges : Source.SourceObjectCrossObjectBridges base common rows rhExit)
    (data :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfData base common rows rhExit bridges)) :
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfData base common rows rhExit bridges)
      (toExpandedSourceFixedSTestFrontEndOfPackageData
        base common rows rhExit bridges data)).window =
      rows.ccm24.sourceSupportWindow :=
  rfl

theorem package_data_finite_prime_visibility_statement
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (rows : Source.SourceObjectExpandedRows base common)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges : Source.SourceObjectCrossObjectBridges base common rows rhExit) :
    WeilFormSymbols.FinitePrimeVisibilityStatement
      (Source.sourceObjectPackageOfData base common rows rhExit bridges).ccm25.weilSymbols
      common.commonTest.sourceTest common.commonTest.sourceTest :=
  finite_prime_visibility_statement_of_concrete_arithmetic_rows
    (Source.sourceObjectPackageOfData base common rows rhExit bridges)

theorem package_data_admissible_for_theorem1
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (rows : Source.SourceObjectExpandedRows base common)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges : Source.SourceObjectCrossObjectBridges base common rows rhExit)
    (data :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfData base common rows rhExit bridges)) :
    AdmissibleForTheorem1
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfData base common rows rhExit bridges)
        (toExpandedSourceFixedSTestFrontEndOfPackageData
          base common rows rhExit bridges data)).test :=
  source_backed_admissible_for_theorem1_of_obligation_data
    (Source.sourceObjectPackageOfData base common rows rhExit bridges) data

end FixedSTestObligationData

end Route
end ConnesWeilRH
