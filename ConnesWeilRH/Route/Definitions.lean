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

end Route
end ConnesWeilRH
