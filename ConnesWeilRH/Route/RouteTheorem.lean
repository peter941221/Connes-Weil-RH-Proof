/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.Exhaustion
import ConnesWeilRH.Route.Bridge

/-!
# Route theorem skeleton

The final theorem targets Mathlib's canonical `RiemannHypothesis`. Phase 1 uses
the CC20 exit as an explicit hypothesis, so this module has no hidden project
axioms.
-/

namespace ConnesWeilRH
namespace Route

structure RouteCertificate (inputs : RouteInputs) where
  sourceBackedTest : SourceBackedFixedSTest inputs
  ledgers : RouteLedgers
  bridge : RouteBridgeCertificate inputs sourceBackedTest ledgers

def route_certificate_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (sourceTraceReadOff : SourceTraceReadOffData inputs g)
    (signDefectClassification :
      SourceSignDefectClassification inputs g sourceTraceReadOff.lambda L)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract inputs g sourceTraceReadOff.lambda
        (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
        L sourceTraceReadOff.ccm25ArithmeticPackage)
    (finalSignBridge :
      FinalSignBridgeContract inputs sourceTraceReadOff.archimedeanTest g
        sourceTraceReadOff.lambda
        (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
        sourceTraceReadOff.ccm25ArithmeticPackage) :
    RouteCertificate inputs where
  sourceBackedTest := g
  ledgers := L
  bridge :=
    route_bridge_certificate_of_sign_defect_classification
      sourceTraceReadOff signDefectClassification
      restrictedToFullQWBridge finalSignBridge

theorem cc20_source_rh_of_route_certificate
    {inputs : RouteInputs} (cert : RouteCertificate inputs) :
    inputs.cc20.rhDefinitionBridge.SourceRH := by
  let hfull := full_weil_positivity_of_source_backed
    (source_backed_full_positivity_of_route_bridge_certificate cert.bridge)
  exact Source.CC20Interface.finite_vanishing_source_rh inputs.cc20
    (toWeilPositivityInput inputs cert.sourceBackedTest cert.ledgers)
    (triple_vanishing_of_source_backed cert.sourceBackedTest)
    hfull

theorem final_connes_weil_rh
    {inputs : RouteInputs} (cert : RouteCertificate inputs) :
    _root_.RiemannHypothesis := by
  let _ := restricted_to_full_qw_bridge_of_route_bridge_certificate cert.bridge
  let _ := final_sign_bridge_of_route_bridge_certificate cert.bridge
  exact Source.RHDefinitionBridge.source_rh_to_mathlib_rh
    inputs.cc20.rhDefinitionBridge
    (cc20_source_rh_of_route_certificate cert)

end Route
end ConnesWeilRH
