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

theorem final_connes_weil_rh
    {inputs : RouteInputs} (cert : RouteCertificate inputs) :
    _root_.RiemannHypothesis := by
  let hfull := full_weil_positivity_of_source_backed
    (source_backed_full_positivity_of_route_bridge_certificate cert.bridge)
  let _ := restricted_to_full_qw_bridge_of_route_bridge_certificate cert.bridge
  let _ := final_sign_bridge_of_route_bridge_certificate cert.bridge
  exact Source.CC20Interface.finite_vanishing_mathlib_rh inputs.cc20
    (toWeilPositivityInput inputs cert.sourceBackedTest cert.ledgers)
    (triple_vanishing_of_source_backed cert.sourceBackedTest)
    hfull

end Route
end ConnesWeilRH
