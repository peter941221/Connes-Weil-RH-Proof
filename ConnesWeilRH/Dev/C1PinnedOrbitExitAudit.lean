/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1PinnedOrbitExit

/-!
# Audit for C1PinnedOrbitExit (Record 1903)

Audits all declarations in `ConnesWeilRH.Dev.C1PinnedOrbitExit`:
- `#check` declarations
- `#print axioms` verifying that each declaration depends strictly on the three standard
  axioms: `[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1PinnedOrbitExitAudit

open ConnesWeilRH.Source.C1PinnedOrbitExit

#check @laplaceAt_spanObj_two
#print axioms laplaceAt_spanObj_two

#check @vanishesOn_cc20Triple_spanObj_two
#print axioms vanishesOn_cc20Triple_spanObj_two

#check @pinned_twoSpan_optimal_vanishesOn_cc20Triple
#print axioms pinned_twoSpan_optimal_vanishesOn_cc20Triple

#check @pinned_twoSpan_optimal_qw_nonneg
#print axioms pinned_twoSpan_optimal_qw_nonneg

#check @false_of_healthyDetectorData_and_orbitWindowSemiLocalGate
#print axioms false_of_healthyDetectorData_and_orbitWindowSemiLocalGate

#check @riemannHypothesis_of_orbitWindowSemiLocalGate
#print axioms riemannHypothesis_of_orbitWindowSemiLocalGate

#check @riemannHypothesis_of_right_orbitGeometry_orbitWindowSemiLocalGate
#print axioms riemannHypothesis_of_right_orbitGeometry_orbitWindowSemiLocalGate

#check @riemannHypothesis_of_right_detector_specific_qw_nonneg
#print axioms riemannHypothesis_of_right_detector_specific_qw_nonneg

#check @riemannHypothesis_of_pinned_geometry_absorption
#print axioms riemannHypothesis_of_pinned_geometry_absorption

end C1PinnedOrbitExitAudit
end Source
end ConnesWeilRH
