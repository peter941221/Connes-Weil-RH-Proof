/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.UnconditionalSkeleton
import ConnesWeilRH.Source.RHDefinition
import ConnesWeilRH.Dev.C1CenterTwoRHExit
import ConnesWeilRH.Dev.C1PositiveTraceLimitBridge

/-!
# Plan 016 current route audit

This import-facing audit prints the full final theorem type and its current
dependency boundary. It must remain conditional until plan 016 retires each project
root.
-/

namespace ConnesWeilRH
namespace Dev
namespace UnifiedRemainingGapsRouteAudit

open UnconditionalSkeleton

#check @unconditional_rh_skeleton
#print unconditional_rh_skeleton
#print axioms unconditional_rh_skeleton

-- Stage-3 analytic route (Route B), registered in UnconditionalSkeleton's root ledger: step① is proved, so Route B rests
-- on exactly two named premises — bare-operator FRONTIER-HS and the single step② root axiom below.  The closure theorem
-- shows that once both hold uniformly in `g`, the RH-level healthy criterion state follows with no further hypothesis.
#print axioms ConnesWeilRH.Source.C1Stage3FrontierCrux.frontierCrux_powerSpectrum_eq_weilValue
#print axioms ConnesWeilRH.Source.C1Stage3FrontierCrux.frontierCrux_closes_healthyCriterionState

-- Route B FINAL HOP (P0-b audit, 2026-08-21): once `healthyCriterionState` is in hand (produced by the closure above),
-- the remaining path to bare `RiemannHypothesis` carries NO hidden axiom — each step below depends only on
-- [propext, Classical.choice, Quot.sound].  The two non-axiomatic obligations that must still be SUPPLIED are:
--   (1) exit premise 1 = CC20YoshidaDetectorExists healthyCC20TestSpace cc20TripleFiniteVanishingSet (open detector transport), and
--   (2) the step② root axiom above — what actually turns a positive-trace family into `healthyCriterionState`.
#check ConnesWeilRH.Source.C1CenterTwoRHExit.healthy_criterion_sourceRH_of_yoshida_detector
#print axioms ConnesWeilRH.Source.C1CenterTwoRHExit.healthy_criterion_sourceRH_of_yoshida_detector
#print axioms ConnesWeilRH.Source.RHDefinitionBridge.source_rh_to_mathlib_rh
-- consumer chain that turns a positive-trace family into `healthyCriterionState`:
#print axioms ConnesWeilRH.Source.C1PositiveTraceLimitBridge.qw_nonnegative_of_positiveTracePairLimitFamily
#print axioms ConnesWeilRH.Source.C1PositiveTraceLimitBridge.spectral_nonnegative_of_positiveTracePairLimitFamily
#print axioms ConnesWeilRH.Source.C1PositiveTraceLimitBridge.healthyCriterionState_of_positiveTracePairLimitFamily
-- the finite-vanishing criterion characterization shared by producer and exit:
#print axioms ConnesWeilRH.Source.C1CenterTwoCriterionBridge.healthyCriterionState_iff_all_vanishing_spectral_nonnegative

end UnifiedRemainingGapsRouteAudit
end Dev
end ConnesWeilRH
