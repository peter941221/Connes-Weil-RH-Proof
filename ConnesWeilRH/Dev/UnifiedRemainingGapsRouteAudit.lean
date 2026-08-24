/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.UnconditionalSkeleton
import ConnesWeilRH.Source.RHDefinition
import ConnesWeilRH.Dev.C1CenterTwoRHExit
import ConnesWeilRH.Dev.C1PositiveTraceLimitBridge
import ConnesWeilRH.Dev.C1Stage3FrontierStatus
import ConnesWeilRH.Dev.C1Stage3WindowedTraceP2
import ConnesWeilRH.Dev.C1Stage3ProjectionDefectBounds

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

-- Stage-3 analytic route (Route B), registered in UnconditionalSkeleton's root ledger: step① (windowed FRONTIER-HS)
-- and step② (FRONTIER-CRUX, power-spectrum = Weil value) are both proved lemmas, axiom-clean.  The former
-- bare-operator FRONTIER-HS premise is REFUTED (2026-08-24): `bareHS_iff_zero_test` shows per-test bare HS holds
-- iff the test is zero, and `not_forall_bare_hilbertSchmidt` refutes the uniform premise outright, so the closure
-- theorem below is a true-but-vacuous producer (its hypothesis is satisfiable only by the zero test).
#print axioms ConnesWeilRH.Source.C1Stage3FrontierCrux.frontierCrux_powerSpectrum_eq_weilValue
#print axioms ConnesWeilRH.Source.C1Stage3FrontierCrux.frontierCrux_closes_healthyCriterionState
#print axioms ConnesWeilRH.Source.C1Stage3BareHSObstruction.bareHS_iff_zero_test
#print axioms ConnesWeilRH.Source.C1Stage3BareHSObstruction.not_forall_bare_hilbertSchmidt

-- P2 windowed renormalization obstruction (2026-08-24): subtracting the divergent bulk from the bump-window trace
-- leaves an identically-zero remainder (`p2_bumpTrace_sub_bulk_zero`), so a renormalized readback to `qw g₀` would
-- force `qw g₀ = 0` by uniqueness of limits — the bulk-subtracted windowed route isolates no Weil content and is dead.
#print axioms ConnesWeilRH.Source.C1Stage3WindowedTraceP2.p2_renormReadback_forces_qw_zero

-- Route B LIVE producers (2026-08-24): after the bare-premise refutation exactly two producers of
-- `healthyCriterionState` remain, both reducing to ONE open analytic obligation — the sign `0 ≤ qw g` on vanishing
-- tests (the RH content itself):
--   * rank-one self-correction (Program P step 2 operator family): sign-transparent — `hqw` is an explicit per-test
--     hypothesis; jointly satisfiable at the narrow root (`frontierStatus_satisfiableAt_gV`), where the sign is
--     independently proven, so the closure is concrete and non-circular there;
--   * projection owner (C†K_S C route): derives the sign from positivity once the kernel-compatibility defect
--     `‖kernelInsertionDefect‖ → 0` along cutoffs (quadratic form of ‖Z†(K_S − id)Z‖) is supplied — the D₁
--     sufficiency theorem exposes exactly that missing analytic input.
#print axioms ConnesWeilRH.Source.C1Stage3FrontierStatus.frontierStatus_satisfiableAt_gV
#print axioms ConnesWeilRH.Source.C1Stage3FrontierStatus.frontierStatus_healthyCriterionState_of_rankOneCorrection
#print axioms ConnesWeilRH.Source.Dev.C1Stage3ProjectionDefectBounds.tendsto_norm_cutoffKernelInsertionSandwich_zero_of_compressedDefect

-- Route B FINAL HOP (P0-b audit, 2026-08-21): once `healthyCriterionState` is in hand (produced by either live
-- producer above), the remaining path to bare `RiemannHypothesis` carries NO hidden axiom — each step below depends
-- only on [propext, Classical.choice, Quot.sound].  The two non-axiomatic obligations that must still be SUPPLIED are:
--   (1) exit premise 1 = CC20YoshidaDetectorExists healthyCC20TestSpace cc20TripleFiniteVanishingSet (open detector transport), and
--   (2) the vanishing-test sign `∀ g vanishing on F, 0 ≤ qw g` — reachable directly as the rank-one producer's `hqw`,
--       or via positivity + kernel compatibility on the projection-owner route; the former bare-operator FRONTIER-HS
--       route to it is refuted, and the P2 bulk-subtracted windowed shortcut is dead.
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
