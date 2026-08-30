/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1SemilocalHardyTitchmarshUnitarityReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace

/-!
# C1: finite-family unitary projection bridge

The F1' ledger consumes the concrete finite-family projection
`targetFourierSupportProjection lambda family`.  The preceding unitarity leaf
establishes its generic list-indexed formula.  This bridge places that formula
on the actual family owner and expands the target prolate remainder into the
unitary normal form used by the remaining smoothing analysis.

No Hilbert--Schmidt, trace-class, positivity, or RH conclusion is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SemilocalFourierProjectionUnitaryBridge

open CC20Concrete
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open C1SemilocalHardyTitchmarshUnitarityReduction

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- The real finite-family second-support projection is the unitary conjugate
of the radial projection. -/
theorem targetFourierSupportProjection_eq_unitary_conjugate
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    targetFourierSupportProjection lambda family =
      (ccm24SemilocalHardyTitchmarsh family.visiblePrimes).toContinuousLinearMap ∘L
        radialSupportProjection lambda ∘L
          (ccm24SemilocalHardyTitchmarsh family.visiblePrimes).toContinuousLinearMap := by
  unfold targetFourierSupportProjection radialSupportProjection
  exact ccm24SemilocalFourierSupport_starProjection_eq_unitary_conjugate
    lambda family.visiblePrimes

/-- The finite-family prolate remainder in the unitary normal form.  This is
the exact `E H_S E H_S E - R_S` operator; it is a structural rewrite only,
not a trace-class assertion. -/
theorem targetProlateRemainder_eq_unitary_normalForm
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    targetProlateRemainder lambda family =
      radialSupportProjection lambda ∘L
        ((ccm24SemilocalHardyTitchmarsh family.visiblePrimes).toContinuousLinearMap ∘L
          radialSupportProjection lambda ∘L
            (ccm24SemilocalHardyTitchmarsh family.visiblePrimes).toContinuousLinearMap) ∘L
        radialSupportProjection lambda -
          targetSoninProjection lambda family := by
  unfold targetProlateRemainder
  rw [targetFourierSupportProjection_eq_unitary_conjugate]

end C1SemilocalFourierProjectionUnitaryBridge
end Source
end ConnesWeilRH
