/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerTwoCarrierSplit
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedSoninProjection

/-!
# Finite-S endpoint alignment for the signed radial owner

At `alpha = 1`, the parameterized Fourier and prolate objects in the radial
owner are the same projections selected by the finite prime-power family.
This module records that equality on the literal `finiteSCarrier`.  It is a
carrier/readback theorem; it does not provide the missing common-root energy
or left-factor bound.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialPhysicalOwnerFiniteSEndpointAlignment

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open AntiresonantFrameLossCommutator
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialPhysicalOwner
open AntiresonantFrameLossRadialPhysicalOwnerTwoCarrierSplit
open CCM24FiniteSParameterizedSoninProjection
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

/-! ## Endpoint projection equalities -/

/-- The synchronized endpoint Fourier-support projection is the concrete
finite-S projection derived from the same prime-power family. -/
theorem parameterizedFourierSupportProjection_one_eq_target
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    parameterizedFourierSupportProjection lambda 1 family.visiblePrimes
        (by norm_num) =
      targetFourierSupportProjection lambda family := by
  unfold parameterizedFourierSupportProjection targetFourierSupportProjection
  apply ContinuousLinearMap.IsStarProjection.ext
    isStarProjection_starProjection isStarProjection_starProjection
  rw [Submodule.range_starProjection, Submodule.range_starProjection]
  exact congrArg (fun P : ClosedSubmodule ℂ finiteSCarrier => P.toSubmodule)
    (parameterizedFourierSupportClosedSubspace_one lambda
      family.visiblePrimes)

/-- The synchronized endpoint Sonin projection is the concrete finite-S
projection selected by the same family. -/
theorem parameterizedSoninProjection_one_eq_target
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    parameterizedSoninProjection lambda 1 family.visiblePrimes
        (by norm_num) =
      targetSoninProjection lambda family := by
  unfold targetSoninProjection
  exact parameterizedSoninProjection_one lambda family.visiblePrimes

/-- The endpoint prolate remainder is the finite-S prolate remainder on the
same carrier, not an unrelated parameterized object. -/
theorem parameterizedProlateRemainder_one_eq_target
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    parameterizedProlateRemainder lambda 1 family.visiblePrimes
        (by norm_num) =
      targetProlateRemainder lambda family := by
  unfold parameterizedProlateRemainder targetProlateRemainder
  rw [parameterizedFourierSupportProjection_one_eq_target,
    parameterizedSoninProjection_one_eq_target]

/-! ## Owner readback -/

/-- The complete signed radial owner at a finite-S endpoint uses the actual
target Fourier/prolate projections selected by the arithmetic family. -/
theorem radialSignedPhysicalOwner_one_eq_targetThreeBranch_add_boundary
    (p : CCM24VisiblePrime) (family : FinitePrimePowerFamily) :
    radialSignedPhysicalOwner p family.visiblePrimes =
      -cc20ThreeBranchCommutator
          (radialSupportProjection unitSoninScale)
          (targetFourierSupportProjection unitSoninScale family)
          (targetProlateRemainder unitSoninScale family)
          (radialCompressedPositiveTranslation p) +
        radialSoninBoundaryCrossing p family.visiblePrimes := by
  unfold radialSignedPhysicalOwner
  rw [parameterizedFourierSupportProjection_one_eq_target,
    parameterizedProlateRemainder_one_eq_target]

/-- The suffix commutator has the same concrete finite-S endpoint readback. -/
theorem suffixPrimeTranslationProjectionCommutator_one_eq_targetThreeBranch_add_boundary
    (p : CCM24VisiblePrime) (family : FinitePrimePowerFamily) :
    suffixPrimeTranslationProjectionCommutator p family.visiblePrimes =
      -cc20ThreeBranchCommutator
          (radialSupportProjection unitSoninScale)
          (targetFourierSupportProjection unitSoninScale family)
          (targetProlateRemainder unitSoninScale family)
          (radialCompressedPositiveTranslation p) +
        radialSoninBoundaryCrossing p family.visiblePrimes := by
  rw [suffixPrimeTranslationProjectionCommutator_eq_radialSignedPhysicalOwner,
    radialSignedPhysicalOwner_one_eq_targetThreeBranch_add_boundary]

end AntiresonantFrameLossRadialPhysicalOwnerFiniteSEndpointAlignment
end CCM25Concrete
end Source
end ConnesWeilRH
