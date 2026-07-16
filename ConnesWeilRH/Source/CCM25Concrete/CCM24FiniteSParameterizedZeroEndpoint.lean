/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualMovingProjection

/-!
# Zero endpoint of the parameterized finite-S geometry

At synchronized time zero every Euler factor is the identity.  The moving
Hardy--Titchmarsh operator, Fourier support, Sonin intersection, and canonical
Gram projection therefore return exactly to their archimedean source owners.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSParameterizedZeroEndpoint

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerGenerator
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSParameterizedEulerEquiv
open CCM24FiniteSParameterizedSoninSubspace
open CCM24FiniteSParameterizedSoninProjection
open CCM24FiniteSGramProjectionCalculus

/-- The complete synchronized Euler product starts at the identity. -/
theorem parameterizedFiniteEulerFactor_zero
    (S : List CCM24VisiblePrime) :
    parameterizedFiniteEulerFactor 0 S = 1 := by
  induction S with
  | nil => rfl
  | cons p S ih =>
      rw [parameterizedFiniteEulerFactor, ih]
      simp only [parameterizedPrimeEulerFactor,
        parameterizedPrimeEulerContraction, Complex.ofReal_zero,
        zero_smul, sub_zero, mul_one]

/-- The actual bounded equivalence starts at the identity equivalence. -/
theorem parameterizedFiniteEulerEquiv_zero
    (S : List CCM24VisiblePrime) :
    parameterizedFiniteEulerEquiv 0 S (by norm_num) =
      ContinuousLinearEquiv.refl ℂ finiteSCarrier := by
  apply ContinuousLinearEquiv.ext
  funext u
  rw [parameterizedFiniteEulerEquiv_apply,
    parameterizedFiniteEulerFactor_zero]
  rfl

/-- Zero-time semilocal Fourier is the archimedean Hardy--Titchmarsh
involution. -/
theorem parameterizedSemilocalHardyTitchmarsh_zero
    (S : List CCM24VisiblePrime) :
    parameterizedSemilocalHardyTitchmarsh 0 S (by norm_num) =
      ccm24ArchimedeanHardyTitchmarsh := by
  unfold parameterizedSemilocalHardyTitchmarsh
  rw [parameterizedFiniteEulerEquiv_zero]
  rfl

/-- The moving Fourier-support subspace starts at the source Fourier support. -/
theorem parameterizedFourierSupportClosedSubspace_zero
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    parameterizedFourierSupportClosedSubspace lambda 0 S (by norm_num) =
      ccm24ArchimedeanFourierSupportClosedSubspace lambda := by
  unfold parameterizedFourierSupportClosedSubspace
    ccm24ArchimedeanFourierSupportClosedSubspace
  rw [parameterizedSemilocalHardyTitchmarsh_zero]

/-- The complete moving Sonin intersection starts at the source intersection. -/
theorem parameterizedSoninClosedSubspace_zero
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    parameterizedSoninClosedSubspace lambda 0 S (by norm_num) =
      ccm24ArchimedeanSoninClosedSubspace lambda := by
  unfold parameterizedSoninClosedSubspace
    ccm24ArchimedeanSoninClosedSubspace
  rw [parameterizedFourierSupportClosedSubspace_zero]

/-- The actual moving orthogonal projection starts at the source Sonin
projection. -/
theorem parameterizedSoninProjection_zero
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    parameterizedSoninProjection lambda 0 S (by norm_num) =
      sourceSoninProjection lambda := by
  unfold parameterizedSoninProjection sourceSoninProjection
  apply ContinuousLinearMap.IsStarProjection.ext
    isStarProjection_starProjection isStarProjection_starProjection
  rw [Submodule.range_starProjection, Submodule.range_starProjection]
  exact congrArg (fun P : ClosedSubmodule ℂ finiteSCarrier => P.toSubmodule)
    (parameterizedSoninClosedSubspace_zero lambda S)

/-- The proof-independent differentiable Gram owner has the same source
endpoint. -/
theorem parameterizedCanonicalGramProjection_zero
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    parameterizedCanonicalGramProjection lambda 0 S =
      sourceSoninProjection lambda := by
  rw [parameterizedCanonicalGramProjection_eq_soninProjection
      lambda 0 S (by norm_num),
    parameterizedSoninProjection_zero]

end CCM24FiniteSParameterizedZeroEndpoint
end CCM25Concrete
end Source
end ConnesWeilRH
