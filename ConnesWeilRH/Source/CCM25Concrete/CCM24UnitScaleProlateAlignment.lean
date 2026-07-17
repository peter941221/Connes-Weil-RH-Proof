/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace

/-!
# Unit-scale alignment of the CCM24 and CC20 prolate owners

CC20's prolate spectral decomposition is stated at cutoff parameter one.
This module proves that the concrete CCM24 source projections at that literal
scale are the same operators as the two-projection owner in
`GlobalLogSoninProjection`.  No spectral expansion or trace estimate is
asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24UnitScaleProlateAlignment

open MeasureTheory
open CC20Concrete
open CCM24FiniteSProjectionTrace

local notation "Hinf" => ccm24ArchimedeanHardyTitchmarsh

/-- The literal cutoff parameter used by CC20 Section 4. -/
def unitSoninScale : CCM24SoninScale :=
  ⟨1, zero_lt_one⟩

@[simp] theorem unitSoninScale_coe : (unitSoninScale : ℝ) = 1 :=
  rfl

@[simp] theorem unitSoninScale_log : Real.log (unitSoninScale : ℝ) = 0 := by
  simp

/-- Logarithmic translation by zero is the identity on the actual `L2`
carrier. -/
theorem unitTranslation_zero_apply (u : finiteSCarrier) :
    cc20GlobalLogTranslation 0 u = u := by
  rw [Lp.ext_iff]
  filter_upwards [cc20GlobalLogTranslation_coeFn 0 u] with t ht
  simpa only [Function.comp_apply, add_zero] using ht

theorem unitTranslation_zero_operator :
    (cc20GlobalLogTranslation 0).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ finiteSCarrier := by
  apply ContinuousLinearMap.ext
  exact unitTranslation_zero_apply

/-- Fixed points of a continuous idempotent are exactly its range. -/
theorem mem_range_iff_of_isIdempotentElem
    (projection : finiteSCarrier →L[ℂ] finiteSCarrier)
    (hprojection : IsIdempotentElem projection)
    (u : finiteSCarrier) :
    u ∈ projection.range ↔ projection u = u := by
  constructor
  · rintro ⟨v, rfl⟩
    have h := congrArg
      (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator v)
      hprojection
    simpa only [ContinuousLinearMap.mul_apply] using h
  · intro hfixed
    exact ⟨u, hfixed⟩

/-- At unit cutoff the CCM24 radial support is the fixed positive half-line. -/
theorem radialSupportProjection_unit :
    radialSupportProjection unitSoninScale =
      cc20PositiveHalfLineProjection := by
  change ccm24LogRadialSupportProjection unitSoninScale = _
  rw [ccm24LogRadialSupportProjection_eq_translation_conjugation]
  simp only [unitSoninScale_log, neg_zero]
  rw [unitTranslation_zero_operator]
  simp

/-- The unit-scale radial closed subspace is the closed range of the concrete
half-line projection. -/
theorem radialSupportClosedSubspace_unit :
    ccm24LogRadialSupportClosedSubspace unitSoninScale =
      cc20PositiveHalfLineClosedRange := by
  apply SetLike.ext
  intro u
  change u ∈ ccm24LogRadialSupportClosedSubspace unitSoninScale ↔
    u ∈ cc20PositiveHalfLineProjection.range
  rw [← ccm24LogRadialSupportProjection_eq_self_iff,
    mem_range_iff_of_isIdempotentElem cc20PositiveHalfLineProjection
      cc20PositiveHalfLineProjection_isIdempotentElem u]
  change radialSupportProjection unitSoninScale u = u ↔
    cc20PositiveHalfLineProjection u = u
  rw [radialSupportProjection_unit]

/-- At unit cutoff the CCM24 source Fourier support is exactly the
Hardy--Titchmarsh transport of the fixed half-line projection. -/
theorem sourceFourierSupportProjection_unit :
    sourceFourierSupportProjection unitSoninScale =
      cc20TransportedHalfLineProjection Hinf := by
  rw [sourceFourierSupportProjection,
    ccm24ArchimedeanFourierSupportProjection_eq_transport]
  unfold ccm24ArchimedeanFourierSupportTransportProjection
  rw [show ccm24LogRadialSupportProjection unitSoninScale =
      cc20PositiveHalfLineProjection by
    exact radialSupportProjection_unit]
  rfl

/-- The unit-scale Fourier-support closed subspace is the transported
half-line closed range used by the CC20 pair-of-projections construction. -/
theorem sourceFourierSupportClosedSubspace_unit :
    ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale =
      cc20TransportedHalfLineClosedRange Hinf := by
  apply SetLike.ext
  intro u
  change u ∈ ccm24ArchimedeanFourierSupportClosedSubspace
      unitSoninScale ↔
    u ∈ (cc20TransportedHalfLineProjection Hinf).range
  have hleft : sourceFourierSupportProjection unitSoninScale u = u ↔
      u ∈ ccm24ArchimedeanFourierSupportClosedSubspace
        unitSoninScale := by
    exact Submodule.starProjection_eq_self_iff
  rw [← hleft,
    mem_range_iff_of_isIdempotentElem
      (cc20TransportedHalfLineProjection Hinf)
      (cc20TransportedHalfLineProjection_isIdempotentElem Hinf) u]
  rw [DFunLike.congr_fun sourceFourierSupportProjection_unit u]

/-- The literal complete Sonin closed subspace agrees on both constructions
at the source cutoff used in CC20. -/
theorem sourceSoninClosedSubspace_unit :
    ccm24ArchimedeanSoninClosedSubspace unitSoninScale =
      cc20TransportedSoninClosedSubspace Hinf := by
  rw [ccm24ArchimedeanSoninClosedSubspace,
    cc20TransportedSoninClosedSubspace,
    radialSupportClosedSubspace_unit,
    sourceFourierSupportClosedSubspace_unit]

/-- The source Sonin orthogonal projection is the same canonical projection
as CC20's unit-scale pair-of-projections owner. -/
theorem sourceSoninProjection_unit :
    sourceSoninProjection unitSoninScale =
      cc20TransportedSoninProjection Hinf := by
  apply ContinuousLinearMap.IsStarProjection.ext
    (sourceSoninProjection_isStarProjection unitSoninScale)
    (cc20TransportedSoninProjection_isStarProjection Hinf)
  unfold sourceSoninProjection cc20TransportedSoninProjection
  rw [Submodule.range_starProjection, Submodule.range_starProjection]
  exact congrArg ClosedSubmodule.toSubmodule
    sourceSoninClosedSubspace_unit

/-- The actual CCM24 source prolate remainder at cutoff one is exactly the
CC20 transported prolate remainder to which Proposition 4.5 applies. -/
theorem sourceProlateRemainder_unit :
    sourceProlateRemainder unitSoninScale =
      cc20TransportedProlateRemainder Hinf := by
  unfold sourceProlateRemainder cc20TransportedProlateRemainder
  rw [radialSupportProjection_unit,
    sourceFourierSupportProjection_unit,
    sourceSoninProjection_unit]

end CCM24UnitScaleProlateAlignment
end CCM25Concrete
end Source
end ConnesWeilRH
