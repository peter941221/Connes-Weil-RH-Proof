/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3DoubledShiftNormalForm
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
import ConnesWeilRH.Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
import ConnesWeilRH.Dev.C1G8R3ZeroDefectClosure

/-!
# R3-SC2: doubled-shift Sonin intersection transport

The radial and Fourier support projections have opposite translation
orientations. This leaf records the resulting exact closed-subspace normal
form. It proves no trace estimate, no Weil sign, and no RH implication.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.SelectedCrossingOperatorBridge

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier

noncomputable def doubledShiftRadialClosedSubspace (b : ℝ) :
    ClosedSubmodule ℂ Carrier :=
  ClosedSubmodule.mapEquiv
    (cc20GlobalLogTranslationEquiv (-2 * b)).toContinuousLinearEquiv
    cc20PositiveHalfLineClosedRange

noncomputable def doubledShiftSoninClosedSubspace (b : ℝ) :
    ClosedSubmodule ℂ Carrier :=
  doubledShiftRadialClosedSubspace b ⊓
    ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale

theorem globalTranslationEquiv_symm_apply (b : ℝ) (u : Carrier) :
    (cc20GlobalLogTranslationEquiv b).symm u =
      cc20GlobalLogTranslation (-b) u := by
  apply (cc20GlobalLogTranslationEquiv b).injective
  rw [(cc20GlobalLogTranslationEquiv b).apply_symm_apply]
  change u = cc20GlobalLogTranslation b
    (cc20GlobalLogTranslation (-b) u)
  rw [cc20GlobalLogTranslation_add_apply]
  have hzero (v : Carrier) : cc20GlobalLogTranslation 0 v = v := by
    apply (cc20GlobalLogTranslation 0).injective
    simpa only [zero_add] using cc20GlobalLogTranslation_add_apply 0 0 v
  rw [show b + -b = 0 by ring, hzero]

theorem globalTranslationContinuousEquiv_symm_apply (b : ℝ) (u : Carrier) :
    (cc20GlobalLogTranslationEquiv b).toContinuousLinearEquiv.symm u =
      cc20GlobalLogTranslation (-b) u := by
  change (cc20GlobalLogTranslationEquiv b).symm u =
    cc20GlobalLogTranslation (-b) u
  exact globalTranslationEquiv_symm_apply b u

theorem doubledShiftSoninClosedSubspace_map_eq_source
    (lambda : CCM24SoninScale) :
    ClosedSubmodule.mapEquiv
        (cc20GlobalLogTranslationEquiv (Real.log lambda)).toContinuousLinearEquiv
        (doubledShiftSoninClosedSubspace (Real.log lambda)) =
      ccm24ArchimedeanSoninClosedSubspace lambda := by
  let b : ℝ := Real.log lambda
  change ClosedSubmodule.mapEquiv
      (cc20GlobalLogTranslationEquiv b).toContinuousLinearEquiv
      (doubledShiftSoninClosedSubspace b) =
    ccm24ArchimedeanSoninClosedSubspace lambda
  have hE0 (v : Carrier) :
      v ∈ cc20PositiveHalfLineClosedRange ↔
        cc20PositiveHalfLineProjection v = v := by
    change v ∈ cc20PositiveHalfLineProjection.range ↔ _
    exact mem_range_iff_of_isIdempotentElem
      cc20PositiveHalfLineProjection
      cc20PositiveHalfLineProjection_isIdempotentElem v
  have hQ0 (v : Carrier) :
      v ∈ ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale ↔
        sourceFourierSupportProjection unitSoninScale v = v := by
    change v ∈ ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale ↔ _
    exact (Submodule.starProjection_eq_self_iff).symm
  have hE (v : Carrier) :
      v ∈ ccm24LogRadialSupportClosedSubspace lambda ↔
        radialSupportProjection lambda v = v := by
    change v ∈ ccm24LogRadialSupportClosedSubspace lambda ↔ _
    exact (Submodule.starProjection_eq_self_iff).symm
  have hQ (v : Carrier) :
      v ∈ ccm24ArchimedeanFourierSupportClosedSubspace lambda ↔
        sourceFourierSupportProjection lambda v = v := by
    change v ∈ ccm24ArchimedeanFourierSupportClosedSubspace lambda ↔ _
    exact (Submodule.starProjection_eq_self_iff).symm
  have hdouble (v : Carrier) :
      cc20GlobalLogTranslation (2 * b)
          (cc20GlobalLogTranslation (-b) v) =
        cc20GlobalLogTranslation b v := by
    rw [cc20GlobalLogTranslation_add_apply]
    simpa only [show 2 * b + -b = b by ring]
  ext u
  constructor
  · intro hu
    have hpre := (ClosedSubmodule.mem_mapEquiv_iff
      (cc20GlobalLogTranslationEquiv b).toContinuousLinearEquiv
      (doubledShiftSoninClosedSubspace b) u).1 hu
    rw [doubledShiftSoninClosedSubspace,
      globalTranslationContinuousEquiv_symm_apply] at hpre
    change
      (cc20GlobalLogTranslation (-b) u ∈
          doubledShiftRadialClosedSubspace b ∧
        cc20GlobalLogTranslation (-b) u ∈
          ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale) at hpre
    rcases hpre with ⟨huRadial, huFourier⟩
    have hmap := (ClosedSubmodule.mem_mapEquiv_iff
      (cc20GlobalLogTranslationEquiv (-2 * b)).toContinuousLinearEquiv
      cc20PositiveHalfLineClosedRange
      (cc20GlobalLogTranslation (-b) u)).1 huRadial
    rw [globalTranslationContinuousEquiv_symm_apply] at hmap
    have hmap' : cc20GlobalLogTranslation (2 * b)
          (cc20GlobalLogTranslation (-b) u) ∈
        cc20PositiveHalfLineClosedRange := by
      convert hmap using 1 <;> ring
    have hradialFixed : cc20PositiveHalfLineProjection
        (cc20GlobalLogTranslation b u) =
        cc20GlobalLogTranslation b u := by
      rw [hdouble u] at hmap'
      exact (hE0 _).1 hmap'
    have hfourierFixed := (hQ0 _).1 huFourier
    constructor
    · apply (hE u).2
      rw [radialSupportProjection_eq_translation_conjugation lambda]
      change cc20GlobalLogTranslation (-b)
          (cc20PositiveHalfLineProjection
            (cc20GlobalLogTranslation b u)) = u
      rw [hradialFixed]
      simpa only [neg_neg] using cc20GlobalLogTranslation_neg_apply (-b) u
    · apply (hQ u).2
      rw [sourceFourierSupportProjection_eq_scale_conjugate_of_zero_defects]
      change cc20GlobalLogTranslation b
          (sourceFourierSupportProjection unitSoninScale
            (cc20GlobalLogTranslation (-b) u)) = u
      rw [hfourierFixed]
      exact cc20GlobalLogTranslation_neg_apply b u
  · rintro hu
    have huRadial := hu.1
    have huFourier := hu.2
    have hradialFixed := (hE u).1 huRadial
    have hfourierFixed := (hQ u).1 huFourier
    apply (ClosedSubmodule.mem_mapEquiv_iff
      (cc20GlobalLogTranslationEquiv b).toContinuousLinearEquiv
      (doubledShiftSoninClosedSubspace b) u).2
    rw [doubledShiftSoninClosedSubspace,
      globalTranslationContinuousEquiv_symm_apply]
    change
      (cc20GlobalLogTranslation (-b) u ∈
          doubledShiftRadialClosedSubspace b ∧
        cc20GlobalLogTranslation (-b) u ∈
          ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale)
    constructor
    · apply (ClosedSubmodule.mem_mapEquiv_iff
        (cc20GlobalLogTranslationEquiv (-2 * b)).toContinuousLinearEquiv
        cc20PositiveHalfLineClosedRange
        (cc20GlobalLogTranslation (-b) u)).2
      rw [globalTranslationContinuousEquiv_symm_apply]
      have hradialFixed0 := hradialFixed
      rw [radialSupportProjection_eq_translation_conjugation lambda]
        at hradialFixed0
      change cc20GlobalLogTranslation (-b)
          (cc20PositiveHalfLineProjection
            (cc20GlobalLogTranslation b u)) = u at hradialFixed0
      have hmap' : cc20GlobalLogTranslation (2 * b)
            (cc20GlobalLogTranslation (-b) u) ∈
          cc20PositiveHalfLineClosedRange := by
        rw [hdouble u]
        have hfixed : cc20PositiveHalfLineProjection
            (cc20GlobalLogTranslation b u) =
              cc20GlobalLogTranslation b u := by
          apply (cc20GlobalLogTranslation (-b)).injective
          have hinv := cc20GlobalLogTranslation_neg_apply (-b) u
          have hinv' : cc20GlobalLogTranslation (-b)
              (cc20GlobalLogTranslation b u) = u := by
            simpa only [neg_neg] using hinv
          rw [hinv']
          exact hradialFixed0
        exact (hE0 _).2 hfixed
      convert hmap' using 1 <;> ring
    · have hfourierFixed0 :
          sourceFourierSupportProjection unitSoninScale
              (cc20GlobalLogTranslation (-b) u) =
            cc20GlobalLogTranslation (-b) u := by
        rw [sourceFourierSupportProjection_eq_scale_conjugate_of_zero_defects]
          at hfourierFixed
        change cc20GlobalLogTranslation b
            (sourceFourierSupportProjection unitSoninScale
              (cc20GlobalLogTranslation (-b) u)) = u at hfourierFixed
        apply (cc20GlobalLogTranslation b).injective
        rw [hfourierFixed]
        exact (cc20GlobalLogTranslation_neg_apply b u).symm
      exact (hQ0 _).2 hfourierFixed0

end Dev
end ConnesWeilRH
