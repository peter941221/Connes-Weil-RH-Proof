/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24LogRadialSupport
import ConnesWeilRH.Source.CC20Concrete.CCM24HardyTitchmarsh
import ConnesWeilRH.Source.CC20Concrete.GlobalLogSoninProjection
import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

/-!
# Alignment of CCM24 radial support with the translated half-line

The radial support condition `t >= log lambda` is the ordinary positive
half-line projection conjugated by logarithmic translation.  The proof is
carried out on the actual `L2` carrier through almost-everywhere indicator
identities, then upgraded to equality of orthogonal projections by range.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set

/-- Translation moving the cutoff `log lambda` to zero. -/
noncomputable def ccm24RadialTranslationEquiv
    (lambda : CCM24SoninScale) :
    cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2 :=
  CCM25Concrete.SelectedCrossingOperatorBridge.cc20GlobalLogTranslationEquiv
    (Real.log lambda)

/-- The zero-boundary half-line projection transported back to the actual
radial cutoff. -/
noncomputable def ccm24TranslatedHalfLineProjection
    (lambda : CCM24SoninScale) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  cc20TransportedHalfLineProjection (ccm24RadialTranslationEquiv lambda)

theorem ccm24TranslatedHalfLineProjection_isStarProjection
    (lambda : CCM24SoninScale) :
    IsStarProjection (ccm24TranslatedHalfLineProjection lambda) :=
  cc20TransportedHalfLineProjection_isStarProjection _

/-- Pointwise `L2` readback: the transported projection is multiplication by
the indicator of `[log lambda, infinity)`. -/
theorem ccm24TranslatedHalfLineProjection_coeFn
    (lambda : CCM24SoninScale) (u : cc20GlobalLogCrossingL2) :
    (ccm24TranslatedHalfLineProjection lambda u : ℝ → ℂ) =ᵐ[volume]
      (Set.Ici (Real.log lambda)).indicator (fun t => u t) := by
  let c := Real.log (lambda : ℝ)
  let Upos := (cc20GlobalLogTranslation c).toContinuousLinearMap
  let Uneg := (cc20GlobalLogTranslation (-c)).toContinuousLinearMap
  have hadjoint : Upos.adjoint = Uneg := by
    simpa only [Upos, Uneg, neg_neg] using
      (CCM25Concrete.SelectedCrossingOperatorBridge.cc20GlobalLogTranslation_neg_adjoint
        (-c))
  have hshape : ccm24TranslatedHalfLineProjection lambda u =
      Uneg (cc20PositiveHalfLineProjection (Upos u)) := by
    unfold ccm24TranslatedHalfLineProjection
      cc20TransportedHalfLineProjection ccm24RadialTranslationEquiv
    change Upos.adjoint (cc20PositiveHalfLineProjection (Upos u)) = _
    rw [hadjoint]
  rw [hshape]
  have houter := cc20GlobalLogTranslation_coeFn (-c)
    (cc20PositiveHalfLineProjection (Upos u))
  have hpositive := cc20PositiveHalfLineProjection_coeFn (Upos u)
  have hpositiveShift :=
    (measurePreserving_add_right volume (-c)).quasiMeasurePreserving.ae_eq
      hpositive
  have hinner := cc20GlobalLogTranslation_coeFn c u
  have hinnerShift :=
    (measurePreserving_add_right volume (-c)).quasiMeasurePreserving.ae_eq
      hinner
  filter_upwards [houter, hpositiveShift, hinnerShift] with t
      houterAt hpositiveAt hinnerAt
  simp only [Function.comp_apply] at hpositiveAt hinnerAt
  change ((cc20GlobalLogTranslation (-c)
      (cc20PositiveHalfLineProjection (Upos u)) :
        cc20GlobalLogCrossingL2) : ℝ → ℂ) t = _
  rw [houterAt, hpositiveAt]
  change cc20PositiveHalfLine.indicator
      (fun s => ((cc20GlobalLogTranslation c u :
        cc20GlobalLogCrossingL2) : ℝ → ℂ) s) (t + -c) =
      (Set.Ici c).indicator (fun s => u s) t
  have hcancel : t + -c + c = t := by ring
  by_cases ht : t ∈ Set.Ici c
  · have hshift : t + -c ∈ cc20PositiveHalfLine := by
      change 0 ≤ t + -c
      change c ≤ t at ht
      linarith
    rw [Set.indicator_of_mem hshift, Set.indicator_of_mem ht]
    rw [hinnerAt, hcancel]
  · have hshift : t + -c ∉ cc20PositiveHalfLine := by
      change ¬ 0 ≤ t + -c
      change ¬ c ≤ t at ht
      linarith
    simp only [Set.indicator, ht, hshift, if_false]

/-- Fixed points of the translated half-line projection are exactly the
literal CCM24 radial support subspace. -/
theorem ccm24TranslatedHalfLineProjection_eq_self_iff
    (lambda : CCM24SoninScale) (u : cc20GlobalLogCrossingL2) :
    ccm24TranslatedHalfLineProjection lambda u = u ↔
      u ∈ ccm24LogRadialSupportClosedSubspace lambda := by
  rw [mem_ccm24LogRadialSupportClosedSubspace_iff]
  constructor
  · intro hfixed
    rw [Lp.ext_iff] at hfixed
    filter_upwards
      [ccm24TranslatedHalfLineProjection_coeFn lambda u, hfixed] with
        t hprojection hsame
    intro ht
    have hnot : t ∉ Set.Ici (Real.log lambda) := by
      simpa only [Set.mem_Ici, not_le] using ht
    have hzero :
        ((Set.Ici (Real.log lambda)).indicator (fun s => u s)) t = 0 := by
      simp only [Set.indicator, hnot, if_false]
    rw [← hsame, hprojection, hzero]
  · intro hsupport
    rw [Lp.ext_iff]
    filter_upwards
      [ccm24TranslatedHalfLineProjection_coeFn lambda u,
        hsupport] with t hprojection hzero
    rw [hprojection]
    by_cases ht : t ∈ Set.Ici (Real.log lambda)
    · simp only [Set.indicator_of_mem ht]
    · have hlt : t < Real.log lambda := by
        simpa only [Set.mem_Ici, not_le] using ht
      rw [hzero hlt]
      simp only [Set.indicator, ht, if_false]

/-- The actual CCM24 radial orthogonal projection is exactly the translated
ordinary half-line projection. -/
theorem ccm24LogRadialSupportProjection_eq_translatedHalfLine
    (lambda : CCM24SoninScale) :
    ccm24LogRadialSupportProjection lambda =
      ccm24TranslatedHalfLineProjection lambda := by
  apply ContinuousLinearMap.IsStarProjection.ext
    (ccm24LogRadialSupportProjection_isStarProjection lambda)
    (ccm24TranslatedHalfLineProjection_isStarProjection lambda)
  ext u
  constructor
  · intro hu
    rcases hu with ⟨v, rfl⟩
    have hsourceFixed : ccm24LogRadialSupportProjection lambda
          (ccm24LogRadialSupportProjection lambda v) =
        ccm24LogRadialSupportProjection lambda v := by
      have hidempotent :=
        (ccm24LogRadialSupportProjection_isStarProjection lambda)
          |>.isIdempotentElem
      have h := congrArg
        (fun A : cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 =>
          A v)
        hidempotent
      simpa only [ContinuousLinearMap.mul_apply] using h
    have htargetFixed : ccm24TranslatedHalfLineProjection lambda
          (ccm24LogRadialSupportProjection lambda v) =
        ccm24LogRadialSupportProjection lambda v :=
      (ccm24TranslatedHalfLineProjection_eq_self_iff lambda _).2
        ((ccm24LogRadialSupportProjection_eq_self_iff lambda _).1
          hsourceFixed)
    exact ⟨ccm24LogRadialSupportProjection lambda v, htargetFixed⟩
  · intro hu
    rcases hu with ⟨v, rfl⟩
    have htargetFixed : ccm24TranslatedHalfLineProjection lambda
          (ccm24TranslatedHalfLineProjection lambda v) =
        ccm24TranslatedHalfLineProjection lambda v := by
      have hidempotent :=
        (ccm24TranslatedHalfLineProjection_isStarProjection lambda)
          |>.isIdempotentElem
      have h := congrArg
        (fun A : cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 =>
          A v)
        hidempotent
      simpa only [ContinuousLinearMap.mul_apply] using h
    have hsourceFixed : ccm24LogRadialSupportProjection lambda
          (ccm24TranslatedHalfLineProjection lambda v) =
        ccm24TranslatedHalfLineProjection lambda v :=
      (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2
        ((ccm24TranslatedHalfLineProjection_eq_self_iff lambda _).1
          htargetFixed)
    exact ⟨ccm24TranslatedHalfLineProjection lambda v, hsourceFixed⟩

/-- Operator form of the cutoff alignment.  The radial projection is a
unitary conjugate of the fixed zero-boundary half-line projection. -/
theorem ccm24LogRadialSupportProjection_eq_translation_conjugation
    (lambda : CCM24SoninScale) :
    ccm24LogRadialSupportProjection lambda =
      (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap ∘L
        cc20PositiveHalfLineProjection ∘L
          (cc20GlobalLogTranslation
            (Real.log lambda)).toContinuousLinearMap := by
  rw [ccm24LogRadialSupportProjection_eq_translatedHalfLine]
  unfold ccm24TranslatedHalfLineProjection
    cc20TransportedHalfLineProjection ccm24RadialTranslationEquiv
  change (cc20GlobalLogTranslation
      (Real.log lambda)).toContinuousLinearMap.adjoint ∘L
        cc20PositiveHalfLineProjection ∘L
          (cc20GlobalLogTranslation
            (Real.log lambda)).toContinuousLinearMap = _
  have hadjoint : (cc20GlobalLogTranslation
      (Real.log lambda)).toContinuousLinearMap.adjoint =
        (cc20GlobalLogTranslation
          (-Real.log lambda)).toContinuousLinearMap := by
    simpa only [neg_neg] using
      (CCM25Concrete.SelectedCrossingOperatorBridge.cc20GlobalLogTranslation_neg_adjoint
        (-Real.log lambda))
  rw [hadjoint]

/-- The concrete orthogonal projection obtained by transporting the radial
support projection through the archimedean Hardy--Titchmarsh unitary. -/
noncomputable def ccm24ArchimedeanFourierSupportTransportProjection
    (lambda : CCM24SoninScale) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  let H := ccm24ArchimedeanHardyTitchmarsh.toContinuousLinearEquiv
    |>.toContinuousLinearMap
  H.adjoint ∘L ccm24LogRadialSupportProjection lambda ∘L H

theorem ccm24ArchimedeanHardyTitchmarsh_symm_apply
    (u : cc20GlobalLogCrossingL2) :
    ccm24ArchimedeanHardyTitchmarsh.symm u =
      ccm24ArchimedeanHardyTitchmarsh u := by
  apply ccm24ArchimedeanHardyTitchmarsh.injective
  rw [ccm24ArchimedeanHardyTitchmarsh.apply_symm_apply]
  rw [ccm24ArchimedeanHardyTitchmarsh_involutive]

theorem ccm24ArchimedeanHardyTitchmarsh_adjoint_apply
    (u : cc20GlobalLogCrossingL2) :
    (ccm24ArchimedeanHardyTitchmarsh.toContinuousLinearEquiv.toContinuousLinearMap).adjoint u =
      ccm24ArchimedeanHardyTitchmarsh u := by
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  exact ccm24ArchimedeanHardyTitchmarsh_symm_apply u

/-- The transported archimedean Fourier-support projection is an orthogonal
projection. -/
theorem ccm24ArchimedeanFourierSupportTransportProjection_isStarProjection
    (lambda : CCM24SoninScale) :
    IsStarProjection
      (ccm24ArchimedeanFourierSupportTransportProjection lambda) := by
  have hself : IsSelfAdjoint
      (ccm24ArchimedeanFourierSupportTransportProjection lambda) := by
    unfold ccm24ArchimedeanFourierSupportTransportProjection
    exact (ccm24LogRadialSupportProjection_isStarProjection lambda)
      |>.isSelfAdjoint.adjoint_conj _
  have hidempotent : IsIdempotentElem
      (ccm24ArchimedeanFourierSupportTransportProjection lambda) := by
    apply ContinuousLinearMap.ext
    intro u
    unfold ccm24ArchimedeanFourierSupportTransportProjection
    simp only [ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.comp_apply]
    simp_rw [ccm24ArchimedeanHardyTitchmarsh_adjoint_apply]
    change ccm24ArchimedeanHardyTitchmarsh
        (ccm24LogRadialSupportProjection lambda
          (ccm24ArchimedeanHardyTitchmarsh
            (ccm24ArchimedeanHardyTitchmarsh
              (ccm24LogRadialSupportProjection lambda
                (ccm24ArchimedeanHardyTitchmarsh u))))) =
      ccm24ArchimedeanHardyTitchmarsh
        (ccm24LogRadialSupportProjection lambda
          (ccm24ArchimedeanHardyTitchmarsh u))
    rw [ccm24ArchimedeanHardyTitchmarsh_involutive]
    have hradial :=
      (ccm24LogRadialSupportProjection_isStarProjection lambda)
        |>.isIdempotentElem
    have hradialAt := congrArg
      (fun P : cc20GlobalLogCrossingL2 →L[ℂ]
        cc20GlobalLogCrossingL2 =>
        P (ccm24ArchimedeanHardyTitchmarsh u)) hradial
    exact congrArg ccm24ArchimedeanHardyTitchmarsh
      (by simpa only [ContinuousLinearMap.mul_apply] using hradialAt)
  exact ⟨hidempotent, hself⟩

/-- Fixed vectors of the transported projection are exactly the literal
archimedean Fourier-support subspace. -/
theorem ccm24ArchimedeanFourierSupportTransportProjection_eq_self_iff
    (lambda : CCM24SoninScale) (u : cc20GlobalLogCrossingL2) :
    ccm24ArchimedeanFourierSupportTransportProjection lambda u = u ↔
      u ∈ ccm24ArchimedeanFourierSupportClosedSubspace lambda := by
  rw [mem_ccm24ArchimedeanFourierSupportClosedSubspace_iff]
  unfold ccm24ArchimedeanFourierSupportTransportProjection
  simp only [ContinuousLinearMap.comp_apply]
  rw [ccm24ArchimedeanHardyTitchmarsh_adjoint_apply]
  constructor
  · intro hfixed
    have hmapped := congrArg ccm24ArchimedeanHardyTitchmarsh hfixed
    rw [ccm24ArchimedeanHardyTitchmarsh_involutive] at hmapped
    exact (ccm24LogRadialSupportProjection_eq_self_iff lambda _).1 hmapped
  · intro hsupport
    have hfixed :=
      (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2 hsupport
    change ccm24ArchimedeanHardyTitchmarsh
        (ccm24LogRadialSupportProjection lambda
          (ccm24ArchimedeanHardyTitchmarsh u)) = u
    rw [hfixed]
    exact ccm24ArchimedeanHardyTitchmarsh_involutive u

/-- The canonical orthogonal projection onto the actual archimedean
Fourier-support closed subspace is the Hardy--Titchmarsh conjugate of the
radial projection. -/
theorem ccm24ArchimedeanFourierSupportProjection_eq_transport
    (lambda : CCM24SoninScale) :
    (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection =
      ccm24ArchimedeanFourierSupportTransportProjection lambda := by
  apply ContinuousLinearMap.IsStarProjection.ext
    isStarProjection_starProjection
    (ccm24ArchimedeanFourierSupportTransportProjection_isStarProjection
      lambda)
  ext u
  constructor
  · intro hu
    rcases hu with ⟨v, rfl⟩
    have hsourceIdempotent :=
      (isStarProjection_starProjection : IsStarProjection
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection)
        |>.isIdempotentElem
    have hsourceFixed := congrArg
      (fun P : cc20GlobalLogCrossingL2 →L[ℂ]
        cc20GlobalLogCrossingL2 => P v) hsourceIdempotent
    simp only [ContinuousLinearMap.mul_apply] at hsourceFixed
    have htargetFixed :=
      (ccm24ArchimedeanFourierSupportTransportProjection_eq_self_iff
        lambda _).2
        ((Submodule.starProjection_eq_self_iff).1 hsourceFixed)
    exact ⟨_, htargetFixed⟩
  · intro hu
    rcases hu with ⟨v, rfl⟩
    have htargetFixed :=
      (ccm24ArchimedeanFourierSupportTransportProjection_isStarProjection
        lambda).isIdempotentElem
    have htargetFixedAt := congrArg
      (fun P : cc20GlobalLogCrossingL2 →L[ℂ]
        cc20GlobalLogCrossingL2 => P v) htargetFixed
    have hsourceFixed := Submodule.starProjection_eq_self_iff.mpr
      ((ccm24ArchimedeanFourierSupportTransportProjection_eq_self_iff
        lambda _).1 (by
          simpa only [ContinuousLinearMap.mul_apply] using htargetFixedAt))
    exact ⟨_, hsourceFixed⟩

/-- A translation-invariant operator has a radial-boundary commutator which
is the unitary translate of its fixed zero-boundary commutator. -/
theorem ccm24RadialCommutator_eq_translation_conjugation
    (lambda : CCM24SoninScale)
    (operator : cc20GlobalLogCrossingL2 →L[ℂ]
      cc20GlobalLogCrossingL2)
    (hpositive : operator ∘L
        (cc20GlobalLogTranslation
          (Real.log lambda)).toContinuousLinearMap =
      (cc20GlobalLogTranslation
        (Real.log lambda)).toContinuousLinearMap ∘L operator)
    (hnegative : operator ∘L
        (cc20GlobalLogTranslation
          (-Real.log lambda)).toContinuousLinearMap =
      (cc20GlobalLogTranslation
        (-Real.log lambda)).toContinuousLinearMap ∘L operator) :
    operator ∘L ccm24LogRadialSupportProjection lambda -
        ccm24LogRadialSupportProjection lambda ∘L operator =
      (cc20GlobalLogTranslation
          (-Real.log lambda)).toContinuousLinearMap ∘L
        (operator ∘L cc20PositiveHalfLineProjection -
          cc20PositiveHalfLineProjection ∘L operator) ∘L
        (cc20GlobalLogTranslation
          (Real.log lambda)).toContinuousLinearMap := by
  rw [ccm24LogRadialSupportProjection_eq_translation_conjugation]
  apply ContinuousLinearMap.ext
  intro u
  let U := (cc20GlobalLogTranslation
    (Real.log lambda)).toContinuousLinearMap
  let V := (cc20GlobalLogTranslation
    (-Real.log lambda)).toContinuousLinearMap
  let z := cc20PositiveHalfLineProjection (U u)
  have hpositiveAt : operator (U u) = U (operator u) := by
    have h := congrArg
      (fun map : cc20GlobalLogCrossingL2 →L[ℂ]
        cc20GlobalLogCrossingL2 => map u) hpositive
    simpa only [U, ContinuousLinearMap.comp_apply] using h
  have hnegativeAt : operator (V z) = V (operator z) := by
    have h := congrArg
      (fun map : cc20GlobalLogCrossingL2 →L[ℂ]
        cc20GlobalLogCrossingL2 => map z) hnegative
    simpa only [V, ContinuousLinearMap.comp_apply] using h
  change operator (V z) - V
      (cc20PositiveHalfLineProjection (U (operator u))) =
    V (operator z -
      cc20PositiveHalfLineProjection (operator (U u)))
  rw [hnegativeAt, ← hpositiveAt, map_sub]

/-- The oriented outer-boundary crossing is likewise a unitary translate of
the fixed half-line crossing.  No norm or trace has been taken. -/
theorem ccm24RadialOrientedCrossing_eq_translation_conjugation
    (lambda : CCM24SoninScale)
    (operator : cc20GlobalLogCrossingL2 →L[ℂ]
      cc20GlobalLogCrossingL2)
    (hnegative : operator ∘L
        (cc20GlobalLogTranslation
          (-Real.log lambda)).toContinuousLinearMap =
      (cc20GlobalLogTranslation
        (-Real.log lambda)).toContinuousLinearMap ∘L operator) :
    (ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2 -
        ccm24LogRadialSupportProjection lambda) ∘L operator ∘L
        ccm24LogRadialSupportProjection lambda =
      (cc20GlobalLogTranslation
          (-Real.log lambda)).toContinuousLinearMap ∘L
        ((ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2 -
            cc20PositiveHalfLineProjection) ∘L operator ∘L
          cc20PositiveHalfLineProjection) ∘L
        (cc20GlobalLogTranslation
          (Real.log lambda)).toContinuousLinearMap := by
  rw [ccm24LogRadialSupportProjection_eq_translation_conjugation]
  apply ContinuousLinearMap.ext
  intro u
  let U := (cc20GlobalLogTranslation
    (Real.log lambda)).toContinuousLinearMap
  let V := (cc20GlobalLogTranslation
    (-Real.log lambda)).toContinuousLinearMap
  let z := cc20PositiveHalfLineProjection (U u)
  have hnegativeAt : operator (V z) = V (operator z) := by
    have h := congrArg
      (fun map : cc20GlobalLogCrossingL2 →L[ℂ]
        cc20GlobalLogCrossingL2 => map z) hnegative
    simpa only [V, ContinuousLinearMap.comp_apply] using h
  have hcancelAt : U (V (operator z)) = operator z := by
    simpa only [U, V] using
      (cc20GlobalLogTranslation_neg_apply
        (Real.log lambda) (operator z))
  change operator (V z) - V
      (cc20PositiveHalfLineProjection (U (operator (V z)))) =
    V (operator z - cc20PositiveHalfLineProjection (operator z))
  rw [hnegativeAt, hcancelAt, map_sub]

end CC20Concrete
end Source
end ConnesWeilRH
