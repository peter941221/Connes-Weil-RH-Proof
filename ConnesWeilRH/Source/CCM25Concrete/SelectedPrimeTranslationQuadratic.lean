/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

/-!
# Selected finite-prime translation quadratic form

This module places the selected finite-prime terms directly on the convolution
root Hilbert space.  Unlike the crossing trace operator, the translation
operator below is independent of the selected test; the selected test enters
only as the vector at which its quadratic form is evaluated.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace SelectedPrimeTranslationQuadratic

open MeasureTheory
open CC20Concrete
open SelectedWeilSquare
open SelectedCrossingOperatorBridge

noncomputable def sourceRootLp
    (owner : SelectedWeilSquareOwner) : cc20GlobalLogCrossingL2 :=
  owner.sourceTest.test.toLp 2

theorem inner_sourceRootLp_translation_eq_convolutionSquare
    (owner : SelectedWeilSquareOwner) (b : ℝ) :
    inner ℂ (sourceRootLp owner)
        (cc20GlobalLogTranslation b (sourceRootLp owner)) =
      owner.convolutionSquare.test b := by
  rw [L2.inner_def]
  have hroot := owner.sourceTest.test.coeFn_toLp
    2 (volume : Measure ℝ)
  have hroot_shift :=
    (measurePreserving_add_right volume b).quasiMeasurePreserving.ae_eq hroot
  have htranslation :=
    cc20GlobalLogTranslation_coeFn b (sourceRootLp owner)
  calc
    (∫ t : ℝ,
        inner ℂ ((sourceRootLp owner) t)
          ((cc20GlobalLogTranslation b (sourceRootLp owner)) t)) =
        ∫ t : ℝ,
          star (owner.sourceTest.test t) *
            owner.sourceTest.test (t + b) := by
      apply integral_congr_ae
      filter_upwards [hroot, hroot_shift, htranslation] with t hr hrs ht
      rw [ht]
      rw [RCLike.inner_apply]
      rw [sourceRootLp]
      rw [hr]
      have hrs' : (owner.sourceTest.test.toLp 2 : ℝ → ℂ) (t + b) =
          owner.sourceTest.test (t + b) := by
        simpa only [Function.comp_apply] using hrs
      rw [hrs']
      rw [starRingEnd_apply]
      exact mul_comm _ _
    _ = ∫ u : ℝ,
        star (owner.sourceTest.test (-u)) *
          owner.sourceTest.test (b - u) := by
      let f : ℝ → ℂ := fun u =>
        star (owner.sourceTest.test (-u)) *
          owner.sourceTest.test (b - u)
      simpa only [f, neg_neg, sub_neg_eq_add, add_comm] using
        (integral_neg_eq_self f (volume : Measure ℝ))
    _ = owner.convolutionSquare.test b := by
      exact (SelectedWeilSquareOwner.convolutionSquare_apply owner b).symm

noncomputable def primePowerTranslationWeight
    (p m : ℕ) : ℝ :=
  Real.log (p : ℝ) / Real.sqrt ((p ^ m : ℕ) : ℝ)

noncomputable def primePowerTranslationOperator
    (p m : ℕ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  ((primePowerTranslationWeight p m : ℂ) •
    ((cc20GlobalLogTranslation
        ((m : ℝ) * Real.log (p : ℝ))).toContinuousLinearMap +
      (cc20GlobalLogTranslation
        (-((m : ℝ) * Real.log (p : ℝ)))).toContinuousLinearMap))

theorem primePowerTranslationOperator_isSelfAdjoint
    (p m : ℕ) :
    IsSelfAdjoint (primePowerTranslationOperator p m) := by
  rw [primePowerTranslationOperator]
  apply IsSelfAdjoint.smul
  · change IsSelfAdjoint ((primePowerTranslationWeight p m : ℝ) : ℂ)
    simp [IsSelfAdjoint]
  · have h := IsSelfAdjoint.add_star_self
      (cc20GlobalLogTranslation
        ((m : ℝ) * Real.log (p : ℝ))).toContinuousLinearMap
    rw [ContinuousLinearMap.star_eq_adjoint] at h
    have hadjoint :
        (cc20GlobalLogTranslation
          ((m : ℝ) * Real.log (p : ℝ))).toContinuousLinearMap.adjoint =
          (cc20GlobalLogTranslation
            (-((m : ℝ) * Real.log (p : ℝ)))).toContinuousLinearMap := by
      simpa only [neg_neg] using
        (cc20GlobalLogTranslation_neg_adjoint
          (-((m : ℝ) * Real.log (p : ℝ))))
    rw [hadjoint] at h
    exact h

theorem inner_primePowerTranslationOperator_eq_finitePrimeTerm_pow
    (owner : SelectedWeilSquareOwner) {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0) :
    inner ℂ (sourceRootLp owner)
        (primePowerTranslationOperator p m (sourceRootLp owner)) =
      owner.finitePrimeTerm (p ^ m) := by
  rw [primePowerTranslationOperator,
    primePowerTranslationWeight,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    inner_smul_right, inner_add_right]
  change
    ((Real.log (p : ℝ) / Real.sqrt ((p ^ m : ℕ) : ℝ) : ℝ) : ℂ) *
        (inner ℂ (sourceRootLp owner)
            (cc20GlobalLogTranslation
              ((m : ℝ) * Real.log (p : ℝ)) (sourceRootLp owner)) +
          inner ℂ (sourceRootLp owner)
            (cc20GlobalLogTranslation
              (-((m : ℝ) * Real.log (p : ℝ))) (sourceRootLp owner))) =
      owner.finitePrimeTerm (p ^ m)
  rw [
    inner_sourceRootLp_translation_eq_convolutionSquare,
    inner_sourceRootLp_translation_eq_convolutionSquare]
  rw [SelectedWeilSquareOwner.finitePrimeTerm,
    SelectedWeilSquareOwner.primePowerValue,
    ArithmeticFunction.vonMangoldt_apply_pow hm,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  simp only [Nat.cast_pow, Real.log_pow]
  push_cast
  ring

noncomputable def finitePrimeTranslationOperatorSum
    (terms : Finset (ℕ × ℕ)) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  ∑ pm ∈ terms, primePowerTranslationOperator pm.1 pm.2

theorem finitePrimeTranslationOperatorSum_isSelfAdjoint
    (terms : Finset (ℕ × ℕ)) :
    IsSelfAdjoint (finitePrimeTranslationOperatorSum terms) := by
  rw [finitePrimeTranslationOperatorSum]
  exact isSelfAdjoint_sum terms fun pm _ =>
    primePowerTranslationOperator_isSelfAdjoint pm.1 pm.2

theorem inner_finitePrimeTranslationOperatorSum_eq_finitePrimeTerm_pow_sum
    (owner : SelectedWeilSquareOwner)
    (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    (hnonzero : ∀ pm ∈ terms, pm.2 ≠ 0) :
    inner ℂ (sourceRootLp owner)
        (finitePrimeTranslationOperatorSum terms (sourceRootLp owner)) =
      ∑ pm ∈ terms, owner.finitePrimeTerm (pm.1 ^ pm.2) := by
  rw [finitePrimeTranslationOperatorSum,
    ContinuousLinearMap.sum_apply]
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro pm hpm
  exact inner_primePowerTranslationOperator_eq_finitePrimeTerm_pow
    owner (hprime pm hpm) (hnonzero pm hpm)

end SelectedPrimeTranslationQuadratic
end CCM25Concrete
end Source
end ConnesWeilRH
