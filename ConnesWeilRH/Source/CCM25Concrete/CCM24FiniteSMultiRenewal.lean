/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkov

/-!
# Multi-prime causal renewal law

This module flattens the recursive finite Euler Markov composition into one
multi-index renewal law.  Each index records one geometric count per visible
prime, its weight is the product probability, and its displacement is the sum
of the genuine one-sided prime-log translations.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMultiRenewal

open scoped InnerProduct

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCausalMarkov
open SelectedCrossingOperatorBridge

/-- One geometric count for every occurrence in the visible-prime list. -/
abbrev FiniteEulerRenewalIndex : List CCM24VisiblePrime → Type
  | [] => PUnit
  | _ :: S => ℕ × FiniteEulerRenewalIndex S

/-- Product probability of a finite Euler renewal multi-index. -/
noncomputable def finiteEulerRenewalWeight :
    (S : List CCM24VisiblePrime) → FiniteEulerRenewalIndex S → ℝ
  | [], _ => 1
  | p :: S, index =>
      primeEulerRenewalWeight p index.1 *
        finiteEulerRenewalWeight S index.2

/-- Total causal logarithmic displacement of a renewal multi-index. -/
noncomputable def finiteEulerRenewalDisplacement :
    (S : List CCM24VisiblePrime) → FiniteEulerRenewalIndex S → ℝ
  | [], _ => 0
  | p :: S, index =>
      (index.1 : ℝ) * Real.log p +
        finiteEulerRenewalDisplacement S index.2

theorem finiteEulerRenewalWeight_nonneg
    (S : List CCM24VisiblePrime) (index : FiniteEulerRenewalIndex S) :
    0 ≤ finiteEulerRenewalWeight S index := by
  induction S with
  | nil => simp [finiteEulerRenewalWeight]
  | cons p S ih =>
      exact mul_nonneg (primeEulerRenewalWeight_nonneg p index.1)
        (ih index.2)

theorem finiteEulerRenewalDisplacement_nonneg
    (S : List CCM24VisiblePrime) (index : FiniteEulerRenewalIndex S) :
    0 ≤ finiteEulerRenewalDisplacement S index := by
  induction S with
  | nil => simp [finiteEulerRenewalDisplacement]
  | cons p S ih =>
      exact add_nonneg
        (mul_nonneg (Nat.cast_nonneg index.1)
          (Real.log_nonneg (by exact_mod_cast p.property.le)))
        (ih index.2)

/-- The complete product probability law sums to one. -/
theorem finiteEulerRenewalWeight_hasSum_one
    (S : List CCM24VisiblePrime) :
    HasSum (finiteEulerRenewalWeight S) 1 := by
  induction S with
  | nil =>
      simp [finiteEulerRenewalWeight]
  | cons p S ih =>
      have hp : HasSum (primeEulerRenewalWeight p) 1 := by
        simpa [tsum_primeEulerRenewalWeight p] using
          (summable_primeEulerRenewalWeight p).hasSum
      have hprod : Summable (fun index :
          ℕ × FiniteEulerRenewalIndex S =>
            primeEulerRenewalWeight p index.1 *
              finiteEulerRenewalWeight S index.2) := by
        rw [summable_prod_of_nonneg]
        · constructor
          · intro n
            exact ih.summable.mul_left (primeEulerRenewalWeight p n)
          · have hfiber : ∀ n : ℕ,
                ∑' index : FiniteEulerRenewalIndex S,
                    primeEulerRenewalWeight p n *
                      finiteEulerRenewalWeight S index =
                  primeEulerRenewalWeight p n := by
              intro n
              rw [ih.summable.tsum_mul_left, ih.tsum_eq, mul_one]
            simpa only [hfiber] using hp.summable
        · intro index
          exact mul_nonneg (primeEulerRenewalWeight_nonneg p index.1)
            (finiteEulerRenewalWeight_nonneg S index.2)
      simpa [finiteEulerRenewalWeight] using hp.mul ih hprod

/-- Absolute summability of the complete product probability law. -/
theorem summable_finiteEulerRenewalWeight
    (S : List CCM24VisiblePrime) :
    Summable (finiteEulerRenewalWeight S) :=
  (finiteEulerRenewalWeight_hasSum_one S).summable

/-- The complete multi-prime renewal law has total mass one. -/
theorem tsum_finiteEulerRenewalWeight (S : List CCM24VisiblePrime) :
    ∑' index : FiniteEulerRenewalIndex S,
      finiteEulerRenewalWeight S index = 1 := by
  exact (finiteEulerRenewalWeight_hasSum_one S).tsum_eq

/-!
Compact support may be applied to the causal probability law before any
absolute value.  The following truncated first moment is the scalar core of
the outer-boundary estimate: its mass is still probability mass, and its
displacement cost is at most the support radius.
-/
noncomputable def finiteEulerRenewalCompactMoment
    (B : ℝ) (S : List CCM24VisiblePrime)
    (index : FiniteEulerRenewalIndex S) : ℝ :=
  if finiteEulerRenewalDisplacement S index ≤ B then
    finiteEulerRenewalWeight S index *
      finiteEulerRenewalDisplacement S index
  else 0

theorem finiteEulerRenewalCompactMoment_nonneg
    (B : ℝ) (S : List CCM24VisiblePrime)
    (index : FiniteEulerRenewalIndex S) :
    0 ≤ finiteEulerRenewalCompactMoment B S index := by
  unfold finiteEulerRenewalCompactMoment
  split_ifs
  · exact mul_nonneg (finiteEulerRenewalWeight_nonneg S index)
      (finiteEulerRenewalDisplacement_nonneg S index)
  · exact le_rfl

theorem tsum_finiteEulerRenewalCompactMoment_le
    (B : ℝ) (hB : 0 ≤ B) (S : List CCM24VisiblePrime) :
    ∑' index : FiniteEulerRenewalIndex S,
      finiteEulerRenewalCompactMoment B S index ≤ B := by
  have hweight : Summable (finiteEulerRenewalWeight S) :=
    summable_finiteEulerRenewalWeight S
  have hmajorant : Summable (fun index : FiniteEulerRenewalIndex S =>
      B * finiteEulerRenewalWeight S index) :=
    hweight.mul_left B
  have hpoint : ∀ index : FiniteEulerRenewalIndex S,
      finiteEulerRenewalCompactMoment B S index ≤
        B * finiteEulerRenewalWeight S index := by
    intro index
    unfold finiteEulerRenewalCompactMoment
    split_ifs with hsmall
    · exact (mul_le_mul_of_nonneg_left hsmall
        (finiteEulerRenewalWeight_nonneg S index)).trans_eq (by ring)
    · exact mul_nonneg hB (finiteEulerRenewalWeight_nonneg S index)
  calc
    ∑' index : FiniteEulerRenewalIndex S,
        finiteEulerRenewalCompactMoment B S index ≤
      ∑' index : FiniteEulerRenewalIndex S,
        B * finiteEulerRenewalWeight S index := by
      exact (Summable.of_nonneg_of_le
        (fun index => finiteEulerRenewalCompactMoment_nonneg B S index)
        hpoint hmajorant).tsum_le_tsum hpoint hmajorant
    _ = B := by
      rw [tsum_mul_left, tsum_finiteEulerRenewalWeight]
      ring

/-! The compactly retained outer-pair atom is the object on which the
probability-moment bound is used. -/
noncomputable def finiteEulerRenewalCompactOuterPairAtom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (B : ℝ) (S : List CCM24VisiblePrime)
    (index : FiniteEulerRenewalIndex S) : ℂ :=
  if finiteEulerRenewalDisplacement S index ≤ B then
    (finiteEulerRenewalWeight S index : ℂ) *
        (finiteEulerRenewalDisplacement S index : ℂ) *
      (owner.convolutionSquare.test
          (finiteEulerRenewalDisplacement S index) +
        owner.convolutionSquare.test
          (-finiteEulerRenewalDisplacement S index))
  else 0

theorem norm_finiteEulerRenewalCompactOuterPairAtom_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (B : ℝ) (S : List CCM24VisiblePrime)
    (M : ℝ) (hM : ∀ x : ℝ,
      ‖owner.convolutionSquare.test x‖ ≤ M) (hM_nonneg : 0 ≤ M)
    (index : FiniteEulerRenewalIndex S) :
    ‖finiteEulerRenewalCompactOuterPairAtom owner B S index‖ ≤
      2 * M * finiteEulerRenewalCompactMoment B S index := by
  have hweight := finiteEulerRenewalWeight_nonneg S index
  have hdisp := finiteEulerRenewalDisplacement_nonneg S index
  by_cases hsmall : finiteEulerRenewalDisplacement S index ≤ B
  · rw [finiteEulerRenewalCompactOuterPairAtom, if_pos hsmall,
      norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hweight, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hdisp]
    have hsum : ‖owner.convolutionSquare.test
          (finiteEulerRenewalDisplacement S index) +
        owner.convolutionSquare.test
          (-finiteEulerRenewalDisplacement S index)‖ ≤ 2 * M := by
      calc
        ‖owner.convolutionSquare.test
              (finiteEulerRenewalDisplacement S index) +
            owner.convolutionSquare.test
              (-finiteEulerRenewalDisplacement S index)‖ ≤
          ‖owner.convolutionSquare.test
              (finiteEulerRenewalDisplacement S index)‖ +
            ‖owner.convolutionSquare.test
              (-finiteEulerRenewalDisplacement S index)‖ :=
          norm_add_le _ _
        _ ≤ M + M := add_le_add
          (hM (finiteEulerRenewalDisplacement S index))
          (hM (-finiteEulerRenewalDisplacement S index))
        _ = 2 * M := by ring
    calc
      finiteEulerRenewalWeight S index *
          finiteEulerRenewalDisplacement S index *
          ‖owner.convolutionSquare.test
              (finiteEulerRenewalDisplacement S index) +
            owner.convolutionSquare.test
              (-finiteEulerRenewalDisplacement S index)‖ ≤
        finiteEulerRenewalWeight S index *
          finiteEulerRenewalDisplacement S index * (2 * M) := by
            exact mul_le_mul_of_nonneg_left hsum
              (mul_nonneg hweight hdisp)
      _ = 2 * M * finiteEulerRenewalCompactMoment B S index := by
        simp [finiteEulerRenewalCompactMoment, hsmall]
        ring
  · simp [finiteEulerRenewalCompactOuterPairAtom, hsmall,
      finiteEulerRenewalCompactMoment]

theorem tsum_norm_finiteEulerRenewalCompactOuterPairAtom_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (S : List CCM24VisiblePrime) (M : ℝ)
    (hM : ∀ x : ℝ,
      ‖owner.convolutionSquare.test x‖ ≤ M)
    (hM_nonneg : 0 ≤ M) :
    ∑' index : FiniteEulerRenewalIndex S,
      ‖finiteEulerRenewalCompactOuterPairAtom owner
        owner.supportRadius S index‖ ≤
      2 * M * owner.supportRadius := by
  have hB := owner.supportRadius_nonnegative
  have hmoment : Summable (finiteEulerRenewalCompactMoment
      owner.supportRadius S) := by
    have hweight := summable_finiteEulerRenewalWeight S
    have hmajorant : Summable (fun index : FiniteEulerRenewalIndex S =>
        owner.supportRadius * finiteEulerRenewalWeight S index) :=
      hweight.mul_left owner.supportRadius
    apply Summable.of_nonneg_of_le
      (fun index => finiteEulerRenewalCompactMoment_nonneg
        owner.supportRadius S index)
      (fun index => by
        unfold finiteEulerRenewalCompactMoment
        split_ifs with hsmall
        · exact (mul_le_mul_of_nonneg_left hsmall
            (finiteEulerRenewalWeight_nonneg S index)).trans_eq (by ring)
        · exact mul_nonneg hB
            (finiteEulerRenewalWeight_nonneg S index))
      hmajorant
  have hpoint : ∀ index : FiniteEulerRenewalIndex S,
      ‖finiteEulerRenewalCompactOuterPairAtom owner
          owner.supportRadius S index‖ ≤
        2 * M * finiteEulerRenewalCompactMoment
          owner.supportRadius S index := by
    intro index
    exact norm_finiteEulerRenewalCompactOuterPairAtom_le owner
      owner.supportRadius S M hM hM_nonneg index
  have hmajorant := hmoment.mul_left (2 * M)
  calc
    ∑' index : FiniteEulerRenewalIndex S,
        ‖finiteEulerRenewalCompactOuterPairAtom owner
            owner.supportRadius S index‖ ≤
      ∑' index : FiniteEulerRenewalIndex S,
        2 * M * finiteEulerRenewalCompactMoment
          owner.supportRadius S index := by
      exact (Summable.of_nonneg_of_le
        (fun index => norm_nonneg _)
        hpoint hmajorant).tsum_le_tsum hpoint hmajorant
    _ = 2 * M *
        (∑' index : FiniteEulerRenewalIndex S,
          finiteEulerRenewalCompactMoment owner.supportRadius S index) := by
      rw [tsum_mul_left]
    _ ≤ 2 * M * owner.supportRadius := by
      exact mul_le_mul_of_nonneg_left
        (tsum_finiteEulerRenewalCompactMoment_le
          owner.supportRadius hB S)
        (mul_nonneg (by norm_num) hM_nonneg)

/-- One vector term of the complete renewal translation average. -/
noncomputable def finiteEulerRenewalTerm
    (S : List CCM24VisiblePrime) (u : finiteSCarrier)
    (index : FiniteEulerRenewalIndex S) : finiteSCarrier :=
  (finiteEulerRenewalWeight S index : ℂ) •
    cc20GlobalLogTranslation (-finiteEulerRenewalDisplacement S index) u

/-- The operator-valued form of one renewal atom.  Keeping this object in the
operator Banach space makes it legal to take adjoints before inserting the
transported Sonin projection. -/
noncomputable def finiteEulerRenewalOperatorTerm
    (S : List CCM24VisiblePrime)
    (index : FiniteEulerRenewalIndex S) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (finiteEulerRenewalWeight S index : ℂ) •
    (cc20GlobalLogTranslation
      (-finiteEulerRenewalDisplacement S index)).toContinuousLinearMap

theorem finiteEulerRenewalOperatorTerm_apply
    (S : List CCM24VisiblePrime) (index : FiniteEulerRenewalIndex S)
    (u : finiteSCarrier) :
    finiteEulerRenewalOperatorTerm S index u =
      finiteEulerRenewalTerm S u index := by
  rfl

/-- The renewal series is absolutely summable in operator norm, not merely
pointwise on vectors. -/
theorem summable_finiteEulerRenewalOperatorTerm
    (S : List CCM24VisiblePrime) :
    Summable (finiteEulerRenewalOperatorTerm S) := by
  apply Summable.of_norm_bounded
    (summable_finiteEulerRenewalWeight S)
  intro index
  rw [finiteEulerRenewalOperatorTerm, norm_smul, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (finiteEulerRenewalWeight_nonneg S index)]
  calc
    finiteEulerRenewalWeight S index *
          ‖(cc20GlobalLogTranslation
            (-finiteEulerRenewalDisplacement S index)).toContinuousLinearMap‖ ≤
        finiteEulerRenewalWeight S index * 1 :=
      mul_le_mul_of_nonneg_left
        (cc20GlobalLogTranslation
          (-finiteEulerRenewalDisplacement S index)).norm_toContinuousLinearMap_le
        (finiteEulerRenewalWeight_nonneg S index)
    _ = finiteEulerRenewalWeight S index := mul_one _

theorem summable_finiteEulerRenewalTerm
    (S : List CCM24VisiblePrime) (u : finiteSCarrier) :
    Summable (finiteEulerRenewalTerm S u) := by
  apply Summable.of_norm
  have hweight :=
    (summable_finiteEulerRenewalWeight S).mul_right ‖u‖
  simpa only [finiteEulerRenewalTerm, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (finiteEulerRenewalWeight_nonneg S _),
    norm_cc20GlobalLogTranslation] using hweight

/-- Flattening theorem: the recursively composed normalized Euler inverse is
exactly one probability average over the total causal displacement. -/
theorem finiteEulerCausalAverage_apply_eq_multiRenewal
    (S : List CCM24VisiblePrime) (u : finiteSCarrier) :
    finiteEulerCausalAverage S u =
      ∑' index : FiniteEulerRenewalIndex S,
        finiteEulerRenewalTerm S u index := by
  induction S generalizing u with
  | nil =>
      simp [finiteEulerCausalAverage, finiteEulerRenewalTerm,
        finiteEulerRenewalWeight, finiteEulerRenewalDisplacement,
        cc20GlobalLogTranslation_zero_apply]
  | cons p S ih =>
      rw [finiteEulerCausalAverage, ContinuousLinearMap.comp_apply,
        normalizedPrimeEulerInverse_apply_eq_tsum]
      have hprime : Summable (fun n : ℕ =>
          (primeEulerRenewalWeight p n : ℂ) •
            cc20GlobalLogTranslation (-(n : ℝ) * Real.log p) u) := by
        apply Summable.of_norm
        simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (primeEulerRenewalWeight_nonneg p _),
          norm_cc20GlobalLogTranslation] using
            (summable_primeEulerRenewalWeight p).mul_right ‖u‖
      rw [(finiteEulerCausalAverage S).map_tsum hprime]
      have hpair := summable_finiteEulerRenewalTerm (p :: S) u
      calc
        (∑' n : ℕ, finiteEulerCausalAverage S
            ((primeEulerRenewalWeight p n : ℂ) •
              cc20GlobalLogTranslation (-(n : ℝ) * Real.log p) u)) =
            ∑' n : ℕ, ∑' index : FiniteEulerRenewalIndex S,
              finiteEulerRenewalTerm (p :: S) u (n, index) := by
          apply tsum_congr
          intro n
          rw [map_smul, ih, ← tsum_const_smul'']
          apply tsum_congr
          intro index
          simp only [finiteEulerRenewalTerm, finiteEulerRenewalWeight,
            finiteEulerRenewalDisplacement, smul_smul]
          rw [cc20GlobalLogTranslation_add_apply]
          congr 1
          · exact (Complex.ofReal_mul _ _).symm
          · apply congrArg (fun shift => cc20GlobalLogTranslation shift u)
            ring
        _ = ∑' index : FiniteEulerRenewalIndex (p :: S),
              finiteEulerRenewalTerm (p :: S) u index :=
          (Summable.tsum_prod hpair).symm

/-- The actual normalized inverse covariance-side operator has the same
flattened causal law. -/
theorem normalizedFiniteEulerInverse_apply_eq_multiRenewal
    (family : FinitePrimePowerFamily) (u : finiteSCarrier) :
    CCM24FiniteSInverseMetric.normalizedFiniteEulerInverse family u =
      ∑' index : FiniteEulerRenewalIndex family.visiblePrimes,
        finiteEulerRenewalTerm family.visiblePrimes u index := by
  rw [normalizedFiniteEulerInverse_eq_causalAverage]
  exact finiteEulerCausalAverage_apply_eq_multiRenewal _ _

/-- Operator-norm version of the complete multi-prime renewal expansion. -/
theorem normalizedFiniteEulerInverse_eq_multiRenewalOperator
    (family : FinitePrimePowerFamily) :
    CCM24FiniteSInverseMetric.normalizedFiniteEulerInverse family =
      ∑' index : FiniteEulerRenewalIndex family.visiblePrimes,
        finiteEulerRenewalOperatorTerm family.visiblePrimes index := by
  apply ContinuousLinearMap.ext
  intro u
  rw [normalizedFiniteEulerInverse_apply_eq_multiRenewal]
  exact ((ContinuousLinearMap.apply ℂ finiteSCarrier u).map_tsum
    (summable_finiteEulerRenewalOperatorTerm family.visiblePrimes)).symm

/-- The adjoint normalized inverse is the positive-displacement renewal
series.  This is an operator-norm identity, so a bounded operator may be
inserted on either side without changing summation order. -/
theorem normalizedFiniteEulerInverse_adjoint_eq_multiRenewalOperator
    (family : FinitePrimePowerFamily) :
    (CCM24FiniteSInverseMetric.normalizedFiniteEulerInverse family)† =
      ∑' index : FiniteEulerRenewalIndex family.visiblePrimes,
        (finiteEulerRenewalWeight family.visiblePrimes index : ℂ) •
          (cc20GlobalLogTranslation
            (finiteEulerRenewalDisplacement family.visiblePrimes index)).toContinuousLinearMap := by
  rw [normalizedFiniteEulerInverse_eq_multiRenewalOperator]
  rw [Function.LeftInverse.map_tsum
    (fun index : FiniteEulerRenewalIndex family.visiblePrimes =>
      finiteEulerRenewalOperatorTerm family.visiblePrimes index)
    (g := (ContinuousLinearMap.adjoint :
      (finiteSCarrier →L[ℂ] finiteSCarrier) ≃ₗᵢ⋆[ℂ]
        (finiteSCarrier →L[ℂ] finiteSCarrier)))
    ContinuousLinearMap.adjoint.continuous
    ContinuousLinearMap.adjoint.continuous
    (fun operator => ContinuousLinearMap.adjoint_adjoint operator)]
  apply tsum_congr
  intro index
  simp only [finiteEulerRenewalOperatorTerm, map_smulₛₗ,
    starRingEnd_apply]
  have hstar :
      star (finiteEulerRenewalWeight family.visiblePrimes index : ℂ) =
        (finiteEulerRenewalWeight family.visiblePrimes index : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [hstar, cc20GlobalLogTranslation_neg_adjoint]

/-- The paired outer scalar attached to one complete multi-prime renewal
atom. -/
noncomputable def finiteEulerRenewalOuterPairAtom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (S : List CCM24VisiblePrime) (index : FiniteEulerRenewalIndex S) : ℂ :=
  (finiteEulerRenewalWeight S index : ℂ) *
    (finiteEulerRenewalDisplacement S index : ℂ) *
      (owner.convolutionSquare.test
          (finiteEulerRenewalDisplacement S index) +
        owner.convolutionSquare.test
          (-finiteEulerRenewalDisplacement S index))

/-- Compact support truncates the complete multi-prime renewal atom before
the first absolute value. -/
theorem finiteEulerRenewalOuterPairAtom_eq_zero_of_support_lt
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (S : List CCM24VisiblePrime) (index : FiniteEulerRenewalIndex S)
    (hfar : owner.supportRadius <
      finiteEulerRenewalDisplacement S index) :
    finiteEulerRenewalOuterPairAtom owner S index = 0 := by
  have hdisp := finiteEulerRenewalDisplacement_nonneg S index
  have hforward := owner.convolutionSquare_eq_zero_of_abs_gt
    (finiteEulerRenewalDisplacement S index)
    (by simpa [abs_of_nonneg hdisp] using hfar)
  have hreflected := owner.convolutionSquare_eq_zero_of_abs_gt
    (-finiteEulerRenewalDisplacement S index)
    (by simpa [abs_neg, abs_of_nonneg hdisp] using hfar)
  simp [finiteEulerRenewalOuterPairAtom, hforward, hreflected]

/-!
The compact atom is not a new approximation: it is the original renewal atom
with its already-vanishing tail made explicit.  This is the exact reattachment
needed before transferring the compact first-moment estimate to the physical
outer renewal series.
-/
theorem finiteEulerRenewalOuterPairAtom_eq_compact
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (S : List CCM24VisiblePrime) (index : FiniteEulerRenewalIndex S) :
    finiteEulerRenewalOuterPairAtom owner S index =
      finiteEulerRenewalCompactOuterPairAtom owner owner.supportRadius S index := by
  by_cases hsmall : finiteEulerRenewalDisplacement S index ≤ owner.supportRadius
  · simp only [finiteEulerRenewalOuterPairAtom,
      finiteEulerRenewalCompactOuterPairAtom, if_pos hsmall]
  · have hfar : owner.supportRadius <
        finiteEulerRenewalDisplacement S index := lt_of_not_ge hsmall
    rw [finiteEulerRenewalOuterPairAtom_eq_zero_of_support_lt
      owner S index hfar]
    simp [finiteEulerRenewalCompactOuterPairAtom, hsmall]

theorem tsum_norm_finiteEulerRenewalOuterPairAtom_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (S : List CCM24VisiblePrime) (M : ℝ)
    (hM : ∀ x : ℝ,
      ‖owner.convolutionSquare.test x‖ ≤ M)
    (hM_nonneg : 0 ≤ M) :
    ∑' index : FiniteEulerRenewalIndex S,
      ‖finiteEulerRenewalOuterPairAtom owner S index‖ ≤
      2 * M * owner.supportRadius := by
  calc
    ∑' index : FiniteEulerRenewalIndex S,
        ‖finiteEulerRenewalOuterPairAtom owner S index‖ =
      ∑' index : FiniteEulerRenewalIndex S,
        ‖finiteEulerRenewalCompactOuterPairAtom owner
          owner.supportRadius S index‖ := by
      apply tsum_congr
      intro index
      rw [finiteEulerRenewalOuterPairAtom_eq_compact]
    _ ≤ 2 * M * owner.supportRadius :=
      tsum_norm_finiteEulerRenewalCompactOuterPairAtom_le owner S M hM
        hM_nonneg

theorem summable_finiteEulerRenewalOuterPairAtom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (S : List CCM24VisiblePrime) (M : ℝ)
    (hM : ∀ x : ℝ,
      ‖owner.convolutionSquare.test x‖ ≤ M)
    (hM_nonneg : 0 ≤ M) :
    Summable (finiteEulerRenewalOuterPairAtom owner S) := by
  have hmoment : Summable (finiteEulerRenewalCompactMoment
      owner.supportRadius S) := by
    have hweight := summable_finiteEulerRenewalWeight S
    have hmajorant : Summable (fun index : FiniteEulerRenewalIndex S =>
        owner.supportRadius * finiteEulerRenewalWeight S index) :=
      hweight.mul_left owner.supportRadius
    apply Summable.of_nonneg_of_le
      (fun index => finiteEulerRenewalCompactMoment_nonneg
        owner.supportRadius S index)
      (fun index => by
        unfold finiteEulerRenewalCompactMoment
        split_ifs with hsmall
        · exact (mul_le_mul_of_nonneg_left hsmall
            (finiteEulerRenewalWeight_nonneg S index)).trans_eq (by ring)
        · exact mul_nonneg owner.supportRadius_nonnegative
            (finiteEulerRenewalWeight_nonneg S index))
      hmajorant
  have hmajorant := hmoment.mul_left (2 * M)
  apply Summable.of_norm_bounded hmajorant
  intro index
  calc
    ‖finiteEulerRenewalOuterPairAtom owner S index‖ =
        ‖finiteEulerRenewalCompactOuterPairAtom owner
          owner.supportRadius S index‖ := by
      rw [finiteEulerRenewalOuterPairAtom_eq_compact]
    _ ≤ 2 * M * finiteEulerRenewalCompactMoment
        owner.supportRadius S index :=
      norm_finiteEulerRenewalCompactOuterPairAtom_le owner
        owner.supportRadius S M hM hM_nonneg index

theorem norm_tsum_finiteEulerRenewalOuterPairAtom_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (S : List CCM24VisiblePrime) (M : ℝ)
    (hM : ∀ x : ℝ,
      ‖owner.convolutionSquare.test x‖ ≤ M)
    (hM_nonneg : 0 ≤ M) :
    ‖∑' index : FiniteEulerRenewalIndex S,
      finiteEulerRenewalOuterPairAtom owner S index‖ ≤
      2 * M * owner.supportRadius := by
  have hsum := summable_finiteEulerRenewalOuterPairAtom owner S M hM hM_nonneg
  calc
    ‖∑' index : FiniteEulerRenewalIndex S,
        finiteEulerRenewalOuterPairAtom owner S index‖ ≤
      ∑' index : FiniteEulerRenewalIndex S,
        ‖finiteEulerRenewalOuterPairAtom owner S index‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ 2 * M * owner.supportRadius :=
      tsum_norm_finiteEulerRenewalOuterPairAtom_le owner S M hM hM_nonneg

end CCM24FiniteSMultiRenewal
end CCM25Concrete
end Source
end ConnesWeilRH
