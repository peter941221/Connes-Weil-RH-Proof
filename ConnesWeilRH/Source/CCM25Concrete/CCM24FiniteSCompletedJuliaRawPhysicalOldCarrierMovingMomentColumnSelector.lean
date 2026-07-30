/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceMomentObstruction
import Mathlib.NumberTheory.PrimeCounting

/-!
# Operator-norm selector for the Bone 1 moving source column

The preceding obstruction is stated for an explicitly supplied bounded
sequence in the source Sonin carrier.  This module supplies the exact
functional-analytic selector needed to construct that sequence: a strict
operator-norm lower bound for the one-prime moment column yields unit-ball
source vectors with the same lower bound up to the usual strict margin.

The selected vectors are elements of the actual source Sonin subtype.  No
ambient global-log translation is inserted, and no translation invariance of
the Sonin intersection is assumed.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMovingMomentColumnSelector

open scoped InnerProduct InnerProductSpace
open scoped Topology

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceMomentObstruction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The actual source-domain moment column -/

/-- The one-prime boundary moment after the genuine old/new frame readout.
This operator acts on the actual source Sonin carrier, so its unit-ball
vectors are already legal moving source witnesses. -/
noncomputable def onePrimeBoundaryMomentColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  onePrimeBoundaryMoment owner lambda p ∘L
    ContinuousLinearMap.adjoint
      (suffixEulerFrameSchurStep lambda p []).oldFrame ∘L
    newSuffixFrame lambda []

theorem onePrimeBoundaryMomentColumn_apply
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda) :
    onePrimeBoundaryMomentColumn owner lambda p x =
      onePrimeBoundaryMoment owner lambda p
        ((ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p []).oldFrame)
          (newSuffixFrame lambda [] x)) := by
  rfl

/-! ## The genuine arithmetic-prime sequence -/

/-- The `n`th arithmetic prime, embedded in the project's visible-prime
carrier. Unlike `canonicalVisiblePrimeSequence`, this sequence carries the
actual `Nat.Prime` proof required by arithmetic owners. -/
noncomputable def arithmeticVisiblePrimeSequence (n : ℕ) : CCM24VisiblePrime :=
  ⟨Nat.nth Nat.Prime n, (Nat.prime_nth_prime n).one_lt⟩

theorem arithmeticVisiblePrimeSequence_isPrime (n : ℕ) :
    Nat.Prime (arithmeticVisiblePrimeSequence n).1 := by
  exact Nat.prime_nth_prime n

theorem tendsto_ccm24PrimeEulerCoefficient_arithmeticVisiblePrimeSequence :
    Filter.Tendsto
      (fun n =>
        ccm24PrimeEulerCoefficient (arithmeticVisiblePrimeSequence n))
      Filter.atTop (𝓝 0) := by
  have hprime : Filter.Tendsto
      (fun n => (Nat.nth Nat.Prime n : ℝ))
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun n => ?_)
      tendsto_natCast_atTop_atTop
    have hn' : n + 2 ≤ Nat.nth Nat.Prime n :=
      Nat.add_two_le_nth_prime n
    have hn : n ≤ Nat.nth Nat.Prime n := by
      omega
    exact_mod_cast hn
  have hsqrt : Filter.Tendsto
      (fun n => Real.sqrt (Nat.nth Nat.Prime n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hprime
  have hinv : Filter.Tendsto
      (fun n => (Real.sqrt (Nat.nth Nat.Prime n : ℝ))⁻¹)
      Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  simpa only [arithmeticVisiblePrimeSequence,
    ccm24PrimeEulerCoefficient, one_div] using hinv

/-! ## Unit-ball selection from an operator-norm lower bound -/

theorem exists_uniformly_bounded_movingSource_of_eventually_column_norm_gt
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (prime : ℕ → CCM24VisiblePrime)
    (epsilon : ℝ)
    (hcolumn : ∀ᶠ n in Filter.atTop,
      epsilon < ‖onePrimeBoundaryMomentColumn owner lambda (prime n)‖) :
    ∃ x : ℕ → sourceSoninCarrier lambda,
      (∀ n, ‖x n‖ ≤ 1) ∧
      (∀ᶠ n in Filter.atTop,
        epsilon ≤
          ‖onePrimeBoundaryMoment owner lambda (prime n)
              ((ContinuousLinearMap.adjoint
                (suffixEulerFrameSchurStep lambda (prime n) []).oldFrame)
                (newSuffixFrame lambda [] (x n)))‖) := by
  let x : ℕ → sourceSoninCarrier lambda := fun n =>
    if h : epsilon <
        ‖onePrimeBoundaryMomentColumn owner lambda (prime n)‖ then
      Classical.choose
        (ContinuousLinearMap.exists_lt_apply_of_lt_opNorm
          (onePrimeBoundaryMomentColumn owner lambda (prime n)) h)
    else
      0
  have hx : ∀ n, ‖x n‖ ≤ 1 := by
    intro n
    by_cases h : epsilon <
        ‖onePrimeBoundaryMomentColumn owner lambda (prime n)‖
    · simp only [x, dif_pos h]
      exact (Classical.choose_spec
        (ContinuousLinearMap.exists_lt_apply_of_lt_opNorm
          (onePrimeBoundaryMomentColumn owner lambda (prime n)) h)).1.le
    · simp only [x, dif_neg h]
      exact norm_zero.le.trans (by norm_num)
  refine ⟨x, hx, ?_⟩
  filter_upwards [hcolumn] with n hn
  have hchosen := Classical.choose_spec
    (ContinuousLinearMap.exists_lt_apply_of_lt_opNorm
      (onePrimeBoundaryMomentColumn owner lambda (prime n)) hn)
  have hvalue : epsilon <
      ‖onePrimeBoundaryMomentColumn owner lambda (prime n) (x n)‖ := by
    simp only [x, dif_pos hn]
    exact hchosen.2
  have hvalue' : epsilon ≤
      ‖onePrimeBoundaryMomentColumn owner lambda (prime n) (x n)‖ :=
    hvalue.le
  simpa only [onePrimeBoundaryMomentColumn_apply] using hvalue'

/-! ## Direct Bone 1 obstruction entry point -/

set_option maxHeartbeats 4000000 in
-- The selector, frame readback, and filter obstruction are elaborated together.
set_option maxRecDepth 10000 in
theorem noExistsUniformOldCarrierDomination_of_eventually_column_norm_gt
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (prime : ℕ → CCM24VisiblePrime)
    (hcoeff : Filter.Tendsto
      (fun n => ccm24PrimeEulerCoefficient (prime n))
      Filter.atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hcolumn : ∀ᶠ n in Filter.atTop,
      epsilon < ‖onePrimeBoundaryMomentColumn owner lambda (prime n)‖) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixRawOldCarrierUniformDominationData owner lambda bound) := by
  obtain ⟨x, hx, hmoment⟩ :=
    exists_uniformly_bounded_movingSource_of_eventually_column_norm_gt
      prime epsilon hcolumn
  exact noExistsUniformOldCarrierDomination_of_movingSourceMoment_lowerBound
    prime x hcoeff (sourceBound := 1) zero_le_one hx epsilon hepsilon hmoment

/-! ## Direct arithmetic Bone 1 entry point -/

set_option maxHeartbeats 4000000 in
-- The arithmetic sequence, selector, and filter contradiction elaborate together.
set_option maxRecDepth 10000 in
theorem noExistsUniformOldCarrierDomination_of_eventually_arithmeticPrime_column_norm_gt
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hcolumn : ∀ᶠ n in Filter.atTop,
      epsilon <
        ‖onePrimeBoundaryMomentColumn owner lambda
          (arithmeticVisiblePrimeSequence n)‖) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixRawOldCarrierUniformDominationData owner lambda bound) := by
  exact noExistsUniformOldCarrierDomination_of_eventually_column_norm_gt
    arithmeticVisiblePrimeSequence
    tendsto_ccm24PrimeEulerCoefficient_arithmeticVisiblePrimeSequence
    epsilon hepsilon hcolumn

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMovingMomentColumnSelector
end CCM25Concrete
end Source
end ConnesWeilRH
