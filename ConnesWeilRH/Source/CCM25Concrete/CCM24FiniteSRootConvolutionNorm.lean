/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSHomogeneousPhysicalEnergyBound

/-!
# Support bound for the selected whole-line convolution root

The global logarithmic convolution is a Plancherel multiplier.  Its operator
norm is bounded by the `L1` norm of the Schwartz kernel, and compact support
then turns that norm into the order-zero support--Schwartz polynomial used by
the physical-energy ledger.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootConvolutionNorm

open MeasureTheory
open scoped FourierTransform

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSInverseMetric
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSRootCompletedFirstJet
open CCM24SourceProlateTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSHomogeneousPhysicalEnergyBound
open SelectedCrossingOperatorBridge

set_option maxHeartbeats 800000 in
-- The concrete Fourier multiplier application elaborates its `Lp` coercions deeply.
/-- Fourier multiplication has operator norm at most the multiplier's
`L-infinity` norm. -/
theorem norm_cc20FourierMultiplier_le
    (h : SchwartzMap ℝ ℂ) :
    ‖cc20FourierMultiplier h‖ ≤ ‖(𝓕 h).toLp ⊤‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  rw [cc20FourierMultiplier_apply]
  exact Lp.norm_smul_le _ _

/-- Conjugation by a linear isometric equivalence cannot increase operator
norm. -/
theorem norm_linearIsometryEquiv_conjugation_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (F : H ≃ₗᵢ[ℂ] H) (operator : H →L[ℂ] H) :
    ‖F.symm.toLinearIsometry.toContinuousLinearMap.comp
        (operator.comp F.toLinearIsometry.toContinuousLinearMap)‖ ≤
      ‖operator‖ := by
  rw [LinearIsometry.norm_toContinuousLinearMap_comp]
  exact (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv operator F).le

/-- Plancherel convolution has operator norm at most the kernel's `L1` norm. -/
theorem norm_cc20GlobalLogConvolution_le_toLp_one
    (h : SchwartzMap ℝ ℂ) :
    ‖cc20GlobalLogConvolution h‖ ≤ ‖h.toLp 1‖ := by
  have hmultiplier : ‖cc20FourierMultiplier h‖ ≤ ‖h.toLp 1‖ :=
    (norm_cc20FourierMultiplier_le h).trans
      (SchwartzMap.norm_fourier_Lp_top_leq_toLp_one h)
  have hconjugation := norm_linearIsometryEquiv_conjugation_le
    (Lp.fourierTransformₗᵢ ℝ ℂ) (cc20FourierMultiplier h)
  have hconvolution :
      ‖cc20GlobalLogConvolution h‖ ≤ ‖cc20FourierMultiplier h‖ := by
    simpa only [cc20GlobalLogConvolution] using hconjugation
  exact hconvolution.trans hmultiplier

/-- Compact support bounds the `L1` norm by interval length times the
order-zero Schwartz seminorm. -/
theorem norm_toLp_one_le_supportLength_mul_seminorm
    (h : SchwartzMap ℝ ℂ) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support h ⊆ Set.Icc a c) :
    ‖h.toLp 1‖ ≤
      (c - a) * SchwartzMap.seminorm ℂ 0 0 h := by
  rw [SchwartzMap.norm_toLp_one]
  have hintegral :
      (∫ x : ℝ, ‖h x‖) = ∫ x : ℝ in Set.Icc a c, ‖h x‖ := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Set.Icc a c
    · simp [hx]
    · have hzero : h x = 0 := by
        by_contra hne
        exact hx (hsupp hne)
      simp [hx, hzero]
  rw [hintegral]
  have hnormIntegrable :
      IntegrableOn (fun x : ℝ => ‖h x‖) (Set.Icc a c) volume :=
    h.integrable.norm.integrableOn
  have hconstIntegrable :
      IntegrableOn
        (fun _ : ℝ => SchwartzMap.seminorm ℂ 0 0 h)
        (Set.Icc a c) volume :=
    integrableOn_const measure_Icc_lt_top.ne
  calc
    (∫ x : ℝ in Set.Icc a c, ‖h x‖) ≤
        ∫ _ : ℝ in Set.Icc a c, SchwartzMap.seminorm ℂ 0 0 h := by
      exact setIntegral_mono_on hnormIntegrable hconstIntegrable
        measurableSet_Icc fun x _ => SchwartzMap.norm_le_seminorm ℂ h x
    _ = (c - a) * SchwartzMap.seminorm ℂ 0 0 h := by
      rw [setIntegral_const, smul_eq_mul]
      simp only [Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hac)]

/-- A compactly supported Schwartz kernel gives a support-polynomial
whole-line convolution norm. -/
theorem norm_cc20GlobalLogConvolution_le_supportLength_mul_seminorm
    (h : SchwartzMap ℝ ℂ) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support h ⊆ Set.Icc a c) :
    ‖cc20GlobalLogConvolution h‖ ≤
      (c - a) * SchwartzMap.seminorm ℂ 0 0 h :=
  (norm_cc20GlobalLogConvolution_le_toLp_one h).trans
    (norm_toLp_one_le_supportLength_mul_seminorm h a c hac hsupp)

/-- The CCM25 involution preserves the order-zero Schwartz seminorm. -/
theorem seminorm_zero_zero_involution_eq
    (g : CompactLogConvolution.CompactLogTest) :
    SchwartzMap.seminorm ℂ 0 0 g.involution.test =
      SchwartzMap.seminorm ℂ 0 0 g.test := by
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound ℂ 0 0 _ (by positivity)
    intro x
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero,
      CompactLogConvolution.CompactLogTest.involution_apply, norm_star] using
      (SchwartzMap.norm_le_seminorm ℂ g.test (-x))
  · apply SchwartzMap.seminorm_le_bound ℂ 0 0 _ (by positivity)
    intro x
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero,
      CompactLogConvolution.CompactLogTest.involution_apply, neg_neg,
      norm_star] using
      (SchwartzMap.norm_le_seminorm ℂ g.involution.test (-x))

/-- The actual selected convolution root has the same support-polynomial norm
bound as its compact source test. -/
theorem rootConvolution_norm_le_supportLength_mul_seminorm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c) :
    ‖rootConvolution owner‖ ≤
      (c - a) * SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test := by
  have hreflected : -c ≤ -a := by linarith
  have hroot :=
    norm_cc20GlobalLogConvolution_le_supportLength_mul_seminorm
      owner.sourceTest.involution.test (-c) (-a) hreflected
      (compactLogTest_involution_support_subset_reflected
        owner.sourceTest a c hsupp)
  rw [rootConvolution]
  rw [seminorm_zero_zero_involution_eq] at hroot
  convert hroot using 1
  ring

set_option maxHeartbeats 3000000 in
-- The consumer retains Proof 484's complete finite-S corner and basis data.
/-- The completed finite-Euler corner has a support-polynomial homogeneous
physical-energy bound. -/
theorem sourceRootCompletedFiniteEulerTrace_norm_le_supportPhysicalEnergy
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ‖ordinaryTraceAlong globalBasis
        (sourceRootCompletedFixedQuotientCorner owner lambda
          (radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family ∘L
            radialSupportProjection lambda))‖ ≤
      (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  let P := (c - a) ^ 2 *
    SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2
  let H := ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
    (globalBasis i)‖ ^ 2
  have hH : 0 ≤ H := by
    dsimp [H]
    exact tsum_nonneg fun i => sq_nonneg _
  have hroot := rootConvolution_norm_le_supportLength_mul_seminorm
    owner a c hac hsupp
  have hrootSq : ‖rootConvolution owner‖ ^ 2 ≤ P := by
    have hsquare :=
      (sq_le_sq₀ (norm_nonneg _)
        (by positivity :
          0 ≤ (c - a) * SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test)).2
        hroot
    simpa only [P, mul_pow] using hsquare
  have htrace :=
    sourceRootCompletedFiniteEulerTrace_norm_le_rootNormPhysicalEnergy
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis globalBasis
      boundaryBasis hfactor
  calc
    _ ≤ 6 * P + 2 * ‖rootConvolution owner‖ ^ 2 * H := by
      simpa only [P, H] using htrace
    _ ≤ 6 * P + 2 * P * H := by
      exact add_le_add (le_refl (6 * P))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrootSq
            (by norm_num : (0 : ℝ) ≤ 2)) hH)
    _ = (6 + 2 * H) * P := by ring
    _ = (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
      rfl

end CCM24FiniteSRootConvolutionNorm
end CCM25Concrete
end Source
end ConnesWeilRH
