/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3HardyTranslatedTail
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Source.CC20Concrete.GlobalLogConvolution
import ConnesWeilRH.Source.CC20YoshidaConvolution
import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

/-!
# Lower energy along the translated source-test orbit

For the actual unit-scale R3 Fourier-leakage leg, translating the selected
compact source test far enough into the positive half-line leaves it fixed by
the radial projection. Its Hardy-support projection tends to zero, while the
selected root convolution commutes with translation. The output norm therefore
stays bounded below by a positive owner-dependent constant.

This is a lower-energy orbit statement. It does not yet package the orbit as
an orthonormal family or transfer its energy to a G8 diagonal trace.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open MeasureTheory
open Source
open Source.CC20Concrete
open Source.CC20YoshidaConvolution
open Source.CCM25Concrete
open Source.CCM25Concrete.CompactLogConvolution
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.C1SameOwnerWeil
open scoped Topology
open scoped Convolution

local notation "Carrier" => finiteSCarrier

/-- A nonzero bilateral Laplace value forces the same compact source test to
be nonzero. -/
theorem selectedOwnerSourceTest_ne_zero_of_laplaceAt_ne_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0) :
    owner.sourceTest.test ≠ 0 := by
  intro hzero
  apply hvalue
  unfold CompactLogTest.laplaceAt
  calc
    ∫ x : ℝ, (CompactLogTest.exponentialWeight owner.sourceTest rho).test x =
        ∫ _x : ℝ, (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [CompactLogTest.exponentialWeight_apply,
        DFunLike.congr_fun hzero x]
      simp
    _ = 0 := by simp

private theorem rootConvolution_sourceTest_test_ne_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (htest : owner.sourceTest.test ≠ 0) :
    rootConvolution owner (owner.sourceTest.test.toLp 2) ≠ 0 := by
  have hcont : Continuous
      (fun t : ℝ => Complex.normSq (owner.sourceTest.test t)) := by
    fun_prop
  have hcompact : HasCompactSupport
      (fun t : ℝ => Complex.normSq (owner.sourceTest.test t)) :=
    owner.sourceTest.compactSupport.comp_left (by simp)
  have hintegrable : Integrable
      (fun t : ℝ => Complex.normSq (owner.sourceTest.test t))
      (volume : Measure ℝ) :=
    hcont.integrable_of_hasCompactSupport hcompact
  have hpoint : ∃ t : ℝ, owner.sourceTest.test t ≠ 0 := by
    by_contra h
    apply htest
    ext t
    exact not_ne_iff.mp (not_exists.mp h t)
  obtain ⟨t, ht⟩ := hpoint
  have hmass : 0 < ∫ t : ℝ, Complex.normSq (owner.sourceTest.test t) :=
    integral_pos_of_integrable_nonneg_nonzero hcont hintegrable
      (fun t => Complex.normSq_nonneg _) (Complex.normSq_pos.mpr ht).ne'
  have hsquare0 : owner.sourceTest.convolutionSquare.test 0 ≠ 0 := by
    rw [owner.sourceTest.convolutionSquare_zero_eq_integral_normSq]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hmass)
  have hconv_apply (x : ℝ) :
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
          owner.sourceTest.involution.test owner.sourceTest.test x =
        ∫ t : ℝ, star (owner.sourceTest.test (-t)) *
          owner.sourceTest.test (x - t) := by
    have hcomplex :
        SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
            owner.sourceTest.involution.test owner.sourceTest.test x =
          ∫ t : ℝ, star (owner.sourceTest.test (-t)) *
            owner.sourceTest.test (x - t) := by
      have h := SchwartzMap.convolution_apply
        (ContinuousLinearMap.mul ℂ ℂ)
        owner.sourceTest.involution.test owner.sourceTest.test x
      simpa [MeasureTheory.convolution, CompactLogTest.involution_apply] using h
    calc
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
          owner.sourceTest.involution.test owner.sourceTest.test x
          = SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
              owner.sourceTest.involution.test owner.sourceTest.test x := by
              exact congrArg (fun f : SchwartzMap ℝ ℂ => f x)
                (schwartzConvolution_mul_real_eq_complex
                  owner.sourceTest.involution.test owner.sourceTest.test)
      _ = _ := hcomplex
  have hconv :
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
          owner.sourceTest.involution.test owner.sourceTest.test ≠ 0 := by
    intro hzero
    apply hsquare0
    have heq : owner.sourceTest.convolutionSquare.test =
        SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
          owner.sourceTest.involution.test owner.sourceTest.test := by
      ext x
      rw [owner.sourceTest.convolutionSquare_apply, hconv_apply]
    rw [heq]
    exact congrArg (fun f : SchwartzMap ℝ ℂ => f 0) hzero
  have hconvLp :
      (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        owner.sourceTest.involution.test owner.sourceTest.test).toLp 2 ≠ 0 := by
    intro hzero
    apply hconv
    exact (SchwartzMap.injective_toLp 2) hzero
  have hformula :
      rootConvolution owner (owner.sourceTest.test.toLp 2) =
        (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
          owner.sourceTest.involution.test owner.sourceTest.test).toLp 2 := by
    unfold rootConvolution
    rw [cc20GlobalLogConvolution_toLp]
  rw [hformula]
  exact hconvLp

set_option maxHeartbeats 1000000 in
-- The translated Lp representative requires extra reduction fuel for its AE support proof.
private theorem positiveHalfLineProjection_globalLogTranslation_neg_eq_self_of_schwartz_support
    (f : SchwartzMap ℝ ℂ) (a c : ℝ)
    (hsupp : Function.support f ⊆ Set.Icc a c)
    (n : ℕ) (hn : -a ≤ (n : ℝ)) :
    cc20PositiveHalfLineProjection
        (cc20GlobalLogTranslation (-(n : ℝ)) (f.toLp 2)) =
      cc20GlobalLogTranslation (-(n : ℝ)) (f.toLp 2) := by
  rw [Lp.ext_iff]
  have hprojection := cc20PositiveHalfLineProjection_coeFn
    (cc20GlobalLogTranslation (-(n : ℝ)) (f.toLp 2))
  have htranslation := cc20GlobalLogTranslation_coeFn
    (-(n : ℝ)) (f.toLp 2)
  have hrepresentative :=
    (measurePreserving_add_right (volume : Measure ℝ) (-(n : ℝ)))
      |>.quasiMeasurePreserving.ae_eq_comp (SchwartzMap.coeFn_toLp f 2)
  filter_upwards [hprojection, htranslation, hrepresentative] with x hp ht hf
  have hfAt : (f.toLp 2 : ℝ → ℂ) (x - (n : ℝ)) = f (x - (n : ℝ)) := by
    simpa only [Function.comp_apply, sub_eq_add_neg] using hf
  rw [hp]
  by_cases hx : 0 ≤ x
  · have hmem : x ∈ cc20PositiveHalfLine := by
      simpa [cc20PositiveHalfLine] using hx
    simp [Set.indicator, hmem]
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hzero : f (x - (n : ℝ)) = 0 := by
      by_contra hne
      have hmem : x - (n : ℝ) ∈ Function.support f := hne
      have hlo := (hsupp hmem).1
      change a ≤ x - (n : ℝ) at hlo
      linarith
    have hnotmem : x ∉ cc20PositiveHalfLine := by
      simpa [cc20PositiveHalfLine] using hx
    have htranslatedZero :
        (cc20GlobalLogTranslation (-(n : ℝ)) (f.toLp 2) : ℝ → ℂ) x = 0 := by
      calc
        (cc20GlobalLogTranslation (-(n : ℝ)) (f.toLp 2) : ℝ → ℂ) x =
            (f.toLp 2 : ℝ → ℂ) (x - (n : ℝ)) := by
          simpa only [sub_eq_add_neg] using ht
        _ = f (x - (n : ℝ)) := hfAt
        _ = 0 := hzero
    simp [Set.indicator, hnotmem, htranslatedZero]

/-- The unit-scale R3 leakage column generated by the selected source test. -/
noncomputable def unitSourceTestTranslationLeakageColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (n : ℕ) : Carrier :=
  sourceRootCompletedRightCommutatorLeftLeg owner unitSoninScale
    (cc20GlobalLogTranslation (-(n : ℝ))
      (owner.sourceTest.test.toLp 2))

/-- Norm of the selected root applied to its compact source test. -/
noncomputable def sourceTestRootImageNorm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) : ℝ :=
  ‖rootConvolution owner (owner.sourceTest.test.toLp 2)‖

noncomputable def unitSourceTestRootTranslation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (n : ℕ) : Carrier :=
  cc20GlobalLogTranslation (-(n : ℝ))
    (rootConvolution owner (owner.sourceTest.test.toLp 2))

noncomputable def unitSourceTestTranslationError
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (n : ℕ) : Carrier :=
  rootConvolution owner
    (cc20PositiveHalfLineProjection
      (sourceFourierSupportProjection unitSoninScale
        (cc20GlobalLogTranslation (-(n : ℝ))
          (owner.sourceTest.test.toLp 2))))

/-- A selected compact source test with nonzero Laplace value has nonzero
selected-root image. -/
theorem sourceTestRootImageNorm_pos
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0) :
    0 < sourceTestRootImageNorm owner := by
  apply norm_pos_iff.mpr
  exact rootConvolution_sourceTest_test_ne_zero owner
    (selectedOwnerSourceTest_ne_zero_of_laplaceAt_ne_zero owner rho hvalue)

set_option maxHeartbeats 3000000 in
-- Applying the translated-support limit theorem needs deep Lp definitional reduction.
private theorem unitSourceTestTranslationError_tendsto_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    Tendsto (fun n : ℕ => unitSourceTestTranslationError owner n)
      atTop (𝓝 0) := by
  let C : Carrier →L[ℂ] Carrier := rootConvolution owner
  let P : Carrier →L[ℂ] Carrier := cc20PositiveHalfLineProjection
  have hQ :=
    sourceFourierSupportProjection_unit_globalLogTranslation_neg_tendsto_zero
      (owner.sourceTest.test.toLp 2)
  have herror : Tendsto
      (fun n : ℕ => C (P (sourceFourierSupportProjection unitSoninScale
        (cc20GlobalLogTranslation (-(n : ℝ))
          (owner.sourceTest.test.toLp 2)))))
      atTop (𝓝 0) := by
    have hcontinuous : Continuous (C ∘L P) := (C ∘L P).continuous
    simpa only [Function.comp_apply, map_zero] using
      hcontinuous.tendsto 0 |>.comp hQ
  simpa [unitSourceTestTranslationError, C, P] using herror

private theorem eventually_norm_sub_lowerBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) (a b : ℕ → E)
    (ha : ∀ n, ‖a n‖ = r)
    (hb : Tendsto b atTop (𝓝 (0 : E))) :
    ∀ᶠ n in atTop, ‖a n - b n‖ ≥ r / 2 := by
  have hbNorm : Tendsto (fun n => ‖b n‖) atTop (𝓝 0) :=
    by simpa using (continuous_norm.tendsto (0 : E)).comp hb
  have hsmall := Metric.tendsto_nhds.1 hbNorm (r / 2) (by linarith)
  filter_upwards [hsmall] with n hn
  have hn' : ‖b n‖ < r / 2 := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (norm_nonneg _)] using hn
  have hsum : a n = (a n - b n) + b n := by abel
  have htriangle := norm_add_le (a n - b n) (b n)
  rw [← hsum, ha n] at htriangle
  have hstrict : r / 2 < ‖a n - b n‖ := by linarith
  exact le_of_lt hstrict

set_option maxHeartbeats 1000000 in
-- Unfolding the actual R3 operator into its Fourier-leakage factorization is costly.
private theorem unitSourceTestTranslationLeakageColumn_eq_rootTranslation_sub_error
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (n : ℕ)
    (hn : supportRadius owner.sourceTest ≤ (n : ℝ)) :
    unitSourceTestTranslationLeakageColumn owner n =
      unitSourceTestRootTranslation owner n -
        unitSourceTestTranslationError owner n := by
  let u : Carrier := owner.sourceTest.test.toLp 2
  let C : Carrier →L[ℂ] Carrier := rootConvolution owner
  let P : Carrier →L[ℂ] Carrier := cc20PositiveHalfLineProjection
  let Q : Carrier →L[ℂ] Carrier :=
    sourceFourierSupportProjection unitSoninScale
  have hsupp := support_subset_Icc owner.sourceTest
  have hfixed : P (cc20GlobalLogTranslation (-(n : ℝ)) u) =
      cc20GlobalLogTranslation (-(n : ℝ)) u := by
    change cc20PositiveHalfLineProjection
        (cc20GlobalLogTranslation (-(n : ℝ))
          (owner.sourceTest.test.toLp 2)) = _
    exact positiveHalfLineProjection_globalLogTranslation_neg_eq_self_of_schwartz_support
      owner.sourceTest.test (-supportRadius owner.sourceTest)
      (supportRadius owner.sourceTest) hsupp n (by linarith)
  have htranslatedRoot :
      C (cc20GlobalLogTranslation (-(n : ℝ)) u) =
        cc20GlobalLogTranslation (-(n : ℝ)) (C u) := by
    change rootConvolution owner
        (cc20GlobalLogTranslation (-(n : ℝ)) u) = _
    calc
      rootConvolution owner
          (cc20GlobalLogTranslation (-(n : ℝ)) u) =
          ((rootConvolution owner) ∘L
            (cc20GlobalLogTranslation (-(n : ℝ))).toContinuousLinearMap) u := rfl
      _ = ((cc20GlobalLogTranslation (-(n : ℝ))).toContinuousLinearMap ∘L
          rootConvolution owner) u := by
        rw [rootConvolution_comp_globalLogTranslation]
      _ = cc20GlobalLogTranslation (-(n : ℝ))
          (rootConvolution owner u) := rfl
  have hleakage :
      sourceRootCompletedRightCommutatorLeftLeg owner unitSoninScale =
        C ∘L P ∘L (1 - Q) ∘L P := by
    rw [sourceRootCompletedRightCommutatorLeftLeg_eq_root_fourierLeakage]
    rw [radialSupportProjection_unit]
  have hformula :
      sourceRootCompletedRightCommutatorLeftLeg owner unitSoninScale
          (cc20GlobalLogTranslation (-(n : ℝ)) u) =
        cc20GlobalLogTranslation (-(n : ℝ)) (C u) -
          C (P (Q (cc20GlobalLogTranslation (-(n : ℝ)) u))) := by
    rw [hleakage]
    change C (P ((1 - Q) (P
      (cc20GlobalLogTranslation (-(n : ℝ)) u)))) = _
    rw [hfixed]
    rw [show (1 - Q) (cc20GlobalLogTranslation (-(n : ℝ)) u) =
      cc20GlobalLogTranslation (-(n : ℝ)) u -
        Q (cc20GlobalLogTranslation (-(n : ℝ)) u) by simp]
    calc
      C (P (cc20GlobalLogTranslation (-(n : ℝ)) u -
          Q (cc20GlobalLogTranslation (-(n : ℝ)) u))) =
        C (P (cc20GlobalLogTranslation (-(n : ℝ)) u) -
          P (Q (cc20GlobalLogTranslation (-(n : ℝ)) u))) := by
            rw [map_sub]
      _ = C (P (cc20GlobalLogTranslation (-(n : ℝ)) u)) -
          C (P (Q (cc20GlobalLogTranslation (-(n : ℝ)) u))) := by
            rw [map_sub]
      _ = C (cc20GlobalLogTranslation (-(n : ℝ)) u) -
          C (P (Q (cc20GlobalLogTranslation (-(n : ℝ)) u))) := by
            rw [hfixed]
      _ = cc20GlobalLogTranslation (-(n : ℝ)) (C u) -
          C (P (Q (cc20GlobalLogTranslation (-(n : ℝ)) u))) := by
            rw [htranslatedRoot]
  simpa [unitSourceTestTranslationLeakageColumn, unitSourceTestRootTranslation,
    unitSourceTestTranslationError, u, C, P, Q] using hformula

private theorem unitSourceTestTranslationLeakageColumn_eq_rootTranslation_sub_error_eventually
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    ∀ᶠ n in atTop,
      unitSourceTestTranslationLeakageColumn owner n =
        unitSourceTestRootTranslation owner n -
          unitSourceTestTranslationError owner n := by
  have hlarge : ∀ᶠ n : ℕ in atTop,
      supportRadius owner.sourceTest ≤ (n : ℝ) := by
    filter_upwards [eventually_atTop.2
      ⟨Nat.ceil (supportRadius owner.sourceTest), fun n hn => by
        calc
          supportRadius owner.sourceTest ≤
              (Nat.ceil (supportRadius owner.sourceTest) : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn⟩] with n hn
    exact hn
  filter_upwards [hlarge] with n hn
  exact unitSourceTestTranslationLeakageColumn_eq_rootTranslation_sub_error
    owner n hn

set_option maxHeartbeats 1000000 in
-- This assembly theorem combines several same-owner operator identities.
/-- The actual unit-scale R3 leakage leg has a positive lower bound along
right translates of its own compact source test whenever that test detects a
Laplace value. This is same-owner and uses the exact Fourier-leakage normal
form, not the unrestricted root convolution alone. -/
theorem sourceRootCompletedRightCommutatorLeftLeg_sourceTest_translate_norm_lowerBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0) :
    ∀ᶠ n in atTop,
      ‖unitSourceTestTranslationLeakageColumn owner n‖ ≥
        sourceTestRootImageNorm owner / 2 := by
  have hr := sourceTestRootImageNorm_pos owner rho hvalue
  have ha (n : ℕ) : ‖unitSourceTestRootTranslation owner n‖ =
      sourceTestRootImageNorm owner := by
    rw [unitSourceTestRootTranslation, norm_cc20GlobalLogTranslation,
      sourceTestRootImageNorm]
  have hb := unitSourceTestTranslationError_tendsto_zero owner
  have hbound := eventually_norm_sub_lowerBound
    (sourceTestRootImageNorm owner) hr
    (unitSourceTestRootTranslation owner)
    (unitSourceTestTranslationError owner) ha hb
  have hformula :=
    unitSourceTestTranslationLeakageColumn_eq_rootTranslation_sub_error_eventually owner
  filter_upwards [hbound, hformula] with n hn hleak
  rw [hleak]
  exact hn

end Dev
end ConnesWeilRH
