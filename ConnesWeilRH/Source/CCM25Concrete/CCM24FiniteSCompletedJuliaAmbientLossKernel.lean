/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientDefectFactorization

/-!
# No exact zero mode for the antiresonant ambient loss

The ambient loss column contains the factor `I + U_a`, where `U_a` is right
translation by a positive logarithmic distance.  On the actual radial-support
carrier, a vector killed by this factor is zero: the support boundary gives
the first zero interval, and the relation `u(t) + u(t + a) = 0` propagates it
through every later interval.

This is only an injectivity result.  It does not give a closed-range estimate,
an inverse bound, or the missing uniform Douglas factor.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaAmbientLossKernel

open MeasureTheory Set
open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSParameterizedSoninSubspace
open CCM24FiniteSFixedSourcePolar

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The radial-support translation lemma -/

/-- A positive translation cannot have `-1` as an eigenvalue on an upper
radial-support vector. -/
theorem ccm24LogRadialSupport_add_translation_injective
    (lambda : CCM24SoninScale)
    {u : cc20GlobalLogCrossingL2} (hu :
      u ∈ ccm24LogRadialSupportClosedSubspace lambda)
    {a : ℝ} (ha : 0 < a)
    (hzero : u + cc20GlobalLogTranslation a u = 0) :
    u = 0 := by
  rw [mem_ccm24LogRadialSupportClosedSubspace_iff] at hu
  rw [Lp.ext_iff] at hzero
  have hrel : ∀ᵐ t : ℝ ∂volume, u t + u (t + a) = 0 := by
    filter_upwards
      [hzero,
        Lp.coeFn_add u (cc20GlobalLogTranslation a u),
        cc20GlobalLogTranslation_coeFn a u,
        Lp.coeFn_zero ℂ 2 volume] with t hzeroAt hadd htrans hzeroFn
    rw [hadd] at hzeroAt
    simp only [Pi.add_apply] at hzeroAt
    rw [htrans, hzeroFn] at hzeroAt
    exact hzeroAt
  have hrelShift (n : ℕ) :
      ∀ᵐ x : ℝ ∂volume,
        u (x + (-(n : ℝ) * a)) +
            u ((x + (-(n : ℝ) * a)) + a) = 0 := by
    simpa only using
      ((measurePreserving_add_right volume (-(n : ℝ) * a)).quasiMeasurePreserving.ae
        hrel)
  have hrelAll : ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ,
      u (x + (-(n : ℝ) * a)) +
          u ((x + (-(n : ℝ) * a)) + a) = 0 :=
    ae_all_iff.mpr hrelShift
  have hsuppShift (n : ℕ) :
      ∀ᵐ x : ℝ ∂volume,
        x + (-(n : ℝ) * a) < Real.log lambda →
          u (x + (-(n : ℝ) * a)) = 0 := by
    simpa only using
      ((measurePreserving_add_right volume (-(n : ℝ) * a)).quasiMeasurePreserving.ae
        hu)
  have hsuppAll : ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ,
      x + (-(n : ℝ) * a) < Real.log lambda →
        u (x + (-(n : ℝ) * a)) = 0 :=
    ae_all_iff.mpr hsuppShift
  rw [Lp.ext_iff]
  filter_upwards
    [hrelAll, hsuppAll, Lp.coeFn_zero ℂ 2 volume] with
      x hxrel hxsupp hzeroFn
  obtain ⟨n, hn⟩ := exists_nat_gt ((x - Real.log lambda) / a)
  have hmul : x - Real.log lambda < (n : ℝ) * a := by
    exact (div_lt_iff₀ ha).mp hn
  have hbelow : x + (-(n : ℝ) * a) < Real.log lambda := by
    linarith
  have hprop : ∀ m : ℕ,
      u (x + (-(m : ℝ) * a)) = 0 → u x = 0 := by
    intro m
    induction m with
    | zero =>
        intro hbase
        simpa using hbase
    | succ m ih =>
        intro hbase
        have hsum := hxrel (Nat.succ m)
        have hsum' :
            u (x + (-((m : ℝ) + 1) * a)) +
                u (x + (-(m : ℝ) * a)) = 0 := by
          convert hsum using 1 <;> norm_num [Nat.cast_succ] <;> ring_nf
        have hprev : u (x + (-(m : ℝ) * a)) = 0 := by
          have hbase' : u (x + (-((m : ℝ) + 1) * a)) = 0 := by
            convert hbase using 1 <;> norm_num [Nat.cast_succ] <;> ring_nf
          rw [hbase', zero_add] at hsum'
          exact hsum'
        exact ih hprev
  rw [hzeroFn]
  exact hprop n (hxsupp n hbelow)

/-! ## The actual ambient loss column -/

theorem suffixEulerFrameAmbientLossColumn_eq_zero_imp_oldFrame_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda)
    (hx : suffixEulerFrameAmbientLossColumn lambda p S x = 0) :
    oldSuffixFrame lambda p S x = 0 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one p.property)
  have hcoeff : 0 < ccm24PrimeEulerCoefficient p := by
    unfold ccm24PrimeEulerCoefficient
    exact div_pos zero_lt_one (Real.sqrt_pos.2 hp0)
  have hscale : 0 < primeEulerAmbientLossScale p := by
    unfold primeEulerAmbientLossScale
    exact div_pos (Real.sqrt_pos.2 hcoeff) (by linarith)
  have hscaleC : (primeEulerAmbientLossScale p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hscale.ne'
  have hfactor :
      (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p))
          (oldSuffixFrame lambda p S x) = 0 := by
    change (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p))
        ((suffixEulerFrameSchurStep lambda p S).oldFrame x) = 0
    simpa only [suffixEulerFrameAmbientLossColumn,
      ContinuousLinearMap.comp_apply] using hx
  rw [primeEulerAmbientLossFactor_adjoint_eq] at hfactor
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply] at hfactor
  have hanti :
      oldSuffixFrame lambda p S x +
          cc20GlobalLogTranslation (Real.log p)
            (oldSuffixFrame lambda p S x) = 0 :=
    (smul_eq_zero.mp hfactor).resolve_left hscaleC
  have hframeMem :
      oldSuffixFrame lambda p S x ∈
        (parameterizedSoninClosedSubspace lambda 1 (p :: S) (by norm_num)).toSubmodule := by
    rw [show oldSuffixFrame lambda p S =
        parameterizedSoninPolarFrame lambda 1 (p :: S) (by norm_num) by
      rfl]
    rw [← parameterizedSoninPolarFrame_range lambda 1 (p :: S) (by norm_num)]
    exact ⟨x, rfl⟩
  have hradial :
      oldSuffixFrame lambda p S x ∈
        ccm24LogRadialSupportClosedSubspace lambda :=
    hframeMem.1
  have hpReal : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.property
  have hold := ccm24LogRadialSupport_add_translation_injective
    lambda hradial (Real.log_pos hpReal) hanti
  exact hold

theorem suffixEulerFrameAmbientLossColumn_injective
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    Function.Injective (suffixEulerFrameAmbientLossColumn lambda p S) := by
  intro x y hxy
  have hzero : suffixEulerFrameAmbientLossColumn lambda p S (x - y) = 0 := by
    simpa only [map_sub] using sub_eq_zero.mpr hxy
  have hframe := suffixEulerFrameAmbientLossColumn_eq_zero_imp_oldFrame_eq_zero
    lambda p S (x - y) hzero
  have hnorm : ‖x - y‖ = ‖oldSuffixFrame lambda p S (x - y)‖ := by
    simpa only [oldSuffixFrame] using
      (parameterizedSoninPolarFrame_isometry lambda 1 (p :: S) (by norm_num)
        (x - y)).symm
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [hnorm, hframe, norm_zero]

theorem suffixEulerFrameLeftCoDefect_eq_zero_imp_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0) :
    x = 0 := by
  have hchannels :=
    (suffixEulerFrameLeftCoDefect_eq_zero_iff_channels_eq_zero
      lambda p S x).mp hx
  have hold := suffixEulerFrameAmbientLossColumn_eq_zero_imp_oldFrame_eq_zero
    lambda p S x hchannels.1
  have hnorm : ‖x‖ = ‖oldSuffixFrame lambda p S x‖ := by
    simpa only [oldSuffixFrame] using
      (parameterizedSoninPolarFrame_isometry lambda 1 (p :: S) (by norm_num)
        x).symm
  apply norm_eq_zero.mp
  rw [hnorm, hold, norm_zero]

end CCM24FiniteSCompletedJuliaAmbientLossKernel
end CCM25Concrete
end Source
end ConnesWeilRH
