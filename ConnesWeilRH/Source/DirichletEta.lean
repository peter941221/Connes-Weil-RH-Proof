/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20RHExit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.ZMod

/-!
# Dirichlet eta infrastructure for the CC20 zeta-half boundary

This module introduces the eta series names used by the 05A plan.  The hard
analytic work is intentionally kept in theorem statements that must be proved
from Mathlib/Lean facts before 05A can close.
-/

namespace ConnesWeilRH
namespace Source

open Filter
open Set
open scoped BigOperators
open scoped Topology

/-- The real Dirichlet eta series, indexed from `n = 0`. -/
noncomputable def dirichletEtaReal (x : ℝ) : ℝ :=
  ∑' n : ℕ, ((-1 : ℝ) ^ n) / ((n + 1 : ℝ) ^ x)

/-- The complex Dirichlet eta series, indexed from `n = 0`. -/
noncomputable def dirichletEtaComplex (s : ℂ) : ℂ :=
  ∑' n : ℕ, ((-1 : ℂ) ^ n) / ((n + 1 : ℂ) ^ s)

/-- The real term used in the eta series. -/
noncomputable def dirichletEtaRealTerm (x : ℝ) (n : ℕ) : ℝ :=
  ((-1 : ℝ) ^ n) / ((n + 1 : ℝ) ^ x)

/-- The complex term used in the eta series. -/
noncomputable def dirichletEtaComplexTerm (s : ℂ) (n : ℕ) : ℂ :=
  ((-1 : ℂ) ^ n) / ((n + 1 : ℂ) ^ s)

@[simp] theorem dirichletEtaRealTerm_def (x : ℝ) (n : ℕ) :
    dirichletEtaRealTerm x n =
      ((-1 : ℝ) ^ n) / ((n + 1 : ℝ) ^ x) := by
  rfl

@[simp] theorem dirichletEtaComplexTerm_def (s : ℂ) (n : ℕ) :
    dirichletEtaComplexTerm s n =
      ((-1 : ℂ) ^ n) / ((n + 1 : ℂ) ^ s) := by
  rfl

theorem dirichletEtaReal_eq_tsum (x : ℝ) :
    dirichletEtaReal x = ∑' n : ℕ, dirichletEtaRealTerm x n := by
  rfl

theorem dirichletEtaComplex_eq_tsum (s : ℂ) :
    dirichletEtaComplex s = ∑' n : ℕ, dirichletEtaComplexTerm s n := by
  rfl

theorem riemannZeta_eq_tsum_one_div_nat_add_one_cpow_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s :=
  zeta_eq_tsum_one_div_nat_add_one_cpow hs

theorem analyticOnNhd_riemannZeta_compl_one :
    AnalyticOnNhd ℂ riemannZeta {1}ᶜ :=
  analyticOn_riemannZeta

theorem analyticOnNhd_etaZetaFactorMul_riemannZeta_compl_one :
    AnalyticOnNhd ℂ
      (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
      {1}ᶜ := by
  have htwo : AnalyticOnNhd ℂ (fun _ : ℂ => (2 : ℂ)) {1}ᶜ :=
    analyticOnNhd_const
  have hexponent : AnalyticOnNhd ℂ (fun s : ℂ => (1 : ℂ) - s) {1}ᶜ := by
    simpa using
      (analyticOnNhd_const.sub analyticOnNhd_id :
        AnalyticOnNhd ℂ (fun s : ℂ => (1 : ℂ) - s) {1}ᶜ)
  have hpow : AnalyticOnNhd ℂ (fun s : ℂ => (2 : ℂ) ^ (1 - s)) {1}ᶜ := by
    simpa using
      htwo.cpow hexponent (fun _ _ => Complex.ofNat_mem_slitPlane 2)
  have hfactor :
      AnalyticOnNhd ℂ (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ (1 - s)) {1}ᶜ := by
    simpa using
      (analyticOnNhd_const.sub hpow :
        AnalyticOnNhd ℂ
          (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ (1 - s)) {1}ᶜ)
  simpa using hfactor.mul analyticOn_riemannZeta

theorem two_cpow_one_sub_one :
    (2 : ℂ) ^ (1 - (1 : ℂ)) = 1 := by
  norm_num

theorem etaZetaFactor_eq_zero_at_one :
    ((1 : ℂ) - (2 : ℂ) ^ (1 - (1 : ℂ))) = 0 := by
  norm_num

theorem hasDerivAt_etaZetaFactor_one :
    HasDerivAt (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ (1 - s)) (Complex.log 2) 1 := by
  have hexponent : HasDerivAt (fun s : ℂ => (1 : ℂ) - s) (-1) 1 := by
    simpa using (hasDerivAt_id (1 : ℂ)).const_sub (1 : ℂ)
  have hpow : HasDerivAt (fun s : ℂ => (2 : ℂ) ^ (1 - s)) (-(Complex.log 2)) 1 := by
    have hraw := hexponent.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
    simpa [two_cpow_one_sub_one, mul_assoc] using hraw
  simpa using hpow.const_sub (1 : ℂ)

theorem tendsto_etaZetaFactor_slope_one :
    Tendsto
      (slope (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ (1 - s)) (1 : ℂ))
      (𝓝[≠] (1 : ℂ))
      (𝓝 (Complex.log 2)) :=
  hasDerivAt_etaZetaFactor_one.tendsto_slope

theorem tendsto_etaZetaFactorMul_riemannZeta_nhdsNE_one :
    Tendsto
      (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (Complex.log 2)) := by
  have hprod := tendsto_etaZetaFactor_slope_one.mul riemannZeta_residue_one
  have hprod2 :
      Tendsto
        (fun s : ℂ =>
          slope (fun u : ℂ => (1 : ℂ) - (2 : ℂ) ^ (1 - u)) (1 : ℂ) s *
            ((s - 1) * riemannZeta s))
        (𝓝[≠] (1 : ℂ))
        (𝓝 (Complex.log 2 * 1)) := by
    simpa using hprod
  have hcongr :
      (fun s : ℂ =>
          slope (fun u : ℂ => (1 : ℂ) - (2 : ℂ) ^ (1 - u)) (1 : ℂ) s *
            ((s - 1) * riemannZeta s))
        =ᶠ[𝓝[≠] (1 : ℂ)]
      (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    have hsne : s ≠ (1 : ℂ) := by simpa using hs
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hsne
    have hsub' : -1 + s ≠ 0 := by
      simpa [sub_eq_add_neg, add_comm] using hsub
    rw [slope_fun_def_field]
    rw [etaZetaFactor_eq_zero_at_one]
    field_simp [hsub, hsub']
    ring
  simpa using (hprod2.congr' hcongr)

theorem continuousAt_etaZetaFactorMul_riemannZeta_update_one :
    ContinuousAt
      (Function.update
        (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
        (1 : ℂ)
        (Complex.log 2))
      (1 : ℂ) :=
  continuousAt_update_same.mpr tendsto_etaZetaFactorMul_riemannZeta_nhdsNE_one

theorem analyticAt_etaZetaFactorMul_riemannZeta_update_one :
    AnalyticAt ℂ
      (Function.update
        (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
        (1 : ℂ)
        (Complex.log 2))
      (1 : ℂ) := by
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
    continuousAt_etaZetaFactorMul_riemannZeta_update_one
  filter_upwards [eventually_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ (1 : ℂ) := by simpa using hz
  have hOrig :
      AnalyticAt ℂ
        (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
        z :=
    analyticOnNhd_etaZetaFactorMul_riemannZeta_compl_one z (by simpa using hz)
  have hEq :
      Function.update
          (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
          (1 : ℂ)
          (Complex.log 2)
        =ᶠ[𝓝 z]
      (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
    filter_upwards [isOpen_ne.mem_nhds hz_ne] with y hy
    simp [Function.update_of_ne hy]
  exact hOrig.differentiableAt.congr_of_eventuallyEq hEq

theorem analyticOnNhd_etaZetaFactorMul_riemannZeta_update_univ :
    AnalyticOnNhd ℂ
      (Function.update
        (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
        (1 : ℂ)
        (Complex.log 2))
      (univ : Set ℂ) := by
  intro z _hz
  by_cases hz : z = (1 : ℂ)
  · simpa [hz] using analyticAt_etaZetaFactorMul_riemannZeta_update_one
  · have hOrig :
        AnalyticAt ℂ
          (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
          z :=
      analyticOnNhd_etaZetaFactorMul_riemannZeta_compl_one z (by simpa using hz)
    have hEq :
        (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
          =ᶠ[𝓝 z]
        Function.update
          (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
          (1 : ℂ)
          (Complex.log 2) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with y hy
      simp [Function.update_of_ne hy]
    exact hOrig.congr hEq

/--
The mod-2 periodic coefficient function for the Dirichlet eta continuation.

The `LSeries` API indexes by positive natural numbers.  This coefficient gives
`1` on odd positive indices and `-1` on even positive indices, while its value
at `0 : ZMod 2` is the even coefficient.
-/
noncomputable def etaZModTwoCoeff (j : ZMod 2) : ℂ :=
  if j = 0 then -1 else 1

@[simp] theorem etaZModTwoCoeff_zero :
    etaZModTwoCoeff 0 = -1 := by
  simp [etaZModTwoCoeff]

@[simp] theorem etaZModTwoCoeff_one :
    etaZModTwoCoeff 1 = 1 := by
  norm_num [etaZModTwoCoeff]

theorem etaZModTwoCoeff_sum_eq_zero :
    ∑ j : ZMod 2, etaZModTwoCoeff j = 0 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by rfl]
  norm_num

theorem etaZModTwoCoeff_natCast_of_even
    {n : ℕ} (hn : Even n) :
    etaZModTwoCoeff (n : ZMod 2) = -1 := by
  have h : (n : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr hn
  simp [h]

theorem etaZModTwoCoeff_natCast_of_odd
    {n : ℕ} (hn : Odd n) :
    etaZModTwoCoeff (n : ZMod 2) = 1 := by
  have h : (n : ZMod 2) = 1 :=
    ZMod.natCast_eq_one_iff_odd.mpr hn
  simp [h]

theorem etaZModTwoCoeff_natCast_succ_eq_neg_one_pow
    (n : ℕ) :
    etaZModTwoCoeff ((n + 1 : ℕ) : ZMod 2) =
      ((-1 : ℝ) ^ n : ℂ) := by
  rcases Nat.even_or_odd n with hn | hn
  · have hodd : Odd (n + 1) := hn.add_odd (by decide : Odd 1)
    rw [etaZModTwoCoeff_natCast_of_odd hodd]
    have hp : (-1 : ℝ) ^ n = 1 := Even.neg_one_pow hn
    exact_mod_cast hp.symm
  · have heven : Even (n + 1) := hn.add_odd (by decide : Odd 1)
    rw [etaZModTwoCoeff_natCast_of_even heven]
    have hp : (-1 : ℝ) ^ n = -1 := Odd.neg_one_pow hn
    exact_mod_cast hp.symm

theorem zmodTwo_stdAddChar_one :
    ZMod.stdAddChar (1 : ZMod 2) = (-1 : ℂ) := by
  have hone : ((1 : ℤ) : ZMod 2) = (1 : ZMod 2) := by norm_num
  rw [← hone]
  have h := ZMod.stdAddChar_coe (N := 2) (1 : ℤ)
  rw [h]
  convert Complex.exp_pi_mul_I using 1
  ring_nf

theorem etaZModTwoCoeff_eq_neg_stdAddChar_one
    (j : ZMod 2) :
    etaZModTwoCoeff j = -ZMod.stdAddChar ((1 : ZMod 2) * j) := by
  fin_cases j
  · change etaZModTwoCoeff (0 : ZMod 2) =
      -ZMod.stdAddChar ((1 : ZMod 2) * (0 : ZMod 2))
    rw [etaZModTwoCoeff_zero]
    simp
  · change etaZModTwoCoeff (1 : ZMod 2) =
      -ZMod.stdAddChar ((1 : ZMod 2) * (1 : ZMod 2))
    rw [etaZModTwoCoeff_one]
    change (1 : ℂ) = -ZMod.stdAddChar (1 : ZMod 2)
    rw [zmodTwo_stdAddChar_one]
    norm_num

theorem zmodTwo_toAddCircle_one_ne_zero :
    ZMod.toAddCircle (1 : ZMod 2) ≠ 0 := by
  intro h
  have hone_ne_zero : (1 : ZMod 2) ≠ 0 := by norm_num
  exact hone_ne_zero (ZMod.toAddCircle_eq_zero.mp h)

theorem zmodTwo_toAddCircle_one_neg :
    -ZMod.toAddCircle (1 : ZMod 2) =
      ZMod.toAddCircle (1 : ZMod 2) := by
  rw [← map_neg]
  rw [ZMod.toAddCircle_inj]
  decide

/-- The mod-2 odd-index indicator, represented by the trivial Dirichlet character mod `2`. -/
noncomputable def etaOddIndicator (j : ZMod 2) : ℂ :=
  (1 : DirichletCharacter ℂ 2) j

theorem etaOddIndicator_zero :
    etaOddIndicator 0 = 0 := by
  have hnonunit : ¬ IsUnit (0 : ZMod 2) := not_isUnit_zero
  exact MulChar.map_nonunit (1 : MulChar (ZMod 2) ℂ) hnonunit

theorem etaOddIndicator_one :
    etaOddIndicator 1 = 1 := by
  exact MulChar.one_apply (R' := ℂ) (x := (1 : ZMod 2)) isUnit_one

theorem etaZModTwoCoeff_eq_two_mul_etaOddIndicator_sub_one
    (j : ZMod 2) :
    etaZModTwoCoeff j = 2 * etaOddIndicator j - 1 := by
  fin_cases j
  · change etaZModTwoCoeff (0 : ZMod 2) = 2 * etaOddIndicator (0 : ZMod 2) - 1
    rw [etaOddIndicator_zero]
    norm_num [etaZModTwoCoeff]
  · change etaZModTwoCoeff (1 : ZMod 2) = 2 * etaOddIndicator (1 : ZMod 2) - 1
    rw [etaOddIndicator_one]
    norm_num [etaZModTwoCoeff]

set_option linter.flexible false in
theorem zmodLFunction_etaZModTwoCoeff_eq_linear_etaOddIndicator
    (s : ℂ) :
    ZMod.LFunction etaZModTwoCoeff s =
      2 * ZMod.LFunction etaOddIndicator s -
        ZMod.LFunction (fun _ : ZMod 2 => (1 : ℂ)) s := by
  have hcoeff :
      etaZModTwoCoeff = fun j : ZMod 2 => 2 * etaOddIndicator j - 1 := by
    funext j
    exact etaZModTwoCoeff_eq_two_mul_etaOddIndicator_sub_one j
  simp [ZMod.LFunction, hcoeff, Finset.mul_sum, Finset.sum_sub_distrib, sub_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [← Finset.mul_sum]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring_nf

theorem zmodLFunction_etaOddIndicator_eq_one_sub_two_cpow_neg_mul_riemannZeta
    {s : ℂ} (hs : s ≠ 1) :
    ZMod.LFunction etaOddIndicator s =
      ((1 : ℂ) - (2 : ℂ) ^ (-s)) * riemannZeta s := by
  simpa [etaOddIndicator, DirichletCharacter.LFunctionTrivChar,
    DirichletCharacter.LFunction, Nat.primeFactors, Nat.primeFactorsList_two]
    using (DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
      (N := 2) (s := s) hs)

theorem two_cpow_one_sub_eq_two_mul_cpow_neg
    (s : ℂ) :
    (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
  rw [show (1 : ℂ) - s = (1 : ℂ) + (-s) by ring]
  rw [Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
  rw [Complex.cpow_one]

/--
The analytic Dirichlet eta owner used by the 05A route.

This is not the unordered half-point `tsum`.  It is Mathlib's Hurwitz-zeta
continuation of the mod-2 periodic coefficient function.
-/
noncomputable def dirichletEtaAnalytic (s : ℂ) : ℂ :=
  ZMod.LFunction etaZModTwoCoeff s

theorem differentiable_dirichletEtaAnalytic :
    Differentiable ℂ dirichletEtaAnalytic := by
  simpa [dirichletEtaAnalytic] using
    (ZMod.differentiable_LFunction_of_sum_zero
      (N := 2) etaZModTwoCoeff_sum_eq_zero)

theorem analyticOnNhd_dirichletEtaAnalytic_univ :
    AnalyticOnNhd ℂ dirichletEtaAnalytic (univ : Set ℂ) :=
  differentiable_dirichletEtaAnalytic.differentiableOn.analyticOnNhd isOpen_univ

theorem dirichletEtaAnalytic_eq_LSeries_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    dirichletEtaAnalytic s = LSeries (etaZModTwoCoeff ·) s := by
  simpa [dirichletEtaAnalytic] using
    (ZMod.LFunction_eq_LSeries etaZModTwoCoeff hs)

theorem dirichletEtaAnalytic_eq_neg_expZeta_half
    (s : ℂ) :
    dirichletEtaAnalytic s =
      -HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s := by
  rw [dirichletEtaAnalytic]
  have hcoeff :
      etaZModTwoCoeff =
        fun j : ZMod 2 => -ZMod.stdAddChar ((1 : ZMod 2) * j) := by
    funext j
    exact etaZModTwoCoeff_eq_neg_stdAddChar_one j
  rw [hcoeff]
  have hlin :
      ZMod.LFunction
          (fun j : ZMod 2 => -ZMod.stdAddChar ((1 : ZMod 2) * j))
          s =
        -ZMod.LFunction
          (fun j : ZMod 2 => ZMod.stdAddChar ((1 : ZMod 2) * j))
          s := by
    simp [ZMod.LFunction, Finset.sum_neg_distrib]
  rw [hlin]
  rw [ZMod.LFunction_stdAddChar_eq_expZeta
    (N := 2) (1 : ZMod 2) s (Or.inl (by norm_num))]

theorem differentiable_expZeta_half :
    Differentiable ℂ
      (HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2))) :=
  HurwitzZeta.differentiable_expZeta_of_ne_zero
    zmodTwo_toAddCircle_one_ne_zero

theorem analyticOnNhd_expZeta_half_univ :
    AnalyticOnNhd ℂ
      (HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)))
      (univ : Set ℂ) :=
  differentiable_expZeta_half.differentiableOn.analyticOnNhd isOpen_univ

theorem dirichletEtaAnalytic_half_eq_neg_expZeta_half :
    dirichletEtaAnalytic (1 / 2 : ℂ) =
      -HurwitzZeta.expZeta
        (ZMod.toAddCircle (1 : ZMod 2))
        (1 / 2 : ℂ) := by
  simpa using dirichletEtaAnalytic_eq_neg_expZeta_half (1 / 2 : ℂ)

theorem sinZeta_half_period_eq_zero
    (s : ℂ) :
    HurwitzZeta.sinZeta (ZMod.toAddCircle (1 : ZMod 2)) s = 0 := by
  have hneg := HurwitzZeta.sinZeta_neg (ZMod.toAddCircle (1 : ZMod 2)) s
  rw [zmodTwo_toAddCircle_one_neg] at hneg
  rw [← CharZero.eq_neg_self_iff]
  exact hneg

theorem expZeta_half_period_eq_cosZeta
    (s : ℂ) :
    HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s =
      HurwitzZeta.cosZeta (ZMod.toAddCircle (1 : ZMod 2)) s := by
  simp [HurwitzZeta.expZeta, sinZeta_half_period_eq_zero]

theorem dirichletEtaAnalytic_half_eq_neg_cosZeta_half :
    dirichletEtaAnalytic (1 / 2 : ℂ) =
      -HurwitzZeta.cosZeta
        (ZMod.toAddCircle (1 : ZMod 2))
        (1 / 2 : ℂ) := by
  rw [dirichletEtaAnalytic_half_eq_neg_expZeta_half]
  rw [expZeta_half_period_eq_cosZeta]

theorem exp_real_pi_mul_I_natCast_eq_neg_one_pow (n : ℕ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ)) = (-1 : ℂ) ^ n := by
  rw [show (Real.pi : ℂ) * Complex.I * (n : ℂ) =
      (n : ℂ) * ((Real.pi : ℂ) * Complex.I) by ring]
  rw [Complex.exp_nat_mul]
  rw [Complex.exp_pi_mul_I]

theorem exp_half_period_nat_succ_eq_neg_one_pow_succ (n : ℕ) :
    Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℂ) / 2) *
          ((n + 1 : ℕ) : ℂ)) =
      (-1 : ℂ) ^ (n + 1) := by
  rw [show
      2 * (Real.pi : ℂ) * Complex.I * ((1 : ℂ) / 2) *
          ((n + 1 : ℕ) : ℂ) =
        (Real.pi : ℂ) * Complex.I * ((n + 1 : ℕ) : ℂ) by ring_nf]
  exact exp_real_pi_mul_I_natCast_eq_neg_one_pow (n + 1)

theorem zmodLFunction_const_one_mod_two_eq_riemannZeta_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    ZMod.LFunction (fun _ : ZMod 2 => (1 : ℂ)) s = riemannZeta s := by
  rw [ZMod.LFunction_eq_LSeries (fun _ : ZMod 2 => (1 : ℂ)) hs]
  exact (LSeriesHasSum_one hs).LSeries_eq

theorem dirichletEtaAnalytic_eq_factor_mul_riemannZeta_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    dirichletEtaAnalytic s =
      ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hsne : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  rw [dirichletEtaAnalytic]
  rw [zmodLFunction_etaZModTwoCoeff_eq_linear_etaOddIndicator]
  rw [zmodLFunction_etaOddIndicator_eq_one_sub_two_cpow_neg_mul_riemannZeta hsne]
  rw [zmodLFunction_const_one_mod_two_eq_riemannZeta_of_one_lt_re hs]
  rw [two_cpow_one_sub_eq_two_mul_cpow_neg]
  ring

theorem dirichletEtaAnalytic_eq_etaZetaFactorMul_riemannZeta_update :
    dirichletEtaAnalytic =
      Function.update
        (fun s : ℂ => ((1 : ℂ) - (2 : ℂ) ^ (1 - s)) * riemannZeta s)
        (1 : ℂ)
        (Complex.log 2) := by
  refine
    AnalyticOnNhd.eq_of_eventuallyEq
      analyticOnNhd_dirichletEtaAnalytic_univ
      analyticOnNhd_etaZetaFactorMul_riemannZeta_update_univ
      (z₀ := (2 : ℂ)) ?_
  have hRe :
      {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)
  filter_upwards [hRe] with s hs
  have hsne : s ≠ (1 : ℂ) := by
    intro h
    rw [h] at hs
    norm_num at hs
  simpa [Function.update_of_ne hsne] using
    dirichletEtaAnalytic_eq_factor_mul_riemannZeta_of_one_lt_re (s := s) hs

theorem dirichletEtaAnalytic_half_eq_factor_mul_riemannZeta :
    dirichletEtaAnalytic (1 / 2 : ℂ) =
      ((1 : ℂ) - (2 : ℂ) ^ (1 - (1 / 2 : ℂ))) *
        riemannZeta (1 / 2 : ℂ) := by
  have h :=
    congrFun dirichletEtaAnalytic_eq_etaZetaFactorMul_riemannZeta_update
      (1 / 2 : ℂ)
  have hne : (1 / 2 : ℂ) ≠ (1 : ℂ) := by norm_num
  simpa [Function.update_of_ne hne] using h

/-- The half-point real term for the eta series. -/
noncomputable def etaHalfTerm (n : ℕ) : ℝ :=
  ((n + 1 : ℝ) ^ (1 / 2 : ℝ))⁻¹

theorem etaHalfTerm_eq (n : ℕ) :
    etaHalfTerm n = ((n + 1 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
  rfl

/-- The positive real term used by the ordered eta series at a real exponent. -/
noncomputable def etaSigmaTerm (sigma : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℝ) ^ sigma)⁻¹

theorem etaSigmaTerm_eq (sigma : ℝ) (n : ℕ) :
    etaSigmaTerm sigma n = ((n + 1 : ℝ) ^ sigma)⁻¹ := by
  rfl

theorem etaSigmaTerm_half_eq_etaHalfTerm (n : ℕ) :
    etaSigmaTerm (1 / 2 : ℝ) n = etaHalfTerm n := by
  rfl

theorem lseries_etaZModTwoCoeff_half_term_nat_succ_eq_etaHalfCoeff
    (n : ℕ) :
    LSeries.term (etaZModTwoCoeff ·) (1 / 2 : ℂ) (n + 1) =
      (((-1 : ℝ) ^ n * etaHalfTerm n : ℝ) : ℂ) := by
  rw [LSeries.term_of_ne_zero]
  · rw [etaZModTwoCoeff_natCast_succ_eq_neg_one_pow]
    have hpow :
        ((n + 1 : ℕ) : ℂ) ^ (1 / 2 : ℂ) =
          (((n + 1 : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      simpa using
        (Complex.ofReal_cpow
          (x := (n + 1 : ℝ))
          (by positivity : 0 ≤ (n + 1 : ℝ))
          (1 / 2 : ℝ)).symm
    rw [hpow]
    simp [etaHalfTerm, div_eq_mul_inv]
  · exact Nat.succ_ne_zero n

theorem neg_lseries_cosZeta_half_period_term_nat_succ_eq_etaHalfCoeff
    (n : ℕ) :
    -LSeries.term
        (fun m : ℕ =>
          ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (m : ℝ)) : ℝ) : ℂ))
        (1 / 2 : ℂ)
        (n + 1) =
      (((-1 : ℝ) ^ n * etaHalfTerm n : ℝ) : ℂ) := by
  rw [LSeries.term_of_ne_zero]
  · have hcosR :
        Real.cos (2 * Real.pi * (1 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ)) =
          (-1 : ℝ) ^ (n + 1) := by
      rw [show
          2 * Real.pi * (1 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ) =
            ((n + 1 : ℕ) : ℝ) * Real.pi by
        norm_num
        ring]
      exact Real.cos_nat_mul_pi (n + 1)
    rw [hcosR]
    have hpow :
        ((n + 1 : ℕ) : ℂ) ^ (1 / 2 : ℂ) =
          (((n + 1 : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      simpa using
        (Complex.ofReal_cpow
          (x := (n + 1 : ℝ))
          (by positivity : 0 ≤ (n + 1 : ℝ))
          (1 / 2 : ℝ)).symm
    rw [hpow]
    simp [etaHalfTerm, div_eq_mul_inv, pow_succ]
  · exact Nat.succ_ne_zero n

theorem etaHalfPowerSeries_eq_neg_lseries_cosZeta_half_period_powerSeries
    (x : ℝ) :
    ((∑' n : ℕ, ((-1 : ℝ) ^ n * etaHalfTerm n) * x ^ n : ℝ) : ℂ) =
      ∑' n : ℕ,
        (-LSeries.term
          (fun m : ℕ =>
            ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (m : ℝ)) : ℝ) : ℂ))
          (1 / 2 : ℂ)
          (n + 1)) * (x : ℂ) ^ n := by
  rw [Complex.ofReal_tsum]
  apply (tsum_congr fun n => ?_).symm
  rw [neg_lseries_cosZeta_half_period_term_nat_succ_eq_etaHalfCoeff]
  norm_cast

theorem tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries_of_lseries_term_abel
    (habel :
      Tendsto
        (fun x : ℝ =>
          ∑' n : ℕ,
            (-LSeries.term
              (fun m : ℕ =>
                ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (m : ℝ)) : ℝ) : ℂ))
              (1 / 2 : ℂ)
              (n + 1)) * (x : ℂ) ^ n)
        (𝓝[<] (1 : ℝ))
        (𝓝
          (-HurwitzZeta.cosZeta
            (ZMod.toAddCircle (1 : ZMod 2))
            (1 / 2 : ℂ)))) :
    Tendsto
      (fun x : ℝ =>
        ((∑' n : ℕ, ((-1 : ℝ) ^ n * etaHalfTerm n) * x ^ n : ℝ) : ℂ))
      (𝓝[<] (1 : ℝ))
      (𝓝
        (-HurwitzZeta.cosZeta
          (ZMod.toAddCircle (1 : ZMod 2))
          (1 / 2 : ℂ))) := by
  refine habel.congr' ?_
  filter_upwards with x
  exact (etaHalfPowerSeries_eq_neg_lseries_cosZeta_half_period_powerSeries x).symm

theorem neg_shifted_lseries_cosZeta_half_period_powerSeries_eq_neg_full_div
    (x : ℝ)
    (hx : (x : ℂ) ≠ 0)
    (hs :
      Summable fun m : ℕ =>
        LSeries.term
          (fun k : ℕ =>
            ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ))
          (1 / 2 : ℂ) m * (x : ℂ) ^ m) :
    (∑' n : ℕ,
      (-LSeries.term
        (fun m : ℕ =>
          ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (m : ℝ)) : ℝ) : ℂ))
        (1 / 2 : ℂ)
        (n + 1)) * (x : ℂ) ^ n) =
      -((∑' m : ℕ,
        LSeries.term
          (fun k : ℕ =>
            ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ))
          (1 / 2 : ℂ) m * (x : ℂ) ^ m) / (x : ℂ)) := by
  let coeff : ℕ → ℂ := fun k : ℕ =>
    ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ)
  let a : ℕ → ℂ := fun m : ℕ =>
    LSeries.term coeff (1 / 2 : ℂ) m * (x : ℂ) ^ m
  have hs_a : Summable a := hs
  have hzero : a 0 = 0 := by
    simp [a, LSeries.term_def]
  have hsplit : (∑' m : ℕ, a m) = ∑' n : ℕ, a (n + 1) := by
    rw [hs_a.tsum_eq_zero_add, hzero, zero_add]
  have hshift :
      (∑' n : ℕ, a (n + 1)) =
        (x : ℂ) *
          (∑' n : ℕ,
            LSeries.term coeff (1 / 2 : ℂ) (n + 1) * (x : ℂ) ^ n) := by
    rw [← (show
      Summable
        (fun n : ℕ =>
          LSeries.term coeff (1 / 2 : ℂ) (n + 1) * (x : ℂ) ^ n) from ?_).tsum_mul_left]
    · apply tsum_congr
      intro n
      simp [a, pow_succ, mul_assoc, mul_comm]
    · have htail : Summable fun n : ℕ => a (n + 1) :=
        (summable_nat_add_iff (G := ℂ) 1).mpr hs_a
      rw [show
          (fun n : ℕ => a (n + 1)) =
            fun n : ℕ =>
              (x : ℂ) *
                (LSeries.term coeff (1 / 2 : ℂ) (n + 1) * (x : ℂ) ^ n) by
        funext n
        simp [a, pow_succ, mul_assoc, mul_comm]] at htail
      exact (summable_mul_left_iff hx).mp htail
  have hquot :
      (∑' n : ℕ,
        LSeries.term coeff (1 / 2 : ℂ) (n + 1) * (x : ℂ) ^ n) =
        (∑' m : ℕ, a m) / (x : ℂ) := by
    rw [hsplit, hshift]
    field_simp [hx]
  rw [show
      (∑' n : ℕ,
        (-LSeries.term
          (fun m : ℕ =>
            ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (m : ℝ)) : ℝ) : ℂ))
          (1 / 2 : ℂ)
          (n + 1)) * (x : ℂ) ^ n) =
        -(∑' n : ℕ,
          LSeries.term coeff (1 / 2 : ℂ) (n + 1) * (x : ℂ) ^ n) by
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    simp [coeff, neg_mul]]
  rw [hquot]

theorem norm_lseries_cosZeta_half_period_term_le_one
    (m : ℕ) :
    ‖LSeries.term
      (fun k : ℕ =>
        ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ))
      (1 / 2 : ℂ) m‖ ≤ 1 := by
  let coeff : ℕ → ℂ := fun k : ℕ =>
    ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ)
  change ‖LSeries.term coeff (1 / 2 : ℂ) m‖ ≤ 1
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [LSeries.term_def]
  · rw [LSeries.term_of_ne_zero hm.ne']
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hm]
    have hcoeff : ‖coeff m‖ ≤ 1 := by
      change
        ‖((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (m : ℝ)) : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    have hdenom_nonneg : 0 ≤ (m : ℝ) ^ ((1 / 2 : ℂ).re) :=
      Real.rpow_nonneg (Nat.cast_nonneg m) _
    have hdenom_one : 1 ≤ (m : ℝ) ^ ((1 / 2 : ℂ).re) := by
      have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
      exact Real.one_le_rpow hm1 (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℂ).re)
    calc
      ‖coeff m‖ / (m : ℝ) ^ ((1 / 2 : ℂ).re)
          ≤ 1 / (m : ℝ) ^ ((1 / 2 : ℂ).re) := by
            exact div_le_div_of_nonneg_right hcoeff hdenom_nonneg
      _ ≤ 1 := by
            exact (div_le_one (zero_lt_one.trans_le hdenom_one)).mpr hdenom_one

theorem summable_lseries_cosZeta_half_period_powerSeries_of_norm_lt_one
    (x : ℝ)
    (hx : ‖(x : ℂ)‖ < 1) :
    Summable fun m : ℕ =>
      LSeries.term
        (fun k : ℕ =>
          ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ))
        (1 / 2 : ℂ) m * (x : ℂ) ^ m := by
  let coeff : ℕ → ℂ := fun k : ℕ =>
    ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ)
  change Summable fun m : ℕ =>
    LSeries.term coeff (1 / 2 : ℂ) m * (x : ℂ) ^ m
  refine Summable.of_norm_bounded
    (summable_geometric_of_lt_one (norm_nonneg (x : ℂ)) hx) ?_
  intro m
  rw [norm_mul, norm_pow]
  simpa [one_mul, coeff] using
    mul_le_mul_of_nonneg_right
      (norm_lseries_cosZeta_half_period_term_le_one m)
      (pow_nonneg (norm_nonneg (x : ℂ)) m)

theorem eventually_summable_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt :
    ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ),
      Summable fun m : ℕ =>
        LSeries.term
          (fun k : ℕ =>
            ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ))
          (1 / 2 : ℂ) m * (x : ℂ) ^ m := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with
    x hxlt hxpos
  change x < 1 at hxlt
  change 0 < x at hxpos
  apply summable_lseries_cosZeta_half_period_powerSeries_of_norm_lt_one
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_lt.mpr ⟨by linarith, hxlt⟩

theorem tendsto_neg_shifted_lseries_cosZeta_half_period_abel_of_full_lseries_term_abel
    (hfull :
      Tendsto
        (fun x : ℝ =>
          ∑' m : ℕ,
            LSeries.term
              (fun k : ℕ =>
                ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ))
              (1 / 2 : ℂ) m * (x : ℂ) ^ m)
        (𝓝[<] (1 : ℝ))
        (𝓝
          (HurwitzZeta.cosZeta
            (ZMod.toAddCircle (1 : ZMod 2))
            (1 / 2 : ℂ)))) :
    Tendsto
      (fun x : ℝ =>
        ∑' n : ℕ,
          (-LSeries.term
            (fun m : ℕ =>
              ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (m : ℝ)) : ℝ) : ℂ))
            (1 / 2 : ℂ)
            (n + 1)) * (x : ℂ) ^ n)
      (𝓝[<] (1 : ℝ))
      (𝓝
        (-HurwitzZeta.cosZeta
          (ZMod.toAddCircle (1 : ZMod 2))
          (1 / 2 : ℂ))) := by
  let F : ℝ → ℂ := fun x =>
    ∑' m : ℕ,
      LSeries.term
        (fun k : ℕ =>
          ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ))
        (1 / 2 : ℂ) m * (x : ℂ) ^ m
  have hfullF :
      Tendsto F (𝓝[<] (1 : ℝ))
        (𝓝 (HurwitzZeta.cosZeta
          (ZMod.toAddCircle (1 : ZMod 2)) (1 / 2 : ℂ))) :=
    hfull
  have hx_tend :
      Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    exact (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hinv :
      Tendsto (fun x : ℝ => ((x : ℂ))⁻¹) (𝓝[<] (1 : ℝ)) (𝓝 ((1 : ℂ)⁻¹)) :=
    Filter.Tendsto.inv₀ hx_tend (by norm_num : (1 : ℂ) ≠ 0)
  have hquot :
      Tendsto (fun x : ℝ => -(F x / (x : ℂ))) (𝓝[<] (1 : ℝ))
        (𝓝 (-HurwitzZeta.cosZeta
          (ZMod.toAddCircle (1 : ZMod 2)) (1 / 2 : ℂ))) := by
    simpa [div_eq_mul_inv] using
      Filter.Tendsto.neg (Filter.Tendsto.mul hfullF hinv)
  refine hquot.congr' ?_
  have hnonzero : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), (x : ℂ) ≠ 0 := by
    filter_upwards [show Set.Ioi (0 : ℝ) ∈ 𝓝[<] (1 : ℝ) from
      nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx
    exact_mod_cast ne_of_gt hx
  filter_upwards
    [eventually_summable_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt,
      hnonzero] with x hs hx
  exact
    (neg_shifted_lseries_cosZeta_half_period_powerSeries_eq_neg_full_div
      x hx hs).symm

theorem tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries_of_full_lseries_term_abel
    (hfull :
      Tendsto
        (fun x : ℝ =>
          ∑' m : ℕ,
            LSeries.term
              (fun k : ℕ =>
                ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ))
              (1 / 2 : ℂ) m * (x : ℂ) ^ m)
        (𝓝[<] (1 : ℝ))
        (𝓝
          (HurwitzZeta.cosZeta
            (ZMod.toAddCircle (1 : ZMod 2))
            (1 / 2 : ℂ)))) :
    Tendsto
      (fun x : ℝ =>
        ((∑' n : ℕ, ((-1 : ℝ) ^ n * etaHalfTerm n) * x ^ n : ℝ) : ℂ))
      (𝓝[<] (1 : ℝ))
      (𝓝
        (-HurwitzZeta.cosZeta
          (ZMod.toAddCircle (1 : ZMod 2))
          (1 / 2 : ℂ))) :=
  tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries_of_lseries_term_abel
    (tendsto_neg_shifted_lseries_cosZeta_half_period_abel_of_full_lseries_term_abel
      hfull)

theorem neg_expZeta_half_period_nat_succ_term_eq_etaHalfCoeff (n : ℕ) :
    -Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℂ) / 2) *
          ((n + 1 : ℕ) : ℂ)) /
        (((n + 1 : ℕ) : ℂ) ^ (1 / 2 : ℂ)) =
      (((-1 : ℝ) ^ n * etaHalfTerm n : ℝ) : ℂ) := by
  rw [exp_half_period_nat_succ_eq_neg_one_pow_succ]
  have hpow :
      ((1 + (n : ℂ)) ^ (1 / 2 : ℂ)) =
        (((1 + (n : ℝ)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    simpa using
      (Complex.ofReal_cpow
        (x := (1 + (n : ℝ)))
        (by positivity : 0 ≤ (1 + (n : ℝ)))
        (1 / 2 : ℝ)).symm
  simpa [etaHalfTerm, div_eq_mul_inv, pow_succ, add_comm, add_left_comm, add_assoc] using hpow

/-- Compatibility between the half-point eta series and the named half terms. -/
theorem dirichletEtaReal_half_eq_tsum_etaHalfTerm :
    dirichletEtaReal (1 / 2) =
      ∑' n : ℕ, ((-1 : ℝ) ^ n) * etaHalfTerm n := by
  simp [dirichletEtaReal, etaHalfTerm, div_eq_mul_inv]

theorem etaHalfTerm_nonneg (n : ℕ) :
    0 ≤ etaHalfTerm n := by
  exact inv_nonneg.mpr (Real.rpow_nonneg (by positivity : 0 ≤ (n + 1 : ℝ)) _)

theorem etaHalfTerm_antitone :
    Antitone etaHalfTerm := by
  intro m n hmn
  dsimp [etaHalfTerm]
  apply inv_anti₀
  · exact Real.rpow_pos_of_pos (by positivity : 0 < (m + 1 : ℝ)) _
  · exact
      Real.rpow_le_rpow
        (by positivity : 0 ≤ (m + 1 : ℝ))
        (by exact_mod_cast Nat.succ_le_succ hmn : (m + 1 : ℝ) ≤ n + 1)
        (by norm_num : 0 ≤ (1 / 2 : ℝ))

theorem etaHalfTerm_tendsto_zero :
    Tendsto etaHalfTerm atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  exact
    (((tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp hbase).inv_tendsto_atTop)

theorem etaSigmaTerm_nonneg (sigma : ℝ) (n : ℕ) :
    0 ≤ etaSigmaTerm sigma n := by
  dsimp [etaSigmaTerm]
  positivity

theorem etaSigmaTerm_antitone {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    Antitone (etaSigmaTerm sigma) := by
  intro m n hmn
  dsimp [etaSigmaTerm]
  apply inv_anti₀
  · exact Real.rpow_pos_of_pos (by positivity : 0 < (m + 1 : ℝ)) _
  · exact
      Real.rpow_le_rpow
        (by positivity : 0 ≤ (m + 1 : ℝ))
        (by exact_mod_cast Nat.succ_le_succ hmn : (m + 1 : ℝ) ≤ n + 1)
        hsigma

theorem etaSigmaTerm_tendsto_zero {sigma : ℝ} (hsigma : 0 < sigma) :
    Tendsto (etaSigmaTerm sigma) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  exact (((tendsto_rpow_atTop hsigma).comp hbase).inv_tendsto_atTop)

theorem etaSigmaTerm_alternating_tendsto {sigma : ℝ} (hsigma : 0 < sigma) :
    ∃ l : ℝ,
      Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * etaSigmaTerm sigma i)
        atTop
        (𝓝 l) :=
  (etaSigmaTerm_antitone hsigma.le).tendsto_alternating_series_of_tendsto_zero
    (etaSigmaTerm_tendsto_zero hsigma)

/-- Ordered eta value for real positive exponents, using ordered partial sums. -/
noncomputable def orderedEtaValue (sigma : ℝ) : ℝ :=
  if hsigma : 0 < sigma then
    Classical.choose (etaSigmaTerm_alternating_tendsto hsigma)
  else
    0

theorem orderedEtaValue_tendsto {sigma : ℝ} (hsigma : 0 < sigma) :
    Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * etaSigmaTerm sigma i)
      atTop
      (𝓝 (orderedEtaValue sigma)) := by
  simpa [orderedEtaValue, hsigma] using
    Classical.choose_spec (etaSigmaTerm_alternating_tendsto hsigma)

/-- Ordered eta partial sums at a real exponent. -/
noncomputable def etaSigmaPartialSum (sigma : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * etaSigmaTerm sigma i

theorem etaSigmaPartialSum_eq (sigma : ℝ) (n : ℕ) :
    etaSigmaPartialSum sigma n =
      ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * etaSigmaTerm sigma i := by
  rfl

/-- The adjacent-pair term for the ordered eta series at a real exponent. -/
noncomputable def etaSigmaPairTerm (sigma : ℝ) (n : ℕ) : ℝ :=
  etaSigmaTerm sigma (2 * n) - etaSigmaTerm sigma (2 * n + 1)

theorem etaSigmaPairTerm_nonneg {sigma : ℝ} (hsigma : 0 ≤ sigma) (n : ℕ) :
    0 ≤ etaSigmaPairTerm sigma n := by
  dsimp [etaSigmaPairTerm]
  exact sub_nonneg.mpr
    (etaSigmaTerm_antitone hsigma (by omega : 2 * n ≤ 2 * n + 1))

theorem etaSigmaPairPartialSum_eq_etaSigmaPartialSum_two_mul
    (sigma : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, etaSigmaPairTerm sigma n) =
      etaSigmaPartialSum sigma (2 * N) := by
  induction N with
  | zero => simp [etaSigmaPartialSum]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hpow_even : (-1 : ℝ) ^ (2 * N) = 1 := by
        exact Even.neg_one_pow (even_two.mul_right N)
      have hpow_odd : (-1 : ℝ) ^ (1 + 2 * N) = -1 := by
        rw [show 1 + 2 * N = 2 * N + 1 by omega]
        rw [pow_succ, hpow_even]
        ring
      simp only [etaSigmaPartialSum, etaSigmaPairTerm]
      rw [show 2 * (N + 1) = 2 * N + 2 by omega]
      rw [show 2 * N + 2 = (2 * N + 1) + 1 by omega]
      rw [Finset.sum_range_succ]
      rw [show 2 * N + 1 = (2 * N) + 1 by omega]
      rw [Finset.sum_range_succ]
      simp [hpow_even, hpow_odd, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

theorem tendsto_etaSigmaPairPartialSum {sigma : ℝ} (hsigma : 0 < sigma) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, etaSigmaPairTerm sigma n)
      atTop
      (𝓝 (orderedEtaValue sigma)) := by
  have htwo_atTop : Tendsto (fun N : ℕ => 2 * N) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, ?_⟩
    intro a ha
    omega
  have hordered := orderedEtaValue_tendsto hsigma
  have hsub :
      Tendsto (fun N : ℕ => etaSigmaPartialSum sigma (2 * N)) atTop
        (𝓝 (orderedEtaValue sigma)) := by
    exact hordered.comp htwo_atTop
  refine hsub.congr' ?_
  filter_upwards with N
  exact (etaSigmaPairPartialSum_eq_etaSigmaPartialSum_two_mul sigma N).symm

theorem hasSum_etaSigmaPairTerm {sigma : ℝ} (hsigma : 0 < sigma) :
    HasSum (etaSigmaPairTerm sigma) (orderedEtaValue sigma) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · exact tendsto_etaSigmaPairPartialSum hsigma
  · intro n
    exact etaSigmaPairTerm_nonneg hsigma.le n

theorem orderedEtaValue_eq_tsum_etaSigmaPairTerm {sigma : ℝ} (hsigma : 0 < sigma) :
    orderedEtaValue sigma = ∑' n : ℕ, etaSigmaPairTerm sigma n := by
  exact (hasSum_etaSigmaPairTerm hsigma).tsum_eq.symm

/-- The adjacent-pair eta term with a complex exponent. -/
noncomputable def etaPairTermComplex (s : ℂ) (n : ℕ) : ℂ :=
  ((2 * n + 1 : ℕ) : ℂ) ^ (-s) - ((2 * n + 2 : ℕ) : ℂ) ^ (-s)

theorem norm_nat_cpow_sub_succ_le
    {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B) {z : ℂ}
    (hzre : a ≤ z.re) (hzB : ‖z‖ ≤ B) {m : ℕ} (hm : 0 < m) :
    ‖((m : ℂ) ^ (-z) - ((m + 1 : ℕ) : ℂ) ^ (-z))‖ ≤
      B * (m : ℝ) ^ (-(a + 1)) := by
  by_cases hz : z = 0
  · subst z
    have hmR : 0 ≤ (m : ℝ) := by positivity
    have hpow_nonneg : 0 ≤ (m : ℝ) ^ (-(a + 1)) := Real.rpow_nonneg hmR _
    simpa using mul_nonneg hB hpow_nonneg
  · have hnegz : (-z) ≠ 0 := neg_ne_zero.mpr hz
    let C : ℝ := B * (m : ℝ) ^ (-(a + 1))
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hderiv : ∀ x ∈ Set.Icc (m : ℝ) (m + 1 : ℝ),
        HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-z))
          ((-z) * (x : ℂ) ^ ((-z) - 1))
          (Set.Icc (m : ℝ) (m + 1 : ℝ)) x := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hmR hx.1
      exact (hasDerivAt_ofReal_cpow_const (ne_of_gt hxpos) hnegz).hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Ico (m : ℝ) (m + 1 : ℝ),
        ‖(-z) * (x : ℂ) ^ ((-z) - 1)‖ ≤ C := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hmR hx.1
      have hmx : (m : ℝ) ≤ x := hx.1
      have hm_ge_one : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hre : ((-z) - 1).re ≤ -(a + 1) := by
        rw [Complex.sub_re, Complex.neg_re, Complex.one_re]
        linarith
      have hexp_nonpos : ((-z) - 1).re ≤ 0 := by
        rw [Complex.sub_re, Complex.neg_re, Complex.one_re]
        linarith
      have hpow_xm : x ^ (((-z) - 1).re) ≤ (m : ℝ) ^ (((-z) - 1).re) :=
        Real.rpow_le_rpow_of_nonpos hmR hmx hexp_nonpos
      have hpow_exp : (m : ℝ) ^ (((-z) - 1).re) ≤
          (m : ℝ) ^ (-(a + 1)) :=
        Real.rpow_le_rpow_of_exponent_le hm_ge_one hre
      have hpow : x ^ (((-z) - 1).re) ≤ (m : ℝ) ^ (-(a + 1)) :=
        le_trans hpow_xm hpow_exp
      calc
        ‖(-z) * (x : ℂ) ^ ((-z) - 1)‖
            = ‖z‖ * x ^ (((-z) - 1).re) := by
              rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
        _ ≤ B * (m : ℝ) ^ (-(a + 1)) := by
              exact mul_le_mul hzB hpow (Real.rpow_nonneg hxpos.le _) hB
    have hm1_mem : (m + 1 : ℝ) ∈ Set.Icc (m : ℝ) (m + 1 : ℝ) := by
      constructor <;> linarith
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
      hderiv hbound (m + 1 : ℝ) hm1_mem
    have hsub : ‖((m + 1 : ℝ) : ℂ) ^ (-z) - (m : ℂ) ^ (-z)‖ ≤ C := by
      simpa [C] using hmvt
    simpa [C, norm_sub_rev, Nat.cast_add, Nat.cast_one] using hsub

theorem norm_etaPairTermComplex_le
    {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B) {z : ℂ}
    (hzre : a ≤ z.re) (hzB : ‖z‖ ≤ B) (n : ℕ) :
    ‖etaPairTermComplex z n‖ ≤
      B * (2 * n + 1 : ℝ) ^ (-(a + 1)) := by
  have h :=
    norm_nat_cpow_sub_succ_le ha hB hzre hzB
      (m := 2 * n + 1) (by omega : 0 < 2 * n + 1)
  simpa [etaPairTermComplex, show 2 * n + 1 + 1 = 2 * n + 2 by omega] using h

theorem summable_odd_nat_rpow {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ => (2 * n + 1 : ℝ) ^ (-(a + 1)) := by
  have hp : -(a + 1) < -1 := by linarith
  have hbase : Summable fun n : ℕ => (n : ℝ) ^ (-(a + 1)) :=
    Real.summable_nat_rpow.mpr hp
  have hshift : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(a + 1)) := by
    simpa using
      (summable_nat_add_iff
        (f := fun n : ℕ => (n : ℝ) ^ (-(a + 1))) 1).mpr hbase
  refine Summable.of_nonneg_of_le ?_ ?_ hshift
  · intro n
    exact Real.rpow_nonneg (by positivity) _
  · intro n
    have hbase_le : ((n + 1 : ℕ) : ℝ) ≤ (2 * n + 1 : ℝ) := by
      exact_mod_cast (by omega : n + 1 ≤ 2 * n + 1)
    have hpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hpnonpos : -(a + 1) ≤ 0 := by linarith
    exact Real.rpow_le_rpow_of_nonpos hpos hbase_le hpnonpos

theorem summable_etaPairTermComplex_bound {a B : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ => B * (2 * n + 1 : ℝ) ^ (-(a + 1)) := by
  exact (summable_odd_nat_rpow ha).mul_left B

theorem hasSumUniformlyOn_etaPairTermComplex_of_re_norm_le
    {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B) :
    HasSumUniformlyOn
      (fun n : ℕ => fun z : ℂ => etaPairTermComplex z n)
      (fun z : ℂ => ∑' n : ℕ, etaPairTermComplex z n)
      {z : ℂ | a ≤ z.re ∧ ‖z‖ ≤ B} := by
  refine HasSumUniformlyOn.of_norm_le_summable
    (summable_etaPairTermComplex_bound (a := a) (B := B) ha) ?_
  intro n z hz
  exact norm_etaPairTermComplex_le ha hB hz.1 hz.2 n

theorem summableLocallyUniformlyOn_etaPairTermComplex :
    SummableLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => etaPairTermComplex z n)
      {z : ℂ | 0 < z.re} := by
  refine summableLocallyUniformlyOn_of_of_forall_exists_nhds ?_
  intro z hz
  let a : ℝ := z.re / 2
  let B : ℝ := ‖z‖ + a
  have ha : 0 < a := by
    have hzre0 : 0 < z.re := hz
    dsimp [a]
    linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨Metric.ball z a, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z ha), ?_⟩
  refine (hasSumUniformlyOn_etaPairTermComplex_of_re_norm_le
    (a := a) (B := B) ha hB).mono ?_ |>.summableUniformlyOn
  intro w hw
  have hdist : dist w z < a := by simpa [Metric.mem_ball] using hw
  have hnorm_sub : ‖w - z‖ < a := by simpa [Complex.dist_eq] using hdist
  constructor
  · have hre_abs : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm (w - z)
    have hre_lt : |w.re - z.re| < a := by
      rw [Complex.sub_re] at hre_abs
      exact lt_of_le_of_lt hre_abs hnorm_sub
    have hneg : -a < w.re - z.re := (abs_lt.mp hre_lt).1
    dsimp [a] at hneg ⊢
    linarith
  · have hnorm_le : ‖w‖ ≤ ‖z‖ + ‖z - w‖ := norm_le_norm_add_norm_sub z w
    have hzw : ‖z - w‖ < a := by
      rw [norm_sub_rev]
      exact hnorm_sub
    dsimp [B]
    linarith

theorem isOpen_complex_re_pos : IsOpen {z : ℂ | 0 < z.re} := by
  simpa using
    (isOpen_lt continuous_const Complex.continuous_re :
      IsOpen {z : ℂ | (0 : ℝ) < z.re})

theorem differentiableAt_etaPairTermComplex (n : ℕ) (z : ℂ) :
    DifferentiableAt ℂ (fun s : ℂ => etaPairTermComplex s n) z := by
  dsimp [etaPairTermComplex]
  apply DifferentiableAt.sub
  · exact differentiableAt_id.neg.const_cpow
      (Or.inl (by exact_mod_cast (by omega : 2 * n + 1 ≠ 0) :
        ((2 * n + 1 : ℕ) : ℂ) ≠ 0))
  · exact differentiableAt_id.neg.const_cpow
      (Or.inl (by exact_mod_cast (by omega : 2 * n + 2 ≠ 0) :
        ((2 * n + 2 : ℕ) : ℂ) ≠ 0))

theorem differentiableOn_etaPairTermComplex_tsum :
    DifferentiableOn ℂ
      (fun z : ℂ => ∑' n : ℕ, etaPairTermComplex z n)
      {z : ℂ | 0 < z.re} := by
  exact SummableLocallyUniformlyOn.differentiableOn
    isOpen_complex_re_pos
    summableLocallyUniformlyOn_etaPairTermComplex
    (fun n z _hz => differentiableAt_etaPairTermComplex n z)

theorem analyticOnNhd_etaPairTermComplex_tsum :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∑' n : ℕ, etaPairTermComplex z n)
      {z : ℂ | 0 < z.re} :=
  differentiableOn_etaPairTermComplex_tsum.analyticOnNhd isOpen_complex_re_pos

theorem etaPairTermComplex_ofReal_eq_etaSigmaPairTerm (sigma : ℝ) (n : ℕ) :
    etaPairTermComplex (sigma : ℂ) n = (etaSigmaPairTerm sigma n : ℂ) := by
  have hpow1 :
      (((2 * n + 1 : ℕ) : ℂ) ^ (sigma : ℂ)) =
        (((2 * n + 1 : ℝ) ^ sigma : ℝ) : ℂ) := by
    simpa using
      (Complex.ofReal_cpow
        (x := (2 * n + 1 : ℝ))
        (by positivity : 0 ≤ (2 * n + 1 : ℝ))
        sigma).symm
  have hpow2 :
      (((2 * n + 2 : ℕ) : ℂ) ^ (sigma : ℂ)) =
        (((2 * n + 2 : ℝ) ^ sigma : ℝ) : ℂ) := by
    simpa using
      (Complex.ofReal_cpow
        (x := (2 * n + 2 : ℝ))
        (by positivity : 0 ≤ (2 * n + 2 : ℝ))
        sigma).symm
  simp only [etaPairTermComplex, etaSigmaPairTerm, etaSigmaTerm, Complex.cpow_neg]
  rw [hpow1, hpow2]
  norm_num
  ring_nf

theorem etaPairTermComplex_tsum_ofReal_eq_orderedEtaValue
    {sigma : ℝ} (hsigma : 0 < sigma) :
    (∑' n : ℕ, etaPairTermComplex (sigma : ℂ) n) =
      (orderedEtaValue sigma : ℂ) := by
  rw [orderedEtaValue_eq_tsum_etaSigmaPairTerm hsigma]
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n => etaPairTermComplex_ofReal_eq_etaSigmaPairTerm sigma n

theorem continuousAt_etaSigmaTerm (sigma : ℝ) (n : ℕ) :
    ContinuousAt (fun t : ℝ => etaSigmaTerm t n) sigma := by
  dsimp [etaSigmaTerm]
  have hpow : (n + 1 : ℝ) ^ sigma ≠ 0 := by positivity
  exact (Real.continuousAt_const_rpow
    (by positivity : (n + 1 : ℝ) ≠ 0)).inv₀ hpow

theorem continuous_etaSigmaPartialSum (n : ℕ) :
    Continuous (fun sigma : ℝ => etaSigmaPartialSum sigma n) := by
  dsimp [etaSigmaPartialSum]
  refine continuous_finsetSum _ fun i _ => ?_
  exact continuous_const.mul (by
    dsimp [etaSigmaTerm]
    exact (Real.continuous_const_rpow
      (by positivity : (i + 1 : ℝ) ≠ 0)).inv₀ (fun _ => by positivity))

theorem etaHalfTerm_alternating_tendsto :
    ∃ l : ℝ,
      Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * etaHalfTerm i)
        atTop
        (𝓝 l) :=
  etaHalfTerm_antitone.tendsto_alternating_series_of_tendsto_zero
    etaHalfTerm_tendsto_zero

/-- Ordered partial sums for the conditionally convergent eta series at `1 / 2`. -/
noncomputable def etaHalfPartialSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * etaHalfTerm i

/--
The ordered eta value at the half point.

This is intentionally not defined by `tsum`: the alternating half-point eta
series is only conditionally convergent, while `tsum` over `ℕ` is the unordered
summation API.
-/
noncomputable def dirichletEtaRealHalfOrdered : ℝ :=
  Classical.choose etaHalfTerm_alternating_tendsto

theorem dirichletEtaRealHalfOrdered_tendsto :
    Tendsto etaHalfPartialSum atTop (𝓝 dirichletEtaRealHalfOrdered) := by
  simpa [etaHalfPartialSum, dirichletEtaRealHalfOrdered] using
    Classical.choose_spec etaHalfTerm_alternating_tendsto

theorem etaSigmaPartialSum_half_eq_etaHalfPartialSum (n : ℕ) :
    etaSigmaPartialSum (1 / 2 : ℝ) n = etaHalfPartialSum n := by
  simp [etaSigmaPartialSum, etaHalfPartialSum, etaSigmaTerm, etaHalfTerm]

theorem tendsto_etaSigmaPartialSum_nhdsGT_half (n : ℕ) :
    Tendsto (fun sigma : ℝ => etaSigmaPartialSum sigma n)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 (etaHalfPartialSum n)) := by
  rw [← etaSigmaPartialSum_half_eq_etaHalfPartialSum n]
  exact ((continuous_etaSigmaPartialSum n).tendsto (1 / 2 : ℝ)).mono_left
    nhdsWithin_le_nhds

theorem orderedEtaValue_sub_etaSigmaPartialSum_abs_le
    {sigma : ℝ} (hsigma : 0 < sigma) (n : ℕ) :
    |orderedEtaValue sigma - etaSigmaPartialSum sigma n| ≤
      etaSigmaTerm sigma n := by
  have hlim :
      Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * etaSigmaTerm sigma i)
        atTop
        (𝓝 (orderedEtaValue sigma)) :=
    orderedEtaValue_tendsto hsigma
  have hanti : Antitone (etaSigmaTerm sigma) := etaSigmaTerm_antitone hsigma.le
  have upper := hanti.alternating_series_le_tendsto hlim
  have lower := hanti.tendsto_le_alternating_series hlim
  have hnonneg (n : ℕ) : 0 ≤ etaSigmaTerm sigma n := etaSigmaTerm_nonneg sigma n
  dsimp [etaSigmaPartialSum]
  obtain (h | h) := Nat.even_or_odd n
  · obtain ⟨n, rfl⟩ := even_iff_exists_two_mul.mp h
    specialize upper n
    specialize lower n
    simp only [Finset.sum_range_succ, even_two, Even.mul_right, Even.neg_pow, one_pow,
      one_mul] at lower
    rw [abs_sub_le_iff]
    constructor
    · rwa [sub_le_iff_le_add, add_comm]
    · rw [sub_le_iff_le_add, add_comm]
      exact upper.trans (le_add_of_nonneg_right (hnonneg (2 * n)))
  · obtain ⟨n, rfl⟩ := odd_iff_exists_bit1.mp h
    specialize upper (n + 1)
    specialize lower n
    rw [Nat.mul_add, Finset.sum_range_succ] at upper
    rw [abs_sub_le_iff]
    constructor
    · rw [sub_le_iff_le_add, add_comm]
      exact lower.trans (le_add_of_nonneg_right (hnonneg (2 * n + 1)))
    · simpa [Finset.sum_range_succ, add_comm, pow_add] using upper

theorem orderedEtaValue_half_eq_dirichletEtaRealHalfOrdered :
    orderedEtaValue (1 / 2 : ℝ) = dirichletEtaRealHalfOrdered := by
  have hordered :
      Tendsto etaHalfPartialSum atTop
        (𝓝 (orderedEtaValue (1 / 2 : ℝ))) := by
    convert orderedEtaValue_tendsto (by norm_num : 0 < (1 / 2 : ℝ)) using 1
  exact tendsto_nhds_unique hordered dirichletEtaRealHalfOrdered_tendsto

theorem tendsto_orderedEtaValue_sigma_nhdsGT_half :
    Tendsto (fun sigma : ℝ => orderedEtaValue sigma)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 dirichletEtaRealHalfOrdered) := by
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  rcases eventually_atTop.mp
      (Metric.tendsto_nhds.mp etaHalfTerm_tendsto_zero (ε / 3) hε3) with
    ⟨N, hN⟩
  have hNtail : etaHalfTerm N < ε / 3 := by
    have h := hN N (le_refl N)
    simpa [Real.dist_eq, abs_of_nonneg (etaHalfTerm_nonneg N)] using h
  filter_upwards
    [Metric.tendsto_nhds.mp (tendsto_etaSigmaPartialSum_nhdsGT_half N) (ε / 3) hε3,
      self_mem_nhdsWithin,
      show Set.Ioi (0 : ℝ) ∈ 𝓝[>] (1 / 2 : ℝ) from
        nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with sigma hhead_dist hsgt hspos
  have hspos' : 0 < sigma := hspos
  have hhalf_le_sigma : (1 / 2 : ℝ) ≤ sigma := le_of_lt hsgt
  have htail_sigma_abs :
      |orderedEtaValue sigma - etaSigmaPartialSum sigma N| ≤ etaSigmaTerm sigma N :=
    orderedEtaValue_sub_etaSigmaPartialSum_abs_le hspos' N
  have htail_half_abs :
      |dirichletEtaRealHalfOrdered - etaHalfPartialSum N| ≤ etaHalfTerm N := by
    have h := orderedEtaValue_sub_etaSigmaPartialSum_abs_le
      (by norm_num : 0 < (1 / 2 : ℝ)) N
    rw [orderedEtaValue_half_eq_dirichletEtaRealHalfOrdered,
      etaSigmaPartialSum_half_eq_etaHalfPartialSum,
      etaSigmaTerm_half_eq_etaHalfTerm] at h
    exact h
  have htail_sigma_lt :
      |orderedEtaValue sigma - etaSigmaPartialSum sigma N| < ε / 3 := by
    refine lt_of_le_of_lt htail_sigma_abs ?_
    have hmono : etaSigmaTerm sigma N ≤ etaHalfTerm N := by
      dsimp [etaSigmaTerm, etaHalfTerm]
      have hbase : (1 : ℝ) ≤ N + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
      have hdenom : (N + 1 : ℝ) ^ (1 / 2 : ℝ) ≤ (N + 1 : ℝ) ^ sigma :=
        Real.rpow_le_rpow_of_exponent_le hbase hhalf_le_sigma
      have hpos : 0 < (N + 1 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_pos_of_pos (by positivity : 0 < (N + 1 : ℝ)) (1 / 2 : ℝ)
      simpa [one_div] using one_div_le_one_div_of_le hpos hdenom
    exact lt_of_le_of_lt hmono hNtail
  have htail_half_lt :
      |dirichletEtaRealHalfOrdered - etaHalfPartialSum N| < ε / 3 :=
    lt_of_le_of_lt htail_half_abs hNtail
  have hhead_abs : |etaSigmaPartialSum sigma N - etaHalfPartialSum N| < ε / 3 := by
    simpa [Real.dist_eq] using hhead_dist
  have htri :
      |orderedEtaValue sigma - dirichletEtaRealHalfOrdered| ≤
        |orderedEtaValue sigma - etaSigmaPartialSum sigma N| +
        |etaSigmaPartialSum sigma N - etaHalfPartialSum N| +
        |dirichletEtaRealHalfOrdered - etaHalfPartialSum N| := by
    have h1 :
        |orderedEtaValue sigma - dirichletEtaRealHalfOrdered| ≤
          |orderedEtaValue sigma - etaSigmaPartialSum sigma N| +
          |(etaSigmaPartialSum sigma N - etaHalfPartialSum N) +
            (etaHalfPartialSum N - dirichletEtaRealHalfOrdered)| := by
      calc
        |orderedEtaValue sigma - dirichletEtaRealHalfOrdered|
            = |(orderedEtaValue sigma - etaSigmaPartialSum sigma N) +
                ((etaSigmaPartialSum sigma N - etaHalfPartialSum N) +
                  (etaHalfPartialSum N - dirichletEtaRealHalfOrdered))| := by ring_nf
        _ ≤ |orderedEtaValue sigma - etaSigmaPartialSum sigma N| +
              |(etaSigmaPartialSum sigma N - etaHalfPartialSum N) +
                (etaHalfPartialSum N - dirichletEtaRealHalfOrdered)| := abs_add_le _ _
    have h2 :
        |(etaSigmaPartialSum sigma N - etaHalfPartialSum N) +
          (etaHalfPartialSum N - dirichletEtaRealHalfOrdered)| ≤
        |etaSigmaPartialSum sigma N - etaHalfPartialSum N| +
          |etaHalfPartialSum N - dirichletEtaRealHalfOrdered| :=
      abs_add_le _ _
    calc
      |orderedEtaValue sigma - dirichletEtaRealHalfOrdered|
          ≤ |orderedEtaValue sigma - etaSigmaPartialSum sigma N| +
              |(etaSigmaPartialSum sigma N - etaHalfPartialSum N) +
                (etaHalfPartialSum N - dirichletEtaRealHalfOrdered)| := h1
      _ ≤ |orderedEtaValue sigma - etaSigmaPartialSum sigma N| +
            (|etaSigmaPartialSum sigma N - etaHalfPartialSum N| +
              |etaHalfPartialSum N - dirichletEtaRealHalfOrdered|) := by
              linarith
      _ = |orderedEtaValue sigma - etaSigmaPartialSum sigma N| +
            |etaSigmaPartialSum sigma N - etaHalfPartialSum N| +
            |dirichletEtaRealHalfOrdered - etaHalfPartialSum N| := by
              rw [abs_sub_comm (etaHalfPartialSum N) dirichletEtaRealHalfOrdered]
              ring
  have hsum :
      |orderedEtaValue sigma - dirichletEtaRealHalfOrdered| < ε := by
    calc
      |orderedEtaValue sigma - dirichletEtaRealHalfOrdered|
          ≤ |orderedEtaValue sigma - etaSigmaPartialSum sigma N| +
            |etaSigmaPartialSum sigma N - etaHalfPartialSum N| +
            |dirichletEtaRealHalfOrdered - etaHalfPartialSum N| := htri
      _ < ε / 3 + ε / 3 + ε / 3 := by linarith
      _ = ε := by ring
  simpa [Real.dist_eq] using hsum

theorem orderedEtaValue_eq_tsum_of_summable
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hsum : Summable fun n : ℕ => (-1 : ℝ) ^ n * etaSigmaTerm sigma n) :
    orderedEtaValue sigma =
      ∑' n : ℕ, (-1 : ℝ) ^ n * etaSigmaTerm sigma n := by
  have hordered := orderedEtaValue_tendsto hsigma
  have htsum :
      Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * etaSigmaTerm sigma i)
        atTop
        (𝓝 (∑' n : ℕ, (-1 : ℝ) ^ n * etaSigmaTerm sigma n)) := by
    exact hsum.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hordered htsum

theorem summable_etaSigmaCoeff_of_one_lt
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable fun n : ℕ => (-1 : ℝ) ^ n * etaSigmaTerm sigma n := by
  have hbase : Summable fun n : ℕ => 1 / |(n : ℝ) + 1| ^ sigma :=
    (Real.summable_one_div_nat_add_rpow 1 sigma).2 hsigma
  have hterm : Summable fun n : ℕ => etaSigmaTerm sigma n := by
    refine hbase.congr ?_
    intro n
    simp [etaSigmaTerm, one_div, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
  refine Summable.of_norm_bounded hterm ?_
  intro n
  rw [Real.norm_eq_abs]
  calc
    |(-1 : ℝ) ^ n * etaSigmaTerm sigma n| = etaSigmaTerm sigma n := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (etaSigmaTerm_nonneg sigma n)]
    _ ≤ etaSigmaTerm sigma n := le_rfl

theorem lseries_etaZModTwoCoeff_ofReal_term_nat_succ_eq_etaSigmaCoeff
    (sigma : ℝ) (n : ℕ) :
    LSeries.term (etaZModTwoCoeff ·) (sigma : ℂ) (n + 1) =
      ((-1 : ℝ) ^ n * etaSigmaTerm sigma n : ℂ) := by
  have hpow :
      (((n + 1 : ℕ) : ℂ) ^ (sigma : ℂ)) =
        (((n + 1 : ℝ) ^ sigma : ℝ) : ℂ) := by
    simpa using
      (Complex.ofReal_cpow (by positivity : 0 ≤ (n + 1 : ℝ)) sigma).symm
  calc
    LSeries.term (etaZModTwoCoeff ·) (sigma : ℂ) (n + 1)
        = etaZModTwoCoeff ((n + 1 : ℕ) : ZMod 2) /
            (((n + 1 : ℕ) : ℂ) ^ (sigma : ℂ)) := by
          simp
    _ = ((-1 : ℝ) ^ n : ℂ) / (((n + 1 : ℕ) : ℂ) ^ (sigma : ℂ)) := by
          rw [etaZModTwoCoeff_natCast_succ_eq_neg_one_pow]
    _ = ((-1 : ℝ) ^ n : ℂ) * (((n + 1 : ℝ) ^ sigma : ℝ) : ℂ)⁻¹ := by
          rw [div_eq_mul_inv, hpow]
    _ = ((-1 : ℝ) ^ n * etaSigmaTerm sigma n : ℂ) := by
          simp [etaSigmaTerm]

theorem etaZModTwoCoeff_ordered_partialSum_eq_etaSigmaPartialSum
    (sigma : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n,
        LSeries.term (etaZModTwoCoeff ·) (sigma : ℂ) (i + 1)) =
      (etaSigmaPartialSum sigma n : ℂ) := by
  rw [etaSigmaPartialSum_eq]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [lseries_etaZModTwoCoeff_ofReal_term_nat_succ_eq_etaSigmaCoeff]
  simp

theorem tendsto_etaZModTwoCoeff_ordered_partialSum_of_pos
    {sigma : ℝ} (hsigma : 0 < sigma) :
    Tendsto
      (fun n : ℕ =>
        ∑ i ∈ Finset.range n,
          LSeries.term (etaZModTwoCoeff ·) (sigma : ℂ) (i + 1))
      atTop
      (𝓝 (orderedEtaValue sigma : ℂ)) := by
  have hordered :
      Tendsto
        (fun n : ℕ => (etaSigmaPartialSum sigma n : ℂ))
        atTop
        (𝓝 (orderedEtaValue sigma : ℂ)) :=
    (Complex.continuous_ofReal.tendsto (orderedEtaValue sigma)).comp
      (by simpa [etaSigmaPartialSum] using orderedEtaValue_tendsto hsigma)
  refine hordered.congr' ?_
  filter_upwards with n
  exact (etaZModTwoCoeff_ordered_partialSum_eq_etaSigmaPartialSum sigma n).symm

theorem tendsto_etaZModTwoCoeff_half_ordered_partialSum :
    Tendsto
      (fun n : ℕ =>
        ∑ i ∈ Finset.range n,
          LSeries.term (etaZModTwoCoeff ·) (1 / 2 : ℂ) (i + 1))
      atTop
      (𝓝 (dirichletEtaRealHalfOrdered : ℂ)) := by
  have h :=
    tendsto_etaZModTwoCoeff_ordered_partialSum_of_pos
      (by norm_num : 0 < (1 / 2 : ℝ))
  rw [orderedEtaValue_half_eq_dirichletEtaRealHalfOrdered] at h
  simpa using h

theorem dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_one_lt
    {sigma : ℝ} (hsigma : 1 < sigma) :
    dirichletEtaAnalytic (sigma : ℂ) = (orderedEtaValue sigma : ℂ) := by
  have hsre : 1 < (sigma : ℂ).re := by simpa using hsigma
  have hspos : 0 < sigma := lt_trans zero_lt_one hsigma
  have hordered := orderedEtaValue_eq_tsum_of_summable hspos
    (summable_etaSigmaCoeff_of_one_lt hsigma)
  rw [dirichletEtaAnalytic_eq_LSeries_of_one_lt_re hsre]
  have hseries :
      LSeries (etaZModTwoCoeff ·) (sigma : ℂ) =
        ∑' n : ℕ, ((-1 : ℝ) ^ n * etaSigmaTerm sigma n : ℂ) := by
    rw [LSeries]
    have hsumm : Summable (LSeries.term (etaZModTwoCoeff ·) (sigma : ℂ)) :=
      ZMod.LSeriesSummable_of_one_lt_re etaZModTwoCoeff hsre
    rw [hsumm.tsum_eq_zero_add]
    simp only [LSeries.term_zero, zero_add]
    exact tsum_congr fun n =>
      lseries_etaZModTwoCoeff_ofReal_term_nat_succ_eq_etaSigmaCoeff sigma n
  rw [hseries, hordered]
  simpa [Complex.ofReal_mul, Complex.ofReal_pow] using
    (Complex.ofReal_tsum fun n : ℕ => (-1 : ℝ) ^ n * etaSigmaTerm sigma n).symm

theorem etaPairTermComplex_tsum_ofReal_eq_dirichletEtaAnalytic
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' n : ℕ, etaPairTermComplex (sigma : ℂ) n) =
      dirichletEtaAnalytic (sigma : ℂ) := by
  rw [etaPairTermComplex_tsum_ofReal_eq_orderedEtaValue (lt_trans zero_lt_one hsigma)]
  exact (dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_one_lt hsigma).symm

theorem isPreconnected_complex_re_pos : IsPreconnected {z : ℂ | 0 < z.re} := by
  have hlin : IsLinearMap ℝ (fun z : ℂ => z.re) :=
    IsLinearMap.mk (by intro x y; simp [Complex.add_re]) (by intro c z; simp)
  simpa using (convex_halfSpace_gt hlin (0 : ℝ)).isPreconnected

theorem etaPairTermComplex_tsum_eq_dirichletEtaAnalytic_on_re_pos :
    Set.EqOn
      (fun z : ℂ => ∑' n : ℕ, etaPairTermComplex z n)
      dirichletEtaAnalytic
      {z : ℂ | 0 < z.re} := by
  let S : Set ℂ := {z : ℂ | ∃ sigma : ℝ, 1 < sigma ∧ z = (sigma : ℂ)}
  have hclosure : (2 : ℂ) ∈ closure (S \ {(2 : ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((2 + ε / 2 : ℝ) : ℂ), ?_, ?_⟩
    · constructor
      · exact ⟨2 + ε / 2, by linarith, rfl⟩
      · intro hmem
        rw [Set.mem_singleton_iff] at hmem
        have hreal : 2 + ε / 2 = (2 : ℝ) := Complex.ofReal_injective hmem
        linarith
    · rw [dist_eq_norm]
      have hsub : ((2 : ℂ) - ((2 + ε / 2 : ℝ) : ℂ)) =
          ((-(ε / 2) : ℝ) : ℂ) := by
        norm_num
      rw [hsub]
      have hnorm : ‖((-(ε / 2) : ℝ) : ℂ)‖ = |-(ε / 2)| :=
        RCLike.norm_ofReal (K := ℂ) (-(ε / 2))
      rw [hnorm]
      rw [abs_of_nonpos (by linarith : -(ε / 2) ≤ 0)]
      linarith
  have hfreqS : ∃ᶠ z : ℂ in 𝓝[≠] (2 : ℂ), z ∈ S :=
    mem_closure_ne_iff_frequently_within.mp hclosure
  have hfreqEq :
      ∃ᶠ z : ℂ in 𝓝[≠] (2 : ℂ),
        (∑' n : ℕ, etaPairTermComplex z n) = dirichletEtaAnalytic z := by
    exact hfreqS.mono fun z hzS => by
      rcases hzS with ⟨sigma, hsigma, rfl⟩
      exact etaPairTermComplex_tsum_ofReal_eq_dirichletEtaAnalytic hsigma
  exact analyticOnNhd_etaPairTermComplex_tsum.eqOn_of_preconnected_of_frequently_eq
    (analyticOnNhd_dirichletEtaAnalytic_univ.mono (by intro z _hz; trivial))
    isPreconnected_complex_re_pos
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re})
    hfreqEq

theorem dirichletEtaAnalytic_half_eq_ordered :
    dirichletEtaAnalytic (1 / 2 : ℂ) =
      (dirichletEtaRealHalfOrdered : ℂ) := by
  have hpair :
      (∑' n : ℕ, etaPairTermComplex (1 / 2 : ℂ) n) =
        dirichletEtaAnalytic (1 / 2 : ℂ) :=
    etaPairTermComplex_tsum_eq_dirichletEtaAnalytic_on_re_pos
      (by norm_num : (1 / 2 : ℂ) ∈ {z : ℂ | 0 < z.re})
  have hordered :
      (∑' n : ℕ, etaPairTermComplex ((1 / 2 : ℝ) : ℂ) n) =
        (dirichletEtaRealHalfOrdered : ℂ) := by
    rw [etaPairTermComplex_tsum_ofReal_eq_orderedEtaValue
      (by norm_num : 0 < (1 / 2 : ℝ))]
    rw [orderedEtaValue_half_eq_dirichletEtaRealHalfOrdered]
  have horderedC :
      (∑' n : ℕ, etaPairTermComplex (1 / 2 : ℂ) n) =
        (dirichletEtaRealHalfOrdered : ℂ) := by
    simpa using hordered
  exact hpair.symm.trans horderedC

theorem tendsto_etaSigmaPowerSeries_nhdsWithin_lt
    {sigma : ℝ} (hsigma : 0 < sigma) :
    Tendsto
      (fun x : ℝ =>
        ∑' n : ℕ, ((-1 : ℝ) ^ n * etaSigmaTerm sigma n) * x ^ n)
      (𝓝[<] (1 : ℝ))
      (𝓝 (orderedEtaValue sigma)) := by
  exact
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt
      (by simpa [etaSigmaPartialSum] using orderedEtaValue_tendsto hsigma)

theorem tendsto_etaSigmaPowerSeries_complex_nhdsWithin_lt
    {sigma : ℝ} (hsigma : 0 < sigma) :
    Tendsto
      (fun x : ℝ =>
        ((∑' n : ℕ,
          ((-1 : ℝ) ^ n * etaSigmaTerm sigma n) * x ^ n : ℝ) : ℂ))
      (𝓝[<] (1 : ℝ))
      (𝓝 (orderedEtaValue sigma : ℂ)) := by
  exact Complex.continuous_ofReal.tendsto (orderedEtaValue sigma) |>.comp
    (tendsto_etaSigmaPowerSeries_nhdsWithin_lt hsigma)

theorem tendsto_etaHalfPowerSeries_nhdsWithin_lt :
    Tendsto
      (fun x : ℝ => ∑' n : ℕ, ((-1 : ℝ) ^ n * etaHalfTerm n) * x ^ n)
      (𝓝[<] (1 : ℝ))
      (𝓝 dirichletEtaRealHalfOrdered) := by
  exact
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt
      (f := fun n : ℕ => (-1 : ℝ) ^ n * etaHalfTerm n)
      (l := dirichletEtaRealHalfOrdered)
      (by simpa [etaHalfPartialSum] using dirichletEtaRealHalfOrdered_tendsto)

theorem tendsto_etaHalfPowerSeries_complex_nhdsWithin_lt :
    Tendsto
      (fun x : ℝ =>
        ((∑' n : ℕ, ((-1 : ℝ) ^ n * etaHalfTerm n) * x ^ n : ℝ) : ℂ))
      (𝓝[<] (1 : ℝ))
      (𝓝 (dirichletEtaRealHalfOrdered : ℂ)) := by
  exact Complex.continuous_ofReal.tendsto dirichletEtaRealHalfOrdered |>.comp
    tendsto_etaHalfPowerSeries_nhdsWithin_lt

theorem tendsto_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt_ordered :
    Tendsto
      (fun x : ℝ =>
        ∑' m : ℕ,
          LSeries.term
            (fun k : ℕ =>
              ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ))
            (1 / 2 : ℂ) m * (x : ℂ) ^ m)
      (𝓝[<] (1 : ℝ))
      (𝓝 (-(dirichletEtaRealHalfOrdered : ℂ))) := by
  let coeff : ℕ → ℂ := fun k : ℕ =>
    ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ)
  let F : ℝ → ℂ := fun x =>
    ∑' m : ℕ, LSeries.term coeff (1 / 2 : ℂ) m * (x : ℂ) ^ m
  let G : ℝ → ℂ := fun x =>
    ∑' n : ℕ, (-LSeries.term coeff (1 / 2 : ℂ) (n + 1)) * (x : ℂ) ^ n
  have hG :
      Tendsto G (𝓝[<] (1 : ℝ))
        (𝓝 (dirichletEtaRealHalfOrdered : ℂ)) := by
    refine tendsto_etaHalfPowerSeries_complex_nhdsWithin_lt.congr' ?_
    filter_upwards with x
    exact etaHalfPowerSeries_eq_neg_lseries_cosZeta_half_period_powerSeries x
  have hx_tend :
      Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    exact (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have htarget :
      Tendsto (fun x : ℝ => -((x : ℂ) * G x)) (𝓝[<] (1 : ℝ))
        (𝓝 (-(dirichletEtaRealHalfOrdered : ℂ))) := by
    simpa using (hx_tend.mul hG).neg
  refine htarget.congr' ?_
  have hnonzero : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), (x : ℂ) ≠ 0 := by
    filter_upwards [show Set.Ioi (0 : ℝ) ∈ 𝓝[<] (1 : ℝ) from
      nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx
    exact_mod_cast ne_of_gt hx
  filter_upwards
    [eventually_summable_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt,
      hnonzero] with x hs hx
  have hquot :
      G x = -(F x / (x : ℂ)) := by
    simpa [F, G, coeff] using
      neg_shifted_lseries_cosZeta_half_period_powerSeries_eq_neg_full_div
        x hx hs
  have hdiv : F x / (x : ℂ) = -G x := by
    rw [hquot]
    ring
  calc
    -((x : ℂ) * G x) = (x : ℂ) * (F x / (x : ℂ)) := by
      rw [hdiv]
      ring
    _ = F x := by
      field_simp [hx]

theorem cosZeta_half_period_eq_neg_dirichletEtaRealHalfOrdered_of_full_lseries_abel_limit
    (hfull :
      Tendsto
        (fun x : ℝ =>
          ∑' m : ℕ,
            LSeries.term
              (fun k : ℕ =>
                ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ))
              (1 / 2 : ℂ) m * (x : ℂ) ^ m)
        (𝓝[<] (1 : ℝ))
        (𝓝
          (HurwitzZeta.cosZeta
            (ZMod.toAddCircle (1 : ZMod 2))
            (1 / 2 : ℂ)))) :
    HurwitzZeta.cosZeta
        (ZMod.toAddCircle (1 : ZMod 2))
        (1 / 2 : ℂ) =
      -(dirichletEtaRealHalfOrdered : ℂ) :=
  tendsto_nhds_unique hfull
    tendsto_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt_ordered

theorem dirichletEtaAnalytic_half_eq_ordered_of_neg_expZeta_half_period_abel_limit
    (habel :
      Tendsto
        (fun x : ℝ =>
          ((∑' n : ℕ, ((-1 : ℝ) ^ n * etaHalfTerm n) * x ^ n : ℝ) : ℂ))
        (𝓝[<] (1 : ℝ))
        (𝓝
          (-HurwitzZeta.expZeta
            (ZMod.toAddCircle (1 : ZMod 2))
            (1 / 2 : ℂ)))) :
    dirichletEtaAnalytic (1 / 2 : ℂ) =
      (dirichletEtaRealHalfOrdered : ℂ) := by
  have hordered := tendsto_etaHalfPowerSeries_complex_nhdsWithin_lt
  have hlim :
      -HurwitzZeta.expZeta
          (ZMod.toAddCircle (1 : ZMod 2))
          (1 / 2 : ℂ) =
        (dirichletEtaRealHalfOrdered : ℂ) :=
    tendsto_nhds_unique habel hordered
  rw [dirichletEtaAnalytic_half_eq_neg_expZeta_half]
  exact hlim

theorem dirichletEtaAnalytic_half_eq_ordered_of_neg_cosZeta_half_period_abel_limit
    (habel :
      Tendsto
        (fun x : ℝ =>
          ((∑' n : ℕ, ((-1 : ℝ) ^ n * etaHalfTerm n) * x ^ n : ℝ) : ℂ))
        (𝓝[<] (1 : ℝ))
        (𝓝
          (-HurwitzZeta.cosZeta
            (ZMod.toAddCircle (1 : ZMod 2))
            (1 / 2 : ℂ)))) :
    dirichletEtaAnalytic (1 / 2 : ℂ) =
      (dirichletEtaRealHalfOrdered : ℂ) := by
  have hordered := tendsto_etaHalfPowerSeries_complex_nhdsWithin_lt
  have hlim :
      -HurwitzZeta.cosZeta
          (ZMod.toAddCircle (1 : ZMod 2))
          (1 / 2 : ℂ) =
        (dirichletEtaRealHalfOrdered : ℂ) :=
    tendsto_nhds_unique habel hordered
  rw [dirichletEtaAnalytic_half_eq_neg_cosZeta_half]
  exact hlim

theorem dirichletEtaAnalytic_half_eq_ordered_of_full_lseries_cosZeta_half_period_abel_limit
    (hfull :
      Tendsto
        (fun x : ℝ =>
          ∑' m : ℕ,
            LSeries.term
              (fun k : ℕ =>
                ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ))
              (1 / 2 : ℂ) m * (x : ℂ) ^ m)
        (𝓝[<] (1 : ℝ))
        (𝓝
          (HurwitzZeta.cosZeta
            (ZMod.toAddCircle (1 : ZMod 2))
            (1 / 2 : ℂ)))) :
    dirichletEtaAnalytic (1 / 2 : ℂ) =
      (dirichletEtaRealHalfOrdered : ℂ) := by
  rw [dirichletEtaAnalytic_half_eq_neg_cosZeta_half]
  rw [cosZeta_half_period_eq_neg_dirichletEtaRealHalfOrdered_of_full_lseries_abel_limit
    hfull]
  simp

theorem dirichletEtaRealHalfOrdered_eq_factor_mul_riemannZeta_half_of_cosZeta_abel
    (habel :
      Tendsto
        (fun x : ℝ =>
          ((∑' n : ℕ, ((-1 : ℝ) ^ n * etaHalfTerm n) * x ^ n : ℝ) : ℂ))
        (𝓝[<] (1 : ℝ))
        (𝓝
          (-HurwitzZeta.cosZeta
            (ZMod.toAddCircle (1 : ZMod 2))
            (1 / 2 : ℂ)))) :
    (dirichletEtaRealHalfOrdered : ℂ) =
      ((1 : ℂ) - (2 : ℂ) ^ (1 - (1 / 2 : ℂ))) *
        riemannZeta (1 / 2 : ℂ) := by
  rw [← dirichletEtaAnalytic_half_eq_ordered_of_neg_cosZeta_half_period_abel_limit habel]
  exact dirichletEtaAnalytic_half_eq_factor_mul_riemannZeta

theorem etaHalfTerm_one_lt_one :
    etaHalfTerm 1 < 1 := by
  dsimp [etaHalfTerm]
  exact inv_lt_one_of_one_lt₀
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < ((1 : ℕ) : ℝ) + 1)
      (by norm_num : 0 < (1 / 2 : ℝ)))

theorem dirichletEtaRealHalfOrdered_lower_bound :
    1 - etaHalfTerm 1 ≤ dirichletEtaRealHalfOrdered := by
  have hbound :=
    Antitone.alternating_series_le_tendsto
      dirichletEtaRealHalfOrdered_tendsto etaHalfTerm_antitone 1
  have hsum_eq :
      (∑ i ∈ Finset.range (2 * 1), (-1 : ℝ) ^ i * etaHalfTerm i) =
        1 - etaHalfTerm 1 := by
    norm_num [Finset.sum_range_succ, etaHalfTerm, Real.one_rpow]
    ring
  rw [← hsum_eq]
  exact hbound

theorem dirichletEtaRealHalfOrdered_pos :
    0 < dirichletEtaRealHalfOrdered := by
  have hlower := dirichletEtaRealHalfOrdered_lower_bound
  have hpartial_pos : 0 < 1 - etaHalfTerm 1 := by
    linarith [etaHalfTerm_one_lt_one]
  exact lt_of_lt_of_le hpartial_pos hlower

end Source
end ConnesWeilRH
