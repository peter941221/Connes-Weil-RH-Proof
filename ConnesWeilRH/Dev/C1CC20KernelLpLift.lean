/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20LpOperatorNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Lift an L2 kernel to a bounded L2 operator

`C1CC20LpOperatorNorm` proves the Hilbert--Schmidt estimate on raw functions.
The CC20 endpoint machinery, however, consumes bounded operators on the
almost-everywhere quotient `Lp ℂ 2 volume`.  This leaf performs that passage.

For an L2 kernel `k`, it proves that `applyKernel k` preserves a.e. equality
of L2 inputs, is linear on the quotient, and has operator norm at most the L2
norm of `k`.  The key additivity proof uses `integral_add` only on the a.e.
set where the kernel row is L2, so the zero-on-nonintegrable convention of the
Bochner integral is never used as a fake linearity argument.

This is a generic Hilbert--Schmidt construction.  It does not identify a raw
displacement kernel with a square-window owner, construct the finite-rank
operator `T`, or certify the CC20 profile difference.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20KernelLpLift

open MeasureTheory
open C1CC20LpOperator C1CC20LpOperatorNorm

/-- A general Bochner-to-lintegral bridge for squared complex norms. -/
theorem bochner_sq_norm_eq_lintegral_enorm_sq_general
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℂ}
    (hg : Integrable (fun x => ‖g x‖ ^ 2) μ) :
    ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) = ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ := by
  have hnn : 0 ≤ᵐ[μ] fun x => ‖g x‖ ^ 2 := by
    filter_upwards [] with x
    positivity
  rw [ofReal_integral_eq_lintegral_ofReal hg hnn]
  have hpw : (fun x => ENNReal.ofReal (‖g x‖ ^ 2)) =
      fun x => ‖g x‖ₑ ^ (2 : ℝ) := by
    ext x
    simp
  rw [hpw]

/-- The squared norm of an L2 quotient representative is its ordinary squared
norm mass. -/
theorem norm_toLp_sq_eq_integral_norm_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ (2 : ℕ) = ∫ x, ‖f x‖ ^ (2 : ℕ) ∂μ := by
  have hI : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := by
    positivity
  calc
    ‖hf.toLp f‖ ^ (2 : ℕ) = (lpNorm f 2 μ) ^ (2 : ℕ) := by
      rw [Lp.norm_toLp, lpNorm, if_pos hf.aestronglyMeasurable]
    _ = ((∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) := by
      rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by simp)
        hf.aestronglyMeasurable]
      norm_num
    _ = ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := by
      rw [← Real.rpow_natCast ((∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)) 2]
      calc
        _ = (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (((1 : ℝ) / 2) * (2 : ℝ)) :=
          (Real.rpow_mul hI ((1 : ℝ) / 2) (2 : ℝ)).symm
        _ = _ := by norm_num
    _ = ∫ x, ‖f x‖ ^ (2 : ℕ) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.rpow_two, pow_two]

/-- The raw kernel application is a.e. strongly measurable when its kernel
and input are both L2. -/
theorem aestronglyMeasurable_applyKernel
    {k : ℝ × ℝ → ℂ} {f : ℝ → ℂ}
    (hk : MemLp k (ENNReal.ofReal 2))
    (hf : MemLp f (ENNReal.ofReal 2)) :
    AEStronglyMeasurable (applyKernel k f) volume := by
  have hprod : AEStronglyMeasurable (fun p : ℝ × ℝ => k p * f p.2)
      (volume.prod volume) :=
    hk.1.mul (hf.1.comp_snd)
  simpa only [applyKernel] using hprod.integral_prod_right'

/-- The raw kernel application preserves L2 membership. -/
theorem memLp_applyKernel
    {k : ℝ × ℝ → ℂ} {f : ℝ → ℂ}
    (hk : MemLp k (ENNReal.ofReal 2))
    (hf : MemLp f (ENNReal.ofReal 2)) :
    MemLp (applyKernel k f) (ENNReal.ofReal 2) volume := by
  refine ⟨aestronglyMeasurable_applyKernel hk hf, ?_⟩
  have hpz : ENNReal.ofReal 2 ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  have hpt : ENNReal.ofReal 2 ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hpz hpt]
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
  have hkmass : (∫⁻ p : ℝ × ℝ, ‖k p‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hpz hpt).mp hk.2
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] using h
  have hfmass : (∫⁻ x : ℝ, ‖f x‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hpz hpt).mp hf.2
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] using h
  exact lt_of_le_of_lt (applyKernel_l2_sq_bound hf hk)
    (ENNReal.mul_lt_top hkmass hfmass)

/-- The canonical numeral-2 form of `memLp_applyKernel`, matching the
Hilbert-space instance on `Lp`. -/
theorem memLp_applyKernel_two
    {k : ℝ × ℝ → ℂ} {f : ℝ → ℂ}
    (hk : MemLp k 2) (hf : MemLp f 2) :
    MemLp (applyKernel k f) 2 := by
  simpa using memLp_applyKernel (by simpa using hk) (by simpa using hf)

/-- A.e.-equal inputs give pointwise-equal raw kernel outputs. -/
theorem applyKernel_congr_ae
    {k : ℝ × ℝ → ℂ} {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume] g) :
    applyKernel k f = applyKernel k g := by
  funext x
  unfold applyKernel
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

/-- Additivity of kernel application holds almost everywhere for L2 inputs.
The rowwise `integral_add` step is restricted to the a.e. L2 rows of the
kernel. -/
theorem applyKernel_add_ae
    {k : ℝ × ℝ → ℂ} {f g : ℝ → ℂ}
    (hk : MemLp k (ENNReal.ofReal 2))
    (hf : MemLp f (ENNReal.ofReal 2))
    (hg : MemLp g (ENNReal.ofReal 2)) :
    applyKernel k (fun x => f x + g x) =ᵐ[volume]
      fun x => applyKernel k f x + applyKernel k g x := by
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  letI : ENNReal.HolderConjugate (ENNReal.ofReal 2) (ENNReal.ofReal 2) :=
    hholder.ennrealOfReal
  have hrows := rows_l2_ae_of_kernel_l2 hk
  filter_upwards [hrows] with x hx
  have hfrow : Integrable (fun y : ℝ => k (x, y) * f y) volume := by
    simpa only [Pi.mul_apply] using hx.integrable_mul hf
  have hgrow : Integrable (fun y : ℝ => k (x, y) * g y) volume := by
    simpa only [Pi.mul_apply] using hx.integrable_mul hg
  unfold applyKernel
  rw [← integral_add hfrow hgrow]
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- The numeral-2 form of a.e. additivity, matching `Lp` directly. -/
theorem applyKernel_add_ae_two
    {k : ℝ × ℝ → ℂ} {f g : ℝ → ℂ}
    (hk : MemLp k 2) (hf : MemLp f 2) (hg : MemLp g 2) :
    applyKernel k (fun x => f x + g x) =ᵐ[volume]
      fun x => applyKernel k f x + applyKernel k g x := by
  exact applyKernel_add_ae (by simpa using hk) (by simpa using hf)
    (by simpa using hg)

/-- Scalar multiplication commutes with raw kernel application. -/
theorem applyKernel_smul
    (k : ℝ × ℝ → ℂ) (f : ℝ → ℂ) (z : ℂ) :
    applyKernel k (z • f) = z • applyKernel k f := by
  funext x
  unfold applyKernel
  rw [show (fun y : ℝ => k (x, y) * (z • f) y) =
      fun y => z • (k (x, y) * f y) by
        funext y
        simp only [Pi.smul_apply, smul_eq_mul]
        ring]
  exact integral_smul z _

/-- Adding two `L²` kernels commutes with their raw action on an `L²` input,
almost everywhere.  The rowwise Holder argument is the kernel-side analogue
of `applyKernel_add_ae`: it supplies the two integrability facts before
using `integral_add`, rather than relying on the integral's default value on
nonintegrable functions. -/
theorem applyKernel_kernel_add_ae
    {k l : ℝ × ℝ → ℂ} {f : ℝ → ℂ}
    (hk : MemLp k (ENNReal.ofReal 2))
    (hl : MemLp l (ENNReal.ofReal 2))
    (hf : MemLp f (ENNReal.ofReal 2)) :
    applyKernel (fun p => k p + l p) f =ᵐ[volume]
      fun x => applyKernel k f x + applyKernel l f x := by
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  letI : ENNReal.HolderConjugate (ENNReal.ofReal 2) (ENNReal.ofReal 2) :=
    hholder.ennrealOfReal
  have hkrows := rows_l2_ae_of_kernel_l2 hk
  have hlrows := rows_l2_ae_of_kernel_l2 hl
  filter_upwards [hkrows, hlrows] with x hkx hlx
  have hkint : Integrable (fun y : ℝ => k (x, y) * f y) volume := by
    simpa only [Pi.mul_apply] using hkx.integrable_mul hf
  have hlint : Integrable (fun y : ℝ => l (x, y) * f y) volume := by
    simpa only [Pi.mul_apply] using hlx.integrable_mul hf
  unfold applyKernel
  rw [show (fun y : ℝ => (k (x, y) + l (x, y)) * f y) =
      fun y => k (x, y) * f y + l (x, y) * f y by
        funext y
        ring,
    integral_add hkint hlint]

/-- The linear operator on the L2 quotient induced by an L2 kernel. -/
noncomputable def applyKernelLpLinear
    (k : ℝ × ℝ → ℂ) (hk : MemLp k 2) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun f := (memLp_applyKernel_two hk (Lp.memLp f)).toLp (applyKernel k f)
  map_add' f g := by
    let hf : MemLp (f : ℝ → ℂ) 2 volume := Lp.memLp f
    let hg : MemLp (g : ℝ → ℂ) 2 volume := Lp.memLp g
    let hsum : MemLp ((f + g : Lp ℂ 2 volume) : ℝ → ℂ) 2 volume :=
      Lp.memLp (f + g)
    apply MemLp.toLp_congr
      (memLp_applyKernel_two hk hsum)
      ((memLp_applyKernel_two hk hf).add (memLp_applyKernel_two hk hg))
    have hcoerce := applyKernel_congr_ae (k := k) (Lp.coeFn_add f g)
    rw [hcoerce]
    exact applyKernel_add_ae_two hk hf hg
  map_smul' z f := by
    let hf : MemLp (f : ℝ → ℂ) 2 volume := Lp.memLp f
    let hz : MemLp ((z • f : Lp ℂ 2 volume) : ℝ → ℂ) 2 volume :=
      Lp.memLp (z • f)
    apply MemLp.toLp_congr
      (memLp_applyKernel_two hk hz)
      ((memLp_applyKernel_two hk hf).const_smul z)
    have hcoerce := applyKernel_congr_ae (k := k) (Lp.coeFn_smul z f)
    rw [hcoerce, applyKernel_smul]

/-- The real squared-mass form of the Hilbert--Schmidt estimate. -/
theorem integral_norm_sq_applyKernel_le
    {k : ℝ × ℝ → ℂ} {f : ℝ → ℂ}
    (hk : MemLp k 2) (hf : MemLp f 2) :
    (∫ x, ‖applyKernel k f x‖ ^ 2) ≤
      (∫ p : ℝ × ℝ, ‖k p‖ ^ 2) * (∫ x, ‖f x‖ ^ 2) := by
  have hout : MemLp (applyKernel k f) 2 volume :=
    memLp_applyKernel_two hk hf
  have houtInt : Integrable (fun x => ‖applyKernel k f x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hout.1).mp hout
  have hkInt : Integrable (fun p : ℝ × ℝ => ‖k p‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hk.1).mp hk
  have hfInt : Integrable (fun x => ‖f x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hf.1).mp hf
  have hbound := applyKernel_l2_sq_bound (by simpa using hf) (by simpa using hk)
  have hlin : ENNReal.ofReal (∫ x, ‖applyKernel k f x‖ ^ 2) ≤
      ENNReal.ofReal ((∫ p : ℝ × ℝ, ‖k p‖ ^ 2) * (∫ x, ‖f x‖ ^ 2)) := by
    calc
      ENNReal.ofReal (∫ x, ‖applyKernel k f x‖ ^ 2) =
          ∫⁻ x, ‖applyKernel k f x‖ₑ ^ (2 : ℝ) :=
        bochner_sq_norm_eq_lintegral_enorm_sq_general houtInt
      _ ≤ (∫⁻ p : ℝ × ℝ, ‖k p‖ₑ ^ (2 : ℝ)) *
          (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) := hbound
      _ = ENNReal.ofReal (∫ p : ℝ × ℝ, ‖k p‖ ^ 2) *
          ENNReal.ofReal (∫ x, ‖f x‖ ^ 2) := by
        rw [← bochner_sq_norm_eq_lintegral_enorm_sq_general hkInt,
          ← bochner_sq_norm_eq_lintegral_enorm_sq_general hfInt]
      _ = ENNReal.ofReal ((∫ p : ℝ × ℝ, ‖k p‖ ^ 2) *
          (∫ x, ‖f x‖ ^ 2)) := by
        exact (ENNReal.ofReal_mul (integral_nonneg fun p => sq_nonneg (‖k p‖))).symm
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (integral_nonneg fun p => sq_nonneg (‖k p‖))
      (integral_nonneg fun x => sq_nonneg (‖f x‖)))).mp hlin

/-- The quotient-linear kernel map has norm bounded by the L2 norm of its
kernel representative. -/
theorem norm_applyKernelLpLinear_le
    (k : ℝ × ℝ → ℂ) (hk : MemLp k 2)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖applyKernelLpLinear k hk f‖ ≤ ‖hk.toLp k‖ * ‖f‖ := by
  let hf : MemLp (f : ℝ → ℂ) 2 volume := Lp.memLp f
  let hout : MemLp (applyKernel k f) 2 volume := memLp_applyKernel_two hk hf
  have hmass := integral_norm_sq_applyKernel_le hk hf
  have houtNormSq : ‖applyKernelLpLinear k hk f‖ ^ (2 : ℕ) =
      ∫ x, ‖applyKernel k f x‖ ^ (2 : ℕ) := by
    simpa only [applyKernelLpLinear, hf, hout] using
      norm_toLp_sq_eq_integral_norm_sq hout
  have hkNormSq : ‖hk.toLp k‖ ^ (2 : ℕ) =
      ∫ p : ℝ × ℝ, ‖k p‖ ^ (2 : ℕ) :=
    norm_toLp_sq_eq_integral_norm_sq hk
  have hfNormSq : ‖f‖ ^ (2 : ℕ) = ∫ x, ‖f x‖ ^ (2 : ℕ) := by
    calc
      ‖f‖ ^ (2 : ℕ) = ‖hf.toLp (f : ℝ → ℂ)‖ ^ (2 : ℕ) :=
        congrArg (fun u : Lp ℂ 2 volume => ‖u‖ ^ (2 : ℕ))
          (Lp.toLp_coeFn f hf).symm
      _ = ∫ x, ‖f x‖ ^ (2 : ℕ) := norm_toLp_sq_eq_integral_norm_sq hf
  have hsq : ‖applyKernelLpLinear k hk f‖ ^ (2 : ℕ) ≤
      (‖hk.toLp k‖ * ‖f‖) ^ (2 : ℕ) := by
    calc
      _ = ∫ x, ‖applyKernel k f x‖ ^ (2 : ℕ) := houtNormSq
      _ ≤ (∫ p : ℝ × ℝ, ‖k p‖ ^ (2 : ℕ)) *
          (∫ x, ‖f x‖ ^ (2 : ℕ)) := hmass
      _ = (‖hk.toLp k‖ * ‖f‖) ^ (2 : ℕ) := by
        rw [← hkNormSq, ← hfNormSq]
        ring
  have houtNonneg : 0 ≤ ‖applyKernelLpLinear k hk f‖ := norm_nonneg _
  have hboundNonneg : 0 ≤ ‖hk.toLp k‖ * ‖f‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  exact (sq_le_sq₀ houtNonneg hboundNonneg).mp hsq

/-- The bounded L2 operator induced by an L2 kernel. -/
noncomputable def applyKernelLp
    (k : ℝ × ℝ → ℂ) (hk : MemLp k 2) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  LinearMap.mkContinuous (applyKernelLpLinear k hk) ‖hk.toLp k‖
    (norm_applyKernelLpLinear_le k hk)

/-- The quotient lift is additive in its `L²` kernel.  This is the bridge
needed to read a finite sum of raw Fourier kernels back as the corresponding
finite-rank bounded operator. -/
theorem applyKernelLp_kernel_add
    {k l : ℝ × ℝ → ℂ}
    (hk : MemLp k 2) (hl : MemLp l 2) :
    applyKernelLp (fun p => k p + l p) (hk.add hl) =
      applyKernelLp k hk + applyKernelLp l hl := by
  apply ContinuousLinearMap.ext
  intro f
  let hf : MemLp (f : ℝ → ℂ) 2 volume := Lp.memLp f
  apply MemLp.toLp_congr
    (memLp_applyKernel_two (hk.add hl) hf)
    ((memLp_applyKernel_two hk hf).add (memLp_applyKernel_two hl hf))
  exact applyKernel_kernel_add_ae (by simpa using hk) (by simpa using hl)
    (by simpa using hf)

/-- The quotient lift is homogeneous in its `L²` kernel. -/
theorem applyKernelLp_kernel_smul
    {k : ℝ × ℝ → ℂ} (hk : MemLp k 2) (z : ℂ) :
    applyKernelLp (z • k) (hk.const_smul z) =
      z • applyKernelLp k hk := by
  apply ContinuousLinearMap.ext
  intro f
  let hf : MemLp (f : ℝ → ℂ) 2 volume := Lp.memLp f
  apply MemLp.toLp_congr
    (memLp_applyKernel_two (hk.const_smul z) hf)
    ((memLp_applyKernel_two hk hf).const_smul z)
  change applyKernel (z • k) (f : ℝ → ℂ) =ᵐ[volume]
    z • applyKernel k (f : ℝ → ℂ)
  rw [show z • k = fun p => z * k p by
        rfl]
  filter_upwards with x
  unfold applyKernel
  rw [show (fun y : ℝ => (z * k (x, y)) * (f : ℝ → ℂ) y) =
      fun y => z • (k (x, y) * (f : ℝ → ℂ) y) by
        funext y
        simp only [smul_eq_mul]
        ring,
    integral_smul]
  rfl

/-- The quotient lift preserves kernel subtraction. -/
theorem applyKernelLp_kernel_sub
    {k l : ℝ × ℝ → ℂ}
    (hk : MemLp k 2) (hl : MemLp l 2) :
    applyKernelLp (k - l) (hk.sub hl) =
      applyKernelLp k hk - applyKernelLp l hl := by
  calc
    applyKernelLp (k - l) (hk.sub hl) =
      applyKernelLp k hk +
        applyKernelLp ((-1 : ℂ) • l) (hl.const_smul (-1 : ℂ)) := by
        simpa only [sub_eq_add_neg, neg_one_smul] using
          (applyKernelLp_kernel_add hk (hl.const_smul (-1 : ℂ)))
    _ = applyKernelLp k hk + (-1 : ℂ) • applyKernelLp l hl := by
      rw [applyKernelLp_kernel_smul]
    _ = applyKernelLp k hk - applyKernelLp l hl := by
      simp only [sub_eq_add_neg, neg_smul, one_smul]

/-- The zero `L²` kernel lifts to the zero bounded operator. -/
theorem applyKernelLp_kernel_zero :
    applyKernelLp (fun _ : ℝ × ℝ => (0 : ℂ)) (MemLp.zero) = 0 := by
  simpa using
    (applyKernelLp_kernel_smul
      (k := fun _ : ℝ × ℝ => (0 : ℂ)) (MemLp.zero) 0)

/-- A finite sum of `L²` kernels lifts to the corresponding finite sum of
bounded operators.  The explicit membership proof is retained so future
certificate leaves can use the result without an unproved integrability
shortcut. -/
theorem applyKernelLp_kernel_finsetSum
    {ι : Type*} (s : Finset ι) (k : ι → ℝ × ℝ → ℂ)
    (hk : ∀ i, MemLp (k i) 2) :
    applyKernelLp (∑ i ∈ s, k i)
        (memLp_finsetSum' s fun i _ => hk i) =
      ∑ i ∈ s, applyKernelLp (k i) (hk i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using applyKernelLp_kernel_zero
  | insert a s ha ih =>
      calc
        applyKernelLp (∑ i ∈ insert a s, k i)
            (memLp_finsetSum' (insert a s) fun i _ => hk i) =
          applyKernelLp (k a) (hk a) +
            applyKernelLp (∑ i ∈ s, k i)
              (memLp_finsetSum' s fun i _ => hk i) := by
          simpa only [Finset.sum_insert ha] using
            (applyKernelLp_kernel_add (hk a)
              (memLp_finsetSum' s fun i _ => hk i))
        _ = ∑ i ∈ insert a s, applyKernelLp (k i) (hk i) := by
          rw [ih]
          simp only [Finset.sum_insert ha]

/-- Hilbert--Schmidt control of the induced L2 operator norm. -/
theorem opNorm_applyKernelLp_le
    (k : ℝ × ℝ → ℂ) (hk : MemLp k 2) :
    ‖applyKernelLp k hk‖ ≤ ‖hk.toLp k‖ := by
  refine (applyKernelLp k hk).opNorm_le_bound (norm_nonneg _) ?_
  exact norm_applyKernelLpLinear_le k hk

end C1CC20KernelLpLift
end Source
end ConnesWeilRH
