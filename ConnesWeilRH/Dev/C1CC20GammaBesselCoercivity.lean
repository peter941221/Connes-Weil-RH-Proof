/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20Eq115CoefficientPositivity
import ConnesWeilRH.Dev.C1CC20OperatorGap
import ConnesWeilRH.Dev.C1CC20RootWindowOperator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic.Continuity

/-!
# The (gamma) Bessel-coercivity brick for the concrete eq-(115) operator

This leaf fills the T-side coercivity premise `hT` of the GATE 1 assembly
for every nonnegative scale `lam`.  The observation is elementary but was
hitherto unnoticed in the route design: the equation-(115) BASE frequencies
are exactly the nonzero integers `+-1, ..., +-m`, and the repo's mode
convention `cc20FourierPhase alpha x = exp (2 * pi * I * alpha * x / log 2)`
makes the windowed integer modes an orthonormal SYSTEM once normalized by
`(log 2)^(-1/2)`.  Bessel's inequality over the image set of the
base-frequency map gives

    sum_i ‖⟨unit mode (frequency i), xi⟩‖² ≤ ‖xi‖²,

and since each Fourier projection satisfies
`⟪xi, e_alpha xi⟫ = ‖⟨unit mode alpha, xi⟩‖² ≥ 0`, the PERTURBED summands
of the equation-(119) operator only ADD to the defect form whenever the
coefficients `d_n` are nonnegative.  The result:

    cc20DefectQuadraticForm (cc20FiniteRankOperator (cc20Eq115Data lam)) xi
      ≥ (1 - lam) * ‖xi‖²     (for 0 ≤ lam)

with NO spectral calculus, NO Gershgorin enclosure, and NO dependence on
the endpoint profile chi.  This is the (gamma) payload of GATE 1 in its
admissible elementary form; the sandwich leaf `C1CC20GammaCoercivity`
remains the consumption engine for sharpening the constant `1 - lam`
toward the paper's `epsilon2` budget if a later audit demands it.

Reference: equations (115), (118)-(120) of
<https://arxiv.org/html/2006.13771>; companion records docs/proofs/1046,
docs/proofs/1047.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20GammaBesselCoercivity

open MeasureTheory Set intervalIntegral
open scoped Interval ComplexConjugate InnerProductSpace
open C1CC20FiniteRankApproximation C1CC20RawKernelMass C1CC20Eq115Table
  C1CC20OperatorGap C1CC20Eq115CoefficientPositivity C1CC20RootWindowOperator

noncomputable section

private theorem norm_sq_eq_normSq (z : ℂ) : ‖z‖ ^ 2 = Complex.normSq z := by
  rw [Complex.norm_def, pow_two, Real.mul_self_sqrt (Complex.normSq_nonneg _)]

/-- The root window length `log 2` is nonzero, as a bare inequality usable
by `Continuous.div`. -/
theorem cc20RootLength_ne_zero : cc20RootLength ≠ 0 :=
  cc20RootLength_pos.ne'

/-- The interval integral of one window exponential: Kronecker delta mass. -/
theorem window_exp_integral (n : ℤ) :
    ∫ x in (-cc20RootLength / 2)..(cc20RootLength / 2),
      Complex.exp
        (((2 * Real.pi * (n : ℝ) * x / cc20RootLength : Real) : Complex) * Complex.I) =
      if n = 0 then (cc20RootLength : ℂ) else 0 := by
  have hLc : (cc20RootLength : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr cc20RootLength_pos.ne'
  by_cases hn : n = 0
  · rw [if_pos hn]
    subst hn
    simp only [Int.cast_zero, mul_zero, zero_mul, zero_div, Complex.ofReal_zero,
      Complex.exp_zero]
    rw [intervalIntegral.integral_const, neg_div, sub_neg_eq_add, add_halves,
      Algebra.smul_def, mul_one]
    exact rfl
  · have hc : (2 * Real.pi * (n : ℝ) / cc20RootLength : ℝ) ≠ 0 := by
      refine div_ne_zero ?_ cc20RootLength_pos.ne'
      exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
        (Int.cast_ne_zero.mpr hn)
    have hc0 : ((2 * Real.pi * (n : ℝ) / cc20RootLength : Real) : Complex) * Complex.I ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hc) Complex.I_ne_zero
    set c : ℂ := ((2 * Real.pi * (n : ℝ) / cc20RootLength : Real) : Complex) * Complex.I with hcdef
    have hcexp : ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)))
          (c * Complex.exp (c * (x : ℂ))) x := by
      intro x
      have he : HasDerivAt (fun y : ℂ => Complex.exp (c * y))
          (c * Complex.exp (c * x)) (x : ℂ) := by
        rw [(fun α β => by ring : ∀ α β : ℂ, α * Complex.exp β = Complex.exp β * α)]
        refine (Complex.hasDerivAt_exp (c * x)).comp (x : ℂ) ?_
        simpa using (hasDerivAt_id (x := (x : ℂ))).const_mul c
      exact he.comp_ofReal
    have hF : ∀ x : ℝ,
        HasDerivAt (fun x : ℝ => c⁻¹ * Complex.exp (c * (x : ℂ)))
          (Complex.exp (c * (x : ℂ))) x := by
      intro x
      convert hcexp x |>.const_mul (c⁻¹) using 1
      field_simp
    have hcong :
        (fun x : ℝ => Complex.exp
          (((2 * Real.pi * (n : ℝ) * x / cc20RootLength : Real) : ℂ) * Complex.I)) =
          fun x : ℝ => Complex.exp (c * (x : ℂ)) := by
      funext x
      congr 1
      rw [hcdef]
      push_cast
      ring
    have hcont : Continuous (fun x : ℝ => c * (x : ℂ)) :=
      continuous_const.mul Complex.continuous_ofReal
    have hintg : IntervalIntegrable (fun x : ℝ => Complex.exp (c * (x : ℂ))) volume
        (-cc20RootLength / 2) (cc20RootLength / 2) := by
      apply Continuous.intervalIntegrable
      refine Complex.continuous_exp.comp hcont
    rw [hcong, integral_eq_sub_of_hasDerivAt (fun x _ => hF x) hintg, if_neg hn]
    change c⁻¹ * Complex.exp (c * ((cc20RootLength / 2 : ℝ) : ℂ)) -
        c⁻¹ * Complex.exp (c * ((-(cc20RootLength) / 2 : ℝ) : ℂ)) = 0
    have he1 : c * ((cc20RootLength / 2 : ℝ) : ℂ) = (n : ℂ) * (Real.pi * Complex.I) := by
      rw [hcdef]
      push_cast
      field_simp [hLc]
    have he2 : c * ((-(cc20RootLength) / 2 : ℝ) : ℂ) =
        (n : ℂ) * (Real.pi * Complex.I) - (2 : ℂ) * ((n : ℂ) * (Real.pi * Complex.I)) := by
      rw [hcdef]
      push_cast
      field_simp [hLc]
      ring
    rw [he1, he2, Complex.exp_sub]
    have htwo : Complex.exp ((2 : ℂ) * ((n : ℂ) * (Real.pi * Complex.I))) = 1 := by
      rw [show (2 : ℂ) * ((n : ℂ) * (Real.pi * Complex.I)) =
          (n : ℂ) * (2 * (Real.pi * Complex.I)) by ring,
        Complex.exp_int_mul, ← mul_assoc, Complex.exp_two_pi_mul_I, one_zpow]
    rw [htwo, div_one]
    ring

/-- The pointwise integrand of the Gram entry of two integer modes: the
window indicator of the exponential of the frequency difference. -/
theorem star_cc20WindowFourierModeRaw_mul (m k : ℤ) :
    (fun y : ℝ => star (cc20WindowFourierModeRaw (m : ℝ) y) *
      cc20WindowFourierModeRaw (k : ℝ) y) =
      (cc20Window (cc20RootHalfWidth)).indicator
        (fun y : ℝ => Complex.exp
          (((2 * Real.pi * ((k - m : ℤ) : ℝ) * y / cc20RootLength : Real) : Complex) *
            Complex.I)) := by
  funext y
  by_cases hy : y ∈ cc20Window cc20RootHalfWidth
  · simp only [cc20WindowFourierModeRaw, Set.indicator_of_mem hy]
    rw [star_cc20FourierPhase]
    simp only [cc20FourierPhase]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp only [cc20WindowFourierModeRaw, Set.indicator_of_notMem hy]
    simp

/-- Exact orthogonality of the integer window modes: `⟪v_m, v_k⟫` equals the
window length `log 2` on the diagonal and `0` off it. -/
theorem inner_cc20WindowFourierVector_int_eq (m k : ℤ) :
    inner ℂ (cc20WindowFourierVector (m : ℝ)) (cc20WindowFourierVector (k : ℝ)) =
      if m = k then (cc20RootLength : ℂ) else 0 := by
  have hcongr : (fun y : ℝ => star (cc20WindowFourierModeRaw (m : ℝ) y) *
        ((cc20WindowFourierVector (k : ℝ) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) y) =ᵐ[volume]
      (fun y : ℝ => star (cc20WindowFourierModeRaw (m : ℝ) y) *
        cc20WindowFourierModeRaw (k : ℝ) y) := by
    filter_upwards [coeFn_cc20WindowFourierVector (k : ℝ)] with y hy
    rw [hy]
  rw [← integral_star_cc20WindowFourierModeRaw_mul (m : ℝ)
      (f := cc20WindowFourierVector (k : ℝ)),
    integral_congr_ae hcongr, star_cc20WindowFourierModeRaw_mul m k,
    MeasureTheory.integral_indicator (measurableSet_cc20Window cc20RootHalfWidth),
    cc20Window, cc20RootHalfWidth_eq_half_length, ← neg_div,
    integral_Icc_eq_integral_Ioc, ← integral_of_le
      (by linarith [cc20RootLength_pos] : -cc20RootLength / 2 ≤ cc20RootLength / 2),
    window_exp_integral (k - m)]
  by_cases h : k = m
  · have hkm : k - m = 0 := by omega
    rw [if_pos hkm, if_pos h.symm]
  · have hkm : ¬(k - m = 0) := by omega
    rw [if_neg hkm, if_neg (Ne.symm h)]

/-- The unit-normalized window mode of an arbitrary real frequency. -/
def cc20RealUnitWindowFourierMode (α : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  ((Real.sqrt cc20RootLength : ℝ)⁻¹ : ℂ) • cc20WindowFourierVector α

/-- The unit-normalized window mode of an integer frequency. -/
def cc20UnitWindowFourierMode (m : ℤ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  cc20RealUnitWindowFourierMode (m : ℝ)

theorem cc20Orthonormal_unitWindowFourierMode :
    Orthonormal ℂ cc20UnitWindowFourierMode := by
  rw [orthonormal_iff_ite]
  intro m k
  unfold cc20UnitWindowFourierMode cc20RealUnitWindowFourierMode
  set c : ℂ := ((Real.sqrt cc20RootLength : ℝ)⁻¹ : ℂ) with hcdef
  have hstar : star c * c = ((cc20RootLength⁻¹ : ℝ) : ℂ) := by
    rw [hcdef]
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_inv]
    rw [← mul_inv_rev, ← Complex.ofReal_mul, ← Complex.ofReal_inv,
      (show (Real.sqrt cc20RootLength : ℝ) * Real.sqrt cc20RootLength =
          cc20RootLength from
        Real.mul_self_sqrt cc20RootLength_pos.le)]
  rw [inner_smul_left, inner_smul_right,
    inner_cc20WindowFourierVector_int_eq m k]
  by_cases h : m = k
  · rw [← mul_assoc, starRingEnd_apply, hstar]
    simp only [if_pos h]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ cc20RootLength_ne_zero,
      Complex.ofReal_one]
  · rw [if_neg h, mul_zero, mul_zero, if_neg h]

/-- The quadratic form of one unnormalized Fourier projection is the squared
coefficient of the corresponding unit mode. -/
theorem cc20FourierProjection_inner (α : ℝ)
    (ξ : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ ξ (cc20FourierProjection α ξ) =
      (‖inner ℂ (cc20RealUnitWindowFourierMode α) ξ‖ ^ 2 : ℂ) := by
  have hwstar : ∀ z : ℂ, z * star z = (‖z‖ ^ 2 : ℂ) := by
    intro z
    simp only [Complex.star_def]
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, pow_two,
        ← Complex.ofReal_mul, ← pow_two, norm_sq_eq_normSq]
  have hcn : ‖(starRingEnd ℂ) ((Real.sqrt cc20RootLength : ℝ)⁻¹ : ℂ)‖ ^ 2 =
      (cc20RootLength : ℝ)⁻¹ := by
    rw [Complex.norm_conj, norm_sq_eq_normSq, Complex.normSq_inv,
      Complex.normSq_ofReal, Real.mul_self_sqrt cc20RootLength_pos.le]
  unfold cc20FourierProjection cc20RealUnitWindowFourierMode
  rw [ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply,
    inner_smul_right, inner_smul_right,
    ← inner_conj_symm (x := ξ) (y := cc20WindowFourierVector α),
    starRingEnd_apply, hwstar, inner_smul_left]
  rw [norm_mul, ← Complex.ofReal_pow, ← Complex.ofReal_pow, mul_pow,
    ← Complex.ofReal_mul, hcn]

/-- **The (gamma) Bessel-coercivity brick.**  For any equation-(119)-style
finite-rank data whose base frequencies are an injective integer list and
whose coefficients are nonnegative, the CC20 Lemma-`second` defect form of
the operator is bounded below by `1 - lambda` in the Hilbert norm. -/
theorem cc20DefectQuadraticForm_ge_of_bessel
    {ι : Type*} [Fintype ι]
    (data : CC20FiniteRankData ι)
    (base : ι → ℤ)
    (hbase : ∀ i, data.frequency i = (base i : ℝ))
    (hinj : Function.Injective base)
    (hcoef : ∀ i, 0 ≤ data.coefficient i)
    (hlam : 0 ≤ data.lambda) :
    ∀ ξ : Lp ℂ 2 (volume : Measure ℝ),
      cc20DefectQuadraticForm (cc20FiniteRankOperator data) ξ ≥
        (1 - data.lambda) * ‖ξ‖ ^ 2 := by
  intro ξ
  have hterm : ∀ i : ι,
      inner ℂ ξ (cc20FiniteRankOperatorTerm data i ξ) =
        ((‖inner ℂ (cc20RealUnitWindowFourierMode (data.frequency i)) ξ‖ ^ 2 -
            data.coefficient i *
              ‖inner ℂ (cc20RealUnitWindowFourierMode (data.perturbedFrequency i)) ξ‖ ^ 2) : ℂ) := by
    intro i
    rw [cc20FiniteRankOperatorTerm, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, inner_sub_right, inner_smul_right,
      cc20FourierProjection_inner, cc20FourierProjection_inner]
  have hq : cc20RealQuadraticForm (cc20FiniteRankOperator data) ξ =
      data.lambda * ∑ i : ι,
        (‖inner ℂ (cc20RealUnitWindowFourierMode (data.frequency i)) ξ‖ ^ 2 -
          data.coefficient i *
            ‖inner ℂ (cc20RealUnitWindowFourierMode (data.perturbedFrequency i)) ξ‖ ^ 2) := by
    unfold cc20RealQuadraticForm
    rw [cc20FiniteRankOperator, ContinuousLinearMap.smul_apply,
      inner_smul_right, ContinuousLinearMap.sum_apply, inner_sum]
    simp_rw [hterm, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hfreq : (∑ i : ι,
        ‖inner ℂ (cc20RealUnitWindowFourierMode (data.frequency i)) ξ‖ ^ 2) =
      ∑ i : ι, ‖inner ℂ (cc20UnitWindowFourierMode (base i)) ξ‖ ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [cc20UnitWindowFourierMode, hbase i]
  have hperp : (∑ i : ι, ‖inner ℂ (cc20UnitWindowFourierMode (base i)) ξ‖ ^ 2) ≤
      ‖ξ‖ ^ 2 := by
    have hb := cc20Orthonormal_unitWindowFourierMode.sum_inner_products_le
      (s := Finset.univ.image base) (x := ξ)
    rw [Finset.sum_image (fun i _ j _ hij => hinj hij)] at hb
    exact hb
  have hdrop : (∑ i : ι,
        (‖inner ℂ (cc20RealUnitWindowFourierMode (data.frequency i)) ξ‖ ^ 2 -
          data.coefficient i *
            ‖inner ℂ (cc20RealUnitWindowFourierMode (data.perturbedFrequency i)) ξ‖ ^ 2)) ≤
      ∑ i : ι, ‖inner ℂ (cc20RealUnitWindowFourierMode (data.frequency i)) ξ‖ ^ 2 := by
    refine Finset.sum_le_sum fun i _ => sub_le_self _ ?_
    exact mul_nonneg (hcoef i) (sq_nonneg _)
  have hbound : cc20RealQuadraticForm (cc20FiniteRankOperator data) ξ ≤
      data.lambda * ‖ξ‖ ^ 2 := by
    rw [hq]
    exact mul_le_mul_of_nonneg_left (hdrop.trans (hfreq.trans_le hperp)) hlam
  rw [cc20DefectQuadraticForm_eq_norm_sq_sub_realQuadraticForm]
  linarith

/-! ### Instantiation at the extracted equation-(115) table -/

/-- The base frequency of a paired table index as an integer: `+- (n + 1)`. -/
def cc20Eq115BaseFrequency (i : Fin 1732 × Bool) : ℤ :=
  if i.2 then ((i.1.val : ℤ) + 1) else -((i.1.val : ℤ) + 1)

theorem cc20Eq115BaseFrequency_injective :
    Function.Injective cc20Eq115BaseFrequency := by
  intro a b hab
  obtain ⟨an, ab⟩ := a
  obtain ⟨bn, bb⟩ := b
  cases ab <;> cases bb <;>
    simp [cc20Eq115BaseFrequency] at hab
  · -- (false, false): `-(n+1) = -(m+1)` forces `n = m`.
    have hn : ((an.val : ℤ)) = ((bn.val : ℤ)) := by omega
    refine Prod.ext (Fin.ext ?_) rfl
    exact Int.ofNat_inj.mp hn
  · -- (false, true): negative equals positive, contradiction.
    have hX : (0 : ℤ) < ((an.val : ℤ)) + 1 := Nat.cast_add_one_pos _
    have hY : (0 : ℤ) < ((bn.val : ℤ)) + 1 := Nat.cast_add_one_pos _
    linarith
  · -- (true, false): positive equals negative, contradiction.
    have hX : (0 : ℤ) < ((an.val : ℤ)) + 1 := Nat.cast_add_one_pos _
    have hY : (0 : ℤ) < ((bn.val : ℤ)) + 1 := Nat.cast_add_one_pos _
    linarith
  · -- (true, true): `n+1 = m+1` forces `n = m`.
    have hn : ((an.val : ℤ)) = ((bn.val : ℤ)) := by omega
    refine Prod.ext (Fin.ext ?_) rfl
    exact Int.ofNat_inj.mp hn

theorem cc20Eq115Data_frequency_eq (lam : ℝ) (i : Fin 1732 × Bool) :
    (cc20Eq115Data lam).frequency i = (cc20Eq115BaseFrequency i : ℝ) := by
  obtain ⟨n, b⟩ := i
  cases b <;>
    simp only [cc20Eq115Data, cc20Eq115BaseFrequency,
      reduceIte] <;>
    push_cast <;> ring

/-- **The (gamma) payload at the concrete table:** for every nonnegative
scale, the equation-(119) defect form is coercive with constant `1 - lam`. -/
theorem cc20Eq115DefectBessel_ge (lam : ℝ) (hlam : 0 ≤ lam) :
    ∀ ξ : Lp ℂ 2 (volume : Measure ℝ),
      cc20DefectQuadraticForm (cc20FiniteRankOperator (cc20Eq115Data lam)) ξ ≥
        (1 - lam) * ‖ξ‖ ^ 2 := fun ξ =>
  cc20DefectQuadraticForm_ge_of_bessel (cc20Eq115Data lam)
    cc20Eq115BaseFrequency
    (cc20Eq115Data_frequency_eq lam)
    cc20Eq115BaseFrequency_injective
    (fun i => cc20Eq115Coefficient_nonneg i.1) hlam ξ

/-- **The `hT` premise producer for the GATE 1 flagship.**  At the concrete
eq-(115) operator the flagship's T-side coercivity premise holds with the
linear form `ell = 0` and coefficient `epsilon2 ≤ 1 - lam`, turning the
flagship `cc20Eq115_gate1Residual_nonpositive_of_uniformGrid` into a
theorem whose remaining premises are exactly payloads (alpha), (beta),
(delta) and the gap-data choice. -/
theorem cc20Eq115_gate1hT
    (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (hε : gapData.epsilon2 ≤ 1 - lam) :
    ∀ xi : Lp ℂ 2 (volume : Measure ℝ),
      cc20DefectQuadraticForm (cc20FiniteRankOperator (cc20Eq115Data lam)) xi +
        gapData.a * ((fun _ => (0 : ℝ)) xi) ^ 2 ≥ gapData.epsilon2 * ‖xi‖ ^ 2 := by
  intro xi
  have h₁ := cc20Eq115DefectBessel_ge lam hlam xi
  have h₂ : gapData.epsilon2 * ‖xi‖ ^ 2 ≤ (1 - lam) * ‖xi‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hε (sq_nonneg _)
  have h0 : ((fun _ => (0 : ℝ)) xi) ^ 2 = 0 := by
    simp
  rw [h0, mul_zero, add_zero]
  exact h₂.trans h₁

end

end C1CC20GammaBesselCoercivity
end Source
end ConnesWeilRH
