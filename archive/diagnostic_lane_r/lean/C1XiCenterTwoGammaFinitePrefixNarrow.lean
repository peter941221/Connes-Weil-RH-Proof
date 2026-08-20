/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1XiCenterTwoGammaConstrainedPrefix
import ConnesWeilRH.Dev.C1LaneRNarrowArch
import ConnesWeilRH.Dev.Wall14CoeffBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# C1XiCenterTwoGammaFinitePrefixNarrow - a fixed-prefix narrow-support leaf

This module proves one deliberately restricted producer for the fixed
`N = 21` Gamma_R prefix.  It is not the full prime-free Lane R sign theorem.
The proof uses only the square-support bound, the elementary convolution
mass estimate, and the negative exponential profile outside the support.

The resulting radius is a diagnostic proof brick: it makes the finite-prefix
consumer unconditional on a small support interval while leaving the
finite-rank certificate on the full prime-free interval explicit.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoGammaFinitePrefixNarrow

open MeasureTheory
open Set
open Complex
open C1SameOwnerWeil
open C1XiCenterTwoGamma
open C1XiCenterTwoGammaConstrainedPrefix
open C1LaneRNarrowArch
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open scoped Topology

noncomputable section

private noncomputable def archimedeanCoefficient : Real :=
  Real.log (4 * Real.pi) + Real.eulerMascheroniConstant

private theorem archimedeanCoefficient_lt_eleven_thirds :
    archimedeanCoefficient < (11 / 3 : Real) := by
  have hpi : 4 * Real.pi < (16 : Real) := by
    nlinarith [Real.pi_lt_four]
  have hexp_one : (8 / 3 : Real) < Real.exp 1 := by
    have hnum : (8 / 3 : Real) < (2.7182818283 : Real) := by
      norm_num
    exact hnum.trans Real.exp_one_gt_d9
  have hexp_cube : (8 / 3 : Real) ^ 3 < (Real.exp 1) ^ 3 := by
    exact pow_lt_pow_left₀ hexp_one (by norm_num) (n := 3) (by norm_num)
  have hexp_three : (16 : Real) < Real.exp 3 := by
    calc
      (16 : Real) < (8 / 3 : Real) ^ 3 := by norm_num
      _ < (Real.exp 1) ^ 3 := hexp_cube
      _ = Real.exp 3 := by simpa using (Real.exp_one_pow 3)
  have hlog : Real.log (4 * Real.pi) < (3 : Real) := by
    apply (Real.log_lt_iff_lt_exp (by positivity)).2
    exact lt_trans hpi hexp_three
  have hgamma : Real.eulerMascheroniConstant < (2 / 3 : Real) :=
    Real.eulerMascheroniConstant_lt_two_thirds
  dsimp [archimedeanCoefficient]
  linarith

private theorem laneRPrefixHarmonic_gt_five :
    (5 : Real) <
      ∑ n ∈ Finset.range laneRPrefixLength,
        2 / (2 * (n : Real) + 1) := by
  norm_num [laneRPrefixLength, Finset.sum_range_succ]

private theorem exp_neg_le_one_sub (x : Real) :
    1 - x ≤ Real.exp (-x) := by
  have h := Real.add_one_le_exp (-x)
  linarith

private theorem profile_term_norm_le_four_mass
    (g : CompactLogTest) (n : Nat) {y : Real}
    (hy : 0 ≤ y) :
    ‖gammaRArchProfileTerm g.convolutionSquare n y‖ ≤
      4 * (g.convolutionSquare.test 0).re := by
  let A : Real := (g.convolutionSquare.test 0).re
  have hA : 0 ≤ A := by
    simpa [A] using g.convolutionSquare_zero_re_nonnegative
  have hmassY : ‖g.convolutionSquare.test y‖ ≤ A := by
    simpa [A] using convolutionSquare_norm_le_mass g y
  have hmassNeg : ‖g.convolutionSquare.test (-y)‖ ≤ A := by
    simpa [A] using convolutionSquare_norm_le_mass g (-y)
  have hmassZero : ‖g.convolutionSquare.test 0‖ ≤ A := by
    simpa [A] using convolutionSquare_norm_le_mass g 0
  have hsum : ‖g.convolutionSquare.test y +
      g.convolutionSquare.test (-y)‖ ≤ 2 * A := by
    calc
      ‖g.convolutionSquare.test y + g.convolutionSquare.test (-y)‖ ≤
          ‖g.convolutionSquare.test y‖ +
            ‖g.convolutionSquare.test (-y)‖ := norm_add_le _ _
      _ ≤ A + A := add_le_add hmassY hmassNeg
      _ = 2 * A := by ring
  have hexpFirst :
      ‖Complex.exp (-(((2 * (n : Real) + 1 / 2 : Real) : Complex) *
        (y : Complex)))‖ ≤ 1 := by
    have harg :
        (-(((2 * (n : Real) + 1 / 2 : Real) : Complex) *
          (y : Complex))).re =
          -((2 * (n : Real) + 1 / 2 : Real) * y) := by
      norm_num [Complex.mul_re]
    rw [Complex.norm_exp, harg, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg (by positivity) hy)
  have hexpSecond :
      ‖Complex.exp (-(((2 * (n : Real) + 1 : Real) : Complex) *
        (y : Complex)))‖ ≤ 1 := by
    have harg :
        (-(((2 * (n : Real) + 1 : Real) : Complex) *
          (y : Complex))).re =
          -((2 * (n : Real) + 1 : Real) * y) := by
      norm_num [Complex.mul_re]
    rw [Complex.norm_exp, harg, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg (by positivity) hy)
  have hterm := norm_sub_le
    (Complex.exp (-(((2 * (n : Real) + 1 / 2 : Real) : Complex) *
      (y : Complex))) *
      (g.convolutionSquare.test y + g.convolutionSquare.test (-y)))
    (2 * Complex.exp (-(((2 * (n : Real) + 1 : Real) : Complex) *
      (y : Complex))) * g.convolutionSquare.test 0)
  calc
    ‖gammaRArchProfileTerm g.convolutionSquare n y‖ ≤
        ‖Complex.exp (-(((2 * (n : Real) + 1 / 2 : Real) : Complex) *
          (y : Complex))) *
          (g.convolutionSquare.test y + g.convolutionSquare.test (-y))‖ +
          ‖2 * Complex.exp (-(((2 * (n : Real) + 1 : Real) : Complex) *
            (y : Complex))) * g.convolutionSquare.test 0‖ := by
      unfold gammaRArchProfileTerm
      exact hterm
    _ =
        ‖Complex.exp (-(((2 * (n : Real) + 1 / 2 : Real) : Complex) *
          (y : Complex)))‖ *
            ‖g.convolutionSquare.test y + g.convolutionSquare.test (-y)‖ +
          2 * ‖Complex.exp (-(((2 * (n : Real) + 1 : Real) : Complex) *
            (y : Complex)))‖ * ‖g.convolutionSquare.test 0‖ := by
      rw [norm_mul, norm_mul, norm_mul]
      norm_num
    _ ≤ 1 * (2 * A) + 2 * 1 * A := by
      gcongr
    _ = 4 * A := by ring

private theorem profile_term_re_le_four_mass
    (g : CompactLogTest) (n : Nat) {y : Real} (hy : 0 ≤ y) :
    (gammaRArchProfileTerm g.convolutionSquare n y).re ≤
      4 * (g.convolutionSquare.test 0).re := by
  exact (Complex.re_le_norm _).trans (profile_term_norm_le_four_mass g n hy)

private theorem profile_term_re_eq_support_tail
    (g : CompactLogTest) (R : Real)
    (hsupport : Function.support g.convolutionSquare.test ⊆ Ioo (-R) R)
    (n : Nat) {y : Real} (hyR : R ≤ y) :
    (gammaRArchProfileTerm g.convolutionSquare n y).re =
      -2 * Real.exp (-((2 * (n : Real) + 1) * y)) *
        (g.convolutionSquare.test 0).re := by
  have hyzero : g.convolutionSquare.test y = 0 := by
    by_contra hne
    have hmem := hsupport hne
    exact (not_lt_of_ge hyR) hmem.2
  have hynegzero : g.convolutionSquare.test (-y) = 0 := by
    by_contra hne
    have hmem := hsupport hne
    exact (not_lt_of_ge (neg_le_neg hyR)) hmem.1
  have hzeroim : (g.convolutionSquare.test 0).im = 0 :=
    g.convolutionSquare_zero_im
  have hzero : g.convolutionSquare.test 0 =
      ((g.convolutionSquare.test 0).re : Complex) := by
    apply Complex.ext
    · simp
    · simpa using hzeroim
  unfold gammaRArchProfileTerm
  rw [hyzero, hynegzero]
  simp only [add_zero, zero_add, mul_zero, sub_zero]
  have hexp :
      Complex.exp (-(((2 * (n : Real) + 1 : Real) : Complex) *
        (y : Complex))) =
        (Real.exp (-((2 * (n : Real) + 1) * y)) : Complex) := by
    rw [show -(((2 * (n : Real) + 1 : Real) : Complex) *
        (y : Complex)) =
        ((-((2 * (n : Real) + 1) * y) : Real) : Complex) by
          push_cast
          ring]
    exact (Complex.ofReal_exp_ofReal_re _).symm
  rw [hexp]
  rw [hzero]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.neg_re, Complex.ofReal_neg]
  norm_num
  ring_nf

private noncomputable def narrowPrefixRadius : Real :=
  (1 / 1000 : Real)

private theorem narrowPrefixRadius_pos : 0 < narrowPrefixRadius := by
  norm_num [narrowPrefixRadius]

private theorem narrowPrefixRadius_lt_one : narrowPrefixRadius < 1 := by
  norm_num [narrowPrefixRadius]

private theorem profile_real_integral_eq_near_add_tail
    (g : CompactLogTest) (R : Real) (n : Nat)
    (hRpos : 0 < R) :
    gammaRArchProfileRealIntegral g.convolutionSquare n =
      (∫ y : Real in Ioc (0 : Real) R,
        (gammaRArchProfileTerm g.convolutionSquare n y).re) +
      (∫ y : Real in Ioi R,
        (gammaRArchProfileTerm g.convolutionSquare n y).re) := by
  have hterm : IntegrableOn
      (fun y : Real => (gammaRArchProfileTerm g.convolutionSquare n y).re)
      (Ioi (0 : Real)) :=
    (integrableOn_gammaRArchProfileTerm_public g.convolutionSquare n).re
  have hdisj : Disjoint (Ioc (0 : Real) R) (Ioi R) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    exact (not_lt_of_ge (Set.mem_Ioc.mp hy1).2) (Set.mem_Ioi.mp hy2)
  rw [gammaRArchProfileRealIntegral, ← Set.Ioc_union_Ioi_eq_Ioi hRpos.le]
  exact setIntegral_union hdisj measurableSet_Ioi
    (IntegrableOn.mono_set hterm (fun y hy => (Set.mem_Ioc.mp hy).1))
    (IntegrableOn.mono_set hterm (fun y hy =>
      lt_trans hRpos (Set.mem_Ioi.mp hy)))

private theorem profile_real_integral_near_le
    (g : CompactLogTest) (R : Real) (n : Nat)
    (hRpos : 0 < R) :
    (∫ y : Real in Ioc (0 : Real) R,
      (gammaRArchProfileTerm g.convolutionSquare n y).re) ≤
      4 * (g.convolutionSquare.test 0).re * R := by
  let A : Real := (g.convolutionSquare.test 0).re
  have hA : 0 ≤ A := by
    simpa [A] using g.convolutionSquare_zero_re_nonnegative
  have htermWhole : IntegrableOn
      (fun y : Real => (gammaRArchProfileTerm g.convolutionSquare n y).re)
      (Ioi (0 : Real)) := by
    exact (integrableOn_gammaRArchProfileTerm_public
      g.convolutionSquare n).re
  have hterm : IntegrableOn
      (fun y : Real => (gammaRArchProfileTerm g.convolutionSquare n y).re)
      (Ioc (0 : Real) R) :=
    IntegrableOn.mono_set htermWhole (fun y hy => (Set.mem_Ioc.mp hy).1)
  have hconst : IntegrableOn (fun _ : Real => 4 * A) (Ioc (0 : Real) R) := by
    exact integrableOn_const (by simp [Real.volume_Ioc]) (by finiteness)
  have hmono :
      (∫ y : Real in Ioc (0 : Real) R,
        (gammaRArchProfileTerm g.convolutionSquare n y).re) ≤
      ∫ y : Real in Ioc (0 : Real) R, 4 * A := by
    apply setIntegral_mono_on hterm hconst measurableSet_Ioc
    intro y hy
    simpa [A] using profile_term_re_le_four_mass g n (Set.mem_Ioc.mp hy).1.le
  calc
    (∫ y : Real in Ioc (0 : Real) R,
        (gammaRArchProfileTerm g.convolutionSquare n y).re) ≤
        ∫ y : Real in Ioc (0 : Real) R, 4 * A := hmono
    _ = 4 * A * R := by
      rw [setIntegral_const]
      simp [hRpos.le]
      ring
    _ = 4 * (g.convolutionSquare.test 0).re * R := by rfl
  

end
end C1XiCenterTwoGammaFinitePrefixNarrow
end Source
end ConnesWeilRH
