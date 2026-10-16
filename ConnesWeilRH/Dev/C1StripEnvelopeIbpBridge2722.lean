/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/
import ConnesWeilRH.Dev.C1ExplicitDerivativeLadder
import ConnesWeilRH.Dev.C1CompactSupportLaplaceBounds
import ConnesWeilRH.Dev.C1LaneRD3Root
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Record 2722A: the integration-by-parts bridge for the strip envelopes

The wired row-B contradiction (record 2721) carries three forall-strip
hypotheses `hcontract / hquartic / hquadratic` on `laplaceAt` of generic
`base / correction : CompactLogTest` owners.  This module proves the
mechanism that turns each such quantified strip bound into a consequence
of ONE scalar pin: the order-`k` L1 derivative ladder.

The bridge identity is the committed Laplace-side IBP

    laplaceAt (derivativeShift f 0) s = (0 - s) * laplaceAt f s

iterated `k` times and closed at the top order by the committed compact
support bound `norm_laplaceAt_le_exp_mul_l1Mass`:

    ‖s‖ ^ k * ‖laplaceAt f s‖ ≤ exp (|s.re| * B) * derivOrderL1 k f

for `support f.test ⊆ Icc (-B) B`.  Two corollaries match the exact
statement shape of the wired hypotheses: `wiredStripDecayOfLadderPin`
(the weighted-power form of `hquartic / hquadratic`) and
`wiredContractOfDecayPin` (the threshold form of `hcontract`).

This module proves no numerical fact: the pins `C`, `q` and the ladder
values are hypotheses, tied to the certified record-2720 constants by
the artifact-side checker of the next round.  It removes no wired
hypothesis by itself, and asserts no gate sign, no producer GO, no RH.
-/

namespace ConnesWeilRH
namespace Source
namespace C1StripEnvelopeIbpBridge2722

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaCriticalContraction
open CC20YoshidaCriticalContraction.CompactLogTest
open C1ExplicitFiniteNodeCorrection
open C1LaneRD3Root
open scoped ComplexConjugate

noncomputable section

/-! ## 1. Support and ladder bookkeeping for the zero shift -/

/-- The zero differential shift keeps the support inside the same interval:
the derivative of a compactly supported smooth function vanishes off the
closed support hull. -/
theorem derivativeShiftZero_support_subset (f : CompactLogTest) (B : ℝ)
    (hsupport : Function.support f.test ⊆ Set.Icc (-B) B) :
    Function.support (derivativeShift f 0).test ⊆ Set.Icc (-B) B := by
  have hgf : ((derivativeShift f 0).test : ℝ → ℂ) = deriv (f.test : ℝ → ℂ) := by
    ext x
    simp [derivativeShift_apply]
  have hts : tsupport (f.test : ℝ → ℂ) ⊆ Set.Icc (-B) B := by
    change closure (Function.support (f.test : ℝ → ℂ)) ⊆ Set.Icc (-B) B
    rw [← closure_Icc (-B) B]
    exact closure_mono hsupport
  have hsub : Function.support ((derivativeShift f 0).test : ℝ → ℂ) ⊆
      Function.support (deriv (f.test : ℝ → ℂ)) := by
    rw [hgf]
  calc Function.support (derivativeShift f 0).test
      = Function.support ((derivativeShift f 0).test : ℝ → ℂ) := rfl
      _ ⊆ Function.support (deriv (f.test : ℝ → ℂ)) := hsub
      _ ⊆ tsupport (f.test : ℝ → ℂ) := support_deriv_subset
      _ ⊆ Set.Icc (-B) B := hts

/-- One ladder step is the zero shift: the order-`n` ladder value of the
shifted owner equals the order-`n + 1` ladder value of the original. -/
theorem derivOrderL1_shift_zero (n : ℕ) (f : CompactLogTest) :
    derivOrderL1 n (derivativeShift f 0) = derivOrderL1 (n + 1) f := by
  change (∫ x : ℝ, ‖iteratedDeriv n ((derivativeShift f 0).test : ℝ → ℂ) x‖) =
    (∫ x : ℝ, ‖iteratedDeriv (n + 1) (f.test : ℝ → ℂ) x‖)
  congr 1
  funext x
  rw [iteratedDeriv_derivativeShift_apply]
  simp

/-! ## 2. The IBP bridge -/

/-- Iterated integration by parts for a compact log test: the order-`k`
weighted Laplace norm is bounded by the support weight and the order-`k`
L1 derivative ladder. -/
theorem norm_pow_laplaceAt_le_exp_mul_derivOrderL1 :
    ∀ (k : ℕ) (f : CompactLogTest) (B : ℝ),
      Function.support f.test ⊆ Set.Icc (-B) B →
      ∀ s : ℂ, ‖(s : ℂ)‖ ^ k * ‖laplaceAt f s‖ ≤
        Real.exp (|s.re| * B) * derivOrderL1 k f := by
  intro k
  induction k with
  | zero =>
      intro f B hs s
      rw [pow_zero, one_mul, derivOrderL1_zero]
      exact norm_laplaceAt_le_exp_mul_l1Mass f B hs s
  | succ n ih =>
      intro f B hs s
      have hsup : Function.support (derivativeShift f 0).test ⊆ Set.Icc (-B) B :=
        derivativeShiftZero_support_subset f B hs
      have hnorm : ‖laplaceAt (derivativeShift f 0) s‖ = ‖(s : ℂ)‖ * ‖laplaceAt f s‖ := by
        rw [laplaceAt_derivativeShift]
        simp
      calc ‖(s : ℂ)‖ ^ (n + 1) * ‖laplaceAt f s‖
          = ‖(s : ℂ)‖ ^ n * (‖(s : ℂ)‖ * ‖laplaceAt f s‖) := by ring
          _ = ‖(s : ℂ)‖ ^ n * ‖laplaceAt (derivativeShift f 0) s‖ := by rw [← hnorm]
          _ ≤ Real.exp (|s.re| * B) *
              derivOrderL1 n (derivativeShift f 0) := ih (derivativeShift f 0) B hsup s
          _ = Real.exp (|s.re| * B) * derivOrderL1 (n + 1) f :=
            by rw [derivOrderL1_shift_zero]

/-! ## 3. The strip-point helpers -/

private theorem one_le_two_pi : (1 : ℝ) ≤ 2 * Real.pi := by
  linarith [Real.pi_gt_three]

/-- The imaginary part of the strip point is the height. -/
theorem im_ofReal_add_mul_I (sigma t : ℝ) :
    ((sigma : ℂ) + (t : ℂ) * Complex.I).im = t := by
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.ofReal_re]
  ring

/-- The real part of the strip point is the strip coordinate. -/
theorem re_ofReal_add_mul_I (sigma t : ℝ) :
    ((sigma : ℂ) + (t : ℂ) * Complex.I).re = sigma := by
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.ofReal_re]
  ring

/-- The height is dominated by the modulus of the strip point. -/
theorem abs_le_norm_ofReal_add_mul_I (sigma t : ℝ) :
    |t| ≤ ‖(sigma : ℂ) + (t : ℂ) * Complex.I‖ :=
  calc |t| = |((sigma : ℂ) + (t : ℂ) * Complex.I).im| :=
      (congrArg abs (im_ofReal_add_mul_I sigma t)).symm
    _ ≤ ‖(sigma : ℂ) + (t : ℂ) * Complex.I‖ := Complex.abs_im_le_norm _

/-- On the strip `sigma in [0, 1]` with radius `B >= 0`, the support weight
of the strip point is at most `exp B` times any nonnegative ladder value. -/
theorem exp_weight_le_exp (B : ℝ) (hB : 0 ≤ B) (k : ℕ)
    (f : CompactLogTest) (sigma t : ℝ) (hsigma : sigma ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (|((sigma : ℂ) + (t : ℂ) * Complex.I).re| * B) *
        derivOrderL1 k f ≤
      Real.exp B * derivOrderL1 k f := by
  have hre : |((sigma : ℂ) + (t : ℂ) * Complex.I).re| * B ≤ B := by
    rw [re_ofReal_add_mul_I, abs_of_nonneg hsigma.1]
    calc sigma * B ≤ 1 * B := mul_le_mul_of_nonneg_right hsigma.2 hB
      _ = B := by ring
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hre) ?_
  exact derivOrderL1_nonneg k f

/-! ## 4. Scalar ladder pins imply the wired strip hypotheses -/

/-- The weighted-decay strip form (`hquartic` at `k = 4`, `hquadratic` at
`k = 2`) follows from one scalar ladder pin. -/
theorem wiredStripDecayOfLadderPin
    (f : CompactLogTest) (B C : ℝ) (k : ℕ)
    (hB : 0 ≤ B)
    (hsupport : Function.support f.test ⊆ Set.Icc (-B) B)
    (hpin : Real.exp B * derivOrderL1 k f ≤ C) :
    ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ k *
        ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  intro sigma hsigma t
  have hnorm_le : ‖t / (2 * Real.pi)‖ ≤ ‖(sigma : ℂ) + (t : ℂ) * Complex.I‖ := by
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos Real.two_pi_pos]
    exact (div_le_self (abs_nonneg t) one_le_two_pi).trans
      (abs_le_norm_ofReal_add_mul_I sigma t)
  calc ‖t / (2 * Real.pi)‖ ^ k * ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ‖(sigma : ℂ) + (t : ℂ) * Complex.I‖ ^ k *
          ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hnorm_le k) (norm_nonneg _)
      _ ≤ Real.exp (|((sigma : ℂ) + (t : ℂ) * Complex.I).re| * B) *
            derivOrderL1 k f :=
          norm_pow_laplaceAt_le_exp_mul_derivOrderL1 k f B hsupport _
      _ ≤ Real.exp B * derivOrderL1 k f :=
          exp_weight_le_exp B hB k f sigma t hsigma
      _ ≤ C := hpin

/-- The contraction threshold form (`hcontract`) follows from one scalar
ladder pin at any order `k` against the threshold `T > 0`. -/
theorem wiredContractOfDecayPin
    (f : CompactLogTest) (B T q : ℝ) (k : ℕ)
    (hB : 0 ≤ B) (hT : 0 < T)
    (hsupport : Function.support f.test ⊆ Set.Icc (-B) B)
    (hpin : Real.exp B * derivOrderL1 k f ≤ q * T ^ k) :
    ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, T ≤ |t| →
      ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ q := by
  intro sigma hsigma t ht
  have hzT : T ≤ ‖(sigma : ℂ) + (t : ℂ) * Complex.I‖ :=
    ht.trans (abs_le_norm_ofReal_add_mul_I sigma t)
  have hpz : 0 < ‖(sigma : ℂ) + (t : ℂ) * Complex.I‖ := lt_of_lt_of_le hT hzT
  have hk0 : 0 ≤ derivOrderL1 k f := derivOrderL1_nonneg k f
  have hq : 0 ≤ q := by
    have hnum : 0 ≤ q * T ^ k :=
      (mul_nonneg (Real.exp_nonneg _) hk0).trans hpin
    have h0 : (0 : ℝ) * T ^ k ≤ q * T ^ k := by
      rw [zero_mul]
      exact hnum
    exact le_of_mul_le_mul_right h0 (pow_pos hT k)
  have hmain : ‖(sigma : ℂ) + (t : ℂ) * Complex.I‖ ^ k *
      ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ q * T ^ k :=
    (norm_pow_laplaceAt_le_exp_mul_derivOrderL1 k f B hsupport _).trans
      ((exp_weight_le_exp B hB k f sigma t hsigma).trans hpin)
  have hzTk : T ^ k ≤ ‖(sigma : ℂ) + (t : ℂ) * Complex.I‖ ^ k :=
    pow_le_pow_left₀ (le_of_lt hT) hzT k
  -- Cancellation route (no division lemmas): hmain against the enlarged
  -- right side gives ‖z‖ ^ k * X ≤ ‖z‖ ^ k * q, then the positive factor
  -- ‖z‖ ^ k is cancelled on the left.
  have hkey : ‖(sigma : ℂ) + (t : ℂ) * Complex.I‖ ^ k *
      ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ‖(sigma : ℂ) + (t : ℂ) * Complex.I‖ ^ k * q := by
    rw [mul_comm (‖(sigma : ℂ) + (t : ℂ) * Complex.I‖ ^ k) q]
    exact hmain.trans (mul_le_mul_of_nonneg_left hzTk hq)
  exact le_of_mul_le_mul_left hkey (pow_pos hpz k)

end
end C1StripEnvelopeIbpBridge2722
end Source
end ConnesWeilRH
