import ConnesWeilRH.Dev.C1ExplicitSeedThirdOrderIntervalCertificate
import ConnesWeilRH.Dev.C1CorrectionL1MassBound

/-!
# Cardinal correction budgets from the unweighted seed

Conjugating the differential product by its exponential weight leaves exactly
the same compact log test. The resulting L1 bound needs only the unweighted
seed ladder, with the actual node differences and denominator retained.
This removes the separate weighted-derivative oracle from the correction
budget. It does not prove a signed gate or a spectral tail margin.
-/

namespace ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaCriticalContraction
open CC20YoshidaCriticalContraction.CompactLogTest
open C1LaneRD3Root
open ConnesWeilRH.Source.C1ExplicitSmoothSeed

noncomputable section

theorem derivativeShift_exponentialWeight (f : CompactLogTest) (a t : ℂ) :
    derivativeShift (exponentialWeight f a) t =
      exponentialWeight (derivativeShift f (t + a)) a := by
  ext x
  have hlin : HasDerivAt (fun y : ℝ => a * (y : ℂ)) a x := by
    simpa using ((hasDerivAt_id (x : ℂ)).const_mul a).comp_ofReal
  have hf : HasDerivAt (fun y : ℝ => f.test y)
      (deriv (f.test : ℝ → ℂ) x) x :=
    ((f.test.smooth ⊤).differentiable (by simp) x).hasDerivAt
  have hder := (hlin.cexp.mul hf).deriv
  change deriv (fun y : ℝ => Complex.exp (a * (y : ℂ)) * f.test y) x = _ at hder
  change deriv (fun y : ℝ => Complex.exp (a * (y : ℂ)) * f.test y) x +
    t * (Complex.exp (a * (x : ℂ)) * f.test x) =
    Complex.exp (a * (x : ℂ)) * (deriv (f.test : ℝ → ℂ) x + (t + a) * f.test x)
  rw [hder]
  ring

theorem shiftedProduct_exponentialWeight (nodes : List ℂ) (f : CompactLogTest)
    (a : ℂ) :
    shiftedProduct nodes (exponentialWeight f a) =
      exponentialWeight (shiftedProduct (nodes.map (fun t => t + a)) f) a := by
  induction nodes with
  | nil => rfl
  | cons t ts ih =>
      change derivativeShift (shiftedProduct ts (exponentialWeight f a)) t = _
      rw [ih, derivativeShift_exponentialWeight]
      rfl

theorem cardinalRaw_eq_weight_shifted_differences (nodes : Finset ℂ)
    (f : CompactLogTest) (z : ℂ) :
    cardinalRaw nodes f z = exponentialWeight
      (shiftedProduct ((nodes.erase z).toList.map (fun t => t - z)) f) (-z) := by
  simpa only [cardinalRaw, sub_eq_add_neg] using
    shiftedProduct_exponentialWeight (nodes.erase z).toList f (-z)

theorem l1Mass_cardinalRaw_le_seed_ladder (nodes : Finset ℂ) (f : CompactLogTest)
    (z : ℂ) (B : ℝ) (hsupport : Function.support f.test ⊆ Set.Icc (-B) B) :
    l1Mass (cardinalRaw nodes f z) ≤ Real.exp (|z.re| * B) *
      ladderBound (fun j => derivOrderL1 j f)
        ((nodes.erase z).toList.map (fun t => t - z)) 0 := by
  rw [cardinalRaw_eq_weight_shifted_differences]
  have hw := l1Mass_exponentialWeight_le_of_support
    (shiftedProduct ((nodes.erase z).toList.map (fun t => t - z)) f) B
    (shiftedProduct_support _ f hsupport) (-z)
  simp only [Complex.neg_re, abs_neg] at hw
  exact hw.trans (mul_le_mul_of_nonneg_left
    (l1Mass_shiftedProduct_le_ladder _ f) (Real.exp_nonneg _))

theorem l1Mass_correction_le_seed_ladder (nodes : Finset ℂ) (f : CompactLogTest)
    (y : ℂ → ℂ) (B : ℝ) (hsupport : Function.support f.test ⊆ Set.Icc (-B) B) :
    l1Mass (correction nodes f y) ≤ ∑ z ∈ nodes,
      ‖y z / (nodeProduct nodes z z * laplaceAt f 0)‖ *
        (Real.exp (|z.re| * B) * ladderBound (fun j => derivOrderL1 j f)
          ((nodes.erase z).toList.map (fun t => t - z)) 0) := by
  refine (l1Mass_correction_le nodes f y).trans (Finset.sum_le_sum ?_)
  intro z hz
  exact mul_le_mul_of_nonneg_left
    (l1Mass_cardinalRaw_le_seed_ladder nodes f z B hsupport) (norm_nonneg _)

/-- Only orders through `m + nodes.length` are needed; no infinite oracle is required. -/
theorem ladderBound_mono_on_needed_orders {L L' : ℕ → ℝ} (nodes : List ℂ) (m : ℕ)
    (h : ∀ j, m ≤ j → j ≤ m + nodes.length → L j ≤ L' j) :
    ladderBound L nodes m ≤ ladderBound L' nodes m := by
  induction nodes generalizing m with
  | nil => exact h m le_rfl (by simp)
  | cons a as ih =>
      simp only [ladderBound_cons]
      apply add_le_add
      · apply ih (m + 1)
        intro j hj hj'
        exact h j (by omega) (by simp only [List.length_cons]; omega)
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg a)
        apply ih m
        intro j hj hj'
        exact h j hj (by simp only [List.length_cons]; omega)

/-- The certified first three orders suffice for a three-shift product. -/
theorem l1Mass_shiftedProduct_three_smoothSeed_le (a b c : ℂ) :
    l1Mass (shiftedProduct [a, b, c] smoothSeed) ≤
      787283385 / 10 ^ 7 + 8 * (‖a‖ + ‖b‖ + ‖c‖) +
        2 * (‖a‖ * ‖b‖ + ‖a‖ * ‖c‖ + ‖b‖ * ‖c‖) +
        4 * ‖a‖ * ‖b‖ * ‖c‖ := by
  have h := l1Mass_shiftedProduct_le_ladder [a, b, c] smoothSeed
  simp only [ladderBound_cons, ladderBound_nil] at h
  norm_num only at h
  rw [derivOrderL1_zero, derivOrderL1_one, derivativeL1_smoothSeed_eq_two,
    derivOrderL1_smoothSeed_two] at h
  have h3 := derivOrderL1_smoothSeed_three_mem_Icc.2
  have h0 := smoothSeed_l1Mass_le_four
  have hm := mul_le_mul_of_nonneg_left h0
    (mul_nonneg (mul_nonneg (norm_nonneg a) (norm_nonneg b)) (norm_nonneg c))
  nlinarith

/-- Certified low orders, with only higher orders left to the caller. -/
def smoothSeedBudget (higher : ℕ → ℝ) : ℕ → ℝ
  | 0 => 4
  | 1 => 2
  | 2 => 8
  | 3 => 787283385 / 10 ^ 7
  | j + 4 => higher (j + 4)

theorem derivOrderL1_smoothSeed_le_budget (higher : ℕ → ℝ) (j : ℕ)
    (h : 4 ≤ j → derivOrderL1 j smoothSeed ≤ higher j) :
    derivOrderL1 j smoothSeed ≤ smoothSeedBudget higher j := by
  rcases j with _ | j
  · exact smoothSeed_l1Mass_le_four
  rcases j with _ | j
  · change derivOrderL1 1 smoothSeed ≤ 2
    rw [derivOrderL1_one, derivativeL1_smoothSeed_eq_two]
  rcases j with _ | j
  · exact derivOrderL1_smoothSeed_two.le
  rcases j with _ | j
  · exact derivOrderL1_smoothSeed_three_mem_Icc.2
  · exact h (by omega)

/-- The full correction budget consumes the certified low orders. For `N` actual
nodes, the only derivative premises left are orders `4 <= j < N`. -/
theorem l1Mass_correction_smoothSeed_le_budget (nodes : Finset ℂ) (y : ℂ → ℂ)
    (higher : ℕ → ℝ)
    (hhigh : ∀ j, 4 ≤ j → j < nodes.card → derivOrderL1 j smoothSeed ≤ higher j) :
    l1Mass (correction nodes smoothSeed y) ≤ ∑ z ∈ nodes,
      ‖y z / (nodeProduct nodes z z * laplaceAt smoothSeed 0)‖ *
        (Real.exp (|z.re| * 2) * ladderBound (smoothSeedBudget higher)
          ((nodes.erase z).toList.map (fun t => t - z)) 0) := by
  classical
  refine (l1Mass_correction_le_seed_ladder nodes smoothSeed y 2
    smoothSeedComplex_support_subset).trans (Finset.sum_le_sum ?_)
  intro z hz
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply ladderBound_mono_on_needed_orders
  intro j hj hj'
  apply derivOrderL1_smoothSeed_le_budget
  intro hj4
  apply hhigh j hj4
  have hn : 0 < nodes.card := Finset.card_pos.mpr ⟨z, hz⟩
  simp only [List.length_map, Finset.length_toList, Finset.card_erase_of_mem hz,
    Nat.zero_add] at hj'
  omega

end

end ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection
