import ConnesWeilRH.Dev.C1SeedJetSemantics2731
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Source-level phase derivative bounds for the endpoint calculus in record 2730. -/

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

noncomputable section

theorem iteratedDeriv_inv2732 (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => y⁻¹) x =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) * (x⁻¹) ^ (n + 1) := by
  have h := iteratedDerivWithin_one_div (𝕜 := ℝ) n isOpen_univ (Set.mem_univ x)
  simp only [iteratedDerivWithin_univ, one_div] at h
  rw [show (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast, ← inv_pow] at h
  exact h

theorem iteratedDeriv_reflected_inv2732 (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => (1 - y)⁻¹) x =
      (n.factorial : ℝ) * ((1 - x)⁻¹) ^ (n + 1) := by
  rw [iteratedDeriv_comp_const_sub]
  simp only [smul_eq_mul, iteratedDeriv_inv2732]
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    simp
  rw [← mul_assoc, ← mul_assoc, hsign, one_mul]

theorem iteratedDeriv_transitionPhase2732 (n : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    iteratedDeriv n transitionPhase2731 x =
      -((-1 : ℝ) ^ n * (n.factorial : ℝ) * (x⁻¹) ^ (n + 1)) +
        (n.factorial : ℝ) * ((1 - x)⁻¹) ^ (n + 1) := by
  have hi : ContDiffAt ℝ n (fun y : ℝ => y⁻¹) x :=
    contDiffAt_id.inv (ne_of_gt hx0)
  have hj : ContDiffAt ℝ n (fun y : ℝ => (1 - y)⁻¹) x :=
    (contDiffAt_const.sub contDiffAt_id).inv (ne_of_gt (sub_pos.mpr hx1))
  unfold transitionPhase2731
  rw [iteratedDeriv_fun_add hi.neg hj, iteratedDeriv_fun_neg,
    iteratedDeriv_inv2732, iteratedDeriv_reflected_inv2732]

theorem abs_iteratedDeriv_transitionPhase2732 (n : ℕ) (hn : 0 < n) {x : ℝ}
    (hx0 : 0 < x) (hxhalf : x ≤ 1 / 2) :
    |iteratedDeriv n transitionPhase2731 x| ≤
      2 * (n.factorial : ℝ) * (x⁻¹) ^ (2 * n) := by
  have hx1 : x < 1 := by linarith
  have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
  have hj : 0 ≤ (1 - x)⁻¹ := inv_nonneg.mpr (by linarith)
  have hbase : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).mpr (by linarith)
  have hreflect : (1 - x)⁻¹ ≤ x⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hx0 (show x ≤ 1 - x by linarith)
  have hpower : (x⁻¹) ^ (n + 1) ≤ (x⁻¹) ^ (2 * n) :=
    pow_le_pow_right₀ hbase (by omega)
  have hpower' : ((1 - x)⁻¹) ^ (n + 1) ≤ (x⁻¹) ^ (2 * n) :=
    (pow_le_pow_left₀ hj hreflect (n + 1)).trans hpower
  rw [iteratedDeriv_transitionPhase2732 n hx0 hx1]
  calc
    |-((-1 : ℝ) ^ n * (n.factorial : ℝ) * (x⁻¹) ^ (n + 1)) +
        (n.factorial : ℝ) * ((1 - x)⁻¹) ^ (n + 1)|
      ≤ |-((-1 : ℝ) ^ n * (n.factorial : ℝ) * (x⁻¹) ^ (n + 1))| +
          |(n.factorial : ℝ) * ((1 - x)⁻¹) ^ (n + 1)| := abs_add_le _ _
    _ = (n.factorial : ℝ) * (x⁻¹) ^ (n + 1) +
          (n.factorial : ℝ) * ((1 - x)⁻¹) ^ (n + 1) := by
      simp only [abs_neg, abs_mul, abs_pow, abs_one, one_pow, one_mul,
        Nat.abs_cast, abs_of_nonneg hi, abs_of_nonneg hj]
    _ ≤ (n.factorial : ℝ) * (x⁻¹) ^ (2 * n) +
          (n.factorial : ℝ) * (x⁻¹) ^ (2 * n) :=
      add_le_add (mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hpower' (Nat.cast_nonneg _))
    _ = 2 * (n.factorial : ℝ) * (x⁻¹) ^ (2 * n) := by ring

def endpointExpCoef2732 : ℕ → ℕ
  | 0 => 1 | 1 => 2 | 2 => 8 | 3 => 44 | 4 => 304
  | 5 => 2512 | 6 => 24064 | 7 => 261536 | _ => 0

def endpointReciprocalCoef2732 : ℕ → ℕ
  | 0 => 1 | 1 => 2 | 2 => 16 | 3 => 188 | 4 => 2928
  | 5 => 56912 | 6 => 1326912 | 7 => 36089888 | _ => 0

def endpointTransitionCoef2732 : ℕ → ℕ
  | 0 => 1 | 1 => 4 | 2 => 32 | 3 => 376 | 4 => 5856
  | 5 => 113824 | 6 => 2653824 | 7 => 72179776 | _ => 0

theorem endpointExpCoef_succ2732 (n : ℕ) (hn : n < 7) :
    (endpointExpCoef2732 (n + 1) : ℝ) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        (2 * ((j + 1).factorial : ℝ)) * (endpointExpCoef2732 (n - j) : ℝ) := by
  interval_cases n <;> norm_num [endpointExpCoef2732, Finset.sum_range_succ, Nat.choose]

theorem endpointReciprocalCoef_succ2732 (n : ℕ) (hn : n < 7) :
    (endpointReciprocalCoef2732 (n + 1) : ℝ) =
      ∑ j ∈ Finset.range (n + 1), ((n + 1).choose (j + 1) : ℝ) *
        (endpointExpCoef2732 (j + 1) : ℝ) *
        (endpointReciprocalCoef2732 (n - j) : ℝ) := by
  interval_cases n <;>
    norm_num [endpointExpCoef2732, endpointReciprocalCoef2732, Finset.sum_range_succ, Nat.choose]

theorem endpointTransitionCoef_eq2732 (n : ℕ) (hn : n ≤ 7) :
    (endpointTransitionCoef2732 n : ℝ) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        (endpointExpCoef2732 j : ℝ) * (endpointReciprocalCoef2732 (n - j) : ℝ) := by
  interval_cases n <;> norm_num [endpointExpCoef2732, endpointReciprocalCoef2732,
    endpointTransitionCoef2732, Finset.sum_range_succ, Nat.choose]

theorem transitionExp_le_one2732 {x : ℝ} (hx0 : 0 < x) (hxhalf : x ≤ 1 / 2) :
    transitionExp2731 x ≤ 1 := by
  have hreflect : (1 - x)⁻¹ ≤ x⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hx0 (show x ≤ 1 - x by linarith)
  apply Real.exp_le_one_iff.mpr
  unfold transitionPhase2731
  linarith

theorem abs_iteratedDeriv_transitionExp2732 (n : ℕ) (hn : n ≤ 7) {x : ℝ}
    (hx0 : 0 < x) (hxhalf : x ≤ 1 / 2) :
    |iteratedDeriv n transitionExp2731 x| ≤
      (endpointExpCoef2732 n : ℝ) * transitionExp2731 x * (x⁻¹) ^ (2 * n) := by
  have hx1 : x < 1 := by linarith
  have hEpos : 0 < transitionExp2731 x := Real.exp_pos _
  have hu : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [endpointExpCoef2732, abs_of_pos hEpos]
    | succ m =>
      rw [iteratedDeriv_transitionExp2731 m hx0 hx1]
      have hsum :
          |∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
            iteratedDeriv (j + 1) transitionPhase2731 x *
            iteratedDeriv (m - j) transitionExp2731 x| ≤
          ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
            (2 * ((j + 1).factorial : ℝ) * (x⁻¹) ^ (2 * (j + 1))) *
            ((endpointExpCoef2732 (m - j) : ℝ) * transitionExp2731 x *
              (x⁻¹) ^ (2 * (m - j))) := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hF := abs_iteratedDeriv_transitionPhase2732 (j + 1) (by omega) hx0 hxhalf
        have hE := ih (m - j) (by omega) (by omega)
        simp only [abs_mul, Nat.abs_cast]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg _)) hE
          (abs_nonneg _) (by positivity)
      apply hsum.trans
      apply le_of_eq
      calc
        (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
            (2 * ((j + 1).factorial : ℝ) * (x⁻¹) ^ (2 * (j + 1))) *
            ((endpointExpCoef2732 (m - j) : ℝ) * transitionExp2731 x *
              (x⁻¹) ^ (2 * (m - j)))) =
            ∑ j ∈ Finset.range (m + 1),
              ((m.choose j : ℝ) * (2 * ((j + 1).factorial : ℝ)) *
                (endpointExpCoef2732 (m - j) : ℝ)) *
              (transitionExp2731 x * (x⁻¹) ^ (2 * (m + 1))) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hp : 2 * (j + 1) + 2 * (m - j) = 2 * (m + 1) := by
            have := Finset.mem_range.mp hj
            omega
          calc
            _ = ((m.choose j : ℝ) * (2 * ((j + 1).factorial : ℝ)) *
                  (endpointExpCoef2732 (m - j) : ℝ)) * transitionExp2731 x *
                  ((x⁻¹) ^ (2 * (j + 1)) * (x⁻¹) ^ (2 * (m - j))) := by ring
            _ = _ := by rw [← pow_add, hp]; ring
        _ = (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
              (2 * ((j + 1).factorial : ℝ)) * (endpointExpCoef2732 (m - j) : ℝ)) *
              (transitionExp2731 x * (x⁻¹) ^ (2 * (m + 1))) :=
          (Finset.sum_mul _ _ _).symm
        _ = (endpointExpCoef2732 (m + 1) : ℝ) * transitionExp2731 x *
              (x⁻¹) ^ (2 * (m + 1)) := by
          rw [← endpointExpCoef_succ2732 m (by omega)]
          ring

theorem abs_iteratedDeriv_transitionExp_crude2732 (n : ℕ) (hn : n ≤ 7) {x : ℝ}
    (hx0 : 0 < x) (hxhalf : x ≤ 1 / 2) :
    |iteratedDeriv n transitionExp2731 x| ≤
      (endpointExpCoef2732 n : ℝ) * (x⁻¹) ^ (2 * n) := by
  apply (abs_iteratedDeriv_transitionExp2732 n hn hx0 hxhalf).trans
  calc
    (endpointExpCoef2732 n : ℝ) * transitionExp2731 x * (x⁻¹) ^ (2 * n) ≤
        (endpointExpCoef2732 n : ℝ) * 1 * (x⁻¹) ^ (2 * n) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (transitionExp_le_one2732 hx0 hxhalf)
          (Nat.cast_nonneg _)) (by positivity)
    _ = _ := by ring

theorem abs_iteratedDeriv_transitionReciprocal2732 (n : ℕ) (hn : n ≤ 7) {x : ℝ}
    (hx0 : 0 < x) (hxhalf : x ≤ 1 / 2) :
    |iteratedDeriv n transitionReciprocal2731 x| ≤
      (endpointReciprocalCoef2732 n : ℝ) * (x⁻¹) ^ (2 * n) := by
  have hx1 : x < 1 := by linarith
  have hEpos : 0 < transitionExp2731 x := Real.exp_pos _
  have hden : 1 ≤ 1 + transitionExp2731 x := by linarith
  have hdenpos : 0 < 1 + transitionExp2731 x := by linarith
  have hu : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp only [iteratedDeriv_zero, endpointReciprocalCoef2732, Nat.cast_one,
        mul_zero, pow_zero, mul_one]
      change |(1 + transitionExp2731 x)⁻¹| ≤ 1
      rw [abs_of_pos (inv_pos.mpr hdenpos)]
      simpa only [one_div, inv_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
    | succ m =>
      rw [iteratedDeriv_transitionReciprocal2731 m hx0 hx1]
      have hsum :
          |∑ j ∈ Finset.range (m + 1), ((m + 1).choose (j + 1) : ℝ) *
            iteratedDeriv (j + 1) transitionExp2731 x *
            iteratedDeriv (m - j) transitionReciprocal2731 x| ≤
          ∑ j ∈ Finset.range (m + 1), ((m + 1).choose (j + 1) : ℝ) *
            ((endpointExpCoef2732 (j + 1) : ℝ) * (x⁻¹) ^ (2 * (j + 1))) *
            ((endpointReciprocalCoef2732 (m - j) : ℝ) * (x⁻¹) ^ (2 * (m - j))) := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hE := abs_iteratedDeriv_transitionExp_crude2732 (j + 1) (by omega) hx0 hxhalf
        have hR := ih (m - j) (by omega) (by omega)
        simp only [abs_mul, Nat.abs_cast]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)) hR
          (abs_nonneg _) (by positivity)
      rw [abs_div, abs_neg, abs_of_pos hdenpos]
      apply (div_le_self (abs_nonneg _) hden).trans
      apply hsum.trans
      apply le_of_eq
      calc
        (∑ j ∈ Finset.range (m + 1), ((m + 1).choose (j + 1) : ℝ) *
            ((endpointExpCoef2732 (j + 1) : ℝ) * (x⁻¹) ^ (2 * (j + 1))) *
            ((endpointReciprocalCoef2732 (m - j) : ℝ) * (x⁻¹) ^ (2 * (m - j)))) =
            ∑ j ∈ Finset.range (m + 1),
              (((m + 1).choose (j + 1) : ℝ) * (endpointExpCoef2732 (j + 1) : ℝ) *
                (endpointReciprocalCoef2732 (m - j) : ℝ)) *
              (x⁻¹) ^ (2 * (m + 1)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hp : 2 * (j + 1) + 2 * (m - j) = 2 * (m + 1) := by
            have := Finset.mem_range.mp hj
            omega
          calc
            _ = (((m + 1).choose (j + 1) : ℝ) * (endpointExpCoef2732 (j + 1) : ℝ) *
                  (endpointReciprocalCoef2732 (m - j) : ℝ)) *
                  ((x⁻¹) ^ (2 * (j + 1)) * (x⁻¹) ^ (2 * (m - j))) := by ring
            _ = _ := by rw [← pow_add, hp]
        _ = (∑ j ∈ Finset.range (m + 1), ((m + 1).choose (j + 1) : ℝ) *
              (endpointExpCoef2732 (j + 1) : ℝ) *
              (endpointReciprocalCoef2732 (m - j) : ℝ)) *
              (x⁻¹) ^ (2 * (m + 1)) := (Finset.sum_mul _ _ _).symm
        _ = (endpointReciprocalCoef2732 (m + 1) : ℝ) *
              (x⁻¹) ^ (2 * (m + 1)) := by
          rw [← endpointReciprocalCoef_succ2732 m (by omega)]

theorem abs_iteratedDeriv_smoothTransition_majorant2732 (n : ℕ) (hn : n ≤ 7) {x : ℝ}
    (hx0 : 0 < x) (hxhalf : x ≤ 1 / 2) :
    |iteratedDeriv n Real.smoothTransition x| ≤
      (endpointTransitionCoef2732 n : ℝ) * transitionExp2731 x * (x⁻¹) ^ (2 * n) := by
  have hx1 : x < 1 := by linarith
  have hEpos : 0 < transitionExp2731 x := Real.exp_pos _
  have hu : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
  rw [iteratedDeriv_smoothTransition_product2731 n hx0 hx1]
  have hsum :
      |∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        iteratedDeriv j transitionExp2731 x *
        iteratedDeriv (n - j) transitionReciprocal2731 x| ≤
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        ((endpointExpCoef2732 j : ℝ) * transitionExp2731 x * (x⁻¹) ^ (2 * j)) *
        ((endpointReciprocalCoef2732 (n - j) : ℝ) * (x⁻¹) ^ (2 * (n - j))) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hE := abs_iteratedDeriv_transitionExp2732 j (by omega) hx0 hxhalf
    have hR := abs_iteratedDeriv_transitionReciprocal2732 (n - j) (by omega) hx0 hxhalf
    simp only [abs_mul, Nat.abs_cast]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)) hR
      (abs_nonneg _) (by positivity)
  apply hsum.trans
  apply le_of_eq
  calc
    (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        ((endpointExpCoef2732 j : ℝ) * transitionExp2731 x * (x⁻¹) ^ (2 * j)) *
        ((endpointReciprocalCoef2732 (n - j) : ℝ) * (x⁻¹) ^ (2 * (n - j)))) =
        ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : ℝ) * (endpointExpCoef2732 j : ℝ) *
            (endpointReciprocalCoef2732 (n - j) : ℝ)) *
          (transitionExp2731 x * (x⁻¹) ^ (2 * n)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hp : 2 * j + 2 * (n - j) = 2 * n := by
        have := Finset.mem_range.mp hj
        omega
      calc
        _ = ((n.choose j : ℝ) * (endpointExpCoef2732 j : ℝ) *
              (endpointReciprocalCoef2732 (n - j) : ℝ)) * transitionExp2731 x *
              ((x⁻¹) ^ (2 * j) * (x⁻¹) ^ (2 * (n - j))) := by ring
        _ = _ := by rw [← pow_add, hp]; ring
    _ = (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
          (endpointExpCoef2732 j : ℝ) * (endpointReciprocalCoef2732 (n - j) : ℝ)) *
          (transitionExp2731 x * (x⁻¹) ^ (2 * n)) := (Finset.sum_mul _ _ _).symm
    _ = (endpointTransitionCoef2732 n : ℝ) * transitionExp2731 x *
          (x⁻¹) ^ (2 * n) := by
      rw [← endpointTransitionCoef_eq2732 n hn]
      ring

theorem transitionExp_le_endpoint_exp2732 {x : ℝ}
    (hxhalf : x ≤ 1 / 2) :
    transitionExp2731 x ≤ 8 * Real.exp (-x⁻¹) := by
  have hreflect : (1 - x)⁻¹ ≤ 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (show (1 / 2 : ℝ) ≤ 1 - x by linarith)
    norm_num [one_div] at h
    exact h
  have hexp : Real.exp (2 : ℝ) < 8 := by
    have h1 := Real.exp_one_lt_d9
    have h0 := Real.exp_pos (1 : ℝ)
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  unfold transitionExp2731 transitionPhase2731
  rw [Real.exp_add]
  calc
    Real.exp (-x⁻¹) * Real.exp ((1 - x)⁻¹) ≤
        Real.exp (-x⁻¹) * Real.exp 2 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hreflect) (Real.exp_nonneg _)
    _ ≤ 8 * Real.exp (-x⁻¹) := by nlinarith [Real.exp_pos (-x⁻¹)]

theorem abs_iteratedDeriv_smoothTransition_endpoint2732 (n : ℕ) (hn : n ≤ 7) {x : ℝ}
    (hx0 : 0 < x) (hxhalf : x ≤ 1 / 2) :
    |iteratedDeriv n Real.smoothTransition x| ≤
      8 * (endpointTransitionCoef2732 n : ℝ) * (x⁻¹) ^ (2 * n) * Real.exp (-x⁻¹) := by
  apply (abs_iteratedDeriv_smoothTransition_majorant2732 n hn hx0 hxhalf).trans
  calc
    (endpointTransitionCoef2732 n : ℝ) * transitionExp2731 x * (x⁻¹) ^ (2 * n) ≤
        (endpointTransitionCoef2732 n : ℝ) * (8 * Real.exp (-x⁻¹)) *
          (x⁻¹) ^ (2 * n) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (transitionExp_le_endpoint_exp2732 hxhalf)
          (Nat.cast_nonneg _)) (by positivity)
    _ = _ := by ring

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
