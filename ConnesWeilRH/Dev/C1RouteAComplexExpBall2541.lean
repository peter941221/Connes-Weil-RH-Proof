import ConnesWeilRH.Dev.C1RouteASignedAggregateCell2539

/-! Rounded Horner and squaring bounds for nonzero signed production nodes.
The approximate center remains complex; only the error is scalar. -/

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def expHorner2541 (z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => 1 + z / ((19 - n : ℕ) : ℂ) * expHorner2541 z n

theorem expHorner2541_eq_sum (z : ℂ) :
    expHorner2541 z 19 = ∑ k ∈ Finset.range 20, z ^ k / (k.factorial : ℂ) := by
  norm_num [expHorner2541, Finset.sum_range_succ]
  ring

theorem expHorner2541_error (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - expHorner2541 z 19‖ ≤ (1 : ℝ) / 10 ^ 18 := by
  rw [expHorner2541_eq_sum]
  have h := Complex.exp_bound hz (n := 20) (by norm_num)
  have hp : ‖z‖ ^ 20 ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  have ht : 0 ≤ ((21 : ℝ) * ((20 : ℕ).factorial * (20 : ℝ))⁻¹) := by positivity
  have hprod := mul_le_mul_of_nonneg_right hp ht
  norm_num at h hprod ⊢
  linarith

theorem complex_norm_le_l1_2541 (z : ℂ) (bound : ℝ)
    (h : |z.re| + |z.im| ≤ bound) : ‖z‖ ≤ bound :=
  (Complex.norm_le_abs_re_add_abs_im z).trans h

theorem complex_norm_le_of_sq2541 (z : ℂ) (bound : ℝ) (hb : 0 ≤ bound)
    (h : z.re ^ 2 + z.im ^ 2 ≤ bound ^ 2) : ‖z‖ ≤ bound := by
  have he := Complex.sq_norm z
  rw [Complex.normSq_apply] at he
  nlinarith [norm_nonneg z]

theorem sum30_chain2541 {α : Type*} [AddCommMonoid α] (f : Fin 30 → α) :
    (∑ i, f i) =
      f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 +
      (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 +
      (f 20 + (f 21 + (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + f 29
      )))))))))))))))))))))))))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

theorem weighted_unit_inside_exp2541 (sigma theta radius x : ℝ) (hx : |x| < radius) :
    weightedFunction2348 sigma (externalFamilyValue2344 1 theta radius) x =
      Complex.exp (((sigma*x - 30/(1-(x/radius)^2) : ℝ) : ℂ) +
        ((theta*x : ℝ) : ℂ) * Complex.I) := by
  simp only [weightedFunction2348, weightedExp2348, externalFamilyValue2344, if_pos hx,
    one_mul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem affine_ball2541 (z value center next : ℂ) (radius rounding : ℝ)
    (hz : ‖z‖ ≤ 1) (hvalue : ‖value - center‖ ≤ radius)
    (hround : ‖1 + z * center - next‖ ≤ rounding) :
    ‖1 + z * value - next‖ ≤ radius + rounding := by
  calc
    _ = ‖z * (value - center) + (1 + z * center - next)‖ := by congr 1; ring
    _ ≤ ‖z * (value - center)‖ + ‖1 + z * center - next‖ := norm_add_le _ _
    _ ≤ radius + rounding := by
      rw [norm_mul]
      exact add_le_add ((mul_le_mul hz hvalue (norm_nonneg _) (by norm_num)).trans_eq
        (one_mul radius)) hround

theorem horner_ball_step2541 (z center next : ℂ) (n : ℕ)
    (radius rounding : ℝ) (hn : n < 19) (hz : ‖z‖ ≤ 1)
    (hvalue : ‖expHorner2541 z n - center‖ ≤ radius)
    (hround : ‖1 + z / ((19 - n : ℕ) : ℂ) * center - next‖ ≤ rounding) :
    ‖expHorner2541 z (n + 1) - next‖ ≤ radius + rounding := by
  have hk : (1 : ℝ) ≤ ((19 - n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 19 - n)
  have hquot : ‖z / ((19 - n : ℕ) : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_one (by linarith : (0 : ℝ) < ((19 - n : ℕ) : ℝ))).mpr
    exact hz.trans hk
  exact affine_ball2541 _ _ _ _ _ _ hquot hvalue hround

theorem exp_ball_of_horner2541 (z center : ℂ) (radius : ℝ)
    (hz : ‖z‖ ≤ 1) (hvalue : ‖expHorner2541 z 19 - center‖ ≤ radius) :
    ‖Complex.exp z - center‖ ≤ (1 : ℝ) / 10 ^ 18 + radius := by
  calc
    _ = ‖(Complex.exp z - expHorner2541 z 19) + (expHorner2541 z 19 - center)‖ := by
      congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add (expHorner2541_error z hz) hvalue)

theorem square_ball2541 (value center next : ℂ) (radius magnitude rounding : ℝ)
    (hvalue : ‖value - center‖ ≤ radius) (hmagnitude : ‖center‖ ≤ magnitude)
    (hround : ‖center ^ 2 - next‖ ≤ rounding) :
    ‖value ^ 2 - next‖ ≤ radius * (2 * magnitude + radius) + rounding := by
  have he : 0 ≤ radius := (norm_nonneg _).trans hvalue
  have hsum : ‖value + center‖ ≤ 2 * magnitude + radius := by
    calc
      _ = ‖(value - center) + (center + center)‖ := by congr 1; ring
      _ ≤ ‖value - center‖ + (‖center‖ + ‖center‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ _ := by linarith
  calc
    _ = ‖(value - center) * (value + center) + (center ^ 2 - next)‖ := by congr 1; ring
    _ ≤ ‖(value - center) * (value + center)‖ + ‖center ^ 2 - next‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul hvalue hsum (norm_nonneg _) he) hround

theorem exp_square_ball2541 (z center next : ℂ) (radius magnitude rounding : ℝ)
    (hvalue : ‖Complex.exp z - center‖ ≤ radius) (hmagnitude : ‖center‖ ≤ magnitude)
    (hround : ‖center ^ 2 - next‖ ≤ rounding) :
    ‖Complex.exp (2 * z) - next‖ ≤ radius * (2 * magnitude + radius) + rounding := by
  rw [two_mul, Complex.exp_add, ← pow_two]
  exact square_ball2541 _ _ _ _ _ _ hvalue hmagnitude hround

theorem exp_scaled_square_ball2541 (z center next : ℂ) (k : ℕ)
    (radius magnitude rounding : ℝ)
    (hvalue : ‖Complex.exp ((2 : ℂ) ^ k * z) - center‖ ≤ radius)
    (hmagnitude : ‖center‖ ≤ magnitude) (hround : ‖center ^ 2 - next‖ ≤ rounding) :
    ‖Complex.exp ((2 : ℂ) ^ (k + 1) * z) - next‖ ≤
      radius * (2 * magnitude + radius) + rounding := by
  have heq : (2 : ℂ) ^ (k + 1) * z = 2 * ((2 : ℂ) ^ k * z) := by ring
  rw [heq]
  exact exp_square_ball2541 _ _ _ _ _ _ hvalue hmagnitude hround

end ConnesWeilRH.Dev
