import ConnesWeilRH.Dev.C1RouteACompactExp2542

namespace ConnesWeilRH.Dev

theorem expHorner2541_error_tiny2620 (z : ℂ) (hz : ‖z‖ ≤ (1 : ℝ) / 1000) :
    ‖Complex.exp z - expHorner2541 z 19‖ ≤ (1 : ℝ) / 10 ^ 78 := by
  rw [expHorner2541_eq_sum]
  have hunit : ‖z‖ ≤ 1 := hz.trans (by norm_num)
  have h := Complex.exp_bound hunit (n := 20) (by norm_num)
  have hpower : ‖z‖ ^ 20 ≤ ((1 : ℝ) / 1000) ^ 20 := by gcongr
  have hfactor : 0 ≤ (21 : ℝ) * ((20 : ℕ).factorial * (20 : ℝ))⁻¹ := by positivity
  have hproduct := mul_le_mul_of_nonneg_right hpower hfactor
  apply h.trans
  apply hproduct.trans
  norm_num

def pairRound2620 (a : RatPair2542) : RatPair2542 :=
  (roundDown2542 320 a.1, roundDown2542 320 a.2)

def rounding2620 : ℚ := 1 / 2 ^ 319

theorem embedPair_round_error2620 (a : RatPair2542) :
    ‖embedPair2542 a - embedPair2542 (pairRound2620 a)‖ ≤ (rounding2620 : ℝ) := by
  have hr : |(a.1 : ℝ) - (roundDown2542 320 a.1 : ℝ)| ≤ (1 : ℝ) / 2 ^ 320 := by
    have h : ((|a.1 - roundDown2542 320 a.1| : ℚ) : ℝ) ≤
        ((1 / 2 ^ 320 : ℚ) : ℝ) := Rat.cast_le.mpr (roundDown2542_error 320 a.1)
    simpa using h
  have hi : |(a.2 : ℝ) - (roundDown2542 320 a.2 : ℝ)| ≤ (1 : ℝ) / 2 ^ 320 := by
    have h : ((|a.2 - roundDown2542 320 a.2| : ℚ) : ℝ) ≤
        ((1 / 2 ^ 320 : ℚ) : ℝ) := Rat.cast_le.mpr (roundDown2542_error 320 a.2)
    simpa using h
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  change |(a.1 : ℝ) - (roundDown2542 320 a.1 : ℝ)| +
    |(a.2 : ℝ) - (roundDown2542 320 a.2 : ℝ)| ≤ _
  have h := add_le_add hr hi
  have hsum : (1 : ℝ) / 2 ^ 320 + 1 / 2 ^ 320 = (rounding2620 : ℝ) := by
    norm_num [rounding2620]
    rw [show (320 : ℕ) = 319 + 1 from rfl, pow_succ]
    field_simp
    ring
  exact h.trans_eq hsum

def hornerRat2620 (z : RatPair2542) : ℕ → RatPair2542
  | 0 => (1, 0)
  | n + 1 => pairRound2620
      (pairAdd2542 (1, 0)
        (pairMul2542 (pairScale2542 (1 / (19 - n : ℕ)) z) (hornerRat2620 z n)))

theorem hornerRat_error2620 (z : RatPair2542) (hz : ‖embedPair2542 z‖ ≤ 1)
    (n : ℕ) (hn : n ≤ 19) :
    ‖expHorner2541 (embedPair2542 z) n - embedPair2542 (hornerRat2620 z n)‖ ≤
      (n : ℝ) * (rounding2620 : ℝ) := by
  induction n with
  | zero => simp [expHorner2541, hornerRat2620]
  | succ n ih =>
    have hi := ih (by omega)
    let value := pairAdd2542 (1, 0)
      (pairMul2542 (pairScale2542 (1 / (19 - n : ℕ)) z) (hornerRat2620 z n))
    have he : embedPair2542 value = 1 + embedPair2542 z / ((19 - n : ℕ) : ℂ) *
        embedPair2542 (hornerRat2620 z n) := by
      dsimp [value]
      rw [embedPair_add2542, embedPair_mul2542, embedPair_scale2542, embedPair_one2542]
      push_cast
      ring
    have hr := embedPair_round_error2620 value
    rw [he] at hr
    have h := horner_ball_step2541 (embedPair2542 z)
      (embedPair2542 (hornerRat2620 z n)) (embedPair2542 (hornerRat2620 z (n + 1))) n
      ((n : ℝ) * (rounding2620 : ℝ)) (rounding2620 : ℝ) (by omega) hz hi hr
    apply h.trans
    push_cast
    ring_nf
    exact le_rfl

def initialState2620 (z : RatPair2542) : RatState2542 :=
  (hornerRat2620 z 19, 1 / 10 ^ 78 + 19 * rounding2620)

def squareState2620 (state : RatState2542) : RatState2542 :=
  (pairRound2620 (pairMul2542 state.1 state.1),
    roundUp2542 400
      (state.2 * (2 * pairMagnitude2542 state.1 + state.2) + rounding2620))

def compactExp2620 (z : RatPair2542) : ℕ → RatState2542
  | 0 => initialState2620 z
  | index + 1 => squareState2620 (compactExp2620 z index)

theorem initialState_error2620 (z : RatPair2542)
    (hz : ‖embedPair2542 z‖ ≤ (1 : ℝ) / 1000) :
    ‖Complex.exp (embedPair2542 z) - embedPair2542 (initialState2620 z).1‖ ≤
      ((initialState2620 z).2 : ℝ) := by
  have hunit : ‖embedPair2542 z‖ ≤ 1 := hz.trans (by norm_num)
  have hvalue := hornerRat_error2620 z hunit 19 (by norm_num)
  have htail := expHorner2541_error_tiny2620 (embedPair2542 z) hz
  calc
    _ = ‖(Complex.exp (embedPair2542 z) - expHorner2541 (embedPair2542 z) 19) +
        (expHorner2541 (embedPair2542 z) 19 - embedPair2542 (initialState2620 z).1)‖ := by
      congr 1
      ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add htail hvalue)
    _ = _ := by norm_num [initialState2620]

theorem squareState_error2620 (state : RatState2542) (value : ℂ)
    (hvalue : ‖value - embedPair2542 state.1‖ ≤ (state.2 : ℝ)) :
    ‖value ^ 2 - embedPair2542 (squareState2620 state).1‖ ≤
      ((squareState2620 state).2 : ℝ) := by
  have hr := embedPair_round_error2620 (pairMul2542 state.1 state.1)
  rw [embedPair_mul2542, ← pow_two] at hr
  have h := square_ball2541 value (embedPair2542 state.1)
    (embedPair2542 (squareState2620 state).1) (state.2 : ℝ)
    (pairMagnitude2542 state.1 : ℝ) (rounding2620 : ℝ)
    hvalue (embedPair_magnitude2542 state.1) hr
  apply h.trans
  change (state.2 : ℝ) * (2 * (pairMagnitude2542 state.1 : ℝ) + (state.2 : ℝ)) +
    (rounding2620 : ℝ) ≤ _
  exact_mod_cast le_roundUp2542 400
    (state.2 * (2 * pairMagnitude2542 state.1 + state.2) + rounding2620)

theorem compactExp_error2620 (z : RatPair2542)
    (hz : ‖embedPair2542 z‖ ≤ (1 : ℝ) / 1000) (index : ℕ) :
    ‖Complex.exp ((2 : ℂ) ^ index * embedPair2542 z) -
      embedPair2542 (compactExp2620 z index).1‖ ≤
      ((compactExp2620 z index).2 : ℝ) := by
  induction index with
  | zero => simpa [compactExp2620] using initialState_error2620 z hz
  | succ index ih =>
    have he : Complex.exp ((2 : ℂ) ^ (index + 1) * embedPair2542 z) =
        Complex.exp ((2 : ℂ) ^ index * embedPair2542 z) ^ 2 := by
      rw [show (2 : ℂ) ^ (index + 1) * embedPair2542 z =
        2 * ((2 : ℂ) ^ index * embedPair2542 z) by ring,
        two_mul, Complex.exp_add, pow_two]
    rw [he]
    exact squareState_error2620 (compactExp2620 z index) _ ih

theorem compactExp_real_error2620 (argument : ℚ) (index : ℕ)
    (hsmall : |((argument / (2 : ℚ) ^ index : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000) :
    |Real.exp (argument : ℝ) -
      ((compactExp2620 (argument / (2 : ℚ) ^ index, 0) index).1.1 : ℝ)| ≤
      ((compactExp2620 (argument / (2 : ℚ) ^ index, 0) index).2 : ℝ) := by
  have hz : ‖embedPair2542 (argument / (2 : ℚ) ^ index, 0)‖ ≤ (1 : ℝ) / 1000 := by
    apply complex_norm_le_l1_2541
    simpa [embedPair2542] using hsmall
  have hembed : embedPair2542 (argument / (2 : ℚ) ^ index, 0) =
      ((argument / (2 : ℚ) ^ index : ℚ) : ℂ) := by
    apply Complex.ext <;> simp only [embedPair2542,
      Complex.ratCast_re, Complex.ratCast_im, Rat.cast_zero]
  have hexponent : (2 : ℂ) ^ index *
      embedPair2542 (argument / (2 : ℚ) ^ index, 0) = (argument : ℂ) := by
    rw [hembed]
    push_cast
    field_simp
  have h := compactExp_error2620 (argument / (2 : ℚ) ^ index, 0) hz index
  rw [hexponent] at h
  have hreal := (Complex.abs_re_le_norm
    (Complex.exp (argument : ℂ) -
      embedPair2542 (compactExp2620 (argument / (2 : ℚ) ^ index, 0) index).1)).trans h
  simpa [embedPair2542, Complex.exp_ofReal_re] using hreal

end ConnesWeilRH.Dev
