import ConnesWeilRH.Dev.C1RouteAComplexExpBall2541
import Mathlib.Data.Rat.Floor

/-! Computable rational Horner / squaring with a proved analytic error bound.
The rounding program replaces per - step stored witnesses; all arithmetic is exact. -/

namespace ConnesWeilRH.Dev

def roundDown2542 (bits : ℕ) (q : ℚ) : ℚ :=
  (⌊q * (2 : ℚ) ^ bits⌋ : ℚ) / (2 : ℚ) ^ bits

def roundUp2542 (bits : ℕ) (q : ℚ) : ℚ := -roundDown2542 bits (-q)

theorem roundDown2542_le (bits : ℕ) (q : ℚ) : roundDown2542 bits q ≤ q := by
  exact (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ bits)).mpr (Int.floor_le _)

theorem roundDown2542_error (bits : ℕ) (q : ℚ) :
    |q - roundDown2542 bits q| ≤ (1 : ℚ) / 2 ^ bits := by
  rw [abs_of_nonneg (sub_nonneg.mpr (roundDown2542_le bits q))]
  have ht := Int.lt_floor_add_one (q * (2 : ℚ) ^ bits)
  calc
    _ = (q * (2 : ℚ) ^ bits - (⌊q * (2 : ℚ) ^ bits⌋ : ℚ)) / (2 : ℚ) ^ bits := by
      unfold roundDown2542
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem le_roundUp2542 (bits : ℕ) (q : ℚ) : q ≤ roundUp2542 bits q := by
  have h := roundDown2542_le bits (-q)
  unfold roundUp2542
  linarith

abbrev RatPair2542 := ℚ × ℚ
abbrev RatState2542 := RatPair2542 × ℚ

def pairAdd2542 (a b : RatPair2542) : RatPair2542 := (a.1 + b.1, a.2 + b.2)
def pairMul2542 (a b : RatPair2542) : RatPair2542 :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)
def pairScale2542 (q : ℚ) (a : RatPair2542) : RatPair2542 := (q * a.1, q * a.2)
def pairRound2542 (a : RatPair2542) : RatPair2542 :=
  (roundDown2542 100 a.1, roundDown2542 100 a.2)
def pairMagnitude2542 (a : RatPair2542) : ℚ := |a.1|+|a.2|
def rounding2542 : ℚ := 1 / 2 ^ 99

noncomputable def embedPair2542 (a : RatPair2542) : ℂ := ⟨(a.1 : ℝ),(a.2 : ℝ)⟩

@[simp] theorem embedPair_one2542 : embedPair2542 (1, 0) = 1 := by
  apply Complex.ext <;> norm_num [embedPair2542]

theorem embedPair_add2542 (a b : RatPair2542) :
    embedPair2542 (pairAdd2542 a b) = embedPair2542 a + embedPair2542 b := by
  apply Complex.ext <;> simp [embedPair2542, pairAdd2542]

theorem embedPair_mul2542 (a b : RatPair2542) :
    embedPair2542 (pairMul2542 a b) = embedPair2542 a * embedPair2542 b := by
  apply Complex.ext <;> simp [embedPair2542, pairMul2542, Complex.mul_re, Complex.mul_im]

theorem embedPair_scale2542 (q : ℚ) (a : RatPair2542) :
    embedPair2542 (pairScale2542 q a) = (q : ℂ) * embedPair2542 a := by
  apply Complex.ext <;> simp [embedPair2542, pairScale2542, Complex.mul_re, Complex.mul_im]

theorem embedPair_magnitude2542 (a : RatPair2542) :
    ‖embedPair2542 a‖ ≤ (pairMagnitude2542 a : ℝ) := by
  simpa [embedPair2542, pairMagnitude2542] using
    Complex.norm_le_abs_re_add_abs_im (embedPair2542 a)

theorem embedPair_round_error2542 (a : RatPair2542) :
    ‖embedPair2542 a - embedPair2542 (pairRound2542 a)‖ ≤ (rounding2542 : ℝ) := by
  have hr : |(a.1 : ℝ) - (roundDown2542 100 a.1 : ℝ)| ≤ (1 : ℝ) / 2 ^ 100 := by
    have h : ((|a.1 - roundDown2542 100 a.1| : ℚ) : ℝ) ≤
        ((1 / 2 ^ 100 : ℚ) : ℝ) := Rat.cast_le.mpr (roundDown2542_error 100 a.1)
    simpa using h
  have hi : |(a.2 : ℝ) - (roundDown2542 100 a.2 : ℝ)| ≤ (1 : ℝ) / 2 ^ 100 := by
    have h : ((|a.2 - roundDown2542 100 a.2| : ℚ) : ℝ) ≤
        ((1 / 2 ^ 100 : ℚ) : ℝ) := Rat.cast_le.mpr (roundDown2542_error 100 a.2)
    simpa using h
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  change |(a.1 : ℝ) - (roundDown2542 100 a.1 : ℝ)| +
    |(a.2 : ℝ) - (roundDown2542 100 a.2 : ℝ)| ≤ _
  have h := add_le_add hr hi
  norm_num [rounding2542] at h ⊢
  exact h

def hornerRat2542 (z : RatPair2542) : ℕ → RatPair2542
  | 0 => (1, 0)
  | n + 1 => pairRound2542
      (pairAdd2542 (1, 0) (pairMul2542 (pairScale2542 (1 / (19 - n : ℕ)) z) (hornerRat2542 z n)))

theorem hornerRat_error2542 (z : RatPair2542) (hz : ‖embedPair2542 z‖ ≤ 1)
    (n : ℕ) (hn : n ≤ 19) :
    ‖expHorner2541 (embedPair2542 z) n - embedPair2542 (hornerRat2542 z n)‖ ≤
      (n : ℝ) * (rounding2542 : ℝ) := by
  induction n with
  | zero =>
    simp [expHorner2541, hornerRat2542]
  | succ n ih =>
    have hi := ih (by omega)
    let a := pairAdd2542 (1, 0)
      (pairMul2542 (pairScale2542 (1 / (19 - n : ℕ)) z) (hornerRat2542 z n))
    have he : embedPair2542 a = 1 + embedPair2542 z / ((19 - n : ℕ) : ℂ) *
        embedPair2542 (hornerRat2542 z n) := by
      dsimp [a]
      rw [embedPair_add2542, embedPair_mul2542, embedPair_scale2542, embedPair_one2542]
      push_cast
      ring
    have hr := embedPair_round_error2542 a
    rw [he] at hr
    have h := horner_ball_step2541 (embedPair2542 z)
      (embedPair2542 (hornerRat2542 z n)) (embedPair2542 (hornerRat2542 z (n + 1))) n
      ((n : ℝ) * (rounding2542 : ℝ)) (rounding2542 : ℝ) (by omega) hz hi hr
    apply h.trans
    push_cast
    ring_nf
    exact le_rfl

def initialState2542 (z : RatPair2542) : RatState2542 :=
  (hornerRat2542 z 19, 1 / 10 ^ 18 + 19 * rounding2542)

def squareState2542 (s : RatState2542) : RatState2542 :=
  (pairRound2542 (pairMul2542 s.1 s.1),
    roundUp2542 140 (s.2 * (2 * pairMagnitude2542 s.1 + s.2) + rounding2542))

def compactExp2542 (z : RatPair2542) : ℕ → RatState2542
  | 0 => initialState2542 z
  | k + 1 => squareState2542 (compactExp2542 z k)

theorem initialState_error2542 (z : RatPair2542) (hz : ‖embedPair2542 z‖ ≤ 1) :
    ‖Complex.exp (embedPair2542 z) - embedPair2542 (initialState2542 z).1‖ ≤
      ((initialState2542 z).2 : ℝ) := by
  have h := exp_ball_of_horner2541 (embedPair2542 z) (embedPair2542 (hornerRat2542 z 19))
    ((19 : ℝ) * (rounding2542 : ℝ)) hz (hornerRat_error2542 z hz 19 (by omega))
  simpa [initialState2542] using h

theorem squareState_error2542 (s : RatState2542) (value : ℂ)
    (hvalue : ‖value - embedPair2542 s.1‖ ≤ (s.2 : ℝ)) :
    ‖value ^ 2 - embedPair2542 (squareState2542 s).1‖ ≤ ((squareState2542 s).2 : ℝ) := by
  have hr := embedPair_round_error2542 (pairMul2542 s.1 s.1)
  rw [embedPair_mul2542, ← pow_two] at hr
  have h := square_ball2541 value (embedPair2542 s.1)
    (embedPair2542 (squareState2542 s).1) (s.2 : ℝ)
    (pairMagnitude2542 s.1 : ℝ) (rounding2542 : ℝ) hvalue (embedPair_magnitude2542 s.1) hr
  apply h.trans
  change (s.2 : ℝ) * (2 * (pairMagnitude2542 s.1 : ℝ) + (s.2 : ℝ)) + (rounding2542 : ℝ) ≤ _
  exact_mod_cast le_roundUp2542 140 (s.2 * (2 * pairMagnitude2542 s.1 + s.2) + rounding2542)

theorem compactExp_error2542 (z : RatPair2542) (hz : ‖embedPair2542 z‖ ≤ 1) (k : ℕ) :
    ‖Complex.exp ((2 : ℂ) ^ k * embedPair2542 z) - embedPair2542 (compactExp2542 z k).1‖ ≤
      ((compactExp2542 z k).2 : ℝ) := by
  induction k with
  | zero => simpa [compactExp2542] using initialState_error2542 z hz
  | succ k ih =>
    have he : Complex.exp ((2 : ℂ) ^ (k + 1) * embedPair2542 z) =
        Complex.exp ((2 : ℂ) ^ k * embedPair2542 z) ^ 2 := by
      rw [show (2 : ℂ) ^ (k + 1) * embedPair2542 z =
        2 * ((2 : ℂ) ^ k * embedPair2542 z) by ring, two_mul, Complex.exp_add, pow_two]
    rw [he]
    exact squareState_error2542 (compactExp2542 z k) _ ih

end ConnesWeilRH.Dev
