import ConnesWeilRH.Dev.C1RouteACompactExp2542

/-! The same rounded-Horner/squaring algorithm with 160-bit coordinates.
The base Taylor allowance is unchanged; state radii round upward at 200 bits. -/

namespace ConnesWeilRH.Dev

def pairRound2547 (a : RatPair2542) : RatPair2542 :=
  (roundDown2542 160 a.1, roundDown2542 160 a.2)

def rounding2547 : ℚ := 1 / 2 ^ 159

theorem embedPair_round_error2547 (a : RatPair2542) :
    ‖embedPair2542 a - embedPair2542 (pairRound2547 a)‖ ≤ (rounding2547 : ℝ) := by
  have hr : |(a.1 : ℝ) - (roundDown2542 160 a.1 : ℝ)| ≤ (1 : ℝ) / 2 ^ 160 := by
    have h : ((|a.1 - roundDown2542 160 a.1| : ℚ) : ℝ) ≤
        ((1 / 2 ^ 160 : ℚ) : ℝ) := Rat.cast_le.mpr (roundDown2542_error 160 a.1)
    simpa using h
  have hi : |(a.2 : ℝ) - (roundDown2542 160 a.2 : ℝ)| ≤ (1 : ℝ) / 2 ^ 160 := by
    have h : ((|a.2 - roundDown2542 160 a.2| : ℚ) : ℝ) ≤
        ((1 / 2 ^ 160 : ℚ) : ℝ) := Rat.cast_le.mpr (roundDown2542_error 160 a.2)
    simpa using h
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  change |(a.1 : ℝ) - (roundDown2542 160 a.1 : ℝ)| +
    |(a.2 : ℝ) - (roundDown2542 160 a.2 : ℝ)| ≤ _
  have h := add_le_add hr hi
  norm_num [rounding2547] at h ⊢
  exact h

def hornerRat2547 (z : RatPair2542) : ℕ → RatPair2542
  | 0 => (1, 0)
  | n + 1 => pairRound2547
      (pairAdd2542 (1, 0) (pairMul2542 (pairScale2542 (1 / (19 - n : ℕ)) z) (hornerRat2547 z n)))

theorem hornerRat_error2547 (z : RatPair2542) (hz : ‖embedPair2542 z‖ ≤ 1)
    (n : ℕ) (hn : n ≤ 19) :
    ‖expHorner2541 (embedPair2542 z) n - embedPair2542 (hornerRat2547 z n)‖ ≤
      (n : ℝ) * (rounding2547 : ℝ) := by
  induction n with
  | zero =>
    simp [expHorner2541, hornerRat2547]
  | succ n ih =>
    have hi := ih (by omega)
    let a := pairAdd2542 (1, 0)
      (pairMul2542 (pairScale2542 (1 / (19 - n : ℕ)) z) (hornerRat2547 z n))
    have he : embedPair2542 a = 1 + embedPair2542 z / ((19 - n : ℕ) : ℂ) *
        embedPair2542 (hornerRat2547 z n) := by
      dsimp [a]
      rw [embedPair_add2542, embedPair_mul2542, embedPair_scale2542, embedPair_one2542]
      push_cast
      ring
    have hr := embedPair_round_error2547 a
    rw [he] at hr
    have h := horner_ball_step2541 (embedPair2542 z)
      (embedPair2542 (hornerRat2547 z n)) (embedPair2542 (hornerRat2547 z (n + 1))) n
      ((n : ℝ) * (rounding2547 : ℝ)) (rounding2547 : ℝ) (by omega) hz hi hr
    apply h.trans
    push_cast
    ring_nf
    exact le_rfl

def initialState2547 (z : RatPair2542) : RatState2542 :=
  (hornerRat2547 z 19, 1 / 10 ^ 18 + 19 * rounding2547)

def squareState2547 (s : RatState2542) : RatState2542 :=
  (pairRound2547 (pairMul2542 s.1 s.1),
    roundUp2542 200 (s.2 * (2 * pairMagnitude2542 s.1 + s.2) + rounding2547))

def compactExp2547 (z : RatPair2542) : ℕ → RatState2542
  | 0 => initialState2547 z
  | k + 1 => squareState2547 (compactExp2547 z k)

theorem initialState_error2547 (z : RatPair2542) (hz : ‖embedPair2542 z‖ ≤ 1) :
    ‖Complex.exp (embedPair2542 z) - embedPair2542 (initialState2547 z).1‖ ≤
      ((initialState2547 z).2 : ℝ) := by
  have h := exp_ball_of_horner2541 (embedPair2542 z) (embedPair2542 (hornerRat2547 z 19))
    ((19 : ℝ) * (rounding2547 : ℝ)) hz (hornerRat_error2547 z hz 19 (by omega))
  simpa [initialState2547] using h

theorem squareState_error2547 (s : RatState2542) (value : ℂ)
    (hvalue : ‖value - embedPair2542 s.1‖ ≤ (s.2 : ℝ)) :
    ‖value ^ 2 - embedPair2542 (squareState2547 s).1‖ ≤ ((squareState2547 s).2 : ℝ) := by
  have hr := embedPair_round_error2547 (pairMul2542 s.1 s.1)
  rw [embedPair_mul2542, ← pow_two] at hr
  have h := square_ball2541 value (embedPair2542 s.1)
    (embedPair2542 (squareState2547 s).1) (s.2 : ℝ)
    (pairMagnitude2542 s.1 : ℝ) (rounding2547 : ℝ) hvalue (embedPair_magnitude2542 s.1) hr
  apply h.trans
  change (s.2 : ℝ) * (2 * (pairMagnitude2542 s.1 : ℝ) + (s.2 : ℝ)) + (rounding2547 : ℝ) ≤ _
  exact_mod_cast le_roundUp2542 200 (s.2 * (2 * pairMagnitude2542 s.1 + s.2) + rounding2547)

theorem compactExp_error2547 (z : RatPair2542) (hz : ‖embedPair2542 z‖ ≤ 1) (k : ℕ) :
    ‖Complex.exp ((2 : ℂ) ^ k * embedPair2542 z) - embedPair2542 (compactExp2547 z k).1‖ ≤
      ((compactExp2547 z k).2 : ℝ) := by
  induction k with
  | zero => simpa [compactExp2547] using initialState_error2547 z hz
  | succ k ih =>
    have he : Complex.exp ((2 : ℂ) ^ (k + 1) * embedPair2542 z) =
        Complex.exp ((2 : ℂ) ^ k * embedPair2542 z) ^ 2 := by
      rw [show (2 : ℂ) ^ (k + 1) * embedPair2542 z =
        2 * ((2 : ℂ) ^ k * embedPair2542 z) by ring, two_mul, Complex.exp_add, pow_two]
    rw [he]
    exact squareState_error2547 (compactExp2547 z k) _ ih

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.embedPair_round_error2547
#print axioms ConnesWeilRH.Dev.hornerRat_error2547
#print axioms ConnesWeilRH.Dev.squareState_error2547
#print axioms ConnesWeilRH.Dev.compactExp_error2547
