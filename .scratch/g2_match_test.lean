import Mathlib

def epQ : ℕ → ℚ
  | 0 => 2 * (97 / 100)
  | 1 => 0
  | k + 2 =>
      (97 / 100) / (((k : ℚ) + 1) * (1 - (97 / 100) ^ 2) ^ (k + 1)) +
        ((2 * (k : ℚ) + 1) / (2 * ((k : ℚ) + 1))) * epQ (k + 1)

-- probe 1: full simp (not only)
example : epQ 4 = (2096022596375 / 1238550426) := by
  simp [epQ]; norm_num

-- probe 2: syntactic bridge via show (2+2 form)
example : epQ 4 = (2096022596375 / 1238550426) := by
  show epQ (2 + 2) = _
  rw [epQ]
  norm_num

-- probe 3: helper equation with n+1+1 arity, then unfold through it
theorem epQ_step (n : ℕ) :
    epQ (n + 1 + 1) =
      (97 / 100) / (((n : ℚ) + 1) * (1 - (97 / 100) ^ 2) ^ (n + 1)) +
        ((2 * (n : ℚ) + 1) / (2 * ((n : ℚ) + 1))) * epQ (n + 1) := by
  rw [epQ]

example : epQ 4 = (2096022596375 / 1238550426) := by
  rw [epQ_step 2, epQ_step 1, epQ_step 0]
  norm_num

-- probe 4: decide (expected dead, Rat arithmetic)
example : epQ 4 = (2096022596375 / 1238550426) := by
  decide
