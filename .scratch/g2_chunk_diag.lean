import Mathlib

def epQ3 : ℕ → ℚ
  | 0 => 2 * (97 / 100)
  | 1 => 0
  | k + 2 =>
      (97 / 100) / (((k : ℚ) + 1) * (1 - (97 / 100) ^ 2) ^ (k + 1)) +
        ((2 * (k : ℚ) + 1) / (2 * ((k : ℚ) + 1))) * epQ3 (k + 1)

private theorem epQ3_step (n : ℕ) :
    epQ3 (n + 1 + 1) =
      (97 / 100) / (((n : ℚ) + 1) * (1 - (97 / 100) ^ 2) ^ (n + 1)) +
        ((2 * (n : ℚ) + 1) / (2 * ((n : ℚ) + 1))) * epQ3 (n + 1) := by
  rw [epQ3]

private theorem epQ3_at_0 : epQ3 0 = (97 / 50) := by
  norm_num [epQ3]

private theorem epQ3_at_1 : epQ3 1 = 0 := by rfl

private theorem epQ3_at_2 : epQ3 2 = (9700 / 591) := by
  show epQ3 (0 + 1 + 1) = _
  rw [epQ3_step]
  rw [epQ3_at_1]
  norm_num

private theorem epQ3_at_3 : epQ3 3 = (52799525 / 349281) := by
  show epQ3 (1 + 1 + 1) = _
  rw [epQ3_step]
  rw [epQ3_at_2]
  norm_num

private theorem chunk_1 : (∑ k ∈ Finset.range 2, epQ3 k) = (97 / 50) := by
  simp (config := { maxSteps := 20000000 }) only [Finset.sum_range_succ,
    Finset.sum_empty, epQ3_at_0, epQ3_at_1]
  norm_num (config := { maxSteps := 20000000 })

example : (∑ k ∈ Finset.range 4, epQ3 k) = (2960491507 / 17464050) := by
  show (∑ k ∈ Finset.range (2 + 2), epQ3 k) = _
  rw [Finset.sum_range_add, chunk_1]
  trace_state
  simp (config := { maxSteps := 20000000 }) only [Finset.sum_range_succ,
    Finset.sum_empty, epQ3_at_2, epQ3_at_3]
  trace_state
  norm_num (config := { maxSteps := 20000000 })
  sorry
