import Mathlib

/- RED-7 chunk probe: split-sum theorems via sum_range_add + per-index
   lemmas; validates the shifted-index unwinding inside each chunk. -/

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

private theorem epQ3_at_4 : epQ3 4 = (2096022596375 / 1238550426) := by
  show epQ3 (2 + 1 + 1) = _
  rw [epQ3_step]
  rw [epQ3_at_3]
  norm_num

private theorem epQ3_at_5 : epQ3 5 = (41690415160401125 / 1951955471376) := by
  show epQ3 (3 + 1 + 1) = _
  rw [epQ3_step]
  rw [epQ3_at_4]
  norm_num

-- chunk 1: range 2, straight unwinding
private theorem chunk_1 : (∑ k ∈ Finset.range 2, epQ3 k) = (97 / 50) := by
  simp (config := { maxSteps := 20000000 }) only [Finset.sum_range_succ,
    Finset.sum_empty, epQ3_at_0, epQ3_at_1]
  norm_num (config := { maxSteps := 20000000 })

-- chunk 2: range 4 = 2 + 2, shifted unwinding
private theorem chunk_2 : (∑ k ∈ Finset.range 4, epQ3 k) =
    (2960491507 / 17464050) := by
  show (∑ k ∈ Finset.range (2 + 2), epQ3 k) = _
  rw [Finset.sum_range_add, chunk_1]
  simp (config := { maxSteps := 20000000 }) only [Finset.sum_range_succ,
    Finset.sum_empty, epQ3_at_2, epQ3_at_3]
  norm_num (config := { maxSteps := 20000000 })

-- chunk 3: range 6 = 4 + 2, shifted unwinding
private theorem chunk_3 : (∑ k ∈ Finset.range 6, epQ3 k) =
    (1133116016779654861 / 48798886784400) := by
  show (∑ k ∈ Finset.range (4 + 2), epQ3 k) = _
  rw [Finset.sum_range_add, chunk_2]
  simp (config := { maxSteps := 20000000 }) only [Finset.sum_range_succ,
    Finset.sum_empty, epQ3_at_4, epQ3_at_5]
  norm_num (config := { maxSteps := 20000000 })
