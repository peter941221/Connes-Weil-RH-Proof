import Mathlib.Tactic.Ring

namespace ConnesWeilRH.Dev

def chunkValue2629 : List ℕ → ℕ
  | [] => 0
  | digit :: tail => digit + 1000000000 * chunkValue2629 tail

theorem chunkValue2629_append (left right : List ℕ) :
    chunkValue2629 (left ++ right) =
      chunkValue2629 left + 1000000000 ^ left.length * chunkValue2629 right := by
  induction left with
  | nil => simp [chunkValue2629]
  | cons head tail ih =>
      simp only [List.cons_append, chunkValue2629, List.length_cons, pow_succ]
      rw [ih]
      ring

theorem chunkValue2629_singleton (digit : ℕ) :
    chunkValue2629 [digit] = digit := by
  simp [chunkValue2629]

theorem chunkValue2629_block_assembly
    (left right : List ℕ) (leftValue rightValue productValue : ℕ)
    (hleft : leftValue = chunkValue2629 left)
    (hright : rightValue = chunkValue2629 right)
    (hproduct : productValue = leftValue * rightValue) :
    productValue = chunkValue2629 left * chunkValue2629 right := by
  rw [hproduct, hleft, hright]

/-
  A local carry row is the small exact identity used by the chunked integer
  certificate. Keeping this theorem independent of panel data lets the large
  certificate use small block products instead of one giant reflected multiplication.
-/
theorem weightedCarryRow2629 (base digit carry exponent : ℕ) :
    (digit + base * carry) * base ^ exponent =
      digit * base ^ exponent + carry * base ^ (exponent + 1) := by
  rw [pow_succ]
  ring

theorem twoCarryAssembly2629
    (base raw0 raw1 digit0 digit1 carry1 carry2 : ℤ)
    (h0 : raw0 = digit0 + base * carry1)
    (h1 : raw1 + carry1 = digit1 + base * carry2) :
    raw0 + raw1 * base = digit0 + digit1 * base + carry2 * base ^ 2 := by
  calc
    raw0 + raw1 * base = (digit0 + base * carry1) + raw1 * base := by rw [h0]
    _ = digit0 + (raw1 + carry1) * base := by ring
    _ = digit0 + (digit1 + base * carry2) * base := by rw [h1]
    _ = digit0 + digit1 * base + carry2 * base ^ 2 := by ring

example :
    (37 + 10^9 * 12) * (10^9)^3 =
      37 * (10^9)^3 + 12 * (10^9)^4 := by
  exact weightedCarryRow2629 (10^9) 37 12 3

example :
    12000000037 + 999999999 * (10^9 : ℤ) =
      37 + 11 * (10^9 : ℤ) + 1 * (10^9 : ℤ)^2 := by
  apply twoCarryAssembly2629 (10^9 : ℤ) 12000000037 999999999 37 11 12 1
  · norm_num
  · norm_num

end ConnesWeilRH.Dev
