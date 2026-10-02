import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace ConnesWeilRH.Dev

open scoped BigOperators

/-- A closed axis-aligned rectangle in `ℂ`, used only as the logical target of
the directed interval evaluator.  The numerical construction of its endpoints
is deliberately outside this file. -/
structure ComplexRect2427 where
  reLo : ℝ
  reHi : ℝ
  imLo : ℝ
  imHi : ℝ

def ComplexRect2427.Mem (z : ℂ) (r : ComplexRect2427) : Prop :=
  r.reLo ≤ z.re ∧ z.re ≤ r.reHi ∧
  r.imLo ≤ z.im ∧ z.im ≤ r.imHi

def ComplexRect2427.add (a b : ComplexRect2427) : ComplexRect2427 :=
  { reLo := a.reLo + b.reLo
    reHi := a.reHi + b.reHi
    imLo := a.imLo + b.imLo
    imHi := a.imHi + b.imHi }

theorem ComplexRect2427.mem_add {z w : ℂ} {a b : ComplexRect2427}
    (hz : a.Mem z) (hw : b.Mem w) : (a.add b).Mem (z + w) := by
  rcases hz with ⟨hzrl, hzrh, hzil, hzir⟩
  rcases hw with ⟨hwrl, hwrh, hwil, hwir⟩
  constructor
  · simpa [ComplexRect2427.add] using add_le_add hzrl hwrl
  constructor
  · simpa [ComplexRect2427.add] using add_le_add hzrh hwrh
  constructor
  · simpa [ComplexRect2427.add] using add_le_add hzil hwil
  · simpa [ComplexRect2427.add] using add_le_add hzir hwir

def ComplexRect2427.zero : ComplexRect2427 :=
  { reLo := 0, reHi := 0, imLo := 0, imHi := 0 }

def ComplexRect2427.sum (rect : ℕ → ComplexRect2427) (n : ℕ) : ComplexRect2427 :=
  { reLo := ∑ i ∈ Finset.range n, (rect i).reLo
    reHi := ∑ i ∈ Finset.range n, (rect i).reHi
    imLo := ∑ i ∈ Finset.range n, (rect i).imLo
    imHi := ∑ i ∈ Finset.range n, (rect i).imHi }

theorem ComplexRect2427.mem_sum {term : ℕ → ℂ}
    {rect : ℕ → ComplexRect2427} {n : ℕ}
    (hterm : ∀ i < n, (rect i).Mem (term i)) :
    (ComplexRect2427.sum rect n).Mem (∑ i ∈ Finset.range n, term i) := by
  constructor
  · simpa [ComplexRect2427.sum] using
      (Finset.sum_le_sum (s := Finset.range n)
        (fun i hi => (hterm i (Finset.mem_range.mp hi)).1))
  constructor
  · simpa [ComplexRect2427.sum] using
      (Finset.sum_le_sum (s := Finset.range n)
        (fun i hi => (hterm i (Finset.mem_range.mp hi)).2.1))
  constructor
  · simpa [ComplexRect2427.sum] using
      (Finset.sum_le_sum (s := Finset.range n)
        (fun i hi => (hterm i (Finset.mem_range.mp hi)).2.2.1))
  · simpa [ComplexRect2427.sum] using
      (Finset.sum_le_sum (s := Finset.range n)
        (fun i hi => (hterm i (Finset.mem_range.mp hi)).2.2.2))

end ConnesWeilRH.Dev
