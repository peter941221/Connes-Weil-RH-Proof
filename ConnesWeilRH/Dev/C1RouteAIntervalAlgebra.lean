import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace ConnesWeilRH.Dev

open scoped BigOperators
open Set

structure RealInterval2429 where
  lo : ℝ
  hi : ℝ

def RealInterval2429.Mem (x : ℝ) (r : RealInterval2429) : Prop :=
  r.lo ≤ x ∧ x ≤ r.hi

def RealInterval2429.mul (a b : RealInterval2429) : RealInterval2429 :=
  { lo := min (min (a.lo * b.lo) (a.lo * b.hi))
      (min (a.hi * b.lo) (a.hi * b.hi))
    hi := max (max (a.lo * b.lo) (a.lo * b.hi))
      (max (a.hi * b.lo) (a.hi * b.hi)) }

theorem RealInterval2429.mem_mul {a b : RealInterval2429} {x y : ℝ}
    (ha : a.Mem x) (hb : b.Mem y) : (a.mul b).Mem (x * y) := by
  rcases ha with ⟨hax, hxb⟩
  rcases hb with ⟨hby, hyb⟩
  have hyu : y ∈ uIcc b.lo b.hi := by
    rw [uIcc_of_le hby.le.trans hyb]
    exact hb
  have hay : a.lo * y ∈ uIcc (a.lo * b.lo) (a.lo * b.hi) := by
    have h := image_mul_const_uIcc a.lo b.lo b.hi
    have hm : y * a.lo ∈ (fun t : ℝ => t * a.lo) '' uIcc b.lo b.hi :=
      ⟨y, hyu, rfl⟩
    rw [h] at hm
    simpa [mul_comm] using hm
  have hby' : a.hi * y ∈ uIcc (a.hi * b.lo) (a.hi * b.hi) := by
    have h := image_mul_const_uIcc a.hi b.lo b.hi
    have hm : y * a.hi ∈ (fun t : ℝ => t * a.hi) '' uIcc b.lo b.hi :=
      ⟨y, hyu, rfl⟩
    rw [h] at hm
    simpa [mul_comm] using hm
  rcases mem_uIcc.mp hay with ⟨hayl, hayh⟩
  rcases mem_uIcc.mp hby' with ⟨hbyl, hbyh⟩
  by_cases hy0 : 0 ≤ y
  · have hlow : a.lo * y ≤ x * y :=
      mul_le_mul_of_nonneg_right hax hy0
    have hhigh : x * y ≤ a.hi * y :=
      mul_le_mul_of_nonneg_right hxb hy0
    constructor
    · exact (min_le_min hayl hbyl).trans (hayl.trans hlow)
    · exact hhigh.trans (max_le_max hayh hbyh)
  · have hy0' : y ≤ 0 := le_of_not_ge hy0
    have hlow : a.hi * y ≤ x * y :=
      mul_le_mul_of_nonpos_right hxb hy0'
    have hhigh : x * y ≤ a.lo * y :=
      mul_le_mul_of_nonpos_right hax hy0'
    constructor
    · exact (min_le_min hayl hbyl).trans (hbyl.trans hlow)
    · exact hhigh.trans (max_le_max hayh hbyh)

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

def ComplexRect2427.sub (a b : ComplexRect2427) : ComplexRect2427 :=
  { reLo := a.reLo - b.reHi
    reHi := a.reHi - b.reLo
    imLo := a.imLo - b.imHi
    imHi := a.imHi - b.imLo }

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

theorem ComplexRect2427.mem_sub {z w : ℂ} {a b : ComplexRect2427}
    (hz : a.Mem z) (hw : b.Mem w) : (a.sub b).Mem (z - w) := by
  rcases hz with ⟨hzrl, hzrh, hzil, hzir⟩
  rcases hw with ⟨hwrl, hwrh, hwil, hwir⟩
  constructor
  · simpa [ComplexRect2427.sub] using sub_le_sub hzrl hwrh
  constructor
  · simpa [ComplexRect2427.sub] using sub_le_sub hzrh hwrl
  constructor
  · simpa [ComplexRect2427.sub] using sub_le_sub hzil hwir
  · simpa [ComplexRect2427.sub] using sub_le_sub hzir hwil

def ComplexRect2427.scale (r : ℝ) (a : ComplexRect2427) : ComplexRect2427 :=
  { reLo := r * a.reLo
    reHi := r * a.reHi
    imLo := r * a.imLo
    imHi := r * a.imHi }

theorem ComplexRect2427.mem_scale {r : ℝ} {z : ℂ} {a : ComplexRect2427}
    (hr : 0 ≤ r) (hz : a.Mem z) : (a.scale r).Mem (r • z) := by
  rcases hz with ⟨hzrl, hzrh, hzil, hzir⟩
  constructor
  · simpa [ComplexRect2427.scale, Complex.smul_re] using
      mul_le_mul_of_nonneg_left hzrl hr
  constructor
  · simpa [ComplexRect2427.scale, Complex.smul_re] using
      mul_le_mul_of_nonneg_left hzrh hr
  constructor
  · simpa [ComplexRect2427.scale, Complex.smul_im] using
      mul_le_mul_of_nonneg_left hzil hr
  · simpa [ComplexRect2427.scale, Complex.smul_im] using
      mul_le_mul_of_nonneg_left hzir hr

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
