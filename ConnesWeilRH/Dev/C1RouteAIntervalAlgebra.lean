import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Real.Basic

namespace ConnesWeilRH.Dev

open scoped BigOperators
open scoped Complex.SMul
open Set

structure RealInterval2429 where
  lo : ℝ
  hi : ℝ

def RealInterval2429.Mem (x : ℝ) (r : RealInterval2429) : Prop :=
  r.lo ≤ x ∧ x ≤ r.hi

def RealInterval2429.add (a b : RealInterval2429) : RealInterval2429 :=
  { lo := a.lo + b.lo, hi := a.hi + b.hi }

theorem RealInterval2429.mem_add {a b : RealInterval2429} {x y : ℝ}
    (ha : a.Mem x) (hb : b.Mem y) : (a.add b).Mem (x + y) := by
  constructor
  · exact add_le_add ha.1 hb.1
  · exact add_le_add ha.2 hb.2

def RealInterval2429.mul (a b : RealInterval2429) : RealInterval2429 :=
  { lo := min (min (a.lo * b.lo) (a.lo * b.hi))
      (min (a.hi * b.lo) (a.hi * b.hi))
    hi := max (max (a.lo * b.lo) (a.lo * b.hi))
      (max (a.hi * b.lo) (a.hi * b.hi)) }

def RealInterval2429.sub (a b : RealInterval2429) : RealInterval2429 :=
  { lo := a.lo - b.hi, hi := a.hi - b.lo }

theorem RealInterval2429.mem_sub {a b : RealInterval2429} {x y : ℝ}
    (ha : a.Mem x) (hb : b.Mem y) : (a.sub b).Mem (x - y) := by
  constructor
  · exact sub_le_sub ha.1 hb.2
  · exact sub_le_sub ha.2 hb.1

theorem RealInterval2429.mem_mul {a b : RealInterval2429} {x y : ℝ}
    (ha : a.Mem x) (hb : b.Mem y) : (a.mul b).Mem (x * y) := by
  rcases ha with ⟨hax, hxb⟩
  rcases hb with ⟨hby, hyb⟩
  have hyu : y ∈ uIcc b.lo b.hi := by
    rw [uIcc_of_le (hby.trans hyb)]
    exact ⟨hby, hyb⟩
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
  by_cases hy0 : 0 ≤ y
  · have hlow : a.lo * y ≤ x * y :=
      mul_le_mul_of_nonneg_right hax hy0
    have hhigh : x * y ≤ a.hi * y :=
      mul_le_mul_of_nonneg_right hxb hy0
    constructor
    · exact (min_le_left _ _).trans (hay.1.trans hlow)
    · exact hhigh.trans (hby'.2.trans (le_max_right _ _))
  · have hy0' : y ≤ 0 := le_of_not_ge hy0
    have hlow : a.hi * y ≤ x * y :=
      mul_le_mul_of_nonpos_right hxb hy0'
    have hhigh : x * y ≤ a.lo * y :=
      mul_le_mul_of_nonpos_right hax hy0'
    constructor
    · exact (min_le_right _ _).trans (hby'.1.trans hlow)
    · exact hhigh.trans (hay.2.trans (le_max_left _ _))

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

def ComplexRect2427.point (z : ℂ) : ComplexRect2427 :=
  { reLo := z.re, reHi := z.re, imLo := z.im, imHi := z.im }

theorem ComplexRect2427.point_mem (z : ℂ) :
    (ComplexRect2427.point z).Mem z := by
  simp [ComplexRect2427.point, ComplexRect2427.Mem]

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

def ComplexRect2427.mul (a b : ComplexRect2427) : ComplexRect2427 :=
  let ar : RealInterval2429 := ⟨a.reLo, a.reHi⟩
  let ai : RealInterval2429 := ⟨a.imLo, a.imHi⟩
  let br : RealInterval2429 := ⟨b.reLo, b.reHi⟩
  let bi : RealInterval2429 := ⟨b.imLo, b.imHi⟩
  let rr := (ar.mul br).sub (ai.mul bi)
  let ii := (ar.mul bi).add (ai.mul br)
  { reLo := rr.lo, reHi := rr.hi, imLo := ii.lo, imHi := ii.hi }

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

theorem ComplexRect2427.mem_mul {z w : ℂ} {a b : ComplexRect2427}
    (hz : a.Mem z) (hw : b.Mem w) : (a.mul b).Mem (z * w) := by
  let ar : RealInterval2429 := ⟨a.reLo, a.reHi⟩
  let ai : RealInterval2429 := ⟨a.imLo, a.imHi⟩
  let br : RealInterval2429 := ⟨b.reLo, b.reHi⟩
  let bi : RealInterval2429 := ⟨b.imLo, b.imHi⟩
  have har : ar.Mem z.re := ⟨hz.1, hz.2.1⟩
  have hai : ai.Mem z.im := ⟨hz.2.2.1, hz.2.2.2⟩
  have hbr : br.Mem w.re := ⟨hw.1, hw.2.1⟩
  have hbi : bi.Mem w.im := ⟨hw.2.2.1, hw.2.2.2⟩
  have hrr : (ar.mul br).Mem (z.re * w.re) :=
    RealInterval2429.mem_mul har hbr
  have hii : (ai.mul bi).Mem (z.im * w.im) :=
    RealInterval2429.mem_mul hai hbi
  have hri : (ar.mul bi).Mem (z.re * w.im) :=
    RealInterval2429.mem_mul har hbi
  have hir : (ai.mul br).Mem (z.im * w.re) :=
    RealInterval2429.mem_mul hai hbr
  have hre : ((ar.mul br).sub (ai.mul bi)).Mem
      (z.re * w.re - z.im * w.im) :=
    RealInterval2429.mem_sub hrr hii
  have him : ((ar.mul bi).add (ai.mul br)).Mem
      (z.re * w.im + z.im * w.re) :=
    RealInterval2429.mem_add hri hir
  constructor
  · simpa [ComplexRect2427.mul, ar, ai, br, bi, Complex.mul_re] using hre.1
  constructor
  · simpa [ComplexRect2427.mul, ar, ai, br, bi, Complex.mul_re] using hre.2
  constructor
  · simpa [ComplexRect2427.mul, ar, ai, br, bi, Complex.mul_im] using him.1
  · simpa [ComplexRect2427.mul, ar, ai, br, bi, Complex.mul_im] using him.2

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

def ComplexRect2427.sumFinset {α : Type*}
    (rect : α → ComplexRect2427) (s : Finset α) : ComplexRect2427 :=
  { reLo := ∑ i ∈ s, (rect i).reLo
    reHi := ∑ i ∈ s, (rect i).reHi
    imLo := ∑ i ∈ s, (rect i).imLo
    imHi := ∑ i ∈ s, (rect i).imHi }

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

theorem ComplexRect2427.mem_sumFinset {α : Type*} {term : α → ℂ}
    {rect : α → ComplexRect2427} {s : Finset α}
    (hterm : ∀ i ∈ s, (rect i).Mem (term i)) :
    (ComplexRect2427.sumFinset rect s).Mem (∑ i ∈ s, term i) := by
  constructor
  · simpa [ComplexRect2427.sumFinset] using
      (Finset.sum_le_sum (s := s)
        (fun i hi => (hterm i hi).1))
  constructor
  · simpa [ComplexRect2427.sumFinset] using
      (Finset.sum_le_sum (s := s)
        (fun i hi => (hterm i hi).2.1))
  constructor
  · simpa [ComplexRect2427.sumFinset] using
      (Finset.sum_le_sum (s := s)
        (fun i hi => (hterm i hi).2.2.1))
  · simpa [ComplexRect2427.sumFinset] using
      (Finset.sum_le_sum (s := s)
        (fun i hi => (hterm i hi).2.2.2))

end ConnesWeilRH.Dev
