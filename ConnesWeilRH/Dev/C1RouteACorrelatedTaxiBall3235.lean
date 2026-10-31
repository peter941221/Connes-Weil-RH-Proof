import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

namespace ConnesWeilRH.Dev

open scoped BigOperators

def taxiNorm3235 (z : ℂ) : ℝ := |z.re| + |z.im|

structure ComplexTaxiBall3235 where
  center : ℂ
  radius : ℝ

def ComplexTaxiBall3235.Mem (z : ℂ) (ball : ComplexTaxiBall3235) : Prop :=
  0 ≤ ball.radius ∧ taxiNorm3235 (z - ball.center) ≤ ball.radius

def ComplexTaxiBall3235.point (z : ℂ) : ComplexTaxiBall3235 :=
  { center := z, radius := 0 }

theorem taxiNorm3235_nonneg (z : ℂ) : 0 ≤ taxiNorm3235 z := by
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem taxiNorm3235_add_le (z w : ℂ) :
    taxiNorm3235 (z + w) ≤ taxiNorm3235 z + taxiNorm3235 w := by
  unfold taxiNorm3235
  simp only [Complex.add_re, Complex.add_im]
  calc
    |z.re + w.re| + |z.im + w.im| ≤
        (|z.re| + |w.re|) + (|z.im| + |w.im|) :=
      add_le_add (abs_add_le z.re w.re) (abs_add_le z.im w.im)
    _ = (|z.re| + |z.im|) + (|w.re| + |w.im|) := by ring

theorem taxiNorm3235_mul_le (z w : ℂ) :
    taxiNorm3235 (z * w) ≤ taxiNorm3235 z * taxiNorm3235 w := by
  unfold taxiNorm3235
  simp only [Complex.mul_re, Complex.mul_im]
  calc
    |z.re * w.re - z.im * w.im| +
        |z.re * w.im + z.im * w.re| ≤
        (|z.re * w.re| + |z.im * w.im|) +
          (|z.re * w.im| + |z.im * w.re|) := by
            exact add_le_add
              (by
                calc
                  |z.re * w.re - z.im * w.im| =
                      |z.re * w.re + -(z.im * w.im)| := by ring_nf
                  _ ≤ |z.re * w.re| + |-(z.im * w.im)| :=
                    abs_add_le _ _
                  _ = |z.re * w.re| + |z.im * w.im| := by
                    rw [abs_neg])
              (abs_add_le (z.re * w.im) (z.im * w.re))
    _ = (|z.re| + |z.im|) * (|w.re| + |w.im|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul]
      ring

theorem ComplexTaxiBall3235.point_mem (z : ℂ) :
    (ComplexTaxiBall3235.point z).Mem z := by
  constructor
  · norm_num [ComplexTaxiBall3235.point]
  · simp [ComplexTaxiBall3235.point, taxiNorm3235]

def ComplexTaxiBall3235.add
    (a b : ComplexTaxiBall3235) : ComplexTaxiBall3235 :=
  { center := a.center + b.center
    radius := a.radius + b.radius }

theorem ComplexTaxiBall3235.mem_add {z w : ℂ}
    {a b : ComplexTaxiBall3235}
    (hz : a.Mem z) (hw : b.Mem w) :
    (a.add b).Mem (z + w) := by
  constructor
  · exact add_nonneg hz.1 hw.1
  · calc
      taxiNorm3235 (z + w - (a.center + b.center)) =
          taxiNorm3235 ((z - a.center) + (w - b.center)) := by ring_nf
      _ ≤ taxiNorm3235 (z - a.center) + taxiNorm3235 (w - b.center) :=
        taxiNorm3235_add_le _ _
      _ ≤ a.radius + b.radius := add_le_add hz.2 hw.2

noncomputable def ComplexTaxiBall3235.mul
    (a b : ComplexTaxiBall3235) : ComplexTaxiBall3235 :=
  { center := a.center * b.center
    radius := a.radius * (taxiNorm3235 b.center + b.radius) +
      taxiNorm3235 a.center * b.radius }

theorem ComplexTaxiBall3235.mem_mul {z w : ℂ}
    {a b : ComplexTaxiBall3235}
    (hz : a.Mem z) (hw : b.Mem w) :
    (a.mul b).Mem (z * w) := by
  have hwNorm : taxiNorm3235 w ≤ taxiNorm3235 b.center + b.radius := by
    calc
      taxiNorm3235 w = taxiNorm3235 ((w - b.center) + b.center) := by ring_nf
      _ ≤ taxiNorm3235 (w - b.center) + taxiNorm3235 b.center :=
        taxiNorm3235_add_le _ _
      _ ≤ b.radius + taxiNorm3235 b.center := by
        simpa [add_comm] using (add_le_add_left hw.2 (taxiNorm3235 b.center))
      _ = taxiNorm3235 b.center + b.radius := by ring
  constructor
  · exact add_nonneg
      (mul_nonneg hz.1 (add_nonneg (taxiNorm3235_nonneg _) hw.1))
      (mul_nonneg (taxiNorm3235_nonneg _) hw.1)
  calc
    taxiNorm3235 (z * w - a.center * b.center) =
        taxiNorm3235 ((z - a.center) * w + a.center * (w - b.center)) := by
          ring_nf
    _ ≤ taxiNorm3235 ((z - a.center) * w) +
        taxiNorm3235 (a.center * (w - b.center)) :=
          taxiNorm3235_add_le _ _
    _ ≤ taxiNorm3235 (z - a.center) * taxiNorm3235 w +
        taxiNorm3235 a.center * taxiNorm3235 (w - b.center) :=
          add_le_add (taxiNorm3235_mul_le _ _) (taxiNorm3235_mul_le _ _)
    _ ≤ a.radius * (taxiNorm3235 b.center + b.radius) +
        taxiNorm3235 a.center * b.radius := by
          exact add_le_add
            (calc
              taxiNorm3235 (z - a.center) * taxiNorm3235 w ≤
                  a.radius * taxiNorm3235 w :=
                mul_le_mul_of_nonneg_right hz.2 (taxiNorm3235_nonneg _)
              _ ≤ a.radius * (taxiNorm3235 b.center + b.radius) :=
                mul_le_mul_of_nonneg_left hwNorm hz.1)
            (mul_le_mul_of_nonneg_left hw.2 (taxiNorm3235_nonneg _))

noncomputable def ComplexTaxiBall3235.sumFinset {α : Type*}
    (ball : α → ComplexTaxiBall3235) (s : Finset α) : ComplexTaxiBall3235 :=
  { center := ∑ i ∈ s, (ball i).center
    radius := ∑ i ∈ s, (ball i).radius }

theorem ComplexTaxiBall3235.mem_sumFinset {α : Type*}
    {term : α → ℂ} {ball : α → ComplexTaxiBall3235}
    {s : Finset α}
    (hmem : ∀ i ∈ s, (ball i).Mem (term i)) :
    (ComplexTaxiBall3235.sumFinset ball s).Mem (∑ i ∈ s, term i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [ComplexTaxiBall3235.sumFinset, ComplexTaxiBall3235.Mem,
        taxiNorm3235]
  | @insert a s ha ih =>
      have haMem : (ball a).Mem (term a) := hmem a (by simp)
      have hsMem : (ComplexTaxiBall3235.sumFinset ball s).Mem
          (∑ i ∈ s, term i) := by
        apply ih
        intro i hi
        exact hmem i (by simp [hi])
      have hadd := ComplexTaxiBall3235.mem_add haMem hsMem
      simpa [ComplexTaxiBall3235.sumFinset, Finset.sum_insert, ha]
        using hadd

end ConnesWeilRH.Dev
