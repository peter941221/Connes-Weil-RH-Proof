import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

namespace ConnesWeilRH.Dev

open scoped BigOperators

/- A complex norm ball keeps one shared error radius for a whole complex term.
   This is the replacement primitive for independent real/imaginary boxes. -/
structure ComplexNormBall3233 where
  center : ℂ
  radius : ℝ

def ComplexNormBall3233.Mem (z : ℂ) (ball : ComplexNormBall3233) : Prop :=
  0 ≤ ball.radius ∧ ‖z - ball.center‖ ≤ ball.radius

def ComplexNormBall3233.point (z : ℂ) : ComplexNormBall3233 :=
  { center := z, radius := 0 }

theorem ComplexNormBall3233.point_mem (z : ℂ) :
    (ComplexNormBall3233.point z).Mem z := by
  constructor
  · norm_num [ComplexNormBall3233.point]
  · simp [ComplexNormBall3233.point]

def ComplexNormBall3233.add (a b : ComplexNormBall3233) : ComplexNormBall3233 :=
  { center := a.center + b.center
    radius := a.radius + b.radius }

noncomputable def ComplexNormBall3233.ofRect (rect : ComplexRect2427) :
    ComplexNormBall3233 :=
  { center :=
      { re := (rect.reLo + rect.reHi) / 2
        im := (rect.imLo + rect.imHi) / 2 }
    radius := (rect.reHi - rect.reLo) + (rect.imHi - rect.imLo) }

theorem ComplexNormBall3233.mem_ofRect
    {rect : ComplexRect2427} {z : ℂ}
    (hre : rect.reLo ≤ rect.reHi)
    (him : rect.imLo ≤ rect.imHi)
    (hz : rect.Mem z) :
    (ComplexNormBall3233.ofRect rect).Mem z := by
  have hreHalf :
      |z.re - (rect.reLo + rect.reHi) / 2| ≤
        (rect.reHi - rect.reLo) / 2 := by
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2.1]
  have himHalf :
      |z.im - (rect.imLo + rect.imHi) / 2| ≤
        (rect.imHi - rect.imLo) / 2 := by
    rw [abs_le]
    constructor <;> linarith [hz.2.2.1, hz.2.2.2]
  have hnorm :
      ‖z - (ComplexNormBall3233.ofRect rect).center‖ ≤
        |(z - (ComplexNormBall3233.ofRect rect).center).re| +
          |(z - (ComplexNormBall3233.ofRect rect).center).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  constructor
  · exact add_nonneg (sub_nonneg.mpr hre) (sub_nonneg.mpr him)
  · calc
      ‖z - (ComplexNormBall3233.ofRect rect).center‖ ≤
          |(z - (ComplexNormBall3233.ofRect rect).center).re| +
            |(z - (ComplexNormBall3233.ofRect rect).center).im| := hnorm
      _ = |z.re - (rect.reLo + rect.reHi) / 2| +
          |z.im - (rect.imLo + rect.imHi) / 2| := by
            simp [ComplexNormBall3233.ofRect]
      _ ≤ (rect.reHi - rect.reLo) / 2 +
          (rect.imHi - rect.imLo) / 2 := add_le_add hreHalf himHalf
      _ ≤ (rect.reHi - rect.reLo) + (rect.imHi - rect.imLo) := by
        linarith [sub_nonneg.mpr hre, sub_nonneg.mpr him]

theorem ComplexNormBall3233.mem_add {z w : ℂ}
    {a b : ComplexNormBall3233}
    (hz : a.Mem z) (hw : b.Mem w) :
    (a.add b).Mem (z + w) := by
  constructor
  · exact add_nonneg hz.1 hw.1
  · calc
      ‖z + w - (a.center + b.center)‖ =
          ‖(z - a.center) + (w - b.center)‖ := by ring_nf
      _ ≤ ‖z - a.center‖ + ‖w - b.center‖ := norm_add_le _ _
      _ ≤ a.radius + b.radius := add_le_add hz.2 hw.2

noncomputable def ComplexNormBall3233.sumFinset {α : Type*}
    (ball : α → ComplexNormBall3233) (s : Finset α) : ComplexNormBall3233 :=
  { center := ∑ i ∈ s, (ball i).center
    radius := ∑ i ∈ s, (ball i).radius }

theorem ComplexNormBall3233.mem_sumFinset {α : Type*}
    {term : α → ℂ} {ball : α → ComplexNormBall3233}
    {s : Finset α}
    (hmem : ∀ i ∈ s, (ball i).Mem (term i)) :
    (ComplexNormBall3233.sumFinset ball s).Mem (∑ i ∈ s, term i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [ComplexNormBall3233.sumFinset, ComplexNormBall3233.Mem]
  | @insert a s ha ih =>
      have haMem : (ball a).Mem (term a) := hmem a (by simp)
      have hsMem : (ComplexNormBall3233.sumFinset ball s).Mem
          (∑ i ∈ s, term i) := by
        apply ih
        intro i hi
        exact hmem i (by simp [hi])
      have hadd := ComplexNormBall3233.mem_add haMem hsMem
      simpa [ComplexNormBall3233.sumFinset, Finset.sum_insert, ha]
        using hadd

theorem ComplexNormBall3233.mem_of_norm_sub_le
    {z center : ℂ} {radius : ℝ}
    (hr : 0 ≤ radius) (hz : ‖z - center‖ ≤ radius) :
    ({ center := center, radius := radius } : ComplexNormBall3233).Mem z := by
  exact ⟨hr, hz⟩

theorem ComplexNormBall3233.mem_mul
    {z w c d : ℂ} {r s : ℝ}
    (hr : 0 ≤ r)
    (hz : ‖z - c‖ ≤ r) (hw : ‖w - d‖ ≤ s) :
    ‖z * w - c * d‖ ≤ r * (‖d‖ + s) + ‖c‖ * s := by
  have hwNorm : ‖w‖ ≤ ‖d‖ + s := by
    calc
      ‖w‖ = ‖(w - d) + d‖ := by ring_nf
      _ ≤ ‖w - d‖ + ‖d‖ := norm_add_le _ _
      _ ≤ s + ‖d‖ := by
        simpa [add_comm] using (add_le_add_left hw ‖d‖)
      _ = ‖d‖ + s := by ring
  calc
    ‖z * w - c * d‖ = ‖(z - c) * w + c * (w - d)‖ := by ring_nf
    _ ≤ ‖(z - c) * w‖ + ‖c * (w - d)‖ := norm_add_le _ _
    _ = ‖z - c‖ * ‖w‖ + ‖c‖ * ‖w - d‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ r * (‖d‖ + s) + ‖c‖ * s := by
      gcongr

end ConnesWeilRH.Dev
