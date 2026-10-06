import ConnesWeilRH.Dev.C1RouteACorrectionAnalyticIntervals2597

namespace ConnesWeilRH.Dev

open scoped BigOperators Matrix

noncomputable def matrixProductInterval2598
    (xRect aRect : Matrix (Fin 30) (Fin 30) ComplexRect2427)
    (i j : Fin 30) : ComplexRect2427 :=
  ComplexRect2427.sumFinset
    (fun k => (xRect i k).mul (aRect k j)) Finset.univ

noncomputable def matrixDefectInterval2598
    (xRect aRect : Matrix (Fin 30) (Fin 30) ComplexRect2427)
    (i j : Fin 30) : ComplexRect2427 :=
  (ComplexRect2427.point (if i = j then (1 : ℂ) else 0)).sub
    (matrixProductInterval2598 xRect aRect i j)

noncomputable def matrixDefectEntry2598
    (x a : Matrix (Fin 30) (Fin 30) ℂ) (i j : Fin 30) : ℂ :=
  (if i = j then (1 : ℂ) else 0) - ∑ k : Fin 30, x i k * a k j

theorem matrixDefectInterval2598_mem
    (x a : Matrix (Fin 30) (Fin 30) ℂ)
    (xRect aRect : Matrix (Fin 30) (Fin 30) ComplexRect2427)
    (hx : ∀ i k : Fin 30, (xRect i k).Mem (x i k))
    (ha : ∀ k j : Fin 30, (aRect k j).Mem (a k j))
    (i j : Fin 30) :
    (matrixDefectInterval2598 xRect aRect i j).Mem
      (matrixDefectEntry2598 x a i j) := by
  have hterms : ∀ k : Fin 30,
      ((xRect i k).mul (aRect k j)).Mem (x i k * a k j) := by
    intro k
    exact ComplexRect2427.mem_mul (hx i k) (ha k j)
  have hsum :
      (matrixProductInterval2598 xRect aRect i j).Mem
        (∑ k : Fin 30, x i k * a k j) := by
    simpa [matrixProductInterval2598] using
      (ComplexRect2427.mem_sumFinset (s := (Finset.univ : Finset (Fin 30)))
        (term := fun k : Fin 30 => x i k * a k j)
        (rect := fun k : Fin 30 => (xRect i k).mul (aRect k j))
        (fun k _ => hterms k))
  have hone :
      (ComplexRect2427.point (if i = j then (1 : ℂ) else 0)).Mem
        (if i = j then (1 : ℂ) else 0) :=
    ComplexRect2427.point_mem _
  simpa [matrixDefectInterval2598, matrixDefectEntry2598] using
    (ComplexRect2427.mem_sub hone hsum)


def rectL1Upper2598 (r : ComplexRect2427) : NNReal :=
  ⟨max |r.reLo| |r.reHi| + max |r.imLo| |r.imHi|, by positivity⟩

theorem norm_le_rectL1Upper2598
    {z : ℂ} {r : ComplexRect2427} (hz : r.Mem z) :
    ‖z‖₊ ≤ rectL1Upper2598 r := by
  have hre : |z.re| ≤ max |r.reLo| |r.reHi| := by
    apply (abs_le).2
    constructor
    · calc
        -max |r.reLo| |r.reHi| ≤ -|r.reLo| :=
          neg_le_neg (le_max_left _ _)
        _ ≤ r.reLo := neg_abs_le _
        _ ≤ z.re := hz.1
    · calc
        z.re ≤ r.reHi := hz.2.1
        _ ≤ |r.reHi| := le_abs_self _
        _ ≤ max |r.reLo| |r.reHi| := le_max_right _ _
  have him : |z.im| ≤ max |r.imLo| |r.imHi| := by
    apply (abs_le).2
    constructor
    · calc
        -max |r.imLo| |r.imHi| ≤ -|r.imLo| :=
          neg_le_neg (le_max_left _ _)
        _ ≤ r.imLo := neg_abs_le _
        _ ≤ z.im := hz.2.2.1
    · calc
        z.im ≤ r.imHi := hz.2.2.2
        _ ≤ |r.imHi| := le_abs_self _
        _ ≤ max |r.imLo| |r.imHi| := le_max_right _ _
  have hnorm : ‖z‖ ≤
      max |r.reLo| |r.reHi| + max |r.imLo| |r.imHi| :=
    (Complex.norm_le_abs_re_add_abs_im z).trans
      (add_le_add hre him)
  exact_mod_cast hnorm
end ConnesWeilRH.Dev

