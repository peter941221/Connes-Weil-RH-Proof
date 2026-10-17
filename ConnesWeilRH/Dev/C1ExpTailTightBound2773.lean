import ConnesWeilRH.Dev.C1RepresentativeExpTailBound2772

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

theorem expTail_le_one_div_2402773 {y : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    expTail y ≤ (1 : ℝ) / 240 := by
  rw [expTail]
  have h20 : y ^ 20 ≤ 1 := pow_le_one₀ (n := 20) hy0 hy1
  have hcoef : (21 : ℝ) / ((((20 : ℕ).factorial : ℝ)) * 20) ≤ (1 : ℝ) / 240 := by
    norm_num
  have hp : 0 ≤ y ^ 20 := pow_nonneg hy0 20
  calc
    y ^ 20 * ((20 : ℝ) + 1) / ((((20 : ℕ).factorial : ℝ)) * 20) =
        y ^ 20 * ((21 : ℝ) / ((((20 : ℕ).factorial : ℝ)) * 20)) := by ring
    _ ≤ y ^ 20 * ((1 : ℝ) / 240) :=
      mul_le_mul_of_nonneg_left hcoef hp
    _ ≤ (1 : ℝ) / 240 := by nlinarith

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
