import ConnesWeilRH.Dev.Wall14PlateauIntegrateH

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14Plateau

open MeasureTheory
open scoped Topology
open Filter Set

/-! Mid-band `[1,2]` bounds for the plateau owner.
RH NOT claimed. -/

/-- `e^{y/2}/den(y) <= e^{-y/2}/(1-e^{-2})` on `y >= 1`, via the identity
`den(y)*(e^{-y/2}) = e^{y/2} - e^{-3y/2}`. -/
lemma mid_expHalf_div_den_le (y : Real) (hy : 1 <= y) :
    Real.exp (y / 2) / den y <= Real.exp (-(y / 2)) / (1 - Real.exp (-2 : Real)) := by
  have hdenpos : 0 < den y := den_pos y (by linarith)
  have hcpos : 0 < (1 : Real) - Real.exp (-2 : Real) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  rw [div_le_iff₀ hdenpos]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ hcpos]
  have hdenid : Real.exp (-(y / 2)) * den y = Real.exp (y / 2) - Real.exp (-(3 : Real) * y / 2) := by
    unfold den
    rw [mul_sub]
    congr 1
    · rw [← Real.exp_add]
      congr 1
      ring
    · rw [← Real.exp_add]
      congr 1
      ring
  have hpower : Real.exp (-(3 : Real) * y / 2) <= Real.exp (y / 2) * Real.exp (-2 : Real) := by
    rw [← Real.exp_add]
    rw [Real.exp_le_exp]
    nlinarith
  have hx : Real.exp (y / 2) * (1 - Real.exp (-2 : Real))
      <= Real.exp (y / 2) - Real.exp (-(3 : Real) * y / 2) := by
    rw [mul_sub]; rw [mul_one]
    exact sub_le_sub_left hpower (Real.exp (y / 2))
  calc
    Real.exp (y / 2) * (1 - Real.exp (-2 : Real)) <= Real.exp (y / 2) - Real.exp (-(3 : Real) * y / 2) := hx
    _ = Real.exp (-(y / 2)) * den y := by rw [← hdenid]

/-- pointwise mid-band bound: `|g| <= 2 e^{-y/2}/(1-e^{-2}) * A`, then `e^{-y/2} <= e^{-1/2}`. -/
lemma plateauG_abs_le_midconst (y : Real) (hy1 : 1 <= y) :
    |plateauArchG y| <= (2 : Real) * (Real.exp (-1 / 2 : Real) / (1 - Real.exp (-2 : Real))) * plateauA := by
  have hgt : 0 < y := by linarith
  have hbase := plateauG_abs_le_mid y hgt

  have hA0 : (0 : Real) <= 2 * plateauA := mul_nonneg (by norm_num) (le_of_lt plateauA_pos)
  have hA : |plateauArchG y| <= (2 * plateauA) * (Real.exp (y / 2) / den y) := by
    calc
      |plateauArchG y| <= (2 : Real) * (Real.exp (y / 2) * plateauA) / den y := hbase
      _ = (2 * plateauA) * (Real.exp (y / 2) / den y) := by
        rw [mul_div_assoc]
        ring
  calc
    |plateauArchG y| <= (2 * plateauA) * (Real.exp (y / 2) / den y) := hA
    _ <= (2 * plateauA) * (Real.exp (-(y / 2)) / (1 - Real.exp (-2 : Real))) := by
      exact mul_le_mul_of_nonneg_left (mid_expHalf_div_den_le y hy1) hA0
    _ <= (2 * plateauA) * (Real.exp (-1 / 2 : Real) / (1 - Real.exp (-2 : Real))) := by
      have he : Real.exp (-(y / 2)) <= Real.exp (-1 / 2 : Real) := by
        rw [Real.exp_le_exp]
        nlinarith [hy1]
      have hc : (0 : Real) <= 1 - Real.exp (-2 : Real) :=
        le_of_lt (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he hc) hA0
    _ <= (2 : Real) * (Real.exp (-1 / 2 : Real) / (1 - Real.exp (-2 : Real))) * plateauA := by
      have hrest : (2 * plateauA) * (Real.exp (-1 / 2 : Real) / (1 - Real.exp (-2 : Real)))
          = (2 : Real) * (Real.exp (-1 / 2 : Real) / (1 - Real.exp (-2 : Real))) * plateauA := by
        ring
      exact le_of_eq hrest

end Wall14Plateau
end Dev
end Source
end ConnesWeilRH