import ConnesWeilRH.Dev._2

namespace ConnesWeilRH.Source.Dev.Wall14Plateau

open MeasureTheory Filter Set
open scoped Topology Interval

/-- change of variable `u ↦ -u` on an interval. -/
lemma neg_sub (F : ℝ → ℝ) (a b : ℝ) :
    (∫ u in a..b, F u) = ∫ u in -b..-a, F (-u) := by
  have hA : (∫ x in (-b)..(-a), F (-x)) = -∫ x in b..a, F x := by
    have hc : ((-1 : ℝ) : ℝ) ≠ 0 := by norm_num
    have h := intervalIntegral.integral_comp_mul_left (f := F) (c := (-1 : ℝ)) (a := (-b : ℝ)) (b := (-a : ℝ)) hc
    -- h : ∫ x in (-b)..(-a), F (x * -1) = (-1)⁻¹ • ∫ x in (-1)*(-b)..(-1)*(-a), F x
    simpa using h
  calc
    (∫ x in a..b, F x) = -(-(∫ x in a..b, F x)) := by ring
    _ = -∫ x in b..a, F x := by rw [intervalIntegral.integral_symm]
    _ = ∫ x in -b..-a, F (-x) := by rw [hA]

/-- the negative band piece rewrites into the `(9/10,1)` folded form. -/
lemma bb_neg_piece (x : ℝ) :
    (∫ u in (-1)..(-(9/10 : ℝ)), bb x u)
        = (∫ u in (9/10)..(1), bumpReal (x + u) * (-(bd u))) := by
  rw [neg_sub (bb x) (-1) (-(9/10 : ℝ))]
  congr 2
  funext n
  -- bb x (-n) = bumpReal(x + n) * (-bd n)
  unfold bb
  rw [bd_neg]
  ring

/-- pairing: the derivative is the folded band integral. -/
theorem bumpF_pairing (x : ℝ) :
    bumpFderiv x = ∫ u in (9/10)..1, (bumpReal (x - u) - bumpReal (x + u)) * bd u := by
  calc
    bumpFderiv x = ∫ u : ℝ, bb x u := by
      rw [bumpFderiv_custom_sub]
      rfl
    _ = ∫ u in (-2)..2, bb x u := bb_integral_reduce x
    _ = ∫ u in (-1)..(-(9/10 : ℝ)), bb x u + ∫ u in (9/10)..1, bb x u := bb_two_band x
    _ = (∫ u in (9/10)..1, bumpReal (x + u) * (-(bd u)))
        + ∫ u in (9/10)..1, (bumpReal (x - u) * bd u) := by
      rw [bb_neg_piece x]
    _ = ∫ u in (9/10)..1, (bumpReal (x - u) - bumpReal (x + u)) * bd u := by
      congr 1
      funext u
      ring

end ConnesWeilRH.Source.Dev.Wall14Plateau
