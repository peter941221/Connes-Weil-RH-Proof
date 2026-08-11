import ConnesWeilRH.Dev.Wall14PlateauIntegral

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14Plateau

open MeasureTheory
open scoped Topology
open Filter Set

lemma abs_expHalf_F_sub_A_le (y : Real) (hy : 0 <= y) :
    |Real.exp (y / 2) * plateauF y - plateauA| <= Real.exp (y / 2) * plateauA := by
  have hF_nn : 0 <= plateauF y := plateauF_nonneg y
  have hF_le : plateauF y <= plateauA := plateauF_le_A y
  have he_pos : 0 < Real.exp (y / 2) := Real.exp_pos (y / 2)
  have he_one : 1 <= Real.exp (y / 2) := Real.one_le_exp (by positivity : 0 <= y / 2)
  have hA0 : 0 <= plateauA := le_of_lt plateauA_pos
  rw [abs_le]
  constructor
  · have hA : plateauA <= plateauA * Real.exp (y / 2) := by
      calc
        plateauA = plateauA * 1 := by ring
        _ <= plateauA * Real.exp (y / 2) := (mul_le_mul_of_nonneg_left he_one hA0)
    nlinarith [mul_nonneg (le_of_lt he_pos) hF_nn]
  · have h1 : Real.exp (y / 2) * plateauF y - plateauA
          <= Real.exp (y / 2) * plateauF y := by linarith
    have h2 : Real.exp (y / 2) * plateauF y <= Real.exp (y / 2) * plateauA :=
      mul_le_mul_of_nonneg_left hF_le (le_of_lt he_pos)
    exact h1.trans h2

lemma plateauG_abs_le_mid (y : ℝ) (hy : 0 < y) :
    |plateauArchG y| <= (2 : ℝ) * (Real.exp (y / 2) * plateauA) / den y := by
  unfold plateauArchG
  rw [archimedeanNumeratorRe_eq_two_G]
  have hdp : 0 < den y := den_pos y (by linarith)
  have hy0 : 0 <= y := le_of_lt hy
  have hb : |Real.exp (y / 2) * plateauF y - plateauA| <= Real.exp (y / 2) * plateauA :=
      abs_expHalf_F_sub_A_le y hy0
  rw [abs_div]
  have hdab : |den y| = den y := abs_of_nonneg (le_of_lt hdp)
  rw [hdab]
  rw [abs_mul]
  have h2c : 0 <= (2 : ℝ) := by norm_num
  rw [abs_of_nonneg h2c]
  have hn := mul_le_mul_of_nonneg_left hb h2c
  exact div_le_div_of_nonneg_right hn (le_of_lt hdp)

end Wall14Plateau
end Dev
end Source
end ConnesWeilRH
