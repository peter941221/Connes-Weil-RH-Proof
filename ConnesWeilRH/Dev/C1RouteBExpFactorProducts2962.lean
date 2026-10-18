import ConnesWeilRH.Dev.C1RouteBExpTaylorRemainder2943
import ConnesWeilRH.Dev.C1RouteBDoubleATrigBounds2960
import ConnesWeilRH.Dev.C1RouteBExpRectStageConsumer2940
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBExpFactorProducts2962 {x y : ℝ}
    (hxLo : (10231836241932215 : ℝ) / 10 ^ 17 ≤ x)
    (hxHi : x ≤ (103 : ℝ) / 1000)
    (hyLo : (-1715760948859532 : ℝ) / 10 ^ 16 ≤ y)
    (hyHi : y ≤ (-1712505045774558 : ℝ) / 10 ^ 16) :
    (10914 : ℝ) / 10000 ≤ Real.exp x * Real.cos y ∧
      Real.exp x * Real.cos y ≤ (10923 : ℝ) / 10000 ∧
      (-1893 : ℝ) / 10000 ≤ Real.exp x * Real.sin y ∧
      Real.exp x * Real.sin y ≤ (-1887 : ℝ) / 10000 := by
  have hElo : (1107736 : ℝ) / 10 ^ 6 < Real.exp x := by
    exact lt_of_lt_of_le (routeBExpAtDoubledLowerEndpoint2943)
      (Real.exp_le_exp.mpr hxLo)
  have hEhi : Real.exp x < (11085 : ℝ) / 10000 := by
    exact lt_of_le_of_lt (Real.exp_le_exp.mpr hxHi)
      routeBExpAt103Over1000TightUpper2943
  have htrig := routeBDoubleATrigBounds2960 hyLo hyHi
  rcases htrig with ⟨hsLo, hsHi, hcLo, hcHi⟩
  have hElo0 : 0 ≤ Real.exp x := (Real.exp_pos x).le
  have hcLo0 : 0 ≤ Real.cos y := by linarith
  have hsLo0 : Real.sin y ≤ 0 := by linarith
  have hsHi0 : Real.sin y ≤ 0 := by linarith
  have hsLoConst : (-1707357 : ℝ) / 10 ^ 7 ≤ 0 := by norm_num
  have hsHiConst : (-1704146 : ℝ) / 10 ^ 7 ≤ 0 := by norm_num
  have hprodReLo :
      (1107736 : ℝ) / 10 ^ 6 * ((9853167 : ℝ) / 10 ^ 7) ≤
        Real.exp x * Real.cos y := by
    exact mul_le_mul (le_of_lt hElo) (le_of_lt hcLo) (by positivity) hElo0
  have hprodReHi :
      Real.exp x * Real.cos y ≤
        (11085 : ℝ) / 10000 * ((9853726 : ℝ) / 10 ^ 7) := by
    exact mul_le_mul (le_of_lt hEhi) (le_of_lt hcHi) hcLo0 (by positivity)
  have hprodImLo :
      (11085 : ℝ) / 10000 * ((-1707357 : ℝ) / 10 ^ 7) ≤
        Real.exp x * Real.sin y := by
    exact (mul_le_mul_of_nonpos_right (le_of_lt hEhi) hsLoConst).trans
      (mul_le_mul_of_nonneg_left (le_of_lt hsLo) hElo0)
  have hprodImHi :
      Real.exp x * Real.sin y ≤
        (1107736 : ℝ) / 10 ^ 6 * ((-1704146 : ℝ) / 10 ^ 7) := by
    exact (mul_le_mul_of_nonneg_left (le_of_lt hsHi) hElo0).trans
      (mul_le_mul_of_nonpos_right (le_of_lt hElo) hsHiConst)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num at hprodReLo hprodReHi hprodImLo hprodImHi ⊢ <;>
    linarith

end ConnesWeilRH.Dev
