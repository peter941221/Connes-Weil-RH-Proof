import ConnesWeilRH.Dev.C1RouteBSmallAngleSinEndpoint2953
import ConnesWeilRH.Dev.C1RouteBSmallAngleCosEndpoint2954
import ConnesWeilRH.Dev.C1RouteBSmallAngleSinEndpoint2956
import ConnesWeilRH.Dev.C1RouteBSmallAngleCosEndpoint2957
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBDoubleATrigBounds2960 {y : ℝ}
    (hyLo : (-1715760948859532 : ℝ) / 10 ^ 16 ≤ y)
    (hyHi : y ≤ (-1712505045774558 : ℝ) / 10 ^ 16) :
    (-1707357 : ℝ) / 10 ^ 7 < Real.sin y ∧
      Real.sin y < (-1704146 : ℝ) / 10 ^ 7 ∧
      (9853167 : ℝ) / 10 ^ 7 < Real.cos y ∧
      Real.cos y < (9853726 : ℝ) / 10 ^ 7 := by
  norm_num at hyLo hyHi
  have huLo : (1712505045774558 : ℝ) / 10 ^ 16 ≤ -y := by linarith
  have huHi : -y ≤ (1715760948859532 : ℝ) / 10 ^ 16 := by linarith
  have hpi : (1715760948859532 : ℝ) / 10 ^ 16 ≤ Real.pi / 2 := by
    have hp := Real.pi_gt_d20
    norm_num
    nlinarith
  have hslo : Real.sin ((1712505045774558 : ℝ) / 10 ^ 16) ≤ Real.sin (-y) := by
    apply Real.monotoneOn_sin
    · constructor <;> nlinarith [Real.pi_gt_d20]
    · constructor <;> nlinarith [Real.pi_gt_d20]
    · exact huLo
  have hshi : Real.sin (-y) ≤ Real.sin ((1715760948859532 : ℝ) / 10 ^ 16) := by
    apply Real.monotoneOn_sin
    · constructor <;> nlinarith [Real.pi_gt_d20]
    · constructor <;> nlinarith [Real.pi_gt_d20]
    · exact huHi
  have hclo : Real.cos ((1715760948859532 : ℝ) / 10 ^ 16) ≤ Real.cos (-y) := by
    apply Real.antitoneOn_cos
    · constructor <;> nlinarith [Real.pi_gt_d20]
    · constructor <;> nlinarith [Real.pi_gt_d20]
    · exact huHi
  have hchi : Real.cos (-y) ≤ Real.cos ((1712505045774558 : ℝ) / 10 ^ 16) := by
    apply Real.antitoneOn_cos
    · constructor <;> nlinarith [Real.pi_gt_d20]
    · constructor <;> nlinarith [Real.pi_gt_d20]
    · exact huLo
  have hsinEq : Real.sin y = -Real.sin (-y) := by
    rw [Real.sin_neg]
    ring
  have hcosEq : Real.cos y = Real.cos (-y) := by
    rw [Real.cos_neg]
  rw [hsinEq, hcosEq]
  have hsl := routeBSmallAngleSinEndpoint2953.1
  have hsu := routeBSmallAngleSinEndpoint2956.2
  have hcl := routeBSmallAngleCosEndpoint2957.1
  have hcu := routeBSmallAngleCosEndpoint2954.2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

end ConnesWeilRH.Dev
