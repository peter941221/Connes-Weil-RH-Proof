import ConnesWeilRH.Dev.C1RouteBThetaSharpCircle2999
import ConnesWeilRH.Dev.C1RouteBThetaRealQuotientBounds3002
import ConnesWeilRH.Dev.C1RouteBThetaImagQuotientBounds3003
import ConnesWeilRH.Dev.C1RouteBArgumentRectBridge2988
import ConnesWeilRH.Dev.C1RouteBThetaDoubledArgument2992

namespace ConnesWeilRH.Dev

theorem routeBThetaArgumentRectMem3004 {δ : ℝ}
    (hδlo : Real.pi / 192 ≤ δ)
    (hδhi : δ ≤ Real.pi / 192 + Real.pi / 1024) :
    ComplexRect2427.Mem
      (routeBThetaDoubledArgument2992 (5 * Real.pi / 3 + δ))
      routeBArgumentTargetRect2988 := by
  let t := routeBThetaTCoarse2982 (5 * Real.pi / 3 + δ)
  let x : ℝ := t.re
  let y : ℝ := t.im
  let d : ℝ := (1 - x ^ 2 + y ^ 2) ^ 2 + (2 * x * y) ^ 2
  have hxy := routeBThetaTSharperCoordinates2998 hδlo hδhi
  have hcircle := routeBThetaTSharperCircle2999 hδlo hδhi
  have hd : 0 < d := by
    dsimp [d, x, y, t]
    have h := routeBThetaDoubledDenominatorLower2999
      (5 * Real.pi / 3 + δ)
    nlinarith
  have hdEq : d = ((401 : ℝ) / 400) ^ 2 - 4 * x ^ 2 := by
    exact routeBThetaQuotientDenominatorCircle3001 hcircle
  have hre := routeBThetaRealQuotientBounds3002
    (x := x) (d := d) hxy.1 hxy.2.1 hd hdEq
  have him := routeBThetaImagQuotientBounds3003
    (x := x) (y := y) (d := d)
    hxy.1 hxy.2.1 hxy.2.2.1 hxy.2.2.2 hcircle hd hdEq
  have hden : (1 - x ^ 2 + y ^ 2) ^ 2 + (2 * x * y) ^ 2 ≠ 0 := by
    nlinarith [hd]
  change routeBArgumentTargetRect2988.reLo ≤
      (routeBThetaDoubledArgument2992 (5 * Real.pi / 3 + δ)).re ∧
    (routeBThetaDoubledArgument2992 (5 * Real.pi / 3 + δ)).re ≤
      routeBArgumentTargetRect2988.reHi ∧
    routeBArgumentTargetRect2988.imLo ≤
      (routeBThetaDoubledArgument2992 (5 * Real.pi / 3 + δ)).im ∧
    (routeBThetaDoubledArgument2992 (5 * Real.pi / 3 + δ)).im ≤
      routeBArgumentTargetRect2988.imHi
  simp only [routeBArgumentTargetRect2988, ComplexRect2427.mk]
  have hre' := routeBDoubledArgumentReFormula2990 (x := x) (y := y) hden
  have him' := routeBDoubledArgumentImFormula2990 (x := x) (y := y) hden
  dsimp [routeBThetaDoubledArgument2992, routeBThetaTCoarse2982,
    x, y, t, d] at hre him hre' him'
  norm_num at hre him hre' him' ⊢
  constructor <;> nlinarith [hre.1, hre.2, him.1, him.2]

end ConnesWeilRH.Dev
