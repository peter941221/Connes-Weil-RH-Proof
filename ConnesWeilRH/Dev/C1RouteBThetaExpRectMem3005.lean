import ConnesWeilRH.Dev.C1RouteBThetaArgumentRectMem3004
import ConnesWeilRH.Dev.C1RouteBExpRectMembership2963

namespace ConnesWeilRH.Dev

theorem routeBThetaExpRectMem3005 {δ : ℝ}
    (hδlo : Real.pi / 192 ≤ δ)
    (hδhi : δ ≤ Real.pi / 192 + Real.pi / 1024) :
    ComplexRect2427.Mem
      (Complex.exp
        (routeBThetaDoubledArgument2992 (5 * Real.pi / 3 + δ)))
      routeBLocalStageExpRect2907 := by
  have hz := routeBThetaArgumentRectMem3004 hδlo hδhi
  change routeBArgumentTargetRect2988.reLo ≤
      (routeBThetaDoubledArgument2992 (5 * Real.pi / 3 + δ)).re ∧
    (routeBThetaDoubledArgument2992 (5 * Real.pi / 3 + δ)).re ≤
      routeBArgumentTargetRect2988.reHi ∧
    routeBArgumentTargetRect2988.imLo ≤
      (routeBThetaDoubledArgument2992 (5 * Real.pi / 3 + δ)).im ∧
    (routeBThetaDoubledArgument2992 (5 * Real.pi / 3 + δ)).im ≤
      routeBArgumentTargetRect2988.imHi at hz
  exact routeBSubcellExpRectMembership2963 hz.1 hz.2.1 hz.2.2.1 hz.2.2.2

end ConnesWeilRH.Dev
