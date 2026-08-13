import ConnesWeilRH.Source.CC20ZetaCounting

/-!
# C1XiGrowth

Task #2 of Gate 2: uniform control of the completed Riemann xi function on the
doubled Jensen circle `sphere (2 : ℂ) |2 ⋅ (T + 2)|`.

Via `CC20ZetaCounting.norm_completedRiemannXi_le_kernelMoment` it reduces to a
uniform bound for `completedRiemannXiKernelMoment σ` on the critical strip
`[0,1]`.  Everything here is unconditional: no RH, no `sorry`, no new `axiom`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiGrowth

open scoped Topology BigOperators
open CC20ZetaCounting

/-- The decisive exponential Gamma moment governing the large-`t` tail of the
completed-decided kernel: with the exponent written as `1/2 - 1` structurally
equal to the checked-in real Gamma-moment identity, `a := 1/2` and `r := π`.
This is exactly the exponential moment used to integrate the large theta-kernel
branch. -/
theorem kernelGammaMoment_halfRe :
    (∫ t : ℝ in Set.Ioi 0,
      t ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(Real.pi * t))) =
        (1 / Real.pi) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2) := by
  -- a := 1/2 gives t^(a-1) and r := π the exponential scale; exact match.
  exact integral_rpow_mul_exp_neg_mul_Ioi_eq_gamma
    (a := (1 / 2 : ℝ)) (r := Real.pi) (by norm_num) Real.pi_pos

end C1XiGrowth
end Source
end ConnesWeilRH