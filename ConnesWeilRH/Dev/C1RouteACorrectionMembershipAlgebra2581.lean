import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

namespace ConnesWeilRH.Dev

theorem coefficient_distance_of_left_inverse2581
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : E →L[ℂ] F)
    (X : F →L[ℂ] E)
    (coefficient center : E) (target : F) (residual : ℝ)
    (hleft : X.comp A = ContinuousLinearMap.id ℂ E)
    (hsolution : A coefficient = target)
    (hresidual : ‖target - A center‖ ≤ residual) :
    ‖coefficient - center‖ ≤ ‖X‖ * residual := by
  have hleft_apply (x : E) : X (A x) = x := by
    have h := congrArg (fun L : E →L[ℂ] E => L x) hleft
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h
  have hrewrite : coefficient - center = X (target - A center) := by
    calc
      coefficient - center = X (A coefficient) - X (A center) := by
        rw [hleft_apply, hleft_apply]
      _ = X (A coefficient - A center) := by rw [map_sub]
      _ = X (target - A center) := by rw [hsolution]
  rw [hrewrite]
  calc
    ‖X (target - A center)‖ ≤ ‖X‖ * ‖target - A center‖ :=
      X.le_opNorm (target - A center)
    _ ≤ ‖X‖ * residual := by
      exact mul_le_mul_of_nonneg_left hresidual (norm_nonneg X)

end ConnesWeilRH.Dev
