import ConnesWeilRH.Dev.C1RouteAAnalyticMomentSystem
import ConnesWeilRH.Dev.C1RouteACorrectionNeumann2587
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace ConnesWeilRH.Dev

noncomputable def ownerMomentOperator2588
    (modulations : Fin 30 → ℝ) (nodes : Fin 30 → ℂ) :
    (Fin 30 → ℂ) →L[ℂ] (Fin 30 → ℂ) :=
  ContinuousLinearMap.mk
    (ownerMomentMatrix2351 modulations nodes).mulVecLin
    (by fun_prop)

theorem ownerMomentOperator2588_apply
    (modulations : Fin 30 → ℝ) (nodes : Fin 30 → ℂ)
    (coefficients : Fin 30 → ℂ) :
    ownerMomentOperator2588 modulations nodes coefficients =
      Matrix.mulVec (ownerMomentMatrix2351 modulations nodes) coefficients := rfl

theorem ownerMomentMatrix_det_ne_zero_of_operator_injective2588
    (modulations : Fin 30 → ℝ) (nodes : Fin 30 → ℂ)
    (hinj : Function.Injective (ownerMomentOperator2588 modulations nodes)) :
    (ownerMomentMatrix2351 modulations nodes).det ≠ 0 := by
  have hmul : Function.Injective (Matrix.mulVec (ownerMomentMatrix2351 modulations nodes)) := by
    intro coefficients₁ coefficients₂ heq
    apply hinj
    calc
      ownerMomentOperator2588 modulations nodes coefficients₁ =
          Matrix.mulVec (ownerMomentMatrix2351 modulations nodes) coefficients₁ :=
        ownerMomentOperator2588_apply modulations nodes coefficients₁
      _ = Matrix.mulVec (ownerMomentMatrix2351 modulations nodes) coefficients₂ := heq
      _ = ownerMomentOperator2588 modulations nodes coefficients₂ :=
        (ownerMomentOperator2588_apply modulations nodes coefficients₂).symm
  have hunit : IsUnit (ownerMomentMatrix2351 modulations nodes) :=
    Matrix.mulVec_injective_iff_isUnit.mp hmul
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
end ConnesWeilRH.Dev