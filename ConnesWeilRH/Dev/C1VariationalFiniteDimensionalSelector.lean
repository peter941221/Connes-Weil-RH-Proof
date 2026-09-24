import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace ConnesWeilRH
namespace Source
namespace C1VariationalFiniteDimensionalSelector

noncomputable section

/-!
# C1VariationalFiniteDimensionalSelector

This leaf proves the non-circular variational core needed by a future physical
selector: in a finite-dimensional Hilbert interpolation space, every affine
fiber of a linear map has a minimum-norm representative.  It does not encode
the Weil gate or its desired sign.
-/

theorem exists_min_norm_preimage
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →ₗ[ℂ] F) (x : E) :
    ∃ z : E, L z = L x ∧
      ∀ w : E, L w = L x → ‖z‖ ≤ ‖w‖ := by
  let K : Submodule ℂ E := LinearMap.ker L
  obtain ⟨v, hvK, hvmin⟩ :=
    K.exists_norm_eq_iInf_of_complete_subspace
      (Submodule.complete_of_finiteDimensional K) (-x)
  refine ⟨x + v, ?_, ?_⟩
  · change L (x + v) = L x
    rw [map_add]
    have hv0 : L v = 0 := hvK
    rw [hv0, add_zero]
  · intro w hw
    have hwK : w - x ∈ K := by
      change L (w - x) = 0
      rw [map_sub, hw, sub_self]
    have hle : ‖(-x) - v‖ ≤ ‖(-x) - (w - x)‖ := by
      rw [hvmin]
      exact ciInf_le
        (show BddBelow (Set.range (fun q : (K : Set E) => ‖(-x) - q‖)) from
          ⟨0, by
            rintro _ ⟨q, rfl⟩
            exact norm_nonneg _⟩)
        ⟨w - x, hwK⟩
    calc
      ‖x + v‖ = ‖(-x) - v‖ := by
        rw [show (-x) - v = -(x + v) by abel, norm_neg]
      _ ≤ ‖(-x) - (w - x)‖ := hle
      _ = ‖w‖ := by
        rw [show (-x) - (w - x) = -w by abel, norm_neg]

end
end C1VariationalFiniteDimensionalSelector
end Source
end ConnesWeilRH
