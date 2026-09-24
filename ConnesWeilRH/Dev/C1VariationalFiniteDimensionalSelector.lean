import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.PiL2
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

theorem exists_min_norm_euclidean_coefficient
    {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (vectors : ι → F) (y : F)
    (hy : ∃ c : EuclideanSpace ℂ ι,
      (∑ i, c i • vectors i) = y) :
    ∃ c : EuclideanSpace ℂ ι,
      (∑ i, c i • vectors i) = y ∧
        ∀ d : EuclideanSpace ℂ ι,
          (∑ i, d i • vectors i) = y → ‖c‖ ≤ ‖d‖ := by
  let L : EuclideanSpace ℂ ι →ₗ[ℂ] F :=
    { toFun := fun c => ∑ i, c i • vectors i
      map_add' := by
        intro c d
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        simp [smul_smul, Finset.smul_sum] }
  rcases hy with ⟨c₀, hc₀⟩
  have hc₀L : L c₀ = y := by
    simpa [L] using hc₀
  rcases exists_min_norm_preimage L c₀ with ⟨c, hc, hmin⟩
  refine ⟨c, ?_, ?_⟩
  · exact hc.trans hc₀L
  · intro d hd
    apply hmin d
    have hdL : L d = y := by
      simpa [L] using hd
    exact hdL.trans hc₀L.symm

end
end C1VariationalFiniteDimensionalSelector
end Source
end ConnesWeilRH
