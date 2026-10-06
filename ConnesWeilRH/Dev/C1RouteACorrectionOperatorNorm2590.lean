import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Normed

namespace ConnesWeilRH.Dev

noncomputable def matrixOperator2590
    (M : Matrix (Fin 30) (Fin 30) ℂ) :
    (Fin 30 → ℂ) →L[ℂ] (Fin 30 → ℂ) :=
  ContinuousLinearMap.mk M.mulVecLin (by fun_prop)

theorem matrixOperator2590_apply
    (M : Matrix (Fin 30) (Fin 30) ℂ) (v : Fin 30 → ℂ) :
    matrixOperator2590 M v = Matrix.mulVec M v := rfl

theorem matrixOperator_norm_lt_one_of_row_sum_lt_one2590
    (M : Matrix (Fin 30) (Fin 30) ℂ)
    (hrows : ∀ i : Fin 30, ∑ j : Fin 30, ‖M i j‖ < 1) :
    ‖matrixOperator2590 M‖ < 1 := by
  change ‖ContinuousLinearMap.mk M.mulVecLin (by fun_prop)‖ < 1
  rw [← Matrix.linfty_opNorm_eq_opNorm M]
  rw [Matrix.linfty_opNorm_def]
  have hsup : (Finset.univ.sup (fun i : Fin 30 => ∑ j : Fin 30, ‖M i j‖₊) : NNReal) < 1 := by
    rw [Finset.sup_lt_iff (by norm_num : (0 : NNReal) < 1)]
    intro i hi
    exact_mod_cast hrows i
  exact_mod_cast hsup


theorem matrixOperator_norm_lt_one_of_entrywise_bounds2590
    (M : Matrix (Fin 30) (Fin 30) ℂ)
    (bounds : Matrix (Fin 30) (Fin 30) NNReal)
    (hentry : ∀ i j : Fin 30, ‖M i j‖₊ ≤ bounds i j)
    (hrows : ∀ i : Fin 30, ∑ j : Fin 30, bounds i j < 1) :
    ‖matrixOperator2590 M‖ < 1 := by
  change ‖ContinuousLinearMap.mk M.mulVecLin (by fun_prop)‖ < 1
  rw [← Matrix.linfty_opNorm_eq_opNorm M]
  rw [Matrix.linfty_opNorm_def]
  have hsup :
      (Finset.univ.sup (fun i : Fin 30 => ∑ j : Fin 30, ‖M i j‖₊) : NNReal) < 1 := by
    rw [Finset.sup_lt_iff (by norm_num : (0 : NNReal) < 1)]
    intro i hi
    calc
      ∑ j : Fin 30, ‖M i j‖₊ ≤ ∑ j : Fin 30, bounds i j := by
        gcongr with j hj
        exact hentry i j
      _ < 1 := hrows i
  exact_mod_cast hsup

theorem matrixOperator_norm_lt_one_of_row_norm_bounds2590
    (M : Matrix (Fin 30) (Fin 30) ℂ)
    (rowBounds : Fin 30 → NNReal)
    (hrows : ∀ i : Fin 30, (∑ j : Fin 30, ‖M i j‖₊) ≤ rowBounds i)
    (hbound : ∀ i : Fin 30, rowBounds i < 1) :
    ‖matrixOperator2590 M‖ < 1 := by
  change ‖ContinuousLinearMap.mk M.mulVecLin (by fun_prop)‖ < 1
  rw [← Matrix.linfty_opNorm_eq_opNorm M]
  rw [Matrix.linfty_opNorm_def]
  have hsup :
      (Finset.univ.sup (fun i : Fin 30 => ∑ j : Fin 30, ‖M i j‖₊) : NNReal) < 1 := by
    rw [Finset.sup_lt_iff (by norm_num : (0 : NNReal) < 1)]
    intro i hi
    exact (hrows i).trans_lt (hbound i)
  exact_mod_cast hsup
end ConnesWeilRH.Dev