/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The exact finite-dimensional countermodel from the pole-free anti-maximum
rejection.  It is deliberately independent of any project route structure:
the point is to make the failed implication mechanically checkable.
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace ConnesWeilRH
namespace Dev
namespace PolefreeAntimaxCounterexample

open Matrix

abbrev V := Fin 2 → ℝ

def A : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(-4 : ℝ), -1; -1, 1]

noncomputable def Ainv : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(-1 / 5 : ℝ), (-1 / 5 : ℝ); (-1 / 5 : ℝ), (4 / 5 : ℝ)]

def C : V := ![(1 : ℝ), 1]

def v : V := ![(1 : ℝ), -1]

theorem A_mul_Ainv : A * Ainv = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, Ainv, Matrix.mul_apply,
    Fin.sum_univ_succ]

theorem Ainv_mul_A : Ainv * A = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, Ainv, Matrix.mul_apply,
    Fin.sum_univ_succ]

theorem Ainv_C : Ainv *ᵥ C = ![(-2 / 5 : ℝ), (3 / 5 : ℝ)] := by
  ext i
  fin_cases i
  · norm_num [Ainv, C, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · norm_num [Ainv, C, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem C_dot_Ainv_C : dotProduct C (Ainv *ᵥ C) = (1 / 5 : ℝ) := by
  rw [Ainv_C]
  norm_num [C, dotProduct, Fin.sum_univ_succ]

theorem C_dot_v : dotProduct C v = 0 := by
  norm_num [C, v, dotProduct, Fin.sum_univ_succ]

theorem v_dot_Av : dotProduct v (A *ᵥ v) = (-1 : ℝ) := by
  norm_num [A, v, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem inverse_scalar_positive_despite_negative_C_perp :
    0 < dotProduct C (Ainv *ᵥ C) ∧
      dotProduct C v = 0 ∧
      dotProduct v (A *ᵥ v) < 0 := by
  refine ⟨?_, C_dot_v, ?_⟩
  · rw [C_dot_Ainv_C]
    norm_num
  · rw [v_dot_Av]
    norm_num

end PolefreeAntimaxCounterexample
end Dev
end ConnesWeilRH
