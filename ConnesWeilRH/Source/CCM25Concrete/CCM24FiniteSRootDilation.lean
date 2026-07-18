/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Positive-detector root dilation algebra

This module owns the two-copy noncommutative algebra used by Proof 380.  A
root and a formal adjoint are placed in an off-diagonal matrix.  Squaring the
matrix produces the two positive orderings, while anticommuting it with a
first-copy operator exposes the two root orientations.

No trace, adjoint, Schatten, or analytic factorization premise is stored here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootDilation

variable {A : Type*} [Ring A]

/-- The formal self-adjoint two-copy dilation of a root and its adjoint. -/
def rootDilation (root rootDagger : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![0, rootDagger], ![root, 0]]

/-- Embed an operator in the first copy of a two-copy carrier. -/
def firstCopy (operator : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![operator, 0], ![0, 0]]

/-- The two positive root orderings on the diagonal. -/
def rootSquare (root rootDagger : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![rootDagger * root, 0], ![0, root * rootDagger]]

/-- The two root orientations produced by the first-copy anticommutator. -/
def rootRangeSplit (root rootDagger difference : A) :
    Matrix (Fin 2) (Fin 2) A :=
  ![![0, difference * rootDagger], ![root * difference, 0]]

/-- Squaring the root dilation produces `C†C` and `CC†` without assuming
commutativity. -/
theorem rootDilation_mul_self (root rootDagger : A) :
    rootDilation root rootDagger * rootDilation root rootDagger =
      rootSquare root rootDagger := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootDilation, rootSquare, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The first-copy positive response keeps only the `C†C` ordering. -/
theorem rootSquare_mul_firstCopy (root rootDagger difference : A) :
    rootSquare root rootDagger * firstCopy difference =
      firstCopy (rootDagger * root * difference) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootSquare, firstCopy, Matrix.mul_apply, Fin.sum_univ_succ,
      mul_assoc]

/-- Anticommuting the dilation with a first-copy difference separates the
left and right root orientations used by the range-root row. -/
theorem rootDilation_firstCopy_anticommutator
    (root rootDagger difference : A) :
    rootDilation root rootDagger * firstCopy difference +
        firstCopy difference * rootDilation root rootDagger =
      rootRangeSplit root rootDagger difference := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootDilation, firstCopy, rootRangeSplit, Matrix.mul_apply,
      Fin.sum_univ_succ]

end CCM24FiniteSRootDilation
end CCM25Concrete
end Source
end ConnesWeilRH
