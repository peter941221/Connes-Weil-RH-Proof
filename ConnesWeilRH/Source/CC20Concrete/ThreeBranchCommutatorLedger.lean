/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The signed three-branch commutator ledger

This module formalizes the exact algebraic identity used by the CC20 moving
`E/R/Q/K_prol` route.  It deliberately does not define a semilocal `Q`, `R`,
or `K_prol`; those remain source-level producer obligations.  Once a genuine
producer supplies `R = E Q E - K`, this identity expands the `R` commutator
without splitting or estimating any branch.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The continuous-linear-map commutator `[A,W] = A W - W A`. -/
noncomputable def cc20Commutator
    (A W : H →L[ℂ] H) : H →L[ℂ] H :=
  A.comp W - W.comp A

/-- The outer boundary contribution `E Q [E,W]`. -/
noncomputable def cc20OuterCommutatorBranch
    (E Q W : H →L[ℂ] H) : H →L[ℂ] H :=
  E.comp (Q.comp (cc20Commutator E W))

/-- The second-support contribution `E [Q,W] E`. -/
noncomputable def cc20SecondSupportCommutatorBranch
    (E Q W : H →L[ℂ] H) : H →L[ℂ] H :=
  E.comp ((cc20Commutator Q W).comp E)

/-- The reflected outer contribution `[E,W] Q E`. -/
noncomputable def cc20ReflectedOuterCommutatorBranch
    (E Q W : H →L[ℂ] H) : H →L[ℂ] H :=
  (cc20Commutator E W).comp (Q.comp E)

/-- The prolate contribution `[K,W]`, kept with its signed minus sign in the
complete ledger. -/
noncomputable def cc20ProlateCommutatorBranch
    (K W : H →L[ℂ] H) : H →L[ℂ] H :=
  cc20Commutator K W

/-- The complete signed outer/second-support/prolate commutator. -/
noncomputable def cc20ThreeBranchCommutator
    (E Q K W : H →L[ℂ] H) : H →L[ℂ] H :=
  cc20OuterCommutatorBranch E Q W +
    cc20SecondSupportCommutatorBranch E Q W +
    cc20ReflectedOuterCommutatorBranch E Q W -
    cc20ProlateCommutatorBranch K W

theorem cc20Commutator_eq_threeBranch_of_eq
    (E Q R K W : H →L[ℂ] H)
    (hR : R = E.comp (Q.comp E) - K) :
    cc20Commutator R W = cc20ThreeBranchCommutator E Q K W := by
  rw [hR]
  unfold cc20Commutator cc20ThreeBranchCommutator
    cc20OuterCommutatorBranch cc20SecondSupportCommutatorBranch
    cc20ReflectedOuterCommutatorBranch cc20ProlateCommutatorBranch
  simp only [cc20Commutator]
  ext x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, map_sub]
  abel

/-- The same ledger after pairing with arbitrary vectors.  This is a scalar
identity; no absolute value or branchwise norm has been introduced. -/
theorem cc20Inner_commutator_eq_threeBranch_of_eq
    [InnerProductSpace ℂ H]
    (E Q R K W : H →L[ℂ] H)
    (hR : R = E.comp (Q.comp E) - K)
    (x y : H) :
    inner ℂ x (cc20Commutator R W y) =
      inner ℂ x (cc20ThreeBranchCommutator E Q K W y) := by
  rw [cc20Commutator_eq_threeBranch_of_eq E Q R K W hR]

/-- The Sonin commutator pairing together with CC20's separate distributional
`-2` root pairing. -/
noncomputable def cc20CommutatorResidueResponse
    [InnerProductSpace ℂ H]
    (R W : H →L[ℂ] H) (x y : H) : ℂ :=
  inner ℂ x (cc20Commutator R W y) -
    (2 : ℂ) * inner ℂ x y

/-- The same residue-augmented response after the complete three-branch
expansion. -/
noncomputable def cc20ThreeBranchResidueResponse
    [InnerProductSpace ℂ H]
    (E Q K W : H →L[ℂ] H) (x y : H) : ℂ :=
  inner ℂ x (cc20ThreeBranchCommutator E Q K W y) -
    (2 : ℂ) * inner ℂ x y

theorem cc20CommutatorResidueResponse_eq_threeBranch_of_eq
    [InnerProductSpace ℂ H]
    (E Q R K W : H →L[ℂ] H)
    (hR : R = E.comp (Q.comp E) - K)
    (x y : H) :
    cc20CommutatorResidueResponse R W x y =
      cc20ThreeBranchResidueResponse E Q K W x y := by
  unfold cc20CommutatorResidueResponse cc20ThreeBranchResidueResponse
  rw [cc20Inner_commutator_eq_threeBranch_of_eq E Q R K W hR]

/-- A zero detector commutator does not delete the distributional residue. -/
theorem cc20CommutatorResidueResponse_zero
    [InnerProductSpace ℂ H]
    (R : H →L[ℂ] H) (x y : H) :
    cc20CommutatorResidueResponse R 0 x y =
      -(2 : ℂ) * inner ℂ x y := by
  simp [cc20CommutatorResidueResponse, cc20Commutator]

end CC20Concrete
end Source
end ConnesWeilRH
