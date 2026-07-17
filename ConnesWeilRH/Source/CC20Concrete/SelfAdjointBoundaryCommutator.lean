/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.ThreeBranchCommutatorLedger
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Self-adjoint boundary commutator from one oriented crossing

For self-adjoint `E` and `W`, the commutator `[E,W]` is the adjoint-minus-
forward combination of the single off-diagonal crossing `(I-E)WE`.  This is
the algebraic bridge between a Hilbert--Schmidt pair owner and the CC20
three-branch commutator ledger.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open scoped InnerProduct InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The oriented crossing through a projection boundary. -/
noncomputable def cc20OrientedBoundaryCrossing
    (E W : H →L[ℂ] H) : H →L[ℂ] H :=
  (ContinuousLinearMap.id ℂ H - E) ∘L W ∘L E

/-- A self-adjoint commutator is the reverse orientation minus the forward
orientation. -/
theorem cc20Commutator_eq_orientedBoundaryCrossing_adjoint_sub
    (E W : H →L[ℂ] H)
    (hE : IsSelfAdjoint E) (hW : IsSelfAdjoint W) :
    cc20Commutator E W =
      (cc20OrientedBoundaryCrossing E W).adjoint -
        cc20OrientedBoundaryCrossing E W := by
  unfold cc20Commutator cc20OrientedBoundaryCrossing
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    map_sub,
    ContinuousLinearMap.adjoint_id,
    hE.adjoint_eq, hW.adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  abel

/-- The opposite commutator orientation used by the centered Gram numerator. -/
theorem operatorCommutator_eq_neg_orientedBoundaryCrossing_adjoint_sub
    (E W : H →L[ℂ] H)
    (hE : IsSelfAdjoint E) (hW : IsSelfAdjoint W) :
    W ∘L E - E ∘L W =
      cc20OrientedBoundaryCrossing E W -
        (cc20OrientedBoundaryCrossing E W).adjoint := by
  calc
    W ∘L E - E ∘L W = -cc20Commutator E W := by
      unfold cc20Commutator
      apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply]
      abel
    _ = -((cc20OrientedBoundaryCrossing E W).adjoint -
        cc20OrientedBoundaryCrossing E W) := by
      rw [cc20Commutator_eq_orientedBoundaryCrossing_adjoint_sub
        E W hE hW]
    _ = cc20OrientedBoundaryCrossing E W -
        (cc20OrientedBoundaryCrossing E W).adjoint := by
      apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.neg_apply]
      abel

/-- The commutator of two self-adjoint operators is skew-adjoint. -/
theorem cc20Commutator_adjoint_eq_neg
    (E W : H →L[ℂ] H)
    (hE : IsSelfAdjoint E) (hW : IsSelfAdjoint W) :
    (cc20Commutator E W).adjoint = -cc20Commutator E W := by
  unfold cc20Commutator
  rw [map_sub, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, hE.adjoint_eq, hW.adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply]
  abel

end CC20Concrete
end Source
end ConnesWeilRH
