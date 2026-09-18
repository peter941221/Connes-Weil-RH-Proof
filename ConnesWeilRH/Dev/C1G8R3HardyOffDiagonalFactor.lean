/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ComplementCornerHardyNormalForm
import ConnesWeilRH.Dev.C1G8R3ScaleStrictAngle

/-!
# Off-diagonal Hankel factor of the S3 Hardy defect

The P-side defect is the positive square of the opposite Hardy block
`(I-P) K_b P`.  This identifies the exact first-order Hankel factor whose
columns must be controlled; it is not the already controlled interior block
`(I-P) K_b (I-P)`.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

theorem doubledShiftHardyDefect_eq_offDiagonal_adjoint_comp_self (b : ℝ) :
    cc20PositiveHalfLineProjection -
        (cc20PositiveHalfLineProjection ∘L doubledShiftHardy b ∘L
          cc20PositiveHalfLineProjection ∘L doubledShiftHardy b ∘L
          cc20PositiveHalfLineProjection) =
      ((ContinuousLinearMap.id ℂ Carrier -
          cc20PositiveHalfLineProjection) ∘L doubledShiftHardy b ∘L
        cc20PositiveHalfLineProjection).adjoint ∘L
        ((ContinuousLinearMap.id ℂ Carrier -
          cc20PositiveHalfLineProjection) ∘L doubledShiftHardy b ∘L
        cc20PositiveHalfLineProjection) := by
  let P : Op := cc20PositiveHalfLineProjection
  let M : Op := ContinuousLinearMap.id ℂ Carrier - P
  let K : Op := doubledShiftHardy b
  have hP : P ∘L P = P := by
    dsimp [P]
    exact cc20PositiveHalfLineProjection_isIdempotentElem
  have hP' : P * P = P := by
    simpa only [ContinuousLinearMap.mul_def] using hP
  have hPself : P.adjoint = P := by
    dsimp [P]
    exact cc20PositiveHalfLineProjection_isSelfAdjoint.adjoint_eq
  have hM : M ∘L M = M := by
    dsimp [M]
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    rw [hP]
    abel
  have hMself : M.adjoint = M := by
    dsimp [M]
    rw [map_sub, ContinuousLinearMap.adjoint_id, hPself]
  have hK : K ∘L K = ContinuousLinearMap.id ℂ Carrier := by
    simpa only [K] using doubledShiftHardy_involutive b
  have hKself : K.adjoint = K := by
    have hself : IsSelfAdjoint K := by
      apply LinearMap.IsSymmetric.isSelfAdjoint
      intro u v
      exact doubledShiftHardy_inner_symmetry b u v
    exact hself.adjoint_eq
  change P - P ∘L K ∘L P ∘L K ∘L P =
    (M ∘L K ∘L P).adjoint ∘L (M ∘L K ∘L P)
  have hfactor :
      (M ∘L K ∘L P).adjoint ∘L (M ∘L K ∘L P) =
        P ∘L K ∘L M ∘L K ∘L P := by
    simp only [ContinuousLinearMap.adjoint_comp, hPself, hMself, hKself,
      ContinuousLinearMap.comp_assoc]
    calc
      P ∘L K ∘L M ∘L M ∘L K ∘L P =
          P ∘L K ∘L (M ∘L M) ∘L K ∘L P := by
            simp only [ContinuousLinearMap.comp_assoc]
      _ = P ∘L K ∘L M ∘L K ∘L P := by rw [hM]
  rw [hfactor]
  calc
    P - P * K * P * K * P = P * K * K * P - P * K * P * K * P := by
      have hK' : K * K = (1 : Op) := by
        simpa only [ContinuousLinearMap.mul_def] using hK
      have hKK : P * K * K * P = P := by
        calc
          P * K * K * P = P * (K * K) * P := by noncomm_ring
          _ = P * (1 : Op) * P := by rw [hK']
          _ = P * P := by simp only [ContinuousLinearMap.one_def,
            ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_id]
          _ = P := hP'
      rw [hKK]
    _ = P * K * (M + P) * K * P - P * K * P * K * P := by
      have hMP : M + P = (1 : Op) := by
        dsimp [M]
        abel
      rw [hMP]
      simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_id]
    _ = P * K * M * K * P := by noncomm_ring

end Dev
end ConnesWeilRH
