/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientDefectFactorization

/-!
# Spectral-fibre obstruction to residual-only factorization

The physical inverse and the normalized Schur transport have different
symbols at the antiresonant point.  This file formalizes the exact scalar
fibre calculation used by Proof 554:

```text
U = -I,
E = I - (1/2) U = (3/2) I,
P = (1/2) E⁻¹ = (1/3) I,
T = (1 + 1/2)⁻¹ E = I,
Q = I + U = 0.
```

Therefore `P - T = -(2/3) I` cannot factor through `Q`.  The model is a
spectral fibre, not a claim that the global `L2` carrier contains an exact
plane wave.  Its purpose is to make the residual-only no-go precise and to
force the live proof to keep the complete signed raw row, including the
moving-boundary cancellation.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaResidualOnlyAntiresonantObstruction

local notation "ScalarOp" => ℂ →L[ℂ] ℂ

/-! ## The antiresonant scalar fibre -/

noncomputable def antiresonantModelU : ScalarOp :=
  -(ContinuousLinearMap.id ℂ ℂ)

noncomputable def antiresonantModelEulerFactor : ScalarOp :=
  ContinuousLinearMap.id ℂ ℂ -
    (1 / 2 : ℂ) • antiresonantModelU

noncomputable def antiresonantModelPhysicalInverse : ScalarOp :=
  (1 / 3 : ℂ) • ContinuousLinearMap.id ℂ ℂ

noncomputable def antiresonantModelSchurTransport : ScalarOp :=
  (2 / 3 : ℂ) • antiresonantModelEulerFactor

noncomputable def antiresonantModelAntiresonantLoss : ScalarOp :=
  ContinuousLinearMap.id ℂ ℂ + antiresonantModelU

noncomputable def antiresonantModelResidual : ScalarOp :=
  antiresonantModelPhysicalInverse - antiresonantModelSchurTransport

theorem antiresonantModelEulerFactor_eq_three_halves :
    antiresonantModelEulerFactor =
      (3 / 2 : ℂ) • ContinuousLinearMap.id ℂ ℂ := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [antiresonantModelEulerFactor, antiresonantModelU,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply]
  ring

theorem antiresonantModelSchurTransport_eq_id :
    antiresonantModelSchurTransport =
      ContinuousLinearMap.id ℂ ℂ := by
  rw [antiresonantModelSchurTransport,
    antiresonantModelEulerFactor_eq_three_halves]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.smul_apply, smul_smul,
    ContinuousLinearMap.id_apply]
  norm_num

theorem antiresonantModelAntiresonantLoss_eq_zero :
    antiresonantModelAntiresonantLoss = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [antiresonantModelAntiresonantLoss, antiresonantModelU,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.zero_apply]
  abel

theorem antiresonantModelResidual_eq_neg_two_thirds :
    antiresonantModelResidual =
      (-2 / 3 : ℂ) • ContinuousLinearMap.id ℂ ℂ := by
  rw [antiresonantModelResidual, antiresonantModelSchurTransport_eq_id]
  apply ContinuousLinearMap.ext
  intro x
  simp only [antiresonantModelPhysicalInverse,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  ring

theorem antiresonantModelResidual_ne_zero :
    antiresonantModelResidual ≠ 0 := by
  rw [antiresonantModelResidual_eq_neg_two_thirds]
  intro hzero
  have hpoint := congrArg
    (fun operator : ScalarOp => operator (1 : ℂ)) hzero
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] at hpoint
  norm_num at hpoint

/-! ## No bounded residual-only readout -/

theorem no_antiresonantModel_residual_factor
    (factor : ScalarOp) :
    antiresonantModelResidual ≠
      factor ∘L antiresonantModelAntiresonantLoss := by
  intro hfactor
  rw [antiresonantModelResidual_eq_neg_two_thirds,
    antiresonantModelAntiresonantLoss_eq_zero] at hfactor
  have hpoint := congrArg
    (fun operator : ScalarOp => operator (1 : ℂ)) hfactor
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply, map_zero] at hpoint
  norm_num at hpoint

end CCM24FiniteSCompletedJuliaResidualOnlyAntiresonantObstruction
end CCM25Concrete
end Source
end ConnesWeilRH
