/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteRadialBlockColumn
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedProjectionRawLedger
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundarySplit

/-!
# Source-side bridge for the radial boundary channel

The finite radial block column is a readout of the actual new suffix frame,
whereas `radialSoninBoundaryCrossing` acts on the full common-log carrier.
This module records the exact source-side relation between them and keeps the
remaining full-carrier factorization as an explicit contract.

For the first weighted block, the source-side identity is

```text
radialSoninBoundaryCrossing p S \circ newSuffixFrame S
  = q_p⁻¹ (first radial boundary column),
```

with `q_p = ccm24PrimeEulerCoefficient p`.  The inverse coefficient is kept
visible: the identity is not a uniform bound in `p`.

The factorization structure below is deliberately weaker than a pair owner:
it only factors the source restriction of the boundary channel through a
finite radial column.  It therefore exposes, rather than silently supplies,
the missing extension to the full `finiteSCarrier` needed by the signed pair
consumer.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialBoundaryColumnBridge

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open AntiresonantFrameLossCommutator
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryReadout
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteRadialBlockColumn
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedProjectionRawLedger
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment
open AntiresonantFrameLossRadialBoundarySplit

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The first weighted source column -/

/-- The first coordinate of the finite radial boundary column. -/
noncomputable def finitePrimeEulerRadialGeometricBoundaryFirstCoordinate
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier unitSoninScale →L[ℂ] finiteSCarrier :=
  let i0 : Fin 1 := ⟨0, by simp⟩
  PiLp.proj (p := 2) (β := fun _ : Fin 1 => finiteSCarrier) i0 ∘L
    finitePrimeEulerRadialGeometricBoundaryColumn
      unitSoninScale p S 1

@[simp]
theorem finitePrimeEulerRadialGeometricBoundaryFirstCoordinate_apply
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier unitSoninScale) :
    finitePrimeEulerRadialGeometricBoundaryFirstCoordinate p S x =
      primeEulerRadialGeometricBoundaryTerm unitSoninScale p 0
        (newSuffixFrame unitSoninScale S x) := by
  rfl

/-! ## The target projection fixes the actual polar frame -/

theorem newSuffixRangeProjection_comp_newSuffixFrame_eq_frame
    (S : List CCM24VisiblePrime) :
    newSuffixRangeProjection unitSoninScale S ∘L
        newSuffixFrame unitSoninScale S =
      newSuffixFrame unitSoninScale S := by
  change newSuffixRangeProjection unitSoninScale S ∘L
      (parameterizedSoninFrame unitSoninScale 1 S ∘L
        parameterizedSoninGramInvSqrt unitSoninScale 1 S (by norm_num)) =
    parameterizedSoninFrame unitSoninScale 1 S ∘L
      parameterizedSoninGramInvSqrt unitSoninScale 1 S (by norm_num)
  calc
    newSuffixRangeProjection unitSoninScale S ∘L
          (parameterizedSoninFrame unitSoninScale 1 S ∘L
            parameterizedSoninGramInvSqrt unitSoninScale 1 S (by norm_num)) =
        (newSuffixRangeProjection unitSoninScale S ∘L
          parameterizedSoninFrame unitSoninScale 1 S) ∘L
            parameterizedSoninGramInvSqrt unitSoninScale 1 S (by norm_num) := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = parameterizedSoninFrame unitSoninScale 1 S ∘L
          parameterizedSoninGramInvSqrt unitSoninScale 1 S (by norm_num) := by
      rw [show newSuffixRangeProjection unitSoninScale S ∘L
          parameterizedSoninFrame unitSoninScale 1 S =
            parameterizedSoninFrame unitSoninScale 1 S by
        simpa only [parameterizedSoninFrame] using
          (newSuffixRangeProjection_comp_parameterizedFrame_eq_frame
            unitSoninScale S)]
    _ = parameterizedSoninFrame unitSoninScale 1 S ∘L
          parameterizedSoninGramInvSqrt unitSoninScale 1 S (by norm_num) := rfl

/-! ## Exact source-side boundary readback -/

theorem radialSoninBoundaryCrossing_comp_newSuffixFrame_eq_boundaryStep
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    radialSoninBoundaryCrossing p S ∘L
        newSuffixFrame unitSoninScale S =
      primeEulerRadialBoundaryStep unitSoninScale p ∘L
        newSuffixFrame unitSoninScale S := by
  apply ContinuousLinearMap.ext
  intro x
  have hprojection := DFunLike.congr_fun
    (newSuffixRangeProjection_comp_newSuffixFrame_eq_frame S) x
  have hradial := DFunLike.congr_fun
    (radialSupportProjection_comp_newSuffixFrame unitSoninScale S) x
  simp only [radialSoninBoundaryCrossing, primeEulerRadialBoundaryStep,
    ContinuousLinearMap.comp_apply] at hprojection hradial ⊢
  rw [hprojection, hradial]

theorem radialSoninBoundaryCrossing_comp_newSuffixFrame_eq_inv_smul_firstCoordinate
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    radialSoninBoundaryCrossing p S ∘L
        newSuffixFrame unitSoninScale S =
      ((ccm24PrimeEulerCoefficient p : ℂ)⁻¹) •
        finitePrimeEulerRadialGeometricBoundaryFirstCoordinate p S := by
  have hqreal : ccm24PrimeEulerCoefficient p ≠ 0 :=
    ne_of_gt (ccm24PrimeEulerCoefficient_pos p)
  have hq : (ccm24PrimeEulerCoefficient p : ℂ) ≠ 0 := by
    exact_mod_cast hqreal
  apply ContinuousLinearMap.ext
  intro x
  have hboundary := DFunLike.congr_fun
    (radialSoninBoundaryCrossing_comp_newSuffixFrame_eq_boundaryStep p S) x
  simp only [ContinuousLinearMap.comp_apply,
    finitePrimeEulerRadialGeometricBoundaryFirstCoordinate_apply,
    primeEulerRadialGeometricBoundaryTerm,
    ContinuousLinearMap.smul_apply] at hboundary ⊢
  rw [hboundary]
  simp only [pow_one, Nat.zero_add, add_zero, pow_zero,
    ContinuousLinearMap.one_apply]
  rw [smul_smul, inv_mul_cancel₀ hq, one_smul]

/-! ## Explicit source-side factorization contract -/

/-- A finite-column factorization of the source restriction of the complete
radial boundary channel.  This does not assert a factorization on the full
common-log carrier and therefore cannot be mistaken for the missing pair
owner. -/
structure RadialBoundarySourceColumnFactorizationData
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (N : ℕ) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  readout :
    PiLp 2 (fun _ : Fin N => finiteSCarrier) →L[ℂ] finiteSCarrier
  readout_norm_le : ‖readout‖ ≤ bound
  factorization :
    readout ∘L finitePrimeEulerRadialGeometricBoundaryColumn
        unitSoninScale p S N =
      radialSoninBoundaryCrossing p S ∘L
        newSuffixFrame unitSoninScale S

/-- The exact first-block source factorization.  Its bound is the norm of
`q_p⁻¹`, so it records the non-uniform cost instead of hiding it. -/
noncomputable def canonicalRadialBoundarySourceColumnFactorizationData
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    RadialBoundarySourceColumnFactorizationData p S 1
      ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖ := by
  let i0 : Fin 1 := ⟨0, by simp⟩
  let projection :
      PiLp 2 (fun _ : Fin 1 => finiteSCarrier) →L[ℂ] finiteSCarrier :=
    PiLp.proj (p := 2) (β := fun _ : Fin 1 => finiteSCarrier) i0
  let readout := ((ccm24PrimeEulerCoefficient p : ℂ)⁻¹) • projection
  refine
    { bound_nonneg := norm_nonneg _
      readout := readout
      readout_norm_le := ?_
      factorization := ?_ }
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    calc
      ‖readout x‖ = ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖ *
          ‖projection x‖ := by
        change ‖((ccm24PrimeEulerCoefficient p : ℂ)⁻¹) •
          projection x‖ = ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖ *
            ‖projection x‖
        rw [norm_smul]
      _ ≤ ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖ * ‖x‖ := by
        exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x i0)
          (norm_nonneg _)
  · apply ContinuousLinearMap.ext
    intro x
    have hbridge := DFunLike.congr_fun
      (radialSoninBoundaryCrossing_comp_newSuffixFrame_eq_inv_smul_firstCoordinate
        p S) x
    simp only [readout, projection,
      finitePrimeEulerRadialGeometricBoundaryFirstCoordinate,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply] at hbridge ⊢
    exact hbridge.symm

/-! ## What any such factorization would buy -/

theorem norm_radialSoninBoundaryCrossing_comp_newSuffixFrame_apply_le_of_data
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    {N : ℕ} {bound : ℝ}
    (data : RadialBoundarySourceColumnFactorizationData p S N bound)
    (x : sourceSoninCarrier unitSoninScale) :
    ‖radialSoninBoundaryCrossing p S
        (newSuffixFrame unitSoninScale S x)‖ ≤
      (32 * bound) *
        ‖newFrameAntiresonantColumn unitSoninScale p S x‖ := by
  have hfactor := DFunLike.congr_fun data.factorization x
  have hpoint : data.readout
        (finitePrimeEulerRadialGeometricBoundaryColumn
          unitSoninScale p S N x) =
      radialSoninBoundaryCrossing p S
        (newSuffixFrame unitSoninScale S x) := by
    simpa only [ContinuousLinearMap.comp_apply] using hfactor
  have hcolumn :=
    norm_finitePrimeEulerRadialGeometricBoundaryColumn_apply_le
      unitSoninScale p S N x
  calc
    ‖radialSoninBoundaryCrossing p S
        (newSuffixFrame unitSoninScale S x)‖ =
        ‖data.readout
          (finitePrimeEulerRadialGeometricBoundaryColumn
            unitSoninScale p S N x)‖ := by
      rw [hpoint]
    _ ≤ ‖data.readout‖ *
          ‖finitePrimeEulerRadialGeometricBoundaryColumn
            unitSoninScale p S N x‖ := data.readout.le_opNorm _
    _ ≤ bound *
          ‖finitePrimeEulerRadialGeometricBoundaryColumn
            unitSoninScale p S N x‖ := by
      exact mul_le_mul_of_nonneg_right data.readout_norm_le (norm_nonneg _)
    _ ≤ bound * (32 *
          ‖newFrameAntiresonantColumn unitSoninScale p S x‖) := by
      exact mul_le_mul_of_nonneg_left hcolumn data.bound_nonneg
    _ = (32 * bound) *
          ‖newFrameAntiresonantColumn unitSoninScale p S x‖ := by ring

theorem normSq_radialSoninBoundaryCrossing_comp_newSuffixFrame_apply_le_of_data
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    {N : ℕ} {bound : ℝ}
    (data : RadialBoundarySourceColumnFactorizationData p S N bound)
    (x : sourceSoninCarrier unitSoninScale) :
    ‖radialSoninBoundaryCrossing p S
        (newSuffixFrame unitSoninScale S x)‖ ^ 2 ≤
      (32 * bound) ^ 2 *
        ‖newFrameAntiresonantColumn unitSoninScale p S x‖ ^ 2 := by
  have hnorm :=
    norm_radialSoninBoundaryCrossing_comp_newSuffixFrame_apply_le_of_data
      data x
  have hbound : 0 ≤ 32 * bound :=
    mul_nonneg (by norm_num) data.bound_nonneg
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hbound (norm_nonneg _))).2 hnorm

end AntiresonantFrameLossRadialBoundaryColumnBridge
end CCM25Concrete
end Source
end ConnesWeilRH
