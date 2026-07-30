/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantExteriorAdjointRenewal

/-!
# Radial factorization of the exterior adjoint renewal

Proof 615 reads the complete exterior adjoint-renewal block on every actual
new suffix frame.  The recurrence used there depends only on radial support,
not on the particular frame.  This module upgrades the readback to the whole
radial subspace:

```text
exteriorReadout * ambientLoss^dagger * E = F N^dagger E.
```

The same norm-`32` readout therefore works after every radially supported
column.  This is an operator-level interface for the next metric/forward
regrouping.  It does not identify the signed numerator with the exterior
block or control the remaining Gram correction.  Bone 1, Gate 3U, the
finite-S sign, Burnol's identity, and RH remain open.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantExteriorAdjointRadial

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantExteriorAdjointRenewal
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryReadout
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace

/-! ## The ambient-loss factor on the complete radial range -/

theorem primeEulerAmbientLossFactor_adjoint_comp_radialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    (primeEulerAmbientLossFactor p)† ∘L radialSupportProjection lambda =
      (primeEulerAmbientLossScale p : ℂ) •
        (primeEulerAntiresonantCore p ∘L
          radialSupportProjection lambda) := by
  rw [primeEulerAmbientLossFactor_adjoint_eq]
  apply ContinuousLinearMap.ext
  intro x
  simp only [primeEulerAntiresonantCore,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply]

theorem newFrameAntiresonantRadialBlockReadout_comp_ambientLoss_radialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (n : ℕ) :
    newFrameAntiresonantRadialBlockReadout lambda p n ∘L
        (primeEulerAmbientLossFactor p)† ∘L
          radialSupportProjection lambda =
      primeEulerRadialBoundaryStep lambda p ∘L
        ((primeEulerRadialTail lambda p) ^ n) ∘L
          radialSupportProjection lambda := by
  apply ContinuousLinearMap.ext
  intro x
  let E := radialSupportProjection lambda
  let u := E x
  let scale : ℂ := primeEulerAmbientLossScale p
  have hu : E u = u := by
    exact (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2
      (Submodule.starProjection_apply_mem _ _)
  have hscale : scale ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt
      (primeEulerAmbientLossScale_pos p))
  have hloss :
      ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) u =
        scale • primeEulerAntiresonantCore p u := by
    have h := DFunLike.congr_fun
      (primeEulerAmbientLossFactor_adjoint_comp_radialSupport lambda p) x
    simpa only [ContinuousLinearMap.comp_apply, E, u, scale] using h
  have hblock :=
    primeEulerRadialBlockReadout_antiresonantCore_apply_of_fixed
      lambda p n hu
  simp only [ContinuousLinearMap.comp_apply]
  change newFrameAntiresonantRadialBlockReadout lambda p n
      (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) u) =
    primeEulerRadialBoundaryStep lambda p
      (((primeEulerRadialTail lambda p) ^ n) u)
  rw [hloss]
  simp only [newFrameAntiresonantRadialBlockReadout,
    ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  change (scale * scale⁻¹) •
      primeEulerRadialBlockReadout lambda p n
        (primeEulerAntiresonantCore p u) = _
  rw [mul_inv_cancel₀ hscale, one_smul]
  exact hblock

/-! ## Summing the radial factorization -/

theorem primeEulerRadialGeometricReadoutTerm_comp_ambientLoss_radialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (n : ℕ) :
    primeEulerRadialGeometricReadoutTerm lambda p n ∘L
        (primeEulerAmbientLossFactor p)† ∘L
          radialSupportProjection lambda =
      primeEulerRadialGeometricBoundaryTerm lambda p n ∘L
        radialSupportProjection lambda := by
  have hblock :=
    newFrameAntiresonantRadialBlockReadout_comp_ambientLoss_radialSupport
      lambda p n
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := DFunLike.congr_fun hblock x
  simp only [primeEulerRadialGeometricReadoutTerm,
    primeEulerRadialGeometricBoundaryTerm,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
    at hpoint ⊢
  exact congrArg
    (fun y : finiteSCarrier =>
      ((ccm24PrimeEulerCoefficient p : ℂ) ^ (n + 1)) • y) hpoint

theorem primeEulerRadialGeometricReadout_comp_ambientLoss_radialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerRadialGeometricReadout lambda p ∘L
        (primeEulerAmbientLossFactor p)† ∘L
          radialSupportProjection lambda =
      primeEulerRadialGeometricBoundary lambda p ∘L
        radialSupportProjection lambda := by
  have hreadout :=
    summable_primeEulerRadialGeometricReadoutTerm lambda p
  have hboundary :=
    summable_primeEulerRadialGeometricBoundaryTerm lambda p
  apply ContinuousLinearMap.ext
  intro x
  simp only [primeEulerRadialGeometricReadout,
    primeEulerRadialGeometricBoundary, ContinuousLinearMap.comp_apply]
  have hleft :
      (∑' n : ℕ, primeEulerRadialGeometricReadoutTerm lambda p n)
          (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)
            (radialSupportProjection lambda x)) =
        ∑' n : ℕ, primeEulerRadialGeometricReadoutTerm lambda p n
          (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)
            (radialSupportProjection lambda x)) := by
    simpa using
      (ContinuousLinearMap.apply ℂ finiteSCarrier
        (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)
          (radialSupportProjection lambda x))).map_tsum hreadout
  have hright :
      (∑' n : ℕ, primeEulerRadialGeometricBoundaryTerm lambda p n)
          (radialSupportProjection lambda x) =
        ∑' n : ℕ, primeEulerRadialGeometricBoundaryTerm lambda p n
          (radialSupportProjection lambda x) := by
    simpa using
      (ContinuousLinearMap.apply ℂ finiteSCarrier
        (radialSupportProjection lambda x)).map_tsum hboundary
  rw [hleft, hright]
  apply tsum_congr
  intro n
  have hterm := DFunLike.congr_fun
    (primeEulerRadialGeometricReadoutTerm_comp_ambientLoss_radialSupport
      lambda p n) x
  simpa only [ContinuousLinearMap.comp_apply] using hterm

theorem primeEulerExteriorAdjointCrossing_comp_radialSupport_eq_self
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerExteriorAdjointCrossing lambda p ∘L
        radialSupportProjection lambda =
      primeEulerExteriorAdjointCrossing lambda p := by
  apply ContinuousLinearMap.ext
  intro x
  have hfixed :
      radialSupportProjection lambda (radialSupportProjection lambda x) =
        radialSupportProjection lambda x := by
    exact (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2
      (Submodule.starProjection_apply_mem _ _)
  simp only [primeEulerExteriorAdjointCrossing,
    ContinuousLinearMap.comp_apply]
  rw [hfixed]

/-! ## Complete exterior operator factorization -/

/-- Proof 615's norm-`32` readout factors the complete exterior adjoint block
on the entire radial subspace, independently of a suffix frame. -/
theorem primeEulerExteriorAdjointReadout_comp_ambientLoss_radialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerExteriorAdjointReadout lambda p ∘L
        (primeEulerAmbientLossFactor p)† ∘L
          radialSupportProjection lambda =
      primeEulerExteriorAdjointCrossing lambda p := by
  calc
    primeEulerExteriorAdjointReadout lambda p ∘L
          (primeEulerAmbientLossFactor p)† ∘L
            radialSupportProjection lambda =
        primeEulerExteriorAdjointContinuation lambda p ∘L
          (primeEulerRadialGeometricReadout lambda p ∘L
            (primeEulerAmbientLossFactor p)† ∘L
              radialSupportProjection lambda) := by
      simp only [primeEulerExteriorAdjointReadout,
        ContinuousLinearMap.comp_assoc]
    _ = primeEulerExteriorAdjointContinuation lambda p ∘L
          (primeEulerRadialGeometricBoundary lambda p ∘L
            radialSupportProjection lambda) := by
      rw [primeEulerRadialGeometricReadout_comp_ambientLoss_radialSupport]
    _ = (primeEulerExteriorAdjointContinuation lambda p ∘L
          primeEulerRadialGeometricBoundary lambda p) ∘L
            radialSupportProjection lambda := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = primeEulerExteriorAdjointCrossing lambda p ∘L
          radialSupportProjection lambda := by
      rw [←
        primeEulerExteriorAdjointCrossing_eq_continuation_comp_geometricBoundary]
    _ = primeEulerExteriorAdjointCrossing lambda p :=
      primeEulerExteriorAdjointCrossing_comp_radialSupport_eq_self lambda p

/-- Any radially supported column inherits the same exterior factorization.
This is the reusable interface for the coupled coframe terms. -/
theorem primeEulerExteriorAdjointReadout_comp_ambientLoss_of_radialColumn
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (column : G →L[ℂ] finiteSCarrier)
    (hcolumn : radialSupportProjection lambda ∘L column = column) :
    primeEulerExteriorAdjointReadout lambda p ∘L
        (primeEulerAmbientLossFactor p)† ∘L column =
      primeEulerExteriorAdjointCrossing lambda p ∘L column := by
  apply ContinuousLinearMap.ext
  intro x
  have hfactor := DFunLike.congr_fun
    (primeEulerExteriorAdjointReadout_comp_ambientLoss_radialSupport
      lambda p) (column x)
  have hfixed := DFunLike.congr_fun hcolumn x
  simp only [ContinuousLinearMap.comp_apply] at hfactor hfixed ⊢
  rw [hfixed] at hfactor
  exact hfactor

/-! ## Source columns used by the physical coframe -/

theorem primeEulerExteriorAdjointReadout_comp_ambientLoss_sourceBandProjection
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerExteriorAdjointReadout lambda p ∘L
        (primeEulerAmbientLossFactor p)† ∘L
          sourceBandProjection lambda =
      primeEulerExteriorAdjointCrossing lambda p ∘L
        sourceBandProjection lambda := by
  have hband :
      radialSupportProjection lambda ∘L sourceBandProjection lambda =
        sourceBandProjection lambda := by
    apply ContinuousLinearMap.ext
    intro x
    have hradial :
        radialSupportProjection lambda (radialSupportProjection lambda x) =
          radialSupportProjection lambda x := by
      exact (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2
        (Submodule.starProjection_apply_mem _ _)
    have hsonin := DFunLike.congr_fun
      (radialSupportProjection_comp_sourceSoninProjection lambda) x
    simp only [sourceBandProjection, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, map_sub]
    rw [hradial]
    simpa only [ContinuousLinearMap.comp_apply] using congrArg
      (fun y : finiteSCarrier => radialSupportProjection lambda x - y)
      hsonin
  exact
    primeEulerExteriorAdjointReadout_comp_ambientLoss_of_radialColumn
      lambda p (sourceBandProjection lambda) hband

theorem primeEulerExteriorAdjointReadout_comp_ambientLoss_sourceInclusion
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerExteriorAdjointReadout lambda p ∘L
        (primeEulerAmbientLossFactor p)† ∘L sourceInclusion lambda =
      primeEulerExteriorAdjointCrossing lambda p ∘L
        sourceInclusion lambda := by
  have hinclusion :
      radialSupportProjection lambda ∘L sourceInclusion lambda =
        sourceInclusion lambda := by
    apply ContinuousLinearMap.ext
    intro x
    exact (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2
      (Submodule.mem_inf.mp x.property).1
  exact
    primeEulerExteriorAdjointReadout_comp_ambientLoss_of_radialColumn
      lambda p (sourceInclusion lambda) hinclusion

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantExteriorAdjointRadial
end CCM25Concrete
end Source
end ConnesWeilRH
