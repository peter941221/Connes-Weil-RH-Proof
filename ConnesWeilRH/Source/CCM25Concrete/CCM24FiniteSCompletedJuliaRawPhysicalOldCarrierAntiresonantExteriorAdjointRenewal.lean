/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryResolvent

/-!
# Exterior adjoint renewal from the antiresonant boundary

Write the positive-translation adjoint renewal in radial blocks.  With

```text
E = radial support,       F = I - E,
N = normalizedPrimeEulerInverse(p)^dagger,
X = F N E,               Y = F N F,
V = E U_(log p) E,       C = F U_(log p) E,
```

the genuine Euler equation gives

```text
X (I - q_p V) = q_p Y C.
```

Proof 614 gives `G (I-q_p V)=q_p C`.  Since the common right denominator is
invertible, this module proves `X=Y G`.  The exterior continuation `Y` is a
contraction.  Consequently the uniformly bounded Proof 613 readout can be
postprocessed by `Y` and reads the complete exterior adjoint block with the
same bound `32`.

This closes one complete adjoint-renewal leakage channel.  It does not
identify the full signed numerator with that channel or control the coupled
metric-coframe Gram correction.  Bone 1, Gate 3U, the finite-S sign, Burnol's
identity, and RH remain open.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantExteriorAdjointRenewal

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCausalMarkov
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryReadout
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryResolvent
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSProjectionTrace

/-! ## Radial block owners -/

/-- The full radial-interior to radial-exterior block of the genuine adjoint
renewal. -/
noncomputable def primeEulerExteriorAdjointCrossing
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialComplement lambda ∘L
    (normalizedPrimeEulerInverse p)† ∘L
      radialSupportProjection lambda

/-- Renewal after the trajectory has already exited the radial half-line. -/
noncomputable def primeEulerExteriorAdjointContinuation
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialComplement lambda ∘L
    (normalizedPrimeEulerInverse p)† ∘L
      radialComplement lambda

/-- The Proof 613 readout followed by the genuine exterior continuation. -/
noncomputable def primeEulerExteriorAdjointReadout
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  primeEulerExteriorAdjointContinuation lambda p ∘L
    primeEulerRadialGeometricReadout lambda p

/-! ## Triangular radial algebra -/

theorem primeEulerPositiveTranslation_comp_radialSupport_eq_tail_add_boundary
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    (cc20GlobalLogTranslation
        (Real.log p)).toContinuousLinearMap ∘L
        radialSupportProjection lambda =
      primeEulerRadialTail lambda p +
        primeEulerRadialBoundaryStep lambda p := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [primeEulerRadialTail, primeEulerRadialBoundaryStep,
    radialComplement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply]
  abel

theorem radialSupportProjection_comp_primeEulerRadialTail_eq_self
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    radialSupportProjection lambda ∘L
        primeEulerRadialTail lambda p =
      primeEulerRadialTail lambda p := by
  apply ContinuousLinearMap.ext
  intro x
  have hfixed :
      radialSupportProjection lambda
          (radialSupportProjection lambda
            ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
              (radialSupportProjection lambda x))) =
        radialSupportProjection lambda
          ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
            (radialSupportProjection lambda x)) :=
    (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2
      (Submodule.starProjection_apply_mem _ _)
  simpa only [primeEulerRadialTail,
    ContinuousLinearMap.comp_apply] using hfixed

theorem radialComplement_comp_primeEulerRadialBoundaryStep_eq_self
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    radialComplement lambda ∘L
        primeEulerRadialBoundaryStep lambda p =
      primeEulerRadialBoundaryStep lambda p := by
  have hidempotent :=
    (radialSupportProjection_isStarProjection lambda).one_sub
      |>.isIdempotentElem
  apply ContinuousLinearMap.ext
  intro x
  have hfixed := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator
        ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
          (radialSupportProjection lambda x))) hidempotent
  simpa only [primeEulerRadialBoundaryStep, radialComplement,
    ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.comp_apply] using hfixed

/-- The lower-left block equation of the genuine positive-translation
adjoint renewal. -/
theorem primeEulerExteriorAdjointCrossing_comp_one_sub_tail
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerExteriorAdjointCrossing lambda p ∘L
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          (ccm24PrimeEulerCoefficient p : ℂ) •
            primeEulerRadialTail lambda p) =
      (ccm24PrimeEulerCoefficient p : ℂ) •
        (primeEulerExteriorAdjointContinuation lambda p ∘L
          primeEulerRadialBoundaryStep lambda p) := by
  apply ContinuousLinearMap.ext
  intro x
  let E := radialSupportProjection lambda
  let F := radialComplement lambda
  let N := (normalizedPrimeEulerInverse p)†
  let U := (cc20GlobalLogTranslation
    (Real.log p)).toContinuousLinearMap
  let V := primeEulerRadialTail lambda p
  let C := primeEulerRadialBoundaryStep lambda p
  let q : ℂ := ccm24PrimeEulerCoefficient p
  let a : ℂ := (1 - ccm24PrimeEulerCoefficient p : ℝ)
  have hEfixed (y : finiteSCarrier) : E (E y) = E y := by
    exact (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2
      (Submodule.starProjection_apply_mem _ _)
  have hFcompE : F (E x) = 0 :=
    radialComplement_apply_eq_zero_of_fixed lambda (hEfixed x)
  have hVfixed : E (V x) = V x := by
    have h := DFunLike.congr_fun
      (radialSupportProjection_comp_primeEulerRadialTail_eq_self lambda p) x
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hCfixed : F (C x) = C x := by
    have h := DFunLike.congr_fun
      (radialComplement_comp_primeEulerRadialBoundaryStep_eq_self lambda p) x
    simpa only [ContinuousLinearMap.comp_apply] using h
  have htranslation := DFunLike.congr_fun
    (primeEulerPositiveTranslation_comp_radialSupport_eq_tail_add_boundary
      lambda p) x
  change U (E x) = V x + C x at htranslation
  have hglobal := DFunLike.congr_fun
    (normalizedPrimeEulerInverse_adjoint_comp_positiveEulerFactor p) (E x)
  change N (E x - q • U (E x)) = a • E x at hglobal
  have houter : F (N (E x - q • U (E x))) = 0 := by
    calc
      F (N (E x - q • U (E x))) = F (a • E x) :=
        congrArg F hglobal
      _ = a • F (E x) := by rw [map_smul]
      _ = 0 := by rw [hFcompE, smul_zero]
  simp only [map_sub, map_smul] at houter
  rw [htranslation, map_add, map_add] at houter
  have hsum :
      F (N (E x)) = q • (F (N (V x)) + F (N (C x))) := by
    exact sub_eq_zero.mp houter
  change F (N (E (x - q • V x))) =
    q • F (N (F (C x)))
  rw [map_sub, map_smul, hVfixed, hCfixed]
  simp only [map_sub, map_smul]
  rw [hsum]
  module

/-! ## First-exit factorization -/

/-- The complete exterior adjoint block is the exterior continuation applied
to Proof 613's canonical first-exit boundary. -/
theorem primeEulerExteriorAdjointCrossing_eq_continuation_comp_geometricBoundary
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerExteriorAdjointCrossing lambda p =
      primeEulerExteriorAdjointContinuation lambda p ∘L
        primeEulerRadialGeometricBoundary lambda p := by
  let X := primeEulerExteriorAdjointCrossing lambda p
  let Y := primeEulerExteriorAdjointContinuation lambda p
  let G := primeEulerRadialGeometricBoundary lambda p
  let C := primeEulerRadialBoundaryStep lambda p
  let A := (ccm24PrimeEulerCoefficient p : ℂ) •
    primeEulerRadialTail lambda p
  let R := ∑' n : ℕ, A ^ n
  have hA : ‖A‖ < 1 := by
    simpa only [A] using
      norm_coefficient_smul_primeEulerRadialTail_lt_one lambda p
  have hinverse : (1 - A) * R = 1 := by
    simpa only [R] using mul_neg_geom_series A hA
  have hX : X * (1 - A) =
      (ccm24PrimeEulerCoefficient p : ℂ) • (Y * C) := by
    simpa only [X, Y, C, A, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.one_def] using
      primeEulerExteriorAdjointCrossing_comp_one_sub_tail lambda p
  have hG : G * (1 - A) =
      (ccm24PrimeEulerCoefficient p : ℂ) • C := by
    simpa only [G, C, A, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.one_def] using
      primeEulerRadialGeometricBoundary_comp_one_sub_tail lambda p
  have hscalar :
      (ccm24PrimeEulerCoefficient p : ℂ) • (Y * C) =
        Y * ((ccm24PrimeEulerCoefficient p : ℂ) • C) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smul_apply, map_smul]
  change X = Y * G
  calc
    X = X * 1 := by simp
    _ = X * ((1 - A) * R) := by rw [hinverse]
    _ = (X * (1 - A)) * R := by rw [mul_assoc]
    _ = ((ccm24PrimeEulerCoefficient p : ℂ) • (Y * C)) * R := by
      rw [hX]
    _ = (Y * ((ccm24PrimeEulerCoefficient p : ℂ) • C)) * R := by
      rw [hscalar]
    _ = (Y * (G * (1 - A))) * R := by rw [hG]
    _ = (Y * G) * ((1 - A) * R) := by noncomm_ring
    _ = Y * G := by rw [hinverse, mul_one]

/-! ## Uniform exterior readout -/

private theorem norm_threefold_comp_le_one
    (A B C : finiteSCarrier →L[ℂ] finiteSCarrier)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hC : ‖C‖ ≤ 1) :
    ‖A ∘L B ∘L C‖ ≤ 1 := by
  have hAB : ‖A ∘L B‖ ≤ 1 := by
    calc
      ‖A ∘L B‖ ≤ ‖A‖ * ‖B‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hA hB (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  calc
    ‖A ∘L B ∘L C‖ ≤ ‖A ∘L B‖ * ‖C‖ :=
      ContinuousLinearMap.opNorm_comp_le (A ∘L B) C
    _ ≤ 1 * 1 := mul_le_mul hAB hC (norm_nonneg _) zero_le_one
    _ = 1 := by ring

theorem norm_primeEulerExteriorAdjointContinuation_le_one
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    ‖primeEulerExteriorAdjointContinuation lambda p‖ ≤ 1 := by
  have hF := norm_radialComplement_le_one lambda
  have hN : ‖(normalizedPrimeEulerInverse p)†‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact norm_normalizedPrimeEulerInverse_le_one p
  exact norm_threefold_comp_le_one _ _ _ hF hN hF

theorem norm_primeEulerExteriorAdjointReadout_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    ‖primeEulerExteriorAdjointReadout lambda p‖ ≤ 32 := by
  calc
    ‖primeEulerExteriorAdjointReadout lambda p‖ ≤
        ‖primeEulerExteriorAdjointContinuation lambda p‖ *
          ‖primeEulerRadialGeometricReadout lambda p‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 32 := mul_le_mul
      (norm_primeEulerExteriorAdjointContinuation_le_one lambda p)
      (norm_primeEulerRadialGeometricReadout_le lambda p)
      (norm_nonneg _) zero_le_one
    _ = 32 := by ring

/-- The norm-`32` readout recovers the complete exterior adjoint renewal block
on every actual new suffix frame. -/
theorem primeEulerExteriorAdjointReadout_comp_ambientLossColumn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    primeEulerExteriorAdjointReadout lambda p ∘L
        newFrameAntiresonantColumn lambda p S =
      primeEulerExteriorAdjointCrossing lambda p ∘L
        newSuffixFrame lambda S := by
  rw [primeEulerExteriorAdjointReadout,
    ContinuousLinearMap.comp_assoc,
    primeEulerRadialGeometricReadout_comp_ambientLossColumn]
  rw [← ContinuousLinearMap.comp_assoc,
    ← primeEulerExteriorAdjointCrossing_eq_continuation_comp_geometricBoundary]

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantExteriorAdjointRenewal
end CCM25Concrete
end Source
end ConnesWeilRH
