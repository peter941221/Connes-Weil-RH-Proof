/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkov

/-!
# Resolvent identity for the antiresonant geometric boundary

Proof 613 constructs the genuine Euler-weighted radial boundary series

```text
G_p = sum_(n >= 0) q_p^(n+1) C_p V_p^n.
```

This module identifies its intrinsic renewal equation and right resolvent:

```text
G_p = q_p C_p + q_p G_p V_p,
G_p (I - q_p V_p) = q_p C_p,
G_p = q_p C_p sum_(n >= 0) (q_p V_p)^n.
```

Thus the named series is not an artificial collection of independently
estimated blocks: it is the canonical compressed boundary resolvent.  This
still controls only the geometric radial boundary channel.  It does not
identify the complete signed raw numerator with that channel or control the
remaining metric-coframe Gram correction.  Bone 1, Gate 3U, the finite-S
sign, Burnol's identity, and RH remain open.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryResolvent

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCausalMarkov
open CCM24FiniteSForwardRenewal
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryReadout
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSProjectionTrace
open SelectedCrossingOperatorBridge

/-! ## Renewal recurrence -/

theorem primeEulerRadialGeometricBoundaryTerm_succ
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (n : ℕ) :
    primeEulerRadialGeometricBoundaryTerm lambda p (n + 1) =
      (ccm24PrimeEulerCoefficient p : ℂ) •
        (primeEulerRadialGeometricBoundaryTerm lambda p n ∘L
          primeEulerRadialTail lambda p) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [primeEulerRadialGeometricBoundaryTerm,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    smul_smul]
  rw [pow_succ]
  congr 1
  ring

/-- The geometric boundary is the fixed point of one radial renewal step. -/
theorem primeEulerRadialGeometricBoundary_eq_first_add_renewal
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerRadialGeometricBoundary lambda p =
      (ccm24PrimeEulerCoefficient p : ℂ) •
          primeEulerRadialBoundaryStep lambda p +
        (ccm24PrimeEulerCoefficient p : ℂ) •
          (primeEulerRadialGeometricBoundary lambda p ∘L
            primeEulerRadialTail lambda p) := by
  let term := primeEulerRadialGeometricBoundaryTerm lambda p
  let V := primeEulerRadialTail lambda p
  have hterm : Summable term :=
    summable_primeEulerRadialGeometricBoundaryTerm lambda p
  have htail :
      (∑' n : ℕ, term (n + 1)) =
        (ccm24PrimeEulerCoefficient p : ℂ) •
          (primeEulerRadialGeometricBoundary lambda p ∘L V) := by
    calc
      (∑' n : ℕ, term (n + 1)) =
          ∑' n : ℕ, (ccm24PrimeEulerCoefficient p : ℂ) •
            (term n ∘L V) := by
        apply tsum_congr
        intro n
        simpa only [term, V] using
          primeEulerRadialGeometricBoundaryTerm_succ lambda p n
      _ = (ccm24PrimeEulerCoefficient p : ℂ) •
          (∑' n : ℕ, term n ∘L V) := by
        rw [tsum_const_smul'']
      _ = (ccm24PrimeEulerCoefficient p : ℂ) •
          ((∑' n : ℕ, term n) ∘L V) := by
        change (ccm24PrimeEulerCoefficient p : ℂ) •
            (∑' n : ℕ, term n * V) =
          (ccm24PrimeEulerCoefficient p : ℂ) •
            ((∑' n : ℕ, term n) * V)
        rw [hterm.tsum_mul_right]
      _ = (ccm24PrimeEulerCoefficient p : ℂ) •
          (primeEulerRadialGeometricBoundary lambda p ∘L V) := by
        rfl
  have hzero :
      term 0 = (ccm24PrimeEulerCoefficient p : ℂ) •
        primeEulerRadialBoundaryStep lambda p := by
    change ((ccm24PrimeEulerCoefficient p : ℂ) ^ 1) •
        (primeEulerRadialBoundaryStep lambda p *
          (1 : finiteSCarrier →L[ℂ] finiteSCarrier)) =
      (ccm24PrimeEulerCoefficient p : ℂ) •
        primeEulerRadialBoundaryStep lambda p
    rw [mul_one, pow_one]
  calc
    primeEulerRadialGeometricBoundary lambda p =
        term 0 + ∑' n : ℕ, term (n + 1) := by
      exact hterm.tsum_eq_zero_add
    _ = term 0 + (ccm24PrimeEulerCoefficient p : ℂ) •
        (primeEulerRadialGeometricBoundary lambda p ∘L V) := by
      rw [htail]
    _ = (ccm24PrimeEulerCoefficient p : ℂ) •
          primeEulerRadialBoundaryStep lambda p +
        (ccm24PrimeEulerCoefficient p : ℂ) •
          (primeEulerRadialGeometricBoundary lambda p ∘L
            primeEulerRadialTail lambda p) := by
      rw [hzero]

/-! ## Right resolvent -/

/-- The renewal equation written as a right resolvent identity. -/
theorem primeEulerRadialGeometricBoundary_comp_one_sub_tail
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerRadialGeometricBoundary lambda p ∘L
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          (ccm24PrimeEulerCoefficient p : ℂ) •
            primeEulerRadialTail lambda p) =
      (ccm24PrimeEulerCoefficient p : ℂ) •
        primeEulerRadialBoundaryStep lambda p := by
  apply ContinuousLinearMap.ext
  intro x
  have hrec := DFunLike.congr_fun
    (primeEulerRadialGeometricBoundary_eq_first_add_renewal lambda p) x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply, map_sub,
    map_smul, ContinuousLinearMap.add_apply] at hrec ⊢
  exact sub_eq_iff_eq_add.mpr hrec

theorem norm_coefficient_smul_primeEulerRadialTail_lt_one
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    ‖(ccm24PrimeEulerCoefficient p : ℂ) •
        primeEulerRadialTail lambda p‖ < 1 := by
  have hq := ccm24PrimeEulerCoefficient_nonneg p
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  calc
    ccm24PrimeEulerCoefficient p * ‖primeEulerRadialTail lambda p‖ ≤
        ccm24PrimeEulerCoefficient p * 1 :=
      mul_le_mul_of_nonneg_left
        (norm_primeEulerRadialTail_le_one lambda p) hq
    _ = ccm24PrimeEulerCoefficient p := by ring
    _ < 1 := ccm24PrimeEulerCoefficient_lt_one p

/-- Explicit Neumann-series form of the compressed boundary resolvent. -/
theorem primeEulerRadialGeometricBoundary_eq_resolventSeries
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerRadialGeometricBoundary lambda p =
      ((ccm24PrimeEulerCoefficient p : ℂ) •
          primeEulerRadialBoundaryStep lambda p) ∘L
        (∑' n : ℕ,
          ((ccm24PrimeEulerCoefficient p : ℂ) •
            primeEulerRadialTail lambda p) ^ n) := by
  let A := (ccm24PrimeEulerCoefficient p : ℂ) •
    primeEulerRadialTail lambda p
  let R := ∑' n : ℕ, A ^ n
  have hA : ‖A‖ < 1 := by
    simpa only [A] using
      norm_coefficient_smul_primeEulerRadialTail_lt_one lambda p
  have hinverse : (1 - A) * R = 1 := by
    simpa only [R] using mul_neg_geom_series A hA
  have hboundary :
      primeEulerRadialGeometricBoundary lambda p * (1 - A) =
        (ccm24PrimeEulerCoefficient p : ℂ) •
          primeEulerRadialBoundaryStep lambda p := by
    simpa only [A, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.one_def] using
      primeEulerRadialGeometricBoundary_comp_one_sub_tail lambda p
  change primeEulerRadialGeometricBoundary lambda p =
    ((ccm24PrimeEulerCoefficient p : ℂ) •
      primeEulerRadialBoundaryStep lambda p) * R
  calc
    primeEulerRadialGeometricBoundary lambda p =
        primeEulerRadialGeometricBoundary lambda p * 1 := by simp
    _ = primeEulerRadialGeometricBoundary lambda p * ((1 - A) * R) := by
      rw [hinverse]
    _ = (primeEulerRadialGeometricBoundary lambda p * (1 - A)) * R := by
      rw [mul_assoc]
    _ = ((ccm24PrimeEulerCoefficient p : ℂ) •
        primeEulerRadialBoundaryStep lambda p) * R := by
      rw [hboundary]

/-! ## The actual compressed adjoint renewal -/

/-- Compression of the genuine normalized inverse adjoint to the upper
radial half-line. -/
noncomputable def primeEulerCompressedAdjointRenewal
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialSupportProjection lambda ∘L
    (normalizedPrimeEulerInverse p)† ∘L
      radialSupportProjection lambda

/-- The causal normalized inverse cannot leave the upper radial support. -/
theorem radialComplement_comp_normalizedPrimeEulerInverse_comp_radialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    radialComplement lambda ∘L
        normalizedPrimeEulerInverse p ∘L
          radialSupportProjection lambda = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hsource :
      radialSupportProjection lambda x ∈
        ccm24LogRadialSupportClosedSubspace lambda :=
    Submodule.starProjection_apply_mem _ _
  have hinverse :
      (ccm24PrimeEulerTransportEquiv p).symm
          (radialSupportProjection lambda x) ∈
        ccm24LogRadialSupportClosedSubspace lambda :=
    ccm24PrimeEulerTransportEquiv_symm_mem_logRadialSupport
      lambda p hsource
  have hnormalized :
      normalizedPrimeEulerInverse p
          (radialSupportProjection lambda x) ∈
        ccm24LogRadialSupportClosedSubspace lambda := by
    change ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
        (ccm24PrimeEulerTransportEquiv p).symm
          (radialSupportProjection lambda x) ∈
      ccm24LogRadialSupportClosedSubspace lambda
    exact (ccm24LogRadialSupportClosedSubspace lambda).smul_mem _ hinverse
  have hfixed :=
    (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2 hnormalized
  have hfixed' :
      radialSupportProjection lambda
          (normalizedPrimeEulerInverse p
            (radialSupportProjection lambda x)) =
        normalizedPrimeEulerInverse p
          (radialSupportProjection lambda x) := by
    simpa only [radialSupportProjection,
      ccm24LogRadialSupportProjection] using hfixed
  simp only [radialComplement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply]
  rw [hfixed']
  exact sub_self _

/-- After taking adjoints, vectors which already lie below the radial cutoff
cannot re-enter the compressed renewal. -/
theorem radialSupport_comp_normalizedPrimeEulerInverse_adjoint_comp_complement
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    radialSupportProjection lambda ∘L
        (normalizedPrimeEulerInverse p)† ∘L
          radialComplement lambda = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint
    (radialComplement_comp_normalizedPrimeEulerInverse_comp_radialSupport
      lambda p)
  have hradial :
      (radialSupportProjection lambda)† =
        radialSupportProjection lambda :=
    (radialSupportProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq
  have hcomplement :
      (radialComplement lambda)† = radialComplement lambda :=
    (radialSupportProjection_isStarProjection lambda).one_sub
      |>.isSelfAdjoint.adjoint_eq
  simpa only [ContinuousLinearMap.adjoint_comp, hradial, hcomplement,
    map_zero] using h

/-- The left compression may be inserted on the input side of the adjoint
renewal. This is the operator form of one-sided no-reentry. -/
theorem radialSupport_comp_normalizedPrimeEulerInverse_adjoint_eq_compressed
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    radialSupportProjection lambda ∘L
        (normalizedPrimeEulerInverse p)† =
      radialSupportProjection lambda ∘L
        (normalizedPrimeEulerInverse p)† ∘L
          radialSupportProjection lambda := by
  apply ContinuousLinearMap.ext
  intro x
  have hzero := DFunLike.congr_fun
    (radialSupport_comp_normalizedPrimeEulerInverse_adjoint_comp_complement
      lambda p) x
  simp only [ContinuousLinearMap.comp_apply, radialComplement,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub,
    ContinuousLinearMap.zero_apply] at hzero ⊢
  exact sub_eq_zero.mp hzero

/-- The genuine normalized inverse is a right inverse of the unnormalized
one-prime Euler factor, with total renewal mass `1-q_p`. -/
theorem primeEulerTransport_comp_normalizedPrimeEulerInverse
    (p : CCM24VisiblePrime) :
    (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap ∘L
        normalizedPrimeEulerInverse p =
      ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ finiteSCarrier := by
  apply ContinuousLinearMap.ext
  intro x
  change ccm24PrimeEulerTransportEquiv p
      (((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
        (ccm24PrimeEulerTransportEquiv p).symm x) =
    ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) • x
  rw [map_smul, (ccm24PrimeEulerTransportEquiv p).apply_symm_apply]

/-- Adjoint renewal equation in the positive-translation orientation. -/
theorem normalizedPrimeEulerInverse_adjoint_comp_positiveEulerFactor
    (p : CCM24VisiblePrime) :
    (normalizedPrimeEulerInverse p)† ∘L
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          (ccm24PrimeEulerCoefficient p : ℂ) •
            (cc20GlobalLogTranslation
              (Real.log p)).toContinuousLinearMap) =
      ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ finiteSCarrier := by
  have h := congrArg ContinuousLinearMap.adjoint
    (primeEulerTransport_comp_normalizedPrimeEulerInverse p)
  have hstar :
      star (((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ)) =
        ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  simpa only [ContinuousLinearMap.adjoint_comp, map_smulₛₗ,
    starRingEnd_apply, hstar, ContinuousLinearMap.adjoint_id,
    primeEulerTransportAdjoint_eq] using h

/-- The genuine compressed inverse adjoint has the same right denominator as
the geometric boundary series. -/
theorem primeEulerCompressedAdjointRenewal_comp_one_sub_tail
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerCompressedAdjointRenewal lambda p ∘L
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          (ccm24PrimeEulerCoefficient p : ℂ) •
            primeEulerRadialTail lambda p) =
      ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
        radialSupportProjection lambda := by
  apply ContinuousLinearMap.ext
  intro x
  let E := radialSupportProjection lambda
  let N := (normalizedPrimeEulerInverse p)†
  let U := (cc20GlobalLogTranslation
    (Real.log p)).toContinuousLinearMap
  let V := primeEulerRadialTail lambda p
  let q : ℂ := ccm24PrimeEulerCoefficient p
  let a : ℂ := (1 - ccm24PrimeEulerCoefficient p : ℝ)
  have hEfixed (y : finiteSCarrier) : E (E y) = E y := by
    exact (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2
      (Submodule.starProjection_apply_mem _ _)
  have hVapply : V x = E (U (E x)) := by
    rfl
  have hVfixed : E (V x) = V x := by
    rw [hVapply, hEfixed]
  have hglobal := DFunLike.congr_fun
    (normalizedPrimeEulerInverse_adjoint_comp_positiveEulerFactor p) (E x)
  change N (E x - q • U (E x)) = a • E x at hglobal
  have hglobalCompressed := congrArg E hglobal
  rw [map_smul, hEfixed] at hglobalCompressed
  have hnoReentry := DFunLike.congr_fun
    (radialSupport_comp_normalizedPrimeEulerInverse_adjoint_eq_compressed
      lambda p) (E x - q • U (E x))
  change E (N (E x - q • U (E x))) =
    E (N (E (E x - q • U (E x)))) at hnoReentry
  have hprojected :
      E (E x - q • U (E x)) = E x - q • V x := by
    rw [map_sub, map_smul, hEfixed, hVapply]
  rw [hprojected] at hnoReentry
  change E (N (E (x - q • V x))) = a • E x
  rw [map_sub, map_smul, hVfixed]
  rw [← hnoReentry]
  exact hglobalCompressed

theorem primeEulerRadialBoundaryStep_comp_radialSupportProjection
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerRadialBoundaryStep lambda p ∘L
        radialSupportProjection lambda =
      primeEulerRadialBoundaryStep lambda p := by
  apply ContinuousLinearMap.ext
  intro x
  have hfixed :
      radialSupportProjection lambda
          (radialSupportProjection lambda x) =
        radialSupportProjection lambda x :=
    (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2
      (Submodule.starProjection_apply_mem _ _)
  simp only [primeEulerRadialBoundaryStep,
    ContinuousLinearMap.comp_apply]
  rw [hfixed]

/-- The compressed adjoint renewal is the lower Euler factor times the same
Neumann resolvent which appears in the geometric boundary. -/
theorem primeEulerCompressedAdjointRenewal_eq_resolventSeries
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerCompressedAdjointRenewal lambda p =
      ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
        (radialSupportProjection lambda ∘L
          (∑' n : ℕ,
            ((ccm24PrimeEulerCoefficient p : ℂ) •
              primeEulerRadialTail lambda p) ^ n)) := by
  let A := (ccm24PrimeEulerCoefficient p : ℂ) •
    primeEulerRadialTail lambda p
  let R := ∑' n : ℕ, A ^ n
  have hA : ‖A‖ < 1 := by
    simpa only [A] using
      norm_coefficient_smul_primeEulerRadialTail_lt_one lambda p
  have hinverse : (1 - A) * R = 1 := by
    simpa only [R] using mul_neg_geom_series A hA
  have hcompressed :
      primeEulerCompressedAdjointRenewal lambda p * (1 - A) =
        ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
          radialSupportProjection lambda := by
    simpa only [A, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.one_def] using
      primeEulerCompressedAdjointRenewal_comp_one_sub_tail lambda p
  change primeEulerCompressedAdjointRenewal lambda p =
    ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
      (radialSupportProjection lambda * R)
  calc
    primeEulerCompressedAdjointRenewal lambda p =
        primeEulerCompressedAdjointRenewal lambda p * 1 := by simp
    _ = primeEulerCompressedAdjointRenewal lambda p * ((1 - A) * R) := by
      rw [hinverse]
    _ = (primeEulerCompressedAdjointRenewal lambda p * (1 - A)) * R := by
      rw [mul_assoc]
    _ = (((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
        radialSupportProjection lambda) * R := by
      rw [hcompressed]
    _ = ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
        (radialSupportProjection lambda * R) := by
      rw [smul_mul_assoc]

/-- Identification of Proof 613's series with the top-boundary readout of
the genuine normalized Euler inverse adjoint. -/
theorem primeEulerRadialGeometricBoundary_eq_compressedAdjointRenewal
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerRadialGeometricBoundary lambda p =
      ((ccm24PrimeEulerCoefficient p /
          (1 - ccm24PrimeEulerCoefficient p) : ℝ) : ℂ) •
        (primeEulerRadialBoundaryStep lambda p ∘L
          primeEulerCompressedAdjointRenewal lambda p) := by
  let S := ∑' n : ℕ,
    ((ccm24PrimeEulerCoefficient p : ℂ) •
      primeEulerRadialTail lambda p) ^ n
  have hlower : 1 - ccm24PrimeEulerCoefficient p ≠ 0 :=
    ne_of_gt (sub_pos.mpr (ccm24PrimeEulerCoefficient_lt_one p))
  have hcoefficient :
      (((ccm24PrimeEulerCoefficient p /
          (1 - ccm24PrimeEulerCoefficient p) : ℝ) : ℂ) *
        ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ)) =
      (ccm24PrimeEulerCoefficient p : ℂ) := by
    have hreal :
        (ccm24PrimeEulerCoefficient p /
            (1 - ccm24PrimeEulerCoefficient p)) *
          (1 - ccm24PrimeEulerCoefficient p) =
        ccm24PrimeEulerCoefficient p := by
      field_simp [hlower]
    exact_mod_cast hreal
  rw [primeEulerRadialGeometricBoundary_eq_resolventSeries,
    primeEulerCompressedAdjointRenewal_eq_resolventSeries]
  apply ContinuousLinearMap.ext
  intro x
  have hboundaryFixed := DFunLike.congr_fun
    (primeEulerRadialBoundaryStep_comp_radialSupportProjection lambda p)
    (S x)
  have hboundaryFixed' :
      primeEulerRadialBoundaryStep lambda p
          (radialSupportProjection lambda (S x)) =
        primeEulerRadialBoundaryStep lambda p (S x) := by
    simpa only [ContinuousLinearMap.comp_apply] using hboundaryFixed
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  rw [hboundaryFixed', hcoefficient]

/-- The uniformly bounded Proof 613 readout now lands in the genuine
compressed adjoint-renewal boundary channel on every actual suffix frame. -/
theorem primeEulerRadialGeometricReadout_comp_ambientLossColumn_eq_compressedAdjointRenewal
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    primeEulerRadialGeometricReadout lambda p ∘L
        newFrameAntiresonantColumn lambda p S =
      ((ccm24PrimeEulerCoefficient p /
          (1 - ccm24PrimeEulerCoefficient p) : ℝ) : ℂ) •
        (primeEulerRadialBoundaryStep lambda p ∘L
          primeEulerCompressedAdjointRenewal lambda p ∘L
            newSuffixFrame lambda S) := by
  rw [primeEulerRadialGeometricReadout_comp_ambientLossColumn,
    primeEulerRadialGeometricBoundary_eq_compressedAdjointRenewal]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply]

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryResolvent
end CCM25Concrete
end Source
end ConnesWeilRH
