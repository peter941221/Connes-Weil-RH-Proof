/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantSignedRadialReduction

/-!
# Scalar normalization of the surviving interior renewal

Proof 617 reduces the complete old-carrier signed numerator to the interior
adjoint renewal.  The active coframe normal form uses the scalar-normalized
right inverse

```text
V_scalar = rho_p^(-1) N.
```

Since `rho_p` is real, taking the adjoint preserves that scalar.  After the
radial support projection, the exact surviving pullback is therefore

```text
signedRow * V_scalar^dagger * E
  = rho_p^(-1) * signedRow * (E N^dagger E).
```

The same identity is proved after the actual new suffix frame.  This removes
the scalar normalization from the analytic bottom, but supplies no bound on
the compressed renewal itself.  Bone 1, Gate 3U, the finite-S sign, Burnol's
identity, and RH remain open.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantScalarInterior

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryResolvent
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantSignedRadial
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeScalarRightInverse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
open CCM24FiniteSCausalMarkov
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The real scalar survives the adjoint unchanged -/

theorem scalarNormalizedPrimeEulerInverse_adjoint_eq_inv_smul
    (p : CCM24VisiblePrime) :
    (scalarNormalizedPrimeEulerInverse p)† =
      (primeSchurMarkovScalar p : ℂ)⁻¹ •
        (normalizedPrimeEulerInverse p)† := by
  have hstar : star ((primeSchurMarkovScalar p : ℂ)⁻¹) =
      (primeSchurMarkovScalar p : ℂ)⁻¹ := by
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hadjoint := ContinuousLinearMap.adjoint.map_smulₛₗ
    ((primeSchurMarkovScalar p : ℂ)⁻¹)
    (normalizedPrimeEulerInverse p)
  simpa only [scalarNormalizedPrimeEulerInverse, hstar,
    starRingEnd_apply] using hadjoint

/-! ## Exact scalar-normalized interior owner -/

theorem signedTelescope_comp_scalarInverseAdjoint_radialSupport_eq_inv_smul_compressed
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
        (scalarNormalizedPrimeEulerInverse p)† ∘L
          radialSupportProjection lambda =
      (primeSchurMarkovScalar p : ℂ)⁻¹ •
        (suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
          primeEulerCompressedAdjointRenewal lambda p) := by
  rw [scalarNormalizedPrimeEulerInverse_adjoint_eq_inv_smul]
  apply ContinuousLinearMap.ext
  intro x
  have hbase := DFunLike.congr_fun
    (signedTelescope_comp_inverseAdjoint_radialSupport_eq_compressed
      owner lambda p S) x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul] at hbase ⊢
  rw [hbase]

theorem signedTelescope_comp_scalarInverseAdjoint_newFrame_eq_inv_smul_compressed
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
        (scalarNormalizedPrimeEulerInverse p)† ∘L
          newSuffixFrame lambda S =
      (primeSchurMarkovScalar p : ℂ)⁻¹ •
        (suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
          primeEulerCompressedAdjointRenewal lambda p ∘L
            newSuffixFrame lambda S) := by
  apply ContinuousLinearMap.ext
  intro x
  have hfixed :
      radialSupportProjection lambda (newSuffixFrame lambda S x) =
        newSuffixFrame lambda S x := by
    have h := DFunLike.congr_fun
      (radialSupportProjection_comp_newSuffixFrame lambda S) x
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hbase := DFunLike.congr_fun
    (signedTelescope_comp_scalarInverseAdjoint_radialSupport_eq_inv_smul_compressed
      owner lambda p S)
    (newSuffixFrame lambda S x)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply] at hbase ⊢
  calc
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S
          (ContinuousLinearMap.adjoint
            (scalarNormalizedPrimeEulerInverse p)
              (newSuffixFrame lambda S x)) =
        suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S
          (ContinuousLinearMap.adjoint
            (scalarNormalizedPrimeEulerInverse p)
              (radialSupportProjection lambda
                (newSuffixFrame lambda S x))) := by
      rw [hfixed]
    _ = (primeSchurMarkovScalar p : ℂ)⁻¹ •
        suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S
          (primeEulerCompressedAdjointRenewal lambda p
            (newSuffixFrame lambda S x)) := hbase

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantScalarInterior
end CCM25Concrete
end Source
end ConnesWeilRH
