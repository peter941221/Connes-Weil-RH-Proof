/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientLossKernel
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAmbientChannel

/-!
# Kernel of the renewed antiresonant channel

The Proof 628 denominator is

```text
L_p^dagger * N_p^dagger * newFrame_(p,S).
```

Although `L_p^dagger` has no uniform lower bound, this complete source
column has trivial kernel.  The proof keeps the normalized inverse attached:
if `y = N_p^dagger newFrame x` and `L_p^dagger y = 0`, then the exact Euler
difference identity gives `U_p^dagger y = y`.  The adjoint Euler pairing also
gives `U_p^dagger y = rho_p newFrame x`, so `y` is a nonzero scalar multiple
of the radially supported new frame.  The half-line antiresonant propagation
theorem then forces `x = 0`.

This proves kernel compatibility only.  It supplies no closed-range bound or
route-uniform Douglas quotient.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelKernel

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaAmbientLossKernel
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAmbientChannel
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSParameterizedSoninSubspace
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Ambient Euler identities -/

/-- Adjointing `N_p U_p = rho_p I` in the physical order gives the identity
used by the kernel argument. -/
theorem normalizedPrimeEulerFrameTransport_adjoint_comp_inverse_adjoint
    (p : CCM24VisiblePrime) :
    (normalizedPrimeEulerFrameTransport p)† ∘L
        (normalizedPrimeEulerInverse p)† =
      (primeSchurMarkovScalar p : ℂ) •
        ContinuousLinearMap.id ℂ finiteSCarrier := by
  have h := congrArg ContinuousLinearMap.adjoint
    (normalizedPrimeEulerInverse_comp_frameTransport p)
  have hstar : star (primeSchurMarkovScalar p : ℂ) =
      (primeSchurMarkovScalar p : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  simpa only [ContinuousLinearMap.adjoint_comp, map_smulₛₗ,
    starRingEnd_apply, hstar, ContinuousLinearMap.adjoint_id] using h

/-- The ambient antiresonant loss has trivial kernel on every vector in the
genuine upper radial-support subspace. -/
theorem primeEulerAmbientLossFactor_adjoint_eq_zero_of_mem_radialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (u : finiteSCarrier)
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda)
    (hzero : ((primeEulerAmbientLossFactor p)†) u = 0) :
    u = 0 := by
  have hscale : 0 < primeEulerAmbientLossScale p := by
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (lt_trans Nat.zero_lt_one p.property)
    have hcoeff : 0 < ccm24PrimeEulerCoefficient p := by
      unfold ccm24PrimeEulerCoefficient
      exact div_pos zero_lt_one (Real.sqrt_pos.2 hp0)
    unfold primeEulerAmbientLossScale
    exact div_pos (Real.sqrt_pos.2 hcoeff) (by linarith)
  have hscaleC : (primeEulerAmbientLossScale p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hscale.ne'
  rw [primeEulerAmbientLossFactor_adjoint_eq] at hzero
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply] at hzero
  have hanti :
      u + cc20GlobalLogTranslation (Real.log p) u = 0 :=
    (smul_eq_zero.mp hzero).resolve_left hscaleC
  have hpReal : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.property
  exact ccm24LogRadialSupport_add_translation_injective
    lambda hu (Real.log_pos hpReal) hanti

/-! ## The complete renewed source column -/

/-- A zero of the complete renewed column already has zero new-frame image.
No route-validity premise is needed. -/
theorem suffixEulerFrameRenewedAntiresonantColumn_eq_zero_imp_newFrame_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda)
    (hzero : suffixEulerFrameRenewedAntiresonantColumn lambda p S x = 0) :
    (suffixEulerFrameSchurStep lambda p S).newFrame x = 0 := by
  let u := (suffixEulerFrameSchurStep lambda p S).newFrame x
  let y := ((normalizedPrimeEulerInverse p)†) u
  have hloss : ((primeEulerAmbientLossFactor p)†) y = 0 := by
    simpa only [suffixEulerFrameRenewedAntiresonantColumn,
      ContinuousLinearMap.comp_apply, u, y] using hzero
  have hfixed : ((normalizedPrimeEulerFrameTransport p)†) y = y := by
    have hpoint := DFunLike.congr_fun
      (normalizedPrimeEulerFrameTransport_adjoint_sub_id_eq_neg_sqrtCoefficient_smul_primeEulerAmbientLossFactor_adjoint
        p) y
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
      hloss, smul_zero, neg_zero] at hpoint
    exact sub_eq_zero.mp hpoint
  have hpair := DFunLike.congr_fun
    (normalizedPrimeEulerFrameTransport_adjoint_comp_inverse_adjoint p) u
  have hy : y = (primeSchurMarkovScalar p : ℂ) • u := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply] at hpair
    exact hfixed.symm.trans hpair
  have hlossScaled :
      (primeSchurMarkovScalar p : ℂ) •
          ((primeEulerAmbientLossFactor p)†) u = 0 := by
    rw [hy, map_smul] at hloss
    exact hloss
  have hrho : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (primeSchurMarkovScalar_pos p))
  have hlossU : ((primeEulerAmbientLossFactor p)†) u = 0 :=
    (smul_eq_zero.mp hlossScaled).resolve_left hrho
  have hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda := by
    change newSuffixFrame lambda S x ∈
      ccm24LogRadialSupportClosedSubspace lambda
    exact (newSuffixFrame_mem lambda S x).1
  exact primeEulerAmbientLossFactor_adjoint_eq_zero_of_mem_radialSupport
    lambda p u hu hlossU

/-- The complete renewed source column has trivial kernel for every prime and
suffix, despite lacking a uniform spectral gap. -/
theorem suffixEulerFrameRenewedAntiresonantColumn_eq_zero_iff
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    suffixEulerFrameRenewedAntiresonantColumn lambda p S x = 0 ↔ x = 0 := by
  constructor
  · intro hzero
    have hframe :=
      suffixEulerFrameRenewedAntiresonantColumn_eq_zero_imp_newFrame_eq_zero
        lambda p S x hzero
    have hisometry := DFunLike.congr_fun
      (suffixEulerFrameSchurStep lambda p S).newFrame_isometry x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      hframe, map_zero] at hisometry
    exact hisometry.symm
  · rintro rfl
    exact map_zero _

theorem suffixEulerFrameRenewedAntiresonantColumn_injective
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    Function.Injective
      (suffixEulerFrameRenewedAntiresonantColumn lambda p S) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply
    (suffixEulerFrameRenewedAntiresonantColumn_eq_zero_iff
      lambda p S (x - y)).mp
  simpa only [map_sub] using sub_eq_zero.mpr hxy

/-- The exact kernel-compatibility condition required by any Douglas
factorization is automatic for the genuine renewed channel. -/
theorem signedCompressedInteriorOwner_eq_zero_of_renewedColumn_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda)
    (hzero : suffixEulerFrameRenewedAntiresonantColumn lambda p S x = 0) :
    signedCompressedInteriorOwner owner lambda p S x = 0 := by
  rw [(suffixEulerFrameRenewedAntiresonantColumn_eq_zero_iff
    lambda p S x).mp hzero, map_zero]

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelKernel
end CCM25Concrete
end Source
end ConnesWeilRH
