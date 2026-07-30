/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSwappedLocalPairRadialColumnBridge
import Mathlib.Algebra.Ring.GeomSum

/-!
# Finite-horizon antiresonant coboundary

For an endomorphism `U`, the finite alternating polynomial

```text
P_N(U) = I - U + U^2 - ... + (-U)^(N-1)
```

has the exact right-oriented telescope

```text
P_N(U) (I + U) = I - (-U)^N.
```

Consequently, for `L = s (I + U)` and a complete row `C`, the explicit
readout

```text
H_N = s^(-1) C P_N(U)
```

satisfies

```text
H_N L = C - C (-U)^N.
```

This module instantiates the construction on the actual Bone 1 orientation.
The unadjointed ambient loss uses translation by `-log p`; its adjoint, which
occurs in the raw antiresonant column, uses translation by `+log p`.  The
complete swapped local cofactor remains inside one canonical ambient target.
No outer, reflected, second-support, or prolate branch is split.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary

open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSwappedLocalPairRadialColumnBridge
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Generic finite alternating telescope -/

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Complex E]
  [NormedAddCommGroup F] [NormedSpace Complex F]

/-- The first `N` terms of the alternating orbit polynomial. -/
noncomputable def finiteAntiresonantAlternatingPolynomial
    (U : E →L[Complex] E) (N : Nat) : E →L[Complex] E :=
  ∑ k ∈ Finset.range N, (-U) ^ k

/-- Exact right-oriented alternating telescope. -/
theorem finiteAntiresonantAlternatingPolynomial_comp_id_add
    (U : E →L[Complex] E) (N : Nat) :
    finiteAntiresonantAlternatingPolynomial U N ∘L
        (ContinuousLinearMap.id Complex E + U) =
      ContinuousLinearMap.id Complex E - (-U) ^ N := by
  change (∑ k ∈ Finset.range N, (-U) ^ k) * (1 + U) =
    1 - (-U) ^ N
  simpa only [sub_neg_eq_add] using geom_sum_mul_neg (-U) N

/-- A contraction gives the exact linear-in-horizon polynomial bound. -/
theorem norm_finiteAntiresonantAlternatingPolynomial_le
    (U : E →L[Complex] E) (N : Nat) (hU : ‖U‖ ≤ 1) :
    ‖finiteAntiresonantAlternatingPolynomial U N‖ ≤ (N : Real) := by
  have hneg : ‖-U‖ ≤ (1 : Real) := by
    simpa only [norm_neg] using hU
  have hpow : ∀ k : Nat, ‖(-U) ^ k‖ ≤ (1 : Real) := by
    intro k
    induction k with
    | zero =>
        simpa only [pow_zero] using
          (ContinuousLinearMap.norm_id_le (𝕜 := Complex) (E := E))
    | succ k ih =>
        rw [pow_succ]
        calc
          ‖(-U) ^ k * -U‖ ≤ ‖(-U) ^ k‖ * ‖-U‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ 1 * 1 :=
            mul_le_mul ih hneg (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
  rw [finiteAntiresonantAlternatingPolynomial]
  calc
    ‖∑ k ∈ Finset.range N, (-U) ^ k‖ ≤
        ∑ k ∈ Finset.range N, ‖(-U) ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, (1 : Real) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact hpow k
    _ = (N : Real) := by simp

/-- The explicit finite-horizon readout for `s (I + U)`. -/
noncomputable def finiteHorizonAntiresonantCoboundaryReadout
    (scale : Complex) (U : E →L[Complex] E) (C : E →L[Complex] F)
    (N : Nat) : E →L[Complex] F :=
  scale⁻¹ • (C ∘L finiteAntiresonantAlternatingPolynomial U N)

/-- Exact finite-horizon factorization with its one terminal orbit term. -/
theorem finiteHorizonAntiresonantCoboundaryReadout_comp_scaled_id_add
    (scale : Complex) (U : E →L[Complex] E) (C : E →L[Complex] F)
    (N : Nat) (hscale : scale ≠ 0) :
    finiteHorizonAntiresonantCoboundaryReadout scale U C N ∘L
        (scale • (ContinuousLinearMap.id Complex E + U)) =
      C - C ∘L (-U) ^ N := by
  apply ContinuousLinearMap.ext
  intro x
  have htelescope := DFunLike.congr_fun
    (finiteAntiresonantAlternatingPolynomial_comp_id_add U N) x
  simp only [finiteHorizonAntiresonantCoboundaryReadout,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_smul] at htelescope ⊢
  rw [mul_inv_cancel₀ hscale, one_smul, htelescope, map_sub]

/-- If the terminal orbit is annihilated, the explicit readout is an exact
factor through `s (I + U)`. -/
theorem finiteHorizonAntiresonantCoboundaryReadout_comp_scaled_id_add_of_terminal
    (scale : Complex) (U : E →L[Complex] E) (C : E →L[Complex] F)
    (N : Nat) (hscale : scale ≠ 0)
    (hterminal : C ∘L (-U) ^ N = 0) :
    finiteHorizonAntiresonantCoboundaryReadout scale U C N ∘L
        (scale • (ContinuousLinearMap.id Complex E + U)) = C := by
  rw [finiteHorizonAntiresonantCoboundaryReadout_comp_scaled_id_add
    scale U C N hscale, hterminal, sub_zero]

/-- The readout costs at most the horizon divided by the nonzero loss scale. -/
theorem norm_finiteHorizonAntiresonantCoboundaryReadout_le
    (scale : Complex) (U : E →L[Complex] E) (C : E →L[Complex] F)
    (N : Nat) (_hscale : scale ≠ 0) (hU : ‖U‖ ≤ 1) :
    ‖finiteHorizonAntiresonantCoboundaryReadout scale U C N‖ ≤
      (N : Real) * ‖C‖ / ‖scale‖ := by
  have hscaleNorm : 0 ≤ ‖scale‖⁻¹ := inv_nonneg.mpr (norm_nonneg scale)
  rw [finiteHorizonAntiresonantCoboundaryReadout, norm_smul, norm_inv]
  calc
    ‖scale‖⁻¹ *
          ‖C ∘L finiteAntiresonantAlternatingPolynomial U N‖ ≤
        ‖scale‖⁻¹ *
          (‖C‖ * ‖finiteAntiresonantAlternatingPolynomial U N‖) := by
      exact mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le C
          (finiteAntiresonantAlternatingPolynomial U N)) hscaleNorm
    _ ≤ ‖scale‖⁻¹ * (‖C‖ * (N : Real)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (norm_finiteAntiresonantAlternatingPolynomial_le U N hU)
          (norm_nonneg C)) hscaleNorm
    _ = (N : Real) * ‖C‖ / ‖scale‖ := by
      rw [div_eq_mul_inv]
      ring

/-! ## Actual ambient-loss orientation -/

/-- The unadjointed loss factor uses the negative logarithmic translation. -/
theorem primeEulerAmbientLossFactor_eq_negativeTranslation
    (p : CCM24VisiblePrime) :
    primeEulerAmbientLossFactor p =
      (primeEulerAmbientLossScale p : Complex) •
        (ContinuousLinearMap.id Complex finiteSCarrier +
          (cc20GlobalLogTranslation
            (-Real.log p)).toContinuousLinearMap) := by
  rfl

/-- The raw Bone 1 column uses the adjoint factor and hence the positive
logarithmic translation. -/
theorem primeEulerAmbientLossFactor_adjoint_eq_positiveTranslation
    (p : CCM24VisiblePrime) :
    (primeEulerAmbientLossFactor p)† =
      (primeEulerAmbientLossScale p : Complex) •
        (ContinuousLinearMap.id Complex finiteSCarrier +
          (cc20GlobalLogTranslation
            (Real.log p)).toContinuousLinearMap) :=
  primeEulerAmbientLossFactor_adjoint_eq p

/-! ## Complete coupled ambient target -/

/-- The complete swapped cofactor, dressed by the exact Schur scalar and
transition, and extended canonically from the new frame to the ambient
carrier.  All physical boundary branches remain inside the cofactor. -/
noncomputable def suffixActualBandCompleteCoupledAmbientTarget
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[Complex] sourceSoninCarrier lambda :=
  (-((primeSchurMarkovScalar p : Complex)⁻¹)) •
    ((suffixEulerFrameTransition lambda p S)† ∘L
      suffixActualBandCompleteSwappedLocalCofactor owner lambda p S ∘L
        (newSuffixFrame lambda S)†)

/-- Restricting the canonical ambient target back to the actual new frame
recovers the genuine signed compressed interior. -/
theorem suffixActualBandCompleteCoupledAmbientTarget_comp_newFrame
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandCompleteCoupledAmbientTarget owner lambda p S ∘L
        newSuffixFrame lambda S =
      signedCompressedInteriorOwner owner lambda p S := by
  apply ContinuousLinearMap.ext
  intro x
  have hframe := congrArg
    (fun operator : sourceSoninCarrier lambda →L[Complex]
      sourceSoninCarrier lambda => operator x)
    (parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 S
      (by norm_num))
  have hframePoint :
      ((newSuffixFrame lambda S)†) (newSuffixFrame lambda S x) = x := by
    simpa only [newSuffixFrame, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hframe
  have howner := DFunLike.congr_fun
    (signedCompressedInteriorOwner_eq_neg_scalarInv_smul_transitionAdjoint_comp_localRawDefectAdjoint_comp_reverseAdjoint
      owner lambda p S) x
  simp only [suffixActualBandCompleteCoupledAmbientTarget,
    suffixActualBandCompleteSwappedLocalCofactor,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
  rw [hframePoint]
  exact howner.symm

/-! ## Actual finite-horizon readout and terminal tail -/

/-- The explicit alternating readout on the actual positive-translation
adjoint loss orientation. -/
noncomputable def suffixActualBandFiniteHorizonCoboundaryReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : Nat) :
    finiteSCarrier →L[Complex] sourceSoninCarrier lambda :=
  finiteHorizonAntiresonantCoboundaryReadout
    (primeEulerAmbientLossScale p : Complex)
    (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
    (suffixActualBandCompleteCoupledAmbientTarget owner lambda p S) N

/-- The one terminal coupled tail left by the finite alternating telescope. -/
noncomputable def suffixActualBandFiniteHorizonCoupledTail
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : Nat) :
    sourceSoninCarrier lambda →L[Complex] sourceSoninCarrier lambda :=
  suffixActualBandCompleteCoupledAmbientTarget owner lambda p S ∘L
      ((-(cc20GlobalLogTranslation
        (Real.log p)).toContinuousLinearMap) ^ N) ∘L
      newSuffixFrame lambda S

/-- Before restricting to the new frame, the actual readout has exactly one
ambient terminal orbit remainder. -/
theorem suffixActualBandFiniteHorizonCoboundaryReadout_comp_lossAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : Nat) :
    suffixActualBandFiniteHorizonCoboundaryReadout owner lambda p S N ∘L
        (primeEulerAmbientLossFactor p)† =
      suffixActualBandCompleteCoupledAmbientTarget owner lambda p S -
        suffixActualBandCompleteCoupledAmbientTarget owner lambda p S ∘L
          (-(cc20GlobalLogTranslation
            (Real.log p)).toContinuousLinearMap) ^ N := by
  rw [primeEulerAmbientLossFactor_adjoint_eq_positiveTranslation]
  unfold suffixActualBandFiniteHorizonCoboundaryReadout
  apply finiteHorizonAntiresonantCoboundaryReadout_comp_scaled_id_add
  exact_mod_cast ne_of_gt (primeEulerAmbientLossScale_pos p)

/-- Exact same-object endpoint formula: the explicit readout reconstructs the
full signed interior minus one unsplit coupled terminal tail. -/
theorem suffixActualBandFiniteHorizonCoboundaryReadout_comp_rawColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : Nat) :
    suffixActualBandFiniteHorizonCoboundaryReadout owner lambda p S N ∘L
        newFrameAntiresonantColumn lambda p S =
      signedCompressedInteriorOwner owner lambda p S -
        suffixActualBandFiniteHorizonCoupledTail owner lambda p S N := by
  apply ContinuousLinearMap.ext
  intro x
  have hremainder := DFunLike.congr_fun
    (suffixActualBandFiniteHorizonCoboundaryReadout_comp_lossAdjoint
      owner lambda p S N) (newSuffixFrame lambda S x)
  have htarget := DFunLike.congr_fun
    (suffixActualBandCompleteCoupledAmbientTarget_comp_newFrame
      owner lambda p S) x
  have htargetPoint :
      suffixActualBandCompleteCoupledAmbientTarget owner lambda p S
          (newSuffixFrame lambda S x) =
        signedCompressedInteriorOwner owner lambda p S x := by
    simpa only [ContinuousLinearMap.comp_apply] using htarget
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply] at hremainder
  rw [htargetPoint] at hremainder
  simpa only [newFrameAntiresonantColumn,
    suffixActualBandFiniteHorizonCoupledTail,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply] using
      hremainder

/-- The exact missing source theorem is terminal coupled-tail annihilation.
If it holds at some finite horizon, the displayed alternating readout is a
genuine factor of the complete signed interior through the raw loss column. -/
theorem suffixActualBandFiniteHorizonCoboundaryReadout_comp_rawColumn_of_terminal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : Nat)
    (hterminal :
      suffixActualBandFiniteHorizonCoupledTail owner lambda p S N = 0) :
    suffixActualBandFiniteHorizonCoboundaryReadout owner lambda p S N ∘L
        newFrameAntiresonantColumn lambda p S =
      signedCompressedInteriorOwner owner lambda p S := by
  rw [suffixActualBandFiniteHorizonCoboundaryReadout_comp_rawColumn,
    hterminal, sub_zero]

/-- The actual readout has the sharp generic horizon/scale cost.  No suffix-
uniform bound on the complete coupled ambient target is assumed. -/
theorem norm_suffixActualBandFiniteHorizonCoboundaryReadout_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : Nat) :
    ‖suffixActualBandFiniteHorizonCoboundaryReadout owner lambda p S N‖ ≤
      (N : Real) *
          ‖suffixActualBandCompleteCoupledAmbientTarget owner lambda p S‖ /
        primeEulerAmbientLossScale p := by
  have hscale : (primeEulerAmbientLossScale p : Complex) ≠ 0 := by
    exact_mod_cast ne_of_gt (primeEulerAmbientLossScale_pos p)
  have htranslation :
      ‖(cc20GlobalLogTranslation
        (Real.log p)).toContinuousLinearMap‖ ≤ 1 :=
    (cc20GlobalLogTranslation
      (Real.log p)).norm_toContinuousLinearMap_le
  have hbound := norm_finiteHorizonAntiresonantCoboundaryReadout_le
    (primeEulerAmbientLossScale p : Complex)
    (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
    (suffixActualBandCompleteCoupledAmbientTarget owner lambda p S)
    N hscale htranslation
  simpa only [suffixActualBandFiniteHorizonCoboundaryReadout,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (primeEulerAmbientLossScale_pos p)] using hbound

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
end CCM25Concrete
end Source
end ConnesWeilRH
