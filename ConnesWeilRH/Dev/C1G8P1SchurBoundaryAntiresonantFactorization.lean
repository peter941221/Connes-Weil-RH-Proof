/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24EulerTransport
import ConnesWeilRH.Source.CC20Concrete.CCM24SemilocalFourierSupport
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurCascade
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientDefectFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossCommutatorReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFrameGramCalculus
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedSourcePolar
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJuliaCausal

/-!
# G8 P1 Schur boundary antiresonant factorization

The one-step rectangular Schur boundary dagger of the finite-S Euler
cascade,

```text
boundaryDagger(p,S) = (I - newFrame newFrame†) ∘L transport† ∘L oldFrame,
```

is put into the antiresonant language already used on the radial side of
P1.  The exact algebra is

```text
transport† = I - √q_p • (prime loss factor)†,
```

and, after splitting `oldFrame x` through the suffix range projection
`P_S = newFrame newFrame†`,

```text
boundaryDagger x
  = (I - P_S)(transport†((I - P_S)(oldFrame x)))
    - √q_p • (I - P_S)(antiresonantColumn(newFrame†(oldFrame x))).
```

Hence every metric-side Schur boundary dagger carries the same visible
antiresonant column as the radial crossing channel of the two-channel
ledger, with prefix `newFrame† ∘L oldFrame` in place of `frame†`.  The
pointwise and operator-norm ledgers are recorded with closed constants:
the interior channel costs at most `‖x‖` and the boundary channel costs
`√q_p` times the pulled-back antiresonant column norm.

This is a transport packaging only.  No vanishing, no summability of the
antiresonant column energy, no metric-to-radial cutoff identification, and
no RH-facing sign is claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1SchurBoundaryAntiresonantFactorization

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM25Concrete.SelectedCrossingOperatorBridge
open CCM25Concrete.AntiresonantFrameLossCommutator
open CCM25Concrete.CCM24FiniteSActualSchurCascade
open CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM25Concrete.CCM24FiniteSFrameGramCalculus
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSFixedSourcePolar
open CCM25Concrete.CCM24FiniteSJuliaCausal
open CCM25Concrete.CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The range complement is contractive -/

/-- The complement of the suffix range projection is itself an orthogonal
star projection (onto the orthogonal complement of the semilocal Sonin
subspace), hence contractive. -/
theorem norm_id_sub_newSuffixRangeProjection_apply_le
    (S : List CCM24VisiblePrime) (u : finiteSCarrier) :
    ‖(ContinuousLinearMap.id ℂ finiteSCarrier -
        newSuffixRangeProjection unitSoninScale S) u‖ ≤ ‖u‖ := by
  rw [newSuffixRangeProjection_eq_semilocalSoninStarProjection]
  have horth := Submodule.starProjection_orthogonal'
    (ccm24SemilocalSoninClosedSubspace unitSoninScale S).toSubmodule
  calc ‖(ContinuousLinearMap.id ℂ finiteSCarrier -
      (ccm24SemilocalSoninClosedSubspace unitSoninScale S).toSubmodule.starProjection) u‖
      = ‖((((ccm24SemilocalSoninClosedSubspace unitSoninScale S).toSubmodule)ᗮ).starProjection)
          u‖ := by
        rw [horth, ContinuousLinearMap.one_def]
    _ ≤ ‖u‖ := Submodule.norm_starProjection_apply_le _ _

/-- The new suffix frame lands inside the range of the suffix range
projection, so the range complement kills it. -/
theorem id_sub_newSuffixRangeProjection_apply_newSuffixFrame
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (w : sourceSoninCarrier unitSoninScale) :
    (ContinuousLinearMap.id ℂ finiteSCarrier -
        newSuffixRangeProjection unitSoninScale S)
      (newSuffixFrame unitSoninScale S w) = 0 := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  have hiso := congrArg
    (fun (K2 : sourceSoninCarrier unitSoninScale →L[ℂ] sourceSoninCarrier unitSoninScale) =>
      K2 w)
    (suffixEulerFrameSchurStep unitSoninScale p S).newFrame_isometry
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hiso
  have hiso2 : ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
      ((newSuffixFrame unitSoninScale S) w) = w := hiso
  simp only [newSuffixRangeProjection, ContinuousLinearMap.comp_apply]
  rw [hiso2]
  exact sub_self _

/-! ## Scalar algebra -/

private theorem sqrtCoeff_mul_lossScale_eq_invOneAddCoeff (p : CCM24VisiblePrime) :
    ((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℝ) : ℂ) *
      (primeEulerAmbientLossScale p : ℂ) =
      (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ *
        (ccm24PrimeEulerCoefficient p : ℂ) := by
  have hq := ccm24PrimeEulerCoefficient_nonneg p
  have hsq : Real.sqrt (ccm24PrimeEulerCoefficient p) *
      Real.sqrt (ccm24PrimeEulerCoefficient p) = ccm24PrimeEulerCoefficient p :=
    Real.mul_self_sqrt hq
  have hreal : Real.sqrt (ccm24PrimeEulerCoefficient p) *
      (Real.sqrt (ccm24PrimeEulerCoefficient p) /
        (1 + ccm24PrimeEulerCoefficient p)) =
      (1 + ccm24PrimeEulerCoefficient p)⁻¹ * ccm24PrimeEulerCoefficient p := by
    rw [← mul_div_assoc, hsq]
    ring
  exact_mod_cast hreal

private theorem one_sub_sqrtCoeff_lossScale_eq_invOneAddCoeff (p : CCM24VisiblePrime) :
    (1 : ℂ) - ((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℝ) : ℂ) *
      (primeEulerAmbientLossScale p : ℂ) =
      (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ := by
  have hq := ccm24PrimeEulerCoefficient_nonneg p
  have hsq : Real.sqrt (ccm24PrimeEulerCoefficient p) *
      Real.sqrt (ccm24PrimeEulerCoefficient p) = ccm24PrimeEulerCoefficient p :=
    Real.mul_self_sqrt hq
  have hreal : (1 : ℝ) - Real.sqrt (ccm24PrimeEulerCoefficient p) *
      (Real.sqrt (ccm24PrimeEulerCoefficient p) /
        (1 + ccm24PrimeEulerCoefficient p)) =
      (1 + ccm24PrimeEulerCoefficient p)⁻¹ := by
    have hne : (1 + ccm24PrimeEulerCoefficient p) ≠ 0 := by linarith
    rw [← mul_div_assoc, hsq]
    field_simp [hne]
    ring
  exact_mod_cast hreal

private theorem invOneAddCoeff_add_mul_coeff_eq_one (p : CCM24VisiblePrime) :
    (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ +
      (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ *
        (ccm24PrimeEulerCoefficient p : ℂ) = 1 := by
  have h2 := one_sub_sqrtCoeff_lossScale_eq_invOneAddCoeff p
  have h1 := sqrtCoeff_mul_lossScale_eq_invOneAddCoeff p
  rw [← h1]
  linear_combination -h2

/-! ## The transport adjoint in antiresonant form -/

/-- The normalized forward Euler transport has adjoint exactly
`I - √q_p • (prime loss factor)†`:  the Euler factor `(1 - q_p p^{-s})` and
the antiresonant factor `(1 + p^{-s})` differ by the visible square-root
coefficient and the identity channel. -/
theorem normalizedPrimeEulerFrameTransport_adjoint_eq_id_sub_sqrtCoeff_smul_lossFactorAdjoint
    (p : CCM24VisiblePrime) :
    ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p) =
      ContinuousLinearMap.id ℂ finiteSCarrier
        - ((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℝ) : ℂ) •
          ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) := by
  have hEquiv : (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ finiteSCarrier
        - (ccm24PrimeEulerCoefficient p : ℂ) •
          (cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro u
    simpa using ccm24PrimeEulerTransportEquiv_apply p u
  have htransEq : normalizedPrimeEulerFrameTransport p =
      ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
        (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap := rfl
  rw [htransEq, hEquiv, primeEulerAmbientLossFactor_adjoint_eq]
  have hstar1 : (starRingEnd ℂ) ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) =
      (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ := by
    have hbridge : (starRingEnd ℂ) ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹)
        = star ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) := rfl
    rw [hbridge]
    simp [Complex.conj_ofReal]
  have hstar2 : (starRingEnd ℂ) ((ccm24PrimeEulerCoefficient p : ℂ)) =
      (ccm24PrimeEulerCoefficient p : ℂ) := by
    have hbridge : (starRingEnd ℂ) ((ccm24PrimeEulerCoefficient p : ℂ))
        = star ((ccm24PrimeEulerCoefficient p : ℂ)) := rfl
    rw [hbridge]
    exact Complex.conj_ofReal _
  simp only [map_smulₛₗ, hstar1, hstar2, map_sub,
    ContinuousLinearMap.adjoint_id, cc20GlobalLogTranslation_neg_adjoint,
    smul_smul, star_inv, star_add, star_one, Complex.conj_ofReal]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    smul_sub, sub_smul, smul_add, smul_smul]
  rw [sqrtCoeff_mul_lossScale_eq_invOneAddCoeff]
  have hkey : u - ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ *
      (ccm24PrimeEulerCoefficient p : ℂ)) • u =
      (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ • u := by
    rw [sub_eq_iff_eq_add, ← add_smul,
      invOneAddCoeff_add_mul_coeff_eq_one, one_smul]
  rw [← hkey]
  abel

/-- Pointwise form of the transport adjoint identity. -/
theorem normalizedPrimeEulerFrameTransport_adjoint_apply
    (p : CCM24VisiblePrime) (v : finiteSCarrier) :
    ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p) v =
      v - ((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℝ) : ℂ) •
        ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) v := by
  have h := normalizedPrimeEulerFrameTransport_adjoint_eq_id_sub_sqrtCoeff_smul_lossFactorAdjoint p
  calc ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p) v
      = (ContinuousLinearMap.id ℂ finiteSCarrier
          - ((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℝ) : ℂ) •
            ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) v := by
        rw [h]
    _ = _ := rfl

/-! ## Norm inputs for the ledger -/

/-- The normalized forward Euler transport has contractive adjoint. -/
theorem norm_normalizedPrimeEulerFrameTransport_adjoint_le_one
    (p : CCM24VisiblePrime) :
    ‖ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p)‖ ≤ 1 := by
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact normalizedPrimeEulerFrameTransport_norm_le_one p

/-- The old suffix frame is contractive. -/
theorem norm_oldSuffixFrame_le_one (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖oldSuffixFrame unitSoninScale p S‖ ≤ 1 :=
  norm_le_one_of_isometric_inclusion (oldSuffixFrame unitSoninScale p S) (by
    intro y
    exact parameterizedSoninPolarFrame_isometry unitSoninScale 1 (p :: S)
      (by norm_num) y)

/-! ## The one-step Schur boundary dagger in antiresonant form -/

/-- The one-step rectangular Schur boundary dagger splits into an interior
channel `(I - P_S) ∘ transport† ∘ (I - P_S) ∘ oldFrame` and the visible
antiresonant column channel with coefficient `√q_p`, pulled back through
`newFrame† ∘L oldFrame`. -/
theorem suffixEulerFrameSchurStep_boundaryDagger_apply_eq_interior_add_antiresonant
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier unitSoninScale) :
    (suffixEulerFrameSchurStep unitSoninScale p S).boundaryDagger x =
      (ContinuousLinearMap.id ℂ finiteSCarrier -
          newSuffixRangeProjection unitSoninScale S)
        (ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p)
          ((ContinuousLinearMap.id ℂ finiteSCarrier -
              newSuffixRangeProjection unitSoninScale S)
            (oldSuffixFrame unitSoninScale p S x)))
      - ((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℝ) : ℂ) •
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          newSuffixRangeProjection unitSoninScale S)
          (newFrameAntiresonantColumn unitSoninScale p S
            (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
              (oldSuffixFrame unitSoninScale p S x))) := by
  have hbd : (suffixEulerFrameSchurStep unitSoninScale p S).boundaryDagger x =
      (ContinuousLinearMap.id ℂ finiteSCarrier -
          newSuffixRangeProjection unitSoninScale S)
        (ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p)
          (oldSuffixFrame unitSoninScale p S x)) := rfl
  have hsplit : oldSuffixFrame unitSoninScale p S x =
      newSuffixRangeProjection unitSoninScale S
        (oldSuffixFrame unitSoninScale p S x) +
      (ContinuousLinearMap.id ℂ finiteSCarrier -
        newSuffixRangeProjection unitSoninScale S)
        (oldSuffixFrame unitSoninScale p S x) := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    abel
  have hPO : newSuffixRangeProjection unitSoninScale S
      (oldSuffixFrame unitSoninScale p S x) =
      newSuffixFrame unitSoninScale S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (oldSuffixFrame unitSoninScale p S x)) := rfl
  have hanti : (ContinuousLinearMap.id ℂ finiteSCarrier -
      newSuffixRangeProjection unitSoninScale S)
      (ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p)
        (newSuffixRangeProjection unitSoninScale S
          (oldSuffixFrame unitSoninScale p S x)))
      = ((-((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℝ) : ℂ))) •
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          newSuffixRangeProjection unitSoninScale S)
          (newFrameAntiresonantColumn unitSoninScale p S
            (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
              (oldSuffixFrame unitSoninScale p S x))) := by
    rw [hPO, normalizedPrimeEulerFrameTransport_adjoint_apply,
      ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul,
      id_sub_newSuffixRangeProjection_apply_newSuffixFrame p S _, zero_sub,
      neg_smul, newFrameAntiresonantColumn]
    simp only [ContinuousLinearMap.comp_apply]
  have hadd : (ContinuousLinearMap.id ℂ finiteSCarrier -
      newSuffixRangeProjection unitSoninScale S)
      (ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p)
        (newSuffixRangeProjection unitSoninScale S
          (oldSuffixFrame unitSoninScale p S x) +
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          newSuffixRangeProjection unitSoninScale S)
        (oldSuffixFrame unitSoninScale p S x)))
      = (ContinuousLinearMap.id ℂ finiteSCarrier -
          newSuffixRangeProjection unitSoninScale S)
        (ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p)
          ((ContinuousLinearMap.id ℂ finiteSCarrier -
            newSuffixRangeProjection unitSoninScale S)
          (oldSuffixFrame unitSoninScale p S x)))
      - ((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℝ) : ℂ) •
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          newSuffixRangeProjection unitSoninScale S)
          (newFrameAntiresonantColumn unitSoninScale p S
            (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
              (oldSuffixFrame unitSoninScale p S x))) := by
    rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_add, hanti,
      neg_smul]
    abel
  have step1 : (ContinuousLinearMap.id ℂ finiteSCarrier -
      newSuffixRangeProjection unitSoninScale S)
      (ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p)
        (oldSuffixFrame unitSoninScale p S x)) =
    (ContinuousLinearMap.id ℂ finiteSCarrier -
      newSuffixRangeProjection unitSoninScale S)
      (ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p)
        (newSuffixRangeProjection unitSoninScale S
          (oldSuffixFrame unitSoninScale p S x) +
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          newSuffixRangeProjection unitSoninScale S)
        (oldSuffixFrame unitSoninScale p S x))) := by
    rw [← hsplit]
  exact hbd.trans (step1.trans hadd)

/-! ## The two-channel ledger -/

/-- The one-step Schur boundary dagger costs at most `‖x‖` from the interior
channel plus `√q_p` times the pulled-back antiresonant column norm from the
boundary channel. -/
theorem norm_suffixEulerFrameSchurStep_boundaryDagger_apply_le_twoChannel
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier unitSoninScale) :
    ‖(suffixEulerFrameSchurStep unitSoninScale p S).boundaryDagger x‖ ≤
      ‖x‖ + (Real.sqrt (ccm24PrimeEulerCoefficient p)) *
        ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
            (oldSuffixFrame unitSoninScale p S x))‖ := by
  have hsplit :=
    suffixEulerFrameSchurStep_boundaryDagger_apply_eq_interior_add_antiresonant
      p S x
  have hsqrtpos : 0 ≤ Real.sqrt (ccm24PrimeEulerCoefficient p) :=
    Real.sqrt_nonneg _
  have hcoeff : ‖((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℝ) : ℂ) •
      (ContinuousLinearMap.id ℂ finiteSCarrier -
        newSuffixRangeProjection unitSoninScale S)
        (newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
            (oldSuffixFrame unitSoninScale p S x)))‖ =
      (Real.sqrt (ccm24PrimeEulerCoefficient p)) *
        ‖(ContinuousLinearMap.id ℂ finiteSCarrier -
          newSuffixRangeProjection unitSoninScale S)
          (newFrameAntiresonantColumn unitSoninScale p S
            (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
              (oldSuffixFrame unitSoninScale p S x)))‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsqrtpos]
  have hint : ‖(ContinuousLinearMap.id ℂ finiteSCarrier -
      newSuffixRangeProjection unitSoninScale S)
      (ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p)
        ((ContinuousLinearMap.id ℂ finiteSCarrier -
          newSuffixRangeProjection unitSoninScale S)
        (oldSuffixFrame unitSoninScale p S x)))‖ ≤ ‖x‖ := by
    have hA := norm_id_sub_newSuffixRangeProjection_apply_le S
      (ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p)
        ((ContinuousLinearMap.id ℂ finiteSCarrier -
          newSuffixRangeProjection unitSoninScale S)
        (oldSuffixFrame unitSoninScale p S x)))
    have hB := norm_id_sub_newSuffixRangeProjection_apply_le S
      (oldSuffixFrame unitSoninScale p S x)
    have hD : ‖ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p)
        ((ContinuousLinearMap.id ℂ finiteSCarrier -
          newSuffixRangeProjection unitSoninScale S)
        (oldSuffixFrame unitSoninScale p S x))‖ ≤
        ‖(ContinuousLinearMap.id ℂ finiteSCarrier -
          newSuffixRangeProjection unitSoninScale S)
        (oldSuffixFrame unitSoninScale p S x)‖ := by
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
      refine le_trans (mul_le_mul_of_nonneg_right
        (norm_normalizedPrimeEulerFrameTransport_adjoint_le_one p)
        (norm_nonneg _)) ?_
      rw [one_mul]
    have hC : ‖oldSuffixFrame unitSoninScale p S x‖ ≤ ‖x‖ := by
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
      refine le_trans (mul_le_mul_of_nonneg_right
        (norm_oldSuffixFrame_le_one p S) (norm_nonneg _)) ?_
      rw [one_mul]
    exact le_trans hA (le_trans hD (le_trans hB hC))
  calc ‖(suffixEulerFrameSchurStep unitSoninScale p S).boundaryDagger x‖
      ≤ ‖(ContinuousLinearMap.id ℂ finiteSCarrier -
            newSuffixRangeProjection unitSoninScale S)
          (ContinuousLinearMap.adjoint (normalizedPrimeEulerFrameTransport p)
            ((ContinuousLinearMap.id ℂ finiteSCarrier -
                newSuffixRangeProjection unitSoninScale S)
              (oldSuffixFrame unitSoninScale p S x)))‖ +
        ‖((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℝ) : ℂ) •
          (ContinuousLinearMap.id ℂ finiteSCarrier -
            newSuffixRangeProjection unitSoninScale S)
            (newFrameAntiresonantColumn unitSoninScale p S
              (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
                (oldSuffixFrame unitSoninScale p S x)))‖ := by
        rw [hsplit]
        exact norm_sub_le _ _
    _ ≤ ‖x‖ + (Real.sqrt (ccm24PrimeEulerCoefficient p)) *
          ‖(ContinuousLinearMap.id ℂ finiteSCarrier -
            newSuffixRangeProjection unitSoninScale S)
          (newFrameAntiresonantColumn unitSoninScale p S
            (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
              (oldSuffixFrame unitSoninScale p S x)))‖ := by
        rw [hcoeff]
        exact add_le_add hint le_rfl
    _ ≤ ‖x‖ + (Real.sqrt (ccm24PrimeEulerCoefficient p)) *
          ‖newFrameAntiresonantColumn unitSoninScale p S
            (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
              (oldSuffixFrame unitSoninScale p S x))‖ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (norm_id_sub_newSuffixRangeProjection_apply_le S
            (newFrameAntiresonantColumn unitSoninScale p S
              (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
                (oldSuffixFrame unitSoninScale p S x)))) hsqrtpos)

/-- Operator-norm corollary: the one-step Schur boundary dagger is bounded
by `1` plus `√q_p` times the norm of the antiresonant column pulled back
through `newFrame† ∘L oldFrame`. -/
theorem norm_suffixEulerFrameSchurStep_boundaryDagger_le
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    ‖(suffixEulerFrameSchurStep unitSoninScale p S).boundaryDagger‖ ≤
      1 + (Real.sqrt (ccm24PrimeEulerCoefficient p)) *
        ‖newFrameAntiresonantColumn unitSoninScale p S ∘L
          ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) ∘L
            oldSuffixFrame unitSoninScale p S‖ := by
  have hsqrtpos : 0 ≤ Real.sqrt (ccm24PrimeEulerCoefficient p) :=
    Real.sqrt_nonneg _
  have hnonneg : (0:ℝ) ≤ 1 + (Real.sqrt (ccm24PrimeEulerCoefficient p)) *
      ‖newFrameAntiresonantColumn unitSoninScale p S ∘L
        ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) ∘L
          oldSuffixFrame unitSoninScale p S‖ :=
    add_nonneg zero_le_one
      (mul_nonneg hsqrtpos (norm_nonneg _))
  refine ContinuousLinearMap.opNorm_le_bound _ hnonneg ?_
  intro u
  have hledger :=
    norm_suffixEulerFrameSchurStep_boundaryDagger_apply_le_twoChannel p S u
  have hcol : ‖newFrameAntiresonantColumn unitSoninScale p S
      (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
        (oldSuffixFrame unitSoninScale p S u))‖ ≤
      ‖newFrameAntiresonantColumn unitSoninScale p S ∘L
        ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) ∘L
          oldSuffixFrame unitSoninScale p S‖ * ‖u‖ := by
    refine le_trans ?_ (ContinuousLinearMap.le_opNorm
      (newFrameAntiresonantColumn unitSoninScale p S ∘L
        ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) ∘L
          oldSuffixFrame unitSoninScale p S) u)
    simp only [ContinuousLinearMap.comp_apply]
    exact le_refl _
  calc ‖(suffixEulerFrameSchurStep unitSoninScale p S).boundaryDagger u‖
      ≤ ‖u‖ + (Real.sqrt (ccm24PrimeEulerCoefficient p)) *
          ‖newFrameAntiresonantColumn unitSoninScale p S
            (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
              (oldSuffixFrame unitSoninScale p S u))‖ := hledger
    _ ≤ ‖u‖ + (Real.sqrt (ccm24PrimeEulerCoefficient p)) *
          (‖newFrameAntiresonantColumn unitSoninScale p S ∘L
            ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) ∘L
              oldSuffixFrame unitSoninScale p S‖ * ‖u‖) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hcol hsqrtpos)
    _ = (1 + (Real.sqrt (ccm24PrimeEulerCoefficient p)) *
            ‖newFrameAntiresonantColumn unitSoninScale p S ∘L
              ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) ∘L
                oldSuffixFrame unitSoninScale p S‖) * ‖u‖ := by ring

end C1G8P1SchurBoundaryAntiresonantFactorization
end Source
end ConnesWeilRH
