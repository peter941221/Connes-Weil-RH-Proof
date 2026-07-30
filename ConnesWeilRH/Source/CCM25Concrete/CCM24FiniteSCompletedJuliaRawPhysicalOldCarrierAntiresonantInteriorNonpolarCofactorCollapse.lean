/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaJointProducer
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaMismatchFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarScaledTargetSize

/-!
# Collapse of the non-polar cofactor

Proof 659 splits the complete Bone 1A target into a uniformly controlled
polar part and one non-polar cofactor.  This module removes the redundant
two-sided Schur factors from that cofactor.  If

```text
I_(p,S) = T_(p,S) M_S - M_(p::S) T_(p,S),
```

then the exact non-polar interior is

```text
C_(p,S) = -I_(p,S)^* R_(p,S)^*.
```

The scalar-normalized forward transition recovers `-I_(p,S)^*`, so

```text
||C_(p,S)|| <= ||I_(p,S)|| <= 8 ||C_(p,S)||.
```

After the genuine frame extension, the norm is unchanged.  The final route
theorem proves that a finite route-uniform ambient-loss-scaled bound for the
complete Bone 1A target exists exactly when one exists for the recombined raw
quadratic intertwining defect.  The fixed-bound conversions are

```text
raw B      -> complete (54 ||detector|| + B),
complete B -> raw      (390 ||detector|| + 8 B).
```

This is a reduction of Bone 1A to one same-domain raw row.  It does not prove
that row is uniformly bounded, Gate 3U, a sign theorem, or RH.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorNonpolarCofactorCollapse

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaJointProducer
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSCompletedJuliaSynthesis
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentBoundaryResponse
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarScaledTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierBlockReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeAnnihilationGuard
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Exact Schur cofactor collapse -/

/-- The scalar-normalized forward transition is also a left inverse of the
reverse transition.  Proof 505 used the opposite composition order. -/
theorem suffixMismatchScaledForwardTransition_comp_reverse_eq_id
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixMismatchScaledForwardTransition lambda p S ∘L
        suffixEulerFrameReverseTransition lambda p S =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  have hpair := suffixEulerFrameTransition_comp_reverse lambda p S
  have hscalar : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  apply ContinuousLinearMap.ext
  intro x
  have hx := DFunLike.congr_fun hpair x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hx ⊢
  rw [suffixMismatchScaledForwardTransition_apply, hx, smul_smul,
    inv_mul_cancel₀ hscalar, one_smul]

/-- Adjoint form of the preceding scalar-normalized cancellation. -/
theorem reverseAdjoint_comp_scaledForwardAdjoint_eq_id
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameReverseTransition lambda p S)† ∘L
        (suffixMismatchScaledForwardTransition lambda p S)† =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  have h := congrArg ContinuousLinearMap.adjoint
    (suffixMismatchScaledForwardTransition_comp_reverse_eq_id lambda p S)
  simpa only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_id] using h

set_option maxHeartbeats 4000000 in
-- Four imported cofactor identities elaborate together in this normalization.
/-- The unresolved non-polar cofactor is exactly the one-sided mismatch
adjoint followed by the contractive reverse-transition adjoint. -/
theorem suffixActualBandNonpolarCofactorInterior_eq_neg_mismatchAdjoint_comp_reverseAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandNonpolarCofactorInterior owner lambda p S =
      -((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S)† ∘L
        (suffixEulerFrameReverseTransition lambda p S)†) := by
  rw [suffixActualBandNonpolarCofactorInterior,
    suffixActualBandLocalNonpolarLocalizationGap_eq_routePolarRawMismatchDefect,
    suffixActualBandLocalRoutePolarRawMismatchDefect_eq_intertwining_comp_reverse,
    ContinuousLinearMap.adjoint_comp]
  have hpair :=
    suffixEulerFrameTransitionAdjoint_comp_reverseTransitionAdjoint_eq_scalar
      lambda p S
  have hscalar : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  apply ContinuousLinearMap.ext
  intro x
  have hx := DFunLike.congr_fun hpair
    (((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†)
        (((suffixEulerFrameReverseTransition lambda p S)†) x))
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hx
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply]
  rw [hx, smul_smul, neg_mul, inv_mul_cancel₀ hscalar,
    neg_smul, one_smul]

/-- Composing the collapsed cofactor with the normalized forward adjoint
recovers the complete one-sided mismatch adjoint, including its sign. -/
theorem suffixActualBandNonpolarCofactorInterior_comp_scaledForwardAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandNonpolarCofactorInterior owner lambda p S ∘L
        (suffixMismatchScaledForwardTransition lambda p S)† =
      -(suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S)† := by
  rw [
    suffixActualBandNonpolarCofactorInterior_eq_neg_mismatchAdjoint_comp_reverseAdjoint]
  have hpair := DFunLike.congr_fun
    (reverseAdjoint_comp_scaledForwardAdjoint_eq_id lambda p S)
  apply ContinuousLinearMap.ext
  intro x
  have hpairPoint := hpair x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hpairPoint
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply]
  rw [hpairPoint]

/-! ## One-step norm equivalence -/

/-- The contractive reverse transition cannot enlarge the mismatch adjoint. -/
theorem norm_suffixActualBandNonpolarCofactorInterior_le_mismatch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandNonpolarCofactorInterior owner lambda p S‖ ≤
      ‖suffixActualBandRoutePolarRawMismatchIntertwiningDefect
        owner lambda p S‖ := by
  let mismatch :=
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect owner lambda p S
  let reverse := suffixEulerFrameReverseTransition lambda p S
  rw [
    suffixActualBandNonpolarCofactorInterior_eq_neg_mismatchAdjoint_comp_reverseAdjoint,
    ContinuousLinearMap.opNorm_neg]
  change ‖mismatch† ∘L reverse†‖ ≤ ‖mismatch‖
  calc
    ‖mismatch† ∘L reverse†‖ ≤ ‖mismatch†‖ * ‖reverse†‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖mismatch‖ * ‖reverse‖ := by
      rw [show ‖mismatch†‖ = ‖mismatch‖ by
          exact ContinuousLinearMap.adjoint.norm_map mismatch,
        show ‖reverse†‖ = ‖reverse‖ by
          exact ContinuousLinearMap.adjoint.norm_map reverse]
    _ ≤ ‖mismatch‖ * 1 := by
      exact mul_le_mul_of_nonneg_left
        (suffixEulerFrameReverseTransition_norm_le_one lambda p S)
        (norm_nonneg mismatch)
    _ = ‖mismatch‖ := mul_one _

/-- The scalar-normalized forward recovery costs at most the universal
factor `8`. -/
theorem norm_mismatch_le_eight_mul_suffixActualBandNonpolarCofactorInterior
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandRoutePolarRawMismatchIntertwiningDefect
        owner lambda p S‖ ≤
      8 * ‖suffixActualBandNonpolarCofactorInterior owner lambda p S‖ := by
  let mismatch :=
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect owner lambda p S
  let cofactor := suffixActualBandNonpolarCofactorInterior owner lambda p S
  let scaled := suffixMismatchScaledForwardTransition lambda p S
  have hrecovery :=
    suffixActualBandNonpolarCofactorInterior_comp_scaledForwardAdjoint
      owner lambda p S
  calc
    ‖mismatch‖ = ‖mismatch†‖ := by
      symm
      exact ContinuousLinearMap.adjoint.norm_map mismatch
    _ = ‖-(mismatch†)‖ := by rw [norm_neg]
    _ = ‖cofactor ∘L scaled†‖ := by
      exact congrArg norm hrecovery.symm
    _ ≤ ‖cofactor‖ * ‖scaled†‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖cofactor‖ * ‖scaled‖ := by
      rw [show ‖scaled†‖ = ‖scaled‖ by
        exact ContinuousLinearMap.adjoint.norm_map scaled]
    _ ≤ ‖cofactor‖ * 8 := by
      exact mul_le_mul_of_nonneg_left
        (suffixMismatchScaledForwardTransition_norm_le_eight lambda p S)
        (norm_nonneg cofactor)
    _ = 8 * ‖cofactor‖ := by ring

/-- Restricting the non-polar ambient extension back through the genuine new
frame recovers the non-polar cofactor exactly. -/
theorem suffixActualBandNonpolarCompleteCoupledAmbientTarget_comp_newFrame
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandNonpolarCompleteCoupledAmbientTarget owner lambda p S ∘L
        newSuffixFrame lambda S =
      suffixActualBandNonpolarCofactorInterior owner lambda p S := by
  have hframeOperator :=
    parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 S (by norm_num)
  apply ContinuousLinearMap.ext
  intro x
  have hframe := DFunLike.congr_fun hframeOperator x
  simp only [suffixActualBandNonpolarCompleteCoupledAmbientTarget,
    ContinuousLinearMap.comp_apply]
  simpa only [newSuffixFrame, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using congrArg
      (suffixActualBandNonpolarCofactorInterior owner lambda p S) hframe

/-- Extension by the actual new-frame adjoint preserves the non-polar
cofactor norm exactly. -/
theorem norm_suffixActualBandNonpolarCompleteCoupledAmbientTarget_eq_cofactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandNonpolarCompleteCoupledAmbientTarget owner lambda p S‖ =
      ‖suffixActualBandNonpolarCofactorInterior owner lambda p S‖ := by
  let target :=
    suffixActualBandNonpolarCompleteCoupledAmbientTarget owner lambda p S
  let cofactor := suffixActualBandNonpolarCofactorInterior owner lambda p S
  let frame := newSuffixFrame lambda S
  have hframe : ‖frame‖ ≤ (1 : ℝ) := by
    simpa only [frame] using newSuffixFrame_norm_le_one lambda S
  have hframeAdjoint : ‖frame†‖ ≤ (1 : ℝ) := by
    calc
      ‖frame†‖ = ‖frame‖ := ContinuousLinearMap.adjoint.norm_map frame
      _ ≤ 1 := hframe
  have htarget : target = cofactor ∘L frame† := by
    rfl
  have hrestriction : target ∘L frame = cofactor := by
    exact
      suffixActualBandNonpolarCompleteCoupledAmbientTarget_comp_newFrame
        owner lambda p S
  apply le_antisymm
  · change ‖target‖ ≤ ‖cofactor‖
    rw [htarget]
    calc
      ‖cofactor ∘L frame†‖ ≤ ‖cofactor‖ * ‖frame†‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖cofactor‖ * 1 :=
        mul_le_mul_of_nonneg_left hframeAdjoint (norm_nonneg _)
      _ = ‖cofactor‖ := mul_one _
  · change ‖cofactor‖ ≤ ‖target‖
    rw [← hrestriction]
    calc
      ‖target ∘L frame‖ ≤ ‖target‖ * ‖frame‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖target‖ * 1 :=
        mul_le_mul_of_nonneg_left hframe (norm_nonneg _)
      _ = ‖target‖ := mul_one _

/-! ## The recombined raw-row target -/

/-- The polar/raw mismatch is literally the polar intertwinement minus the
single recombined raw quadratic intertwinement. -/
theorem suffixMismatchIntertwiningDefect_eq_polarIntertwining_sub_raw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect owner lambda p S =
      suffixActualBandPolarIntertwiningDefect owner lambda p S -
        suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S := by
  simpa only [suffixActualBandPolarIntertwiningDefect] using
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect_eq_polar_sub_raw
      owner lambda p S

/-- The polar boundary intertwinement has the same `6 s_p` scale as its
local Julia descendant, without using a reverse-transition inverse. -/
theorem norm_suffixActualBandPolarIntertwiningDefect_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandPolarIntertwiningDefect owner lambda p S‖ ≤
      6 * primeEulerAmbientLossScale p * ‖detectorOperator owner‖ := by
  let leftCoDefect := (suffixEulerFrameSchurStep lambda p S).leftCoDefect
  let factor :=
    (suffixEulerFrameSchurStep lambda p S).boundaryCoDefectFactor.factor
  let detector := detectorOperator owner
  let frame := newSuffixFrame lambda S
  have hleft : ‖leftCoDefect‖ ≤ 6 * primeEulerAmbientLossScale p := by
    simpa only [leftCoDefect] using
      norm_suffixEulerFrameLeftCoDefect_le_six_ambientLossScale lambda p S
  have hfactor : ‖factor†‖ ≤ (1 : ℝ) := by
    simpa only [factor] using
      (suffixEulerFrameSchurStep lambda p S).boundaryCoDefectFactor
        |>.factor_adjoint_norm_le_one
  have hframe : ‖frame‖ ≤ (1 : ℝ) := by
    simpa only [frame] using newSuffixFrame_norm_le_one lambda S
  have hscale : 0 ≤ primeEulerAmbientLossScale p :=
    primeEulerAmbientLossScale_nonneg p
  rw [suffixActualBandPolarIntertwiningDefect_eq_boundary,
    suffixEulerDetectorBoundaryDefect_eq_juliaCoDefect,
    ContinuousLinearMap.opNorm_neg]
  change ‖leftCoDefect ∘L factor† ∘L detector ∘L frame‖ ≤ _
  calc
    ‖leftCoDefect ∘L factor† ∘L detector ∘L frame‖ ≤
        ‖leftCoDefect ∘L factor† ∘L detector‖ * ‖frame‖ :=
      ContinuousLinearMap.opNorm_comp_le
        (leftCoDefect ∘L factor† ∘L detector) frame
    _ ≤ (‖leftCoDefect ∘L factor†‖ * ‖detector‖) * ‖frame‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_comp_le
          (leftCoDefect ∘L factor†) detector)
        (norm_nonneg frame)
    _ ≤ ((‖leftCoDefect‖ * ‖factor†‖) * ‖detector‖) * ‖frame‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.opNorm_comp_le leftCoDefect (factor†))
          (norm_nonneg detector))
        (norm_nonneg frame)
    _ ≤ (((6 * primeEulerAmbientLossScale p) * 1) * ‖detector‖) * 1 := by
      have hleftFactor :
          ‖leftCoDefect‖ * ‖factor†‖ ≤
            (6 * primeEulerAmbientLossScale p) * 1 :=
        mul_le_mul hleft hfactor (norm_nonneg _)
          (mul_nonneg (by norm_num) hscale)
      have hdetector :
          (‖leftCoDefect‖ * ‖factor†‖) * ‖detector‖ ≤
            ((6 * primeEulerAmbientLossScale p) * 1) * ‖detector‖ :=
        mul_le_mul_of_nonneg_right hleftFactor (norm_nonneg detector)
      exact mul_le_mul hdetector hframe (norm_nonneg frame)
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hscale) zero_le_one)
          (norm_nonneg detector))
    _ = 6 * primeEulerAmbientLossScale p * ‖detector‖ := by ring

/-- Dividing the polar boundary intertwinement by `s_p` leaves the uniform
constant `6`. -/
theorem norm_ambientLossScaled_suffixActualBandPolarIntertwiningDefect_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandPolarIntertwiningDefect owner lambda p S‖ ≤
      6 * ‖detectorOperator owner‖ := by
  have hscale : 0 < primeEulerAmbientLossScale p :=
    primeEulerAmbientLossScale_pos p
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hscale]
  calc
    (primeEulerAmbientLossScale p)⁻¹ *
        ‖suffixActualBandPolarIntertwiningDefect owner lambda p S‖ ≤
      (primeEulerAmbientLossScale p)⁻¹ *
        (6 * primeEulerAmbientLossScale p * ‖detectorOperator owner‖) :=
      mul_le_mul_of_nonneg_left
        (norm_suffixActualBandPolarIntertwiningDefect_le owner lambda p S)
        (inv_nonneg.mpr hscale.le)
    _ = 6 * ‖detectorOperator owner‖ := by
      field_simp [ne_of_gt hscale]

/-- A small generic wrapper keeps the large CCM24 operator types out of the
triangle-inequality elaboration below. -/
theorem norm_smul_sub_le_of_norm_smul_left_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (scale : ℂ) (left right : E) (bound : ℝ)
    (hleft : ‖scale • left‖ ≤ bound) :
    ‖scale • (left - right)‖ ≤ bound + ‖scale • right‖ := by
  rw [smul_sub]
  exact (norm_sub_le _ _).trans (add_le_add hleft (le_refl _))

/-- The complete mismatch costs at most the scaled polar boundary plus the
scaled recombined raw row. -/
theorem norm_ambientLossScaled_mismatch_le_polar_add_raw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S‖ ≤
      6 * ‖detectorOperator owner‖ +
        ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
          suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S‖ := by
  rw [suffixMismatchIntertwiningDefect_eq_polarIntertwining_sub_raw]
  exact norm_smul_sub_le_of_norm_smul_left_le
    ((primeEulerAmbientLossScale p : ℂ)⁻¹)
    (suffixActualBandPolarIntertwiningDefect owner lambda p S)
    (suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)
    (6 * ‖detectorOperator owner‖)
    (norm_ambientLossScaled_suffixActualBandPolarIntertwiningDefect_le
      owner lambda p S)

/-- Conversely, the scaled raw row costs at most the polar boundary plus the
complete mismatch. -/
theorem norm_ambientLossScaled_raw_le_polar_add_mismatch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S‖ ≤
      6 * ‖detectorOperator owner‖ +
        ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
          suffixActualBandRoutePolarRawMismatchIntertwiningDefect
            owner lambda p S‖ := by
  have hsplit :=
    suffixMismatchIntertwiningDefect_eq_polarIntertwining_sub_raw
      owner lambda p S
  have hraw :
      suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S =
        suffixActualBandPolarIntertwiningDefect owner lambda p S -
          suffixActualBandRoutePolarRawMismatchIntertwiningDefect
            owner lambda p S := by
    rw [hsplit]
    abel
  rw [hraw]
  exact norm_smul_sub_le_of_norm_smul_left_le
    ((primeEulerAmbientLossScale p : ℂ)⁻¹)
    (suffixActualBandPolarIntertwiningDefect owner lambda p S)
    (suffixActualBandRoutePolarRawMismatchIntertwiningDefect owner lambda p S)
    (6 * ‖detectorOperator owner‖)
    (norm_ambientLossScaled_suffixActualBandPolarIntertwiningDefect_le
      owner lambda p S)

/-! ## Scaled non-polar target comparison -/

/-- At the ambient-loss scale, the non-polar target is no larger than the
one-sided mismatch. -/
theorem norm_scaled_nonpolarCompleteTarget_le_scaled_mismatch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandNonpolarCompleteCoupledAmbientTarget
          owner lambda p S‖ ≤
      ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S‖ := by
  rw [norm_smul, norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [norm_suffixActualBandNonpolarCompleteCoupledAmbientTarget_eq_cofactor]
  exact norm_suffixActualBandNonpolarCofactorInterior_le_mismatch
    owner lambda p S

/-- The converse scaled comparison costs only the universal forward recovery
constant `8`. -/
theorem norm_scaled_mismatch_le_eight_mul_scaled_nonpolarCompleteTarget
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S‖ ≤
      8 * ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandNonpolarCompleteCoupledAmbientTarget
          owner lambda p S‖ := by
  rw [norm_smul, norm_smul]
  calc
    ‖((primeEulerAmbientLossScale p : ℂ)⁻¹)‖ *
        ‖suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S‖ ≤
      ‖((primeEulerAmbientLossScale p : ℂ)⁻¹)‖ *
        (8 * ‖suffixActualBandNonpolarCofactorInterior
          owner lambda p S‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_mismatch_le_eight_mul_suffixActualBandNonpolarCofactorInterior
          owner lambda p S) (norm_nonneg _)
    _ = 8 *
        (‖((primeEulerAmbientLossScale p : ℂ)⁻¹)‖ *
          ‖suffixActualBandNonpolarCompleteCoupledAmbientTarget
            owner lambda p S‖) := by
      rw [norm_suffixActualBandNonpolarCompleteCoupledAmbientTarget_eq_cofactor]
      ring

/-- The non-polar share is bounded by the full target and the already
controlled polar share on the same ambient domain. -/
theorem norm_scaled_nonpolarCompleteTarget_le_complete_add_polar
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandNonpolarCompleteCoupledAmbientTarget
          owner lambda p S‖ ≤
      ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandCompleteCoupledAmbientTarget owner lambda p S‖ +
      ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandPolarCompleteCoupledAmbientTarget owner lambda p S‖ := by
  have hsplit :=
    suffixActualBandCompleteCoupledAmbientTarget_eq_polar_add_nonpolar
      owner lambda p S
  have hnonpolar :
      suffixActualBandNonpolarCompleteCoupledAmbientTarget owner lambda p S =
        suffixActualBandCompleteCoupledAmbientTarget owner lambda p S -
          suffixActualBandPolarCompleteCoupledAmbientTarget
            owner lambda p S := by
    rw [hsplit]
    abel
  rw [hnonpolar, smul_sub]
  exact norm_sub_le _ _

/-! ## Route-uniform Bone 1A equivalence -/

/-- The recombined raw quadratic intertwinement divided by the genuine
ambient-loss scale at one route-valid adjacent step. -/
noncomputable def routeScaledRawQuadraticIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    sourceSoninCarrier unitSoninScale →L[ℂ]
      sourceSoninCarrier unitSoninScale :=
  ((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
    suffixActualBandRawQuadraticIntertwiningDefect
      owner unitSoninScale index.prime index.suffix

/-- One operator-norm bound for every route-valid scaled recombined raw
quadratic intertwinement. -/
def SuffixRawRouteUniformScaledIntertwiningBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : ℝ) : Prop :=
  0 ≤ bound ∧ ∀ index : RouteFiniteHorizonIndex,
    ‖routeScaledRawQuadraticIntertwiningDefect owner index‖ ≤ bound

/-- A route-uniform raw-row bound implies the complete Bone 1A size gate.
The fixed cost is the sum of the `48` polar cofactor and `6` polar boundary
constants. -/
theorem SuffixRawRouteUniformScaledIntertwiningBound.toCompleteTargetBound
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {bound : ℝ}
    (data : SuffixRawRouteUniformScaledIntertwiningBound owner bound) :
    SuffixCompleteCoupledRouteUniformScaledTargetBound owner
      (54 * ‖detectorOperator owner‖ + bound) := by
  refine ⟨add_nonneg
    (mul_nonneg (by norm_num) (norm_nonneg _)) data.1, ?_⟩
  intro index
  have hsplit :=
    suffixActualBandCompleteCoupledAmbientTarget_eq_polar_add_nonpolar
      owner unitSoninScale index.prime index.suffix
  have hscaledSplit :
      routeScaledCompleteCoupledAmbientTarget owner index =
        ((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
            suffixActualBandPolarCompleteCoupledAmbientTarget
              owner unitSoninScale index.prime index.suffix +
          ((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
            suffixActualBandNonpolarCompleteCoupledAmbientTarget
              owner unitSoninScale index.prime index.suffix := by
    unfold routeScaledCompleteCoupledAmbientTarget
    rw [hsplit, smul_add]
  rw [hscaledSplit]
  calc
    ‖((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
          suffixActualBandPolarCompleteCoupledAmbientTarget
            owner unitSoninScale index.prime index.suffix +
        ((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
          suffixActualBandNonpolarCompleteCoupledAmbientTarget
            owner unitSoninScale index.prime index.suffix‖ ≤
      ‖((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
          suffixActualBandPolarCompleteCoupledAmbientTarget
            owner unitSoninScale index.prime index.suffix‖ +
        ‖((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
          suffixActualBandNonpolarCompleteCoupledAmbientTarget
            owner unitSoninScale index.prime index.suffix‖ := norm_add_le _ _
    _ ≤ 48 * ‖detectorOperator owner‖ +
        ‖((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
          suffixActualBandRoutePolarRawMismatchIntertwiningDefect
            owner unitSoninScale index.prime index.suffix‖ :=
      add_le_add
        (norm_ambientLossScaled_suffixActualBandPolarCompleteCoupledAmbientTarget_le
          owner unitSoninScale index.prime index.suffix)
        (norm_scaled_nonpolarCompleteTarget_le_scaled_mismatch
          owner unitSoninScale index.prime index.suffix)
    _ ≤ 48 * ‖detectorOperator owner‖ +
        (6 * ‖detectorOperator owner‖ +
          ‖routeScaledRawQuadraticIntertwiningDefect owner index‖) := by
      exact add_le_add (le_refl _)
        (norm_ambientLossScaled_mismatch_le_polar_add_raw
          owner unitSoninScale index.prime index.suffix)
    _ ≤ 48 * ‖detectorOperator owner‖ +
        (6 * ‖detectorOperator owner‖ + bound) := by
      exact add_le_add (le_refl _)
        (add_le_add (le_refl _) (data.2 index))
    _ = 54 * ‖detectorOperator owner‖ + bound := by ring

/-- A complete Bone 1A size bound recovers the route-uniform scaled raw row.
The mismatch recovery costs `8`; the controlled complete polar term then
contributes `8 * 48`, and the raw polar boundary contributes `6`. -/
theorem SuffixCompleteCoupledRouteUniformScaledTargetBound.toRawIntertwiningBound
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {bound : ℝ}
    (data : SuffixCompleteCoupledRouteUniformScaledTargetBound owner bound) :
    SuffixRawRouteUniformScaledIntertwiningBound owner
      (390 * ‖detectorOperator owner‖ + 8 * bound) := by
  refine ⟨add_nonneg
    (mul_nonneg (by norm_num) (norm_nonneg _))
    (mul_nonneg (by norm_num) data.1), ?_⟩
  intro index
  unfold routeScaledRawQuadraticIntertwiningDefect
  calc
    ‖((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
        suffixActualBandRawQuadraticIntertwiningDefect
          owner unitSoninScale index.prime index.suffix‖ ≤
      6 * ‖detectorOperator owner‖ +
        ‖((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
          suffixActualBandRoutePolarRawMismatchIntertwiningDefect
            owner unitSoninScale index.prime index.suffix‖ :=
      norm_ambientLossScaled_raw_le_polar_add_mismatch
        owner unitSoninScale index.prime index.suffix
    _ ≤ 6 * ‖detectorOperator owner‖ +
        8 * ‖((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
          suffixActualBandNonpolarCompleteCoupledAmbientTarget
            owner unitSoninScale index.prime index.suffix‖ :=
      add_le_add (le_refl _)
        (norm_scaled_mismatch_le_eight_mul_scaled_nonpolarCompleteTarget
          owner unitSoninScale index.prime index.suffix)
    _ ≤ 6 * ‖detectorOperator owner‖ +
        8 * (
          ‖routeScaledCompleteCoupledAmbientTarget owner index‖ +
          ‖((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
            suffixActualBandPolarCompleteCoupledAmbientTarget
              owner unitSoninScale index.prime index.suffix‖) := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (norm_scaled_nonpolarCompleteTarget_le_complete_add_polar
            owner unitSoninScale index.prime index.suffix)
          (by norm_num))
    _ ≤ 6 * ‖detectorOperator owner‖ +
        8 * (bound + 48 * ‖detectorOperator owner‖) := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (add_le_add (data.2 index)
            (norm_ambientLossScaled_suffixActualBandPolarCompleteCoupledAmbientTarget_le
              owner unitSoninScale index.prime index.suffix))
          (by norm_num))
    _ = 390 * ‖detectorOperator owner‖ + 8 * bound := by ring

/-- Bone 1A is now exactly the existence of one route-uniform scaled bound
for the recombined raw quadratic intertwining defect. -/
theorem exists_routeUniformScaledCompleteTargetBound_iff_rawIntertwiningBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (∃ bound : ℝ,
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner bound) ↔
      ∃ bound : ℝ,
        SuffixRawRouteUniformScaledIntertwiningBound owner bound := by
  constructor
  · rintro ⟨bound, data⟩
    exact ⟨390 * ‖detectorOperator owner‖ + 8 * bound,
      SuffixCompleteCoupledRouteUniformScaledTargetBound.toRawIntertwiningBound
        data⟩
  · rintro ⟨bound, data⟩
    exact ⟨54 * ‖detectorOperator owner‖ + bound,
      SuffixRawRouteUniformScaledIntertwiningBound.toCompleteTargetBound data⟩

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorNonpolarCofactorCollapse
end CCM25Concrete
end Source
end ConnesWeilRH
