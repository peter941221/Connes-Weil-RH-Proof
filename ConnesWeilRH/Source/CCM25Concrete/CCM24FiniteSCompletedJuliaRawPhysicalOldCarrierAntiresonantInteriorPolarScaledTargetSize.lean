/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaSignedLocalization

/-!
# The suffix-independent scaled polar target

Proof 658 shows that the two adjacent Sonin range projections differ by at
most `4 q_p`, independently of the suffix.  Conjugating the new projection by
the normalized forward Euler transport costs another `4 q_p`.  The exact
compressed projection identity therefore gives

```text
||D_(p,S)^* D_(p,S)|| <= 8 q_p,
||D_(p,S)|| <= 6 s_p,
```

where `D_(p,S)` is the actual left Julia co-defect and
`s_p = sqrt(q_p)/(1+q_p)` is the ambient antiresonant loss scale.  The right
factor of the polar Julia contribution is a contraction around the detector,
so the ambient-loss-scaled polar Julia channel has norm at most
`6 ||detector||` for every literal suffix.

The final section passes this result through the genuine two-sided Schur
cofactor.  The polar part of the complete coupled ambient target has scaled
norm at most `48 ||detector||`.  The full target is split exactly into this
controlled polar part and one non-polar remainder.  No estimate of that
remainder, Gate 3U theorem, sign statement, or RH premise is introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarScaledTargetSize

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaPolarRawReadout
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierBlockReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction
open CCM24FiniteSCompletedJuliaSignedLocalization
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Exact compressed projection identity -/

/-- The left transition co-defect is the old-frame compression of the gap
between the old range projection and the transported new range projection. -/
theorem rectangularTransitionCoDefect_eq_compressedFrameProjectionGap
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (oldFrame newFrame : H →L[ℂ] K) (transport : K →L[ℂ] K)
    (hold : oldFrame† ∘L oldFrame = ContinuousLinearMap.id ℂ H) :
    rectangularTransitionCoDefect
        (oldFrame† ∘L transport ∘L newFrame)
        ((oldFrame† ∘L transport ∘L newFrame)†) =
      oldFrame† ∘L
        (oldFrame ∘L oldFrame† -
          transport ∘L (newFrame ∘L newFrame†) ∘L transport†) ∘L
        oldFrame := by
  apply ContinuousLinearMap.ext
  intro x
  have holdPoint (z : H) : (oldFrame†) (oldFrame z) = z := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using DFunLike.congr_fun hold z
  simp only [rectangularTransitionCoDefect,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, map_sub, holdPoint]

/-- The actual adjacent left Julia Gram is the compression of the literal
ambient projection gap from the preceding identity. -/
theorem suffixEulerFrameLeftCoDefectGram_eq_compressedProjectionGap
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameSchurStep lambda p S).leftCoDefect† ∘L
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect =
      (oldSuffixFrame lambda p S)† ∘L
        (oldSuffixRangeProjection lambda p S -
          normalizedPrimeEulerFrameTransport p ∘L
            newSuffixRangeProjection lambda S ∘L
              (normalizedPrimeEulerFrameTransport p)†) ∘L
        oldSuffixFrame lambda p S := by
  rw [(suffixEulerFrameSchurStep lambda p S).leftCoDefect_adjoint_comp_self]
  simpa only [suffixEulerFrameSchurStep, suffixEulerFrameTransition,
    oldSuffixRangeProjection, newSuffixRangeProjection] using
    rectangularTransitionCoDefect_eq_compressedFrameProjectionGap
      (oldSuffixFrame lambda p S) (newSuffixFrame lambda S)
      (normalizedPrimeEulerFrameTransport p)
      (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry

/-! ## Transported projection bounds -/

set_option maxHeartbeats 4000000 in
-- The transported projection norm chain elaborates several nested products.
/-- Conjugating the new suffix projection by the near-identity normalized
Euler transport moves it by at most `4 q_p`. -/
theorem norm_newSuffixRangeProjection_sub_transportConjugate_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖newSuffixRangeProjection lambda S -
        normalizedPrimeEulerFrameTransport p ∘L
          newSuffixRangeProjection lambda S ∘L
            (normalizedPrimeEulerFrameTransport p)†‖ ≤
      4 * ccm24PrimeEulerCoefficient p := by
  let projection := newSuffixRangeProjection lambda S
  let transport := normalizedPrimeEulerFrameTransport p
  have hprojection : IsStarProjection projection := by
    simpa only [projection, newSuffixRangeProjection] using
      frame_comp_adjoint_isStarProjection (newSuffixFrame lambda S)
        (suffixEulerFrameSchurStep lambda p S).newFrame_isometry
  have hprojectionNorm : ‖projection‖ ≤ (1 : ℝ) :=
    IsStarProjection.norm_le projection hprojection
  have htransportNorm : ‖transport‖ ≤ (1 : ℝ) := by
    simpa only [transport] using
      normalizedPrimeEulerFrameTransport_norm_le_one p
  have htransportNear :
      ‖ContinuousLinearMap.id ℂ finiteSCarrier - transport‖ ≤
        2 * ccm24PrimeEulerCoefficient p := by
    rw [show ContinuousLinearMap.id ℂ finiteSCarrier - transport =
        -(transport - ContinuousLinearMap.id ℂ finiteSCarrier) by abel,
      norm_neg]
    simpa only [transport] using
      normalizedPrimeEulerFrameTransport_sub_id_norm_le_two_coefficient p
  have htransportAdjointNear :
      ‖ContinuousLinearMap.id ℂ finiteSCarrier - transport†‖ ≤
        2 * ccm24PrimeEulerCoefficient p := by
    rw [show ContinuousLinearMap.id ℂ finiteSCarrier - transport† =
        -(transport† - ContinuousLinearMap.id ℂ finiteSCarrier) by abel,
      norm_neg]
    simpa only [transport] using
      normalizedPrimeEulerFrameTransport_adjoint_sub_id_norm_le_two_coefficient p
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  have hdecomposition :
      projection - transport ∘L projection ∘L transport† =
        (ContinuousLinearMap.id ℂ finiteSCarrier - transport) ∘L
            projection +
          transport ∘L projection ∘L
            (ContinuousLinearMap.id ℂ finiteSCarrier - transport†) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply, map_sub]
    abel
  change ‖projection - transport ∘L projection ∘L transport†‖ ≤ _
  rw [hdecomposition]
  calc
    ‖(ContinuousLinearMap.id ℂ finiteSCarrier - transport) ∘L
          projection +
        transport ∘L projection ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier - transport†)‖ ≤
      ‖(ContinuousLinearMap.id ℂ finiteSCarrier - transport) ∘L
          projection‖ +
        ‖transport ∘L projection ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier - transport†)‖ :=
      norm_add_le _ _
    _ ≤
      ‖ContinuousLinearMap.id ℂ finiteSCarrier - transport‖ *
          ‖projection‖ +
        (‖transport‖ * ‖projection‖) *
          ‖ContinuousLinearMap.id ℂ finiteSCarrier - transport†‖ := by
      exact add_le_add
        (ContinuousLinearMap.opNorm_comp_le
          (ContinuousLinearMap.id ℂ finiteSCarrier - transport) projection)
        (calc
          ‖transport ∘L projection ∘L
              (ContinuousLinearMap.id ℂ finiteSCarrier - transport†)‖ ≤
              ‖transport ∘L projection‖ *
                ‖ContinuousLinearMap.id ℂ finiteSCarrier - transport†‖ :=
            ContinuousLinearMap.opNorm_comp_le
              (transport ∘L projection)
              (ContinuousLinearMap.id ℂ finiteSCarrier - transport†)
          _ ≤ (‖transport‖ * ‖projection‖) *
                ‖ContinuousLinearMap.id ℂ finiteSCarrier - transport†‖ :=
            mul_le_mul_of_nonneg_right
              (ContinuousLinearMap.opNorm_comp_le transport projection)
              (norm_nonneg _))
    _ ≤
      (2 * ccm24PrimeEulerCoefficient p) * 1 +
        (1 * 1) * (2 * ccm24PrimeEulerCoefficient p) := by
      exact add_le_add
        (mul_le_mul htransportNear hprojectionNorm (norm_nonneg _)
          (mul_nonneg (by norm_num) hq))
        (mul_le_mul
          (mul_le_mul htransportNorm hprojectionNorm (norm_nonneg _)
            zero_le_one)
          htransportAdjointNear (norm_nonneg _)
          (mul_nonneg zero_le_one zero_le_one))
    _ = 4 * ccm24PrimeEulerCoefficient p := by ring

/-- The old projection differs from the transported new projection by at
most `8 q_p`, uniformly in the literal suffix. -/
theorem norm_oldSuffixRangeProjection_sub_transportConjugate_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖oldSuffixRangeProjection lambda p S -
        normalizedPrimeEulerFrameTransport p ∘L
          newSuffixRangeProjection lambda S ∘L
            (normalizedPrimeEulerFrameTransport p)†‖ ≤
      8 * ccm24PrimeEulerCoefficient p := by
  have hsplit :
      oldSuffixRangeProjection lambda p S -
          normalizedPrimeEulerFrameTransport p ∘L
            newSuffixRangeProjection lambda S ∘L
              (normalizedPrimeEulerFrameTransport p)† =
        (oldSuffixRangeProjection lambda p S -
          newSuffixRangeProjection lambda S) +
        (newSuffixRangeProjection lambda S -
          normalizedPrimeEulerFrameTransport p ∘L
            newSuffixRangeProjection lambda S ∘L
              (normalizedPrimeEulerFrameTransport p)†) := by
    abel
  rw [hsplit]
  calc
    ‖(oldSuffixRangeProjection lambda p S -
          newSuffixRangeProjection lambda S) +
        (newSuffixRangeProjection lambda S -
          normalizedPrimeEulerFrameTransport p ∘L
            newSuffixRangeProjection lambda S ∘L
              (normalizedPrimeEulerFrameTransport p)†)‖ ≤
      ‖oldSuffixRangeProjection lambda p S -
          newSuffixRangeProjection lambda S‖ +
        ‖newSuffixRangeProjection lambda S -
          normalizedPrimeEulerFrameTransport p ∘L
            newSuffixRangeProjection lambda S ∘L
              (normalizedPrimeEulerFrameTransport p)†‖ := norm_add_le _ _
    _ ≤ 4 * ccm24PrimeEulerCoefficient p +
        4 * ccm24PrimeEulerCoefficient p :=
      add_le_add
        (norm_oldSuffixRangeProjection_sub_newSuffixRangeProjection_le
          lambda p S)
        (norm_newSuffixRangeProjection_sub_transportConjugate_le lambda p S)
    _ = 8 * ccm24PrimeEulerCoefficient p := by ring

/-! ## The actual left co-defect scale -/

set_option maxHeartbeats 4000000 in
-- The compressed projection identity and three norm factors elaborate together.
/-- The Gram operator of the actual adjacent left Julia co-defect is
`O(q_p)` independently of the suffix. -/
theorem norm_suffixEulerFrameLeftCoDefectGram_le_eight_coefficient
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect† ∘L
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect‖ ≤
      8 * ccm24PrimeEulerCoefficient p := by
  let oldFrame := oldSuffixFrame lambda p S
  let gap := oldSuffixRangeProjection lambda p S -
    normalizedPrimeEulerFrameTransport p ∘L
      newSuffixRangeProjection lambda S ∘L
        (normalizedPrimeEulerFrameTransport p)†
  have holdFrame : ‖oldFrame‖ ≤ (1 : ℝ) := by
    simpa only [oldFrame, oldSuffixFrame, newSuffixFrame] using
      newSuffixFrame_norm_le_one lambda (p :: S)
  have holdFrameAdjoint : ‖oldFrame†‖ ≤ (1 : ℝ) := by
    calc
      ‖oldFrame†‖ = ‖oldFrame‖ :=
        ContinuousLinearMap.adjoint.norm_map oldFrame
      _ ≤ 1 := holdFrame
  have hgap : ‖gap‖ ≤ 8 * ccm24PrimeEulerCoefficient p := by
    simpa only [gap] using
      norm_oldSuffixRangeProjection_sub_transportConjugate_le lambda p S
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  rw [suffixEulerFrameLeftCoDefectGram_eq_compressedProjectionGap]
  change ‖oldFrame† ∘L gap ∘L oldFrame‖ ≤ _
  calc
    ‖oldFrame† ∘L gap ∘L oldFrame‖ ≤
        ‖oldFrame† ∘L gap‖ * ‖oldFrame‖ :=
      ContinuousLinearMap.opNorm_comp_le (oldFrame† ∘L gap) oldFrame
    _ ≤ (‖oldFrame†‖ * ‖gap‖) * ‖oldFrame‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_comp_le (oldFrame†) gap)
        (norm_nonneg oldFrame)
    _ ≤ (1 * (8 * ccm24PrimeEulerCoefficient p)) * 1 := by
      exact mul_le_mul
        (mul_le_mul holdFrameAdjoint hgap (norm_nonneg gap) zero_le_one)
        holdFrame (norm_nonneg oldFrame)
        (mul_nonneg zero_le_one (mul_nonneg (by norm_num) hq))
    _ = 8 * ccm24PrimeEulerCoefficient p := by ring

/-- Squaring the left co-defect norm gives the preceding Gram norm. -/
theorem norm_suffixEulerFrameLeftCoDefect_sq_le_eight_coefficient
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect‖ ^ 2 ≤
      8 * ccm24PrimeEulerCoefficient p := by
  have h := norm_suffixEulerFrameLeftCoDefectGram_le_eight_coefficient
    lambda p S
  calc
    ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect‖ ^ 2 =
        ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect† ∘L
          (suffixEulerFrameSchurStep lambda p S).leftCoDefect‖ := by
      symm
      simpa only [pow_two] using
        (ContinuousLinearMap.norm_adjoint_comp_self
          (suffixEulerFrameSchurStep lambda p S).leftCoDefect)
    _ ≤ 8 * ccm24PrimeEulerCoefficient p := h

/-- The square-root Euler coefficient is at most twice the genuine ambient
loss scale. -/
theorem sqrt_coefficient_le_two_mul_primeEulerAmbientLossScale
    (p : CCM24VisiblePrime) :
    Real.sqrt (ccm24PrimeEulerCoefficient p) ≤
      2 * primeEulerAmbientLossScale p := by
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  have hqOne : ccm24PrimeEulerCoefficient p ≤ 1 :=
    (ccm24PrimeEulerCoefficient_lt_one p).le
  have hden : 0 < 1 + ccm24PrimeEulerCoefficient p := by linarith
  unfold primeEulerAmbientLossScale
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hden).2
  nlinarith [Real.sqrt_nonneg (ccm24PrimeEulerCoefficient p)]

/-- The actual left Julia co-defect is `O(s_p)`, with a constant independent
of both the prime and the suffix. -/
theorem norm_suffixEulerFrameLeftCoDefect_le_six_ambientLossScale
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect‖ ≤
      6 * primeEulerAmbientLossScale p := by
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  have hsquare :=
    norm_suffixEulerFrameLeftCoDefect_sq_le_eight_coefficient lambda p S
  have hthree :
      ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect‖ ≤
        3 * Real.sqrt (ccm24PrimeEulerCoefficient p) := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
    nlinarith [Real.sq_sqrt hq]
  calc
    ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect‖ ≤
        3 * Real.sqrt (ccm24PrimeEulerCoefficient p) := hthree
    _ ≤ 3 * (2 * primeEulerAmbientLossScale p) := by
      gcongr
      exact sqrt_coefficient_le_two_mul_primeEulerAmbientLossScale p
    _ = 6 * primeEulerAmbientLossScale p := by ring

/-! ## The polar Julia channel -/

/-- Every factor to the right of the left Julia co-defect is contractive
except for the detector itself. -/
theorem norm_suffixActualBandLocalPolarJuliaRightFactor_le_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandLocalPolarJuliaRightFactor owner lambda p S‖ ≤
      ‖detectorOperator owner‖ := by
  let factor :=
    (suffixEulerFrameSchurStep lambda p S).boundaryCoDefectFactor.factor
  let detector := detectorOperator owner
  let frame := newSuffixFrame lambda S
  let reverse := suffixEulerFrameReverseTransition lambda p S
  have hfactorAdjoint : ‖factor†‖ ≤ (1 : ℝ) := by
    simpa only [factor] using
      (suffixEulerFrameSchurStep lambda p S).boundaryCoDefectFactor
        |>.factor_adjoint_norm_le_one
  have hframe : ‖frame‖ ≤ (1 : ℝ) := by
    simpa only [frame] using newSuffixFrame_norm_le_one lambda S
  have hreverse : ‖reverse‖ ≤ (1 : ℝ) := by
    simpa only [reverse] using
      suffixEulerFrameReverseTransition_norm_le_one lambda p S
  change ‖factor† ∘L detector ∘L frame ∘L reverse‖ ≤ ‖detector‖
  calc
    ‖factor† ∘L detector ∘L frame ∘L reverse‖ ≤
        ‖factor† ∘L detector ∘L frame‖ * ‖reverse‖ :=
      ContinuousLinearMap.opNorm_comp_le
        (factor† ∘L detector ∘L frame) reverse
    _ ≤ (‖factor† ∘L detector‖ * ‖frame‖) * ‖reverse‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_comp_le (factor† ∘L detector) frame)
        (norm_nonneg reverse)
    _ ≤ ((‖factor†‖ * ‖detector‖) * ‖frame‖) * ‖reverse‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.opNorm_comp_le (factor†) detector)
          (norm_nonneg frame))
        (norm_nonneg reverse)
    _ ≤ ((1 * ‖detector‖) * 1) * 1 := by
      gcongr
    _ = ‖detector‖ := by ring

/-- Before dividing by `s_p`, the complete polar Julia contribution has the
required `O(s_p)` size for every suffix. -/
theorem norm_suffixActualBandLocalPolarJuliaContribution_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandLocalPolarJuliaContribution owner lambda p S‖ ≤
      6 * primeEulerAmbientLossScale p * ‖detectorOperator owner‖ := by
  rw [suffixActualBandLocalPolarJuliaContribution_eq_leftCoDefect]
  calc
    ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
        suffixActualBandLocalPolarJuliaRightFactor owner lambda p S‖ ≤
      ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect‖ *
        ‖suffixActualBandLocalPolarJuliaRightFactor owner lambda p S‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (6 * primeEulerAmbientLossScale p) *
        ‖detectorOperator owner‖ := by
      exact mul_le_mul
        (norm_suffixEulerFrameLeftCoDefect_le_six_ambientLossScale
          lambda p S)
        (norm_suffixActualBandLocalPolarJuliaRightFactor_le_detector
          owner lambda p S)
        (norm_nonneg _)
        (mul_nonneg (by norm_num) (primeEulerAmbientLossScale_nonneg p))
    _ = 6 * primeEulerAmbientLossScale p *
        ‖detectorOperator owner‖ := rfl

/-- Dividing the polar Julia channel by the genuine ambient loss scale leaves
the uniform constant `6`. -/
theorem norm_ambientLossScaled_suffixActualBandLocalPolarJuliaContribution_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandLocalPolarJuliaContribution owner lambda p S‖ ≤
      6 * ‖detectorOperator owner‖ := by
  have hscale : 0 < primeEulerAmbientLossScale p :=
    primeEulerAmbientLossScale_pos p
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hscale]
  calc
    (primeEulerAmbientLossScale p)⁻¹ *
        ‖suffixActualBandLocalPolarJuliaContribution owner lambda p S‖ ≤
      (primeEulerAmbientLossScale p)⁻¹ *
        (6 * primeEulerAmbientLossScale p * ‖detectorOperator owner‖) :=
      mul_le_mul_of_nonneg_left
        (norm_suffixActualBandLocalPolarJuliaContribution_le
          owner lambda p S)
        (inv_nonneg.mpr hscale.le)
    _ = 6 * ‖detectorOperator owner‖ := by
      field_simp [ne_of_gt hscale]

/-! ## Two-sided polar cofactor and complete ambient target -/

/-- The part of the signed interior obtained by inserting only the proved
polar Julia term into the exact two-sided Schur cofactor. -/
noncomputable def suffixActualBandPolarCofactorInterior
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
    ((suffixEulerFrameTransition lambda p S)† ∘L
      (suffixActualBandLocalPolarJuliaContribution owner lambda p S)† ∘L
        (suffixEulerFrameReverseTransition lambda p S)†)

/-- The exact complementary cofactor keeps the unresolved first-jet and
route/polar ordering terms coupled. -/
noncomputable def suffixActualBandNonpolarCofactorInterior
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
    ((suffixEulerFrameTransition lambda p S)† ∘L
      (suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)† ∘L
        (suffixEulerFrameReverseTransition lambda p S)†)

set_option linter.style.longLine false in
-- The imported exact cofactor theorem has an identifier longer than 100 characters.
/-- The signed interior is exactly the controlled polar cofactor plus the
single unresolved non-polar cofactor. -/
theorem signedCompressedInteriorOwner_eq_polar_add_nonpolarCofactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    signedCompressedInteriorOwner owner lambda p S =
      suffixActualBandPolarCofactorInterior owner lambda p S +
        suffixActualBandNonpolarCofactorInterior owner lambda p S := by
  rw [
    signedCompressedInteriorOwner_eq_neg_scalarInv_smul_transitionAdjoint_comp_localRawDefectAdjoint_comp_reverseAdjoint]
  rw [suffixActualBandLocalRawDefect_eq_polarJulia_add_nonpolarGap,
    ContinuousLinearMap.adjoint.map_add]
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualBandPolarCofactorInterior,
    suffixActualBandNonpolarCofactorInterior,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, map_add, smul_add]

set_option maxHeartbeats 4000000 in
-- The three adjoint factors and scalar cofactor elaborate together.
/-- The polar cofactor still has `O(s_p)` norm; only the fixed inverse
Schur--Markov scalar costs the factor `8`. -/
theorem norm_suffixActualBandPolarCofactorInterior_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandPolarCofactorInterior owner lambda p S‖ ≤
      48 * primeEulerAmbientLossScale p * ‖detectorOperator owner‖ := by
  have htransition : ‖(suffixEulerFrameTransition lambda p S)†‖ ≤
      (1 : ℝ) := by
    calc
      ‖(suffixEulerFrameTransition lambda p S)†‖ =
          ‖suffixEulerFrameTransition lambda p S‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := suffixEulerFrameTransition_norm_le_one lambda p S
  have hreverse : ‖(suffixEulerFrameReverseTransition lambda p S)†‖ ≤
      (1 : ℝ) := by
    calc
      ‖(suffixEulerFrameReverseTransition lambda p S)†‖ =
          ‖suffixEulerFrameReverseTransition lambda p S‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := suffixEulerFrameReverseTransition_norm_le_one lambda p S
  have hpolarAdjoint :
      ‖(suffixActualBandLocalPolarJuliaContribution owner lambda p S)†‖ ≤
        6 * primeEulerAmbientLossScale p * ‖detectorOperator owner‖ := by
    calc
      ‖(suffixActualBandLocalPolarJuliaContribution owner lambda p S)†‖ =
          ‖suffixActualBandLocalPolarJuliaContribution owner lambda p S‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 6 * primeEulerAmbientLossScale p * ‖detectorOperator owner‖ :=
        norm_suffixActualBandLocalPolarJuliaContribution_le owner lambda p S
  have hcore :
      ‖(suffixEulerFrameTransition lambda p S)† ∘L
          (suffixActualBandLocalPolarJuliaContribution owner lambda p S)† ∘L
            (suffixEulerFrameReverseTransition lambda p S)†‖ ≤
        (1 * (6 * primeEulerAmbientLossScale p *
          ‖detectorOperator owner‖)) * 1 := by
    calc
      ‖(suffixEulerFrameTransition lambda p S)† ∘L
          (suffixActualBandLocalPolarJuliaContribution owner lambda p S)† ∘L
            (suffixEulerFrameReverseTransition lambda p S)†‖ ≤
        ‖(suffixEulerFrameTransition lambda p S)† ∘L
          (suffixActualBandLocalPolarJuliaContribution owner lambda p S)†‖ *
            ‖(suffixEulerFrameReverseTransition lambda p S)†‖ :=
        ContinuousLinearMap.opNorm_comp_le
          ((suffixEulerFrameTransition lambda p S)† ∘L
            (suffixActualBandLocalPolarJuliaContribution owner lambda p S)†)
          ((suffixEulerFrameReverseTransition lambda p S)†)
      _ ≤ (‖(suffixEulerFrameTransition lambda p S)†‖ *
          ‖(suffixActualBandLocalPolarJuliaContribution owner lambda p S)†‖) *
            ‖(suffixEulerFrameReverseTransition lambda p S)†‖ := by
        exact mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.opNorm_comp_le
            ((suffixEulerFrameTransition lambda p S)†)
            ((suffixActualBandLocalPolarJuliaContribution owner lambda p S)†))
          (norm_nonneg _)
      _ ≤ (1 * (6 * primeEulerAmbientLossScale p *
          ‖detectorOperator owner‖)) * 1 := by
        exact mul_le_mul
          (mul_le_mul htransition hpolarAdjoint (norm_nonneg _) zero_le_one)
          hreverse (norm_nonneg _)
          (mul_nonneg zero_le_one
            (mul_nonneg
              (mul_nonneg (by norm_num) (primeEulerAmbientLossScale_nonneg p))
              (norm_nonneg _)))
  rw [suffixActualBandPolarCofactorInterior]
  calc
    ‖(-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
        ((suffixEulerFrameTransition lambda p S)† ∘L
          (suffixActualBandLocalPolarJuliaContribution owner lambda p S)† ∘L
            (suffixEulerFrameReverseTransition lambda p S)†)‖ ≤
      ‖-((primeSchurMarkovScalar p : ℂ)⁻¹)‖ *
        ‖(suffixEulerFrameTransition lambda p S)† ∘L
          (suffixActualBandLocalPolarJuliaContribution owner lambda p S)† ∘L
            (suffixEulerFrameReverseTransition lambda p S)†‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ 8 *
        ((1 * (6 * primeEulerAmbientLossScale p *
          ‖detectorOperator owner‖)) * 1) := by
      have hscalar : ‖-((primeSchurMarkovScalar p : ℂ)⁻¹)‖ ≤
          (8 : ℝ) := by
        rw [norm_neg]
        exact norm_primeSchurMarkovScalar_inv_le_eight p
      exact mul_le_mul hscalar hcore (norm_nonneg _) (by norm_num)
    _ = 48 * primeEulerAmbientLossScale p *
        ‖detectorOperator owner‖ := by ring

/-- The complete ambient target contributed by the polar cofactor. -/
noncomputable def suffixActualBandPolarCompleteCoupledAmbientTarget
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] sourceSoninCarrier lambda :=
  suffixActualBandPolarCofactorInterior owner lambda p S ∘L
    (newSuffixFrame lambda S)†

/-- The complete ambient target contributed by the unresolved non-polar
cofactor. -/
noncomputable def suffixActualBandNonpolarCompleteCoupledAmbientTarget
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] sourceSoninCarrier lambda :=
  suffixActualBandNonpolarCofactorInterior owner lambda p S ∘L
    (newSuffixFrame lambda S)†

/-- The full complete target is exactly the controlled polar target plus one
non-polar remainder on the same ambient domain. -/
theorem suffixActualBandCompleteCoupledAmbientTarget_eq_polar_add_nonpolar
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandCompleteCoupledAmbientTarget owner lambda p S =
      suffixActualBandPolarCompleteCoupledAmbientTarget owner lambda p S +
        suffixActualBandNonpolarCompleteCoupledAmbientTarget
          owner lambda p S := by
  rw [suffixActualBandCompleteCoupledAmbientTarget_eq_interior_comp_frameAdjoint,
    signedCompressedInteriorOwner_eq_polar_add_nonpolarCofactor]
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualBandPolarCompleteCoupledAmbientTarget,
    suffixActualBandNonpolarCompleteCoupledAmbientTarget,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]

/-- After division by the genuine ambient loss scale, the polar share of the
actual complete coupled target has the suffix-independent bound `48`. -/
theorem norm_ambientLossScaled_suffixActualBandPolarCompleteCoupledAmbientTarget_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandPolarCompleteCoupledAmbientTarget
          owner lambda p S‖ ≤
      48 * ‖detectorOperator owner‖ := by
  have hframeAdjoint : ‖(newSuffixFrame lambda S)†‖ ≤ (1 : ℝ) := by
    calc
      ‖(newSuffixFrame lambda S)†‖ = ‖newSuffixFrame lambda S‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := newSuffixFrame_norm_le_one lambda S
  have hpolarTarget :
      ‖suffixActualBandPolarCompleteCoupledAmbientTarget
          owner lambda p S‖ ≤
        48 * primeEulerAmbientLossScale p * ‖detectorOperator owner‖ := by
    rw [suffixActualBandPolarCompleteCoupledAmbientTarget]
    calc
      ‖suffixActualBandPolarCofactorInterior owner lambda p S ∘L
          (newSuffixFrame lambda S)†‖ ≤
        ‖suffixActualBandPolarCofactorInterior owner lambda p S‖ *
          ‖(newSuffixFrame lambda S)†‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (48 * primeEulerAmbientLossScale p *
          ‖detectorOperator owner‖) * 1 := by
        exact mul_le_mul
          (norm_suffixActualBandPolarCofactorInterior_le owner lambda p S)
          hframeAdjoint (norm_nonneg _)
          (mul_nonneg
            (mul_nonneg (by norm_num) (primeEulerAmbientLossScale_nonneg p))
            (norm_nonneg _))
      _ = 48 * primeEulerAmbientLossScale p *
          ‖detectorOperator owner‖ := by ring
  have hscale : 0 < primeEulerAmbientLossScale p :=
    primeEulerAmbientLossScale_pos p
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hscale]
  calc
    (primeEulerAmbientLossScale p)⁻¹ *
        ‖suffixActualBandPolarCompleteCoupledAmbientTarget
          owner lambda p S‖ ≤
      (primeEulerAmbientLossScale p)⁻¹ *
        (48 * primeEulerAmbientLossScale p *
          ‖detectorOperator owner‖) :=
      mul_le_mul_of_nonneg_left hpolarTarget (inv_nonneg.mpr hscale.le)
    _ = 48 * ‖detectorOperator owner‖ := by
      field_simp [ne_of_gt hscale]

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarScaledTargetSize
end CCM25Concrete
end Source
end ConnesWeilRH
