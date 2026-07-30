/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedCorrelationCoboundary
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorNormalizedSuffixMetricRow

/-!
# The one-step size gate for the alternating-primitive route

The horizon-one alternating readout is simply `s_p^(-1) C_(p,S)`. Therefore
Proof 649's pointwise route target necessarily contains a route-uniform size
estimate

```text
sup_(route-valid p,S) ||s_p^(-1) C_(p,S)|| < infinity.
```

This module isolates that condition. It also proves that the canonical
ambient extension `C_(p,S)` has exactly the same norm as the genuine signed
interior on the source carrier. The existing normalized metric estimate has
weight `rho_(p::S)`, not `s_p^(-1)`; it does not close this size gate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize

open MeasureTheory Filter Function Set Topology
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorNormalizedSuffixMetricRow
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedCorrelationCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The canonical ambient extension has no norm loss -/

set_option maxRecDepth 4096 in
/-- The complete coupled ambient target is exactly the signed interior
followed by the adjoint of the actual new suffix frame. -/
theorem suffixActualBandCompleteCoupledAmbientTarget_eq_interior_comp_frameAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandCompleteCoupledAmbientTarget owner lambda p S =
      signedCompressedInteriorOwner owner lambda p S ∘L
        (newSuffixFrame lambda S)† := by
  apply ContinuousLinearMap.ext
  intro u
  have hframeOperator :=
    parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 S (by norm_num)
  have hframe := DFunLike.congr_fun hframeOperator
    (((newSuffixFrame lambda S)†) u)
  have hframePoint :
      ((newSuffixFrame lambda S)†)
          (newSuffixFrame lambda S (((newSuffixFrame lambda S)†) u)) =
        ((newSuffixFrame lambda S)†) u := by
    simpa only [newSuffixFrame, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hframe
  have hprojection :
      suffixActualBandCompleteCoupledAmbientTarget owner lambda p S
          (newSuffixFrame lambda S (((newSuffixFrame lambda S)†) u)) =
        suffixActualBandCompleteCoupledAmbientTarget owner lambda p S u := by
    unfold suffixActualBandCompleteCoupledAmbientTarget
    simp only [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply]
    rw [hframePoint]
  have hrestriction := DFunLike.congr_fun
    (suffixActualBandCompleteCoupledAmbientTarget_comp_newFrame
      owner lambda p S) (((newSuffixFrame lambda S)†) u)
  simp only [ContinuousLinearMap.comp_apply] at hrestriction ⊢
  calc
    suffixActualBandCompleteCoupledAmbientTarget owner lambda p S u =
        suffixActualBandCompleteCoupledAmbientTarget owner lambda p S
          (newSuffixFrame lambda S (((newSuffixFrame lambda S)†) u)) :=
      hprojection.symm
    _ = signedCompressedInteriorOwner owner lambda p S
          (((newSuffixFrame lambda S)†) u) := hrestriction

/-- Extending the signed interior by the frame adjoint preserves its operator
norm exactly. -/
theorem norm_suffixActualBandCompleteCoupledAmbientTarget_eq_interior
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandCompleteCoupledAmbientTarget owner lambda p S‖ =
      ‖signedCompressedInteriorOwner owner lambda p S‖ := by
  let target := suffixActualBandCompleteCoupledAmbientTarget owner lambda p S
  let interior := signedCompressedInteriorOwner owner lambda p S
  let frame := newSuffixFrame lambda S
  have hframe : ‖frame‖ ≤ (1 : Real) :=
    newSuffixFrame_norm_le_one lambda S
  have hframeAdjoint : ‖frame†‖ ≤ (1 : Real) := by
    calc
      ‖frame†‖ = ‖frame‖ := ContinuousLinearMap.adjoint.norm_map frame
      _ ≤ 1 := hframe
  have htarget : target = interior ∘L frame† :=
    suffixActualBandCompleteCoupledAmbientTarget_eq_interior_comp_frameAdjoint
      owner lambda p S
  have hrestriction : target ∘L frame = interior :=
    suffixActualBandCompleteCoupledAmbientTarget_comp_newFrame
      owner lambda p S
  apply le_antisymm
  · change ‖target‖ ≤ ‖interior‖
    rw [htarget]
    calc
      ‖interior ∘L frame†‖ ≤ ‖interior‖ * ‖frame†‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖interior‖ * 1 :=
        mul_le_mul_of_nonneg_left hframeAdjoint (norm_nonneg _)
      _ = ‖interior‖ := mul_one _
  · change ‖interior‖ ≤ ‖target‖
    rw [← hrestriction]
    calc
      ‖target ∘L frame‖ ≤ ‖target‖ * ‖frame‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖target‖ * 1 :=
        mul_le_mul_of_nonneg_left hframe (norm_nonneg _)
      _ = ‖target‖ := mul_one _

/-- The known normalized metric estimate transfers to the canonical ambient
extension, but retains the complete suffix scalar. -/
theorem norm_suffixScalar_smul_completeCoupledAmbientTarget_le_eight
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖(suffixEulerSchurMarkovScalar (p :: S) : Complex) •
        suffixActualBandCompleteCoupledAmbientTarget owner lambda p S‖ ≤
      8 * ‖detectorOperator owner‖ := by
  calc
    ‖(suffixEulerSchurMarkovScalar (p :: S) : Complex) •
        suffixActualBandCompleteCoupledAmbientTarget owner lambda p S‖ =
        ‖(suffixEulerSchurMarkovScalar (p :: S) : Complex)‖ *
          ‖suffixActualBandCompleteCoupledAmbientTarget owner lambda p S‖ :=
      norm_smul _ _
    _ = ‖(suffixEulerSchurMarkovScalar (p :: S) : Complex)‖ *
          ‖signedCompressedInteriorOwner owner lambda p S‖ := by
      rw [norm_suffixActualBandCompleteCoupledAmbientTarget_eq_interior]
    _ = ‖(suffixEulerSchurMarkovScalar (p :: S) : Complex) •
          signedCompressedInteriorOwner owner lambda p S‖ := by
      rw [norm_smul]
    _ ≤ 8 * ‖detectorOperator owner‖ :=
      norm_scalar_smul_signedCompressedInteriorOwner_le_eight_mul_detector
        owner lambda p S

/-! ## Horizon one and the route-uniform size gate -/

/-- At horizon one the alternating polynomial is the identity. -/
theorem finiteHorizonAntiresonantCoboundaryReadout_one
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Complex E]
    [NormedAddCommGroup F] [NormedSpace Complex F]
    (scale : Complex) (U : E →L[Complex] E) (C : E →L[Complex] F) :
    finiteHorizonAntiresonantCoboundaryReadout scale U C 1 =
      scale⁻¹ • C := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [finiteHorizonAntiresonantCoboundaryReadout,
    finiteAntiresonantAlternatingPolynomial, Finset.sum_range_succ,
    Finset.sum_range_zero, pow_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply]

/-- The complete target divided by the actual nonzero ambient-loss scale. -/
noncomputable def routeScaledCompleteCoupledAmbientTarget
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    finiteSCarrier →L[Complex] sourceSoninCarrier unitSoninScale :=
  ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) •
    suffixActualBandCompleteCoupledAmbientTarget
      owner unitSoninScale index.prime index.suffix

set_option maxRecDepth 4096 in
/-- The horizon-one route readout is exactly the scaled complete target. -/
theorem routeFiniteHorizonReadout_withHorizon_one_eq_scaledTarget
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    routeFiniteHorizonReadout owner { index with horizon := 1 } =
      routeScaledCompleteCoupledAmbientTarget owner index := by
  unfold routeFiniteHorizonReadout
    suffixActualBandFiniteHorizonCoboundaryReadout
    routeScaledCompleteCoupledAmbientTarget
  exact finiteHorizonAntiresonantCoboundaryReadout_one _ _ _

/-- One operator-norm bound for all route-valid scaled complete targets. -/
def SuffixCompleteCoupledRouteUniformScaledTargetBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : Real) : Prop :=
  0 ≤ bound ∧ ∀ index : RouteFiniteHorizonIndex,
    ‖routeScaledCompleteCoupledAmbientTarget owner index‖ ≤ bound

/-- The scaled target norm is literally `||C_(p,S)|| / s_p`. -/
theorem norm_routeScaledCompleteCoupledAmbientTarget_eq_div
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    ‖routeScaledCompleteCoupledAmbientTarget owner index‖ =
      ‖suffixActualBandCompleteCoupledAmbientTarget owner unitSoninScale
          index.prime index.suffix‖ /
        primeEulerAmbientLossScale index.prime := by
  rw [routeScaledCompleteCoupledAmbientTarget, norm_smul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (primeEulerAmbientLossScale_pos index.prime), div_eq_mul_inv]
  ring

/-- Proof 649's pointwise target necessarily supplies the horizon-one size
gate by Banach--Steinhaus and restriction to horizon one. -/
theorem exists_routeUniformScaledTargetBound_of_pointwise
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (hpointwise :
      SuffixCompleteCoupledRoutePointwiseFiniteHorizonReadoutBound owner) :
    ∃ bound : Real,
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner bound := by
  obtain ⟨bound, huniform⟩ :=
    exists_routeUniformFiniteHorizonReadoutBound_of_pointwise hpointwise
  refine ⟨bound, huniform.1, ?_⟩
  intro index
  have h := huniform.2 { index with horizon := 1 }
  rw [routeFiniteHorizonReadout_withHorizon_one_eq_scaledTarget] at h
  exact h

/-- The equivalent paired-adjoint-coboundary target therefore also contains
the horizon-one size gate. -/
theorem exists_routeUniformScaledTargetBound_of_pairedAdjointCoboundaryEnvelope
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (hpaired :
      SuffixCompleteCoupledRoutePairedAdjointCoboundaryEnvelopeBound owner) :
    ∃ bound : Real,
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner bound :=
  exists_routeUniformScaledTargetBound_of_pointwise
    ((routePairedAdjointCoboundaryEnvelope_iff_pointwiseFiniteHorizonReadout
      owner).mp hpaired)

/-- A scaled terminal matrix coefficient is a matrix coefficient of the
horizon-one target itself. -/
theorem scaled_even_terminal_eq_inner_scaledTarget
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (N : Nat) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) :
    (starRingEnd Complex)
          ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
        inner Complex
          (cc20GlobalLogTranslation
            ((2 * N : Nat) * Real.log index.prime) u)
          (((suffixActualBandCompleteCoupledAmbientTarget owner
            unitSoninScale index.prime index.suffix)†) v) =
      inner Complex
        (routeScaledCompleteCoupledAmbientTarget owner index
          (cc20GlobalLogTranslation
            ((2 * N : Nat) * Real.log index.prime) u)) v := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [routeScaledCompleteCoupledAmbientTarget,
    ContinuousLinearMap.smul_apply, inner_smul_left]

/-- The size gate controls every terminal term in the paired envelope. -/
theorem norm_scaled_even_terminal_le_of_scaledTargetBound
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner} {bound : Real}
    (hbound : SuffixCompleteCoupledRouteUniformScaledTargetBound owner bound)
    (index : RouteFiniteHorizonIndex) (N : Nat) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) :
    ‖(starRingEnd Complex)
          ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
        inner Complex
          (cc20GlobalLogTranslation
            ((2 * N : Nat) * Real.log index.prime) u)
          (((suffixActualBandCompleteCoupledAmbientTarget owner
            unitSoninScale index.prime index.suffix)†) v)‖ ≤
      bound * ‖u‖ * ‖v‖ := by
  rw [scaled_even_terminal_eq_inner_scaledTarget]
  calc
    ‖inner Complex
        (routeScaledCompleteCoupledAmbientTarget owner index
          (cc20GlobalLogTranslation
            ((2 * N : Nat) * Real.log index.prime) u)) v‖ ≤
        ‖routeScaledCompleteCoupledAmbientTarget owner index
          (cc20GlobalLogTranslation
            ((2 * N : Nat) * Real.log index.prime) u)‖ * ‖v‖ :=
      norm_inner_le_norm _ _
    _ ≤ (‖routeScaledCompleteCoupledAmbientTarget owner index‖ *
          ‖cc20GlobalLogTranslation
            ((2 * N : Nat) * Real.log index.prime) u‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        ((routeScaledCompleteCoupledAmbientTarget owner index).le_opNorm _)
        (norm_nonneg _)
    _ = (‖routeScaledCompleteCoupledAmbientTarget owner index‖ * ‖u‖) *
          ‖v‖ := by
      rw [norm_cc20GlobalLogTranslation]
    _ ≤ (bound * ‖u‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hbound.2 index) (norm_nonneg _))
        (norm_nonneg _)
    _ = bound * ‖u‖ * ‖v‖ := rfl

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
end CCM25Concrete
end Source
end ConnesWeilRH
