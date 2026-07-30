/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPolarBoundaryRawIntertwining
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorTwoStepCoboundaryFactorization

/-!
# Collapse of the two-step coboundary factor gate

Proof 656 treats the horizon-one size gate and a two-step coboundary factor
as two source inputs.  On the actual whole-line `L²` carrier they are not
independent.  For `a > 0`, the one-step coboundary `I - U_(-a)` is injective,
because a translation-fixed `L²` vector would have a nondecaying matrix
coefficient, contradicting weak escape of translations.

Together with

```text
I - U_(-2a) = (I - U_(-a))(I + U_(-a)),
```

this permits exact cancellation in Proof 656's factorization.  Its two-step
factor is therefore equivalent, with the same norm bound, to Proof 648's
ambient antiresonant quotient.  In particular the two-step factor alone
implies the horizon-one size gate and the existing Bone 1 consumers.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace TwoStepFactorCollapse

open MeasureTheory Filter Function Set Topology
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCausalMarkov
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorInfiniteHorizonTail
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedCorrelationCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelColumnEquivalence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorTwoStepCoboundaryFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorUniformAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "GlobalOp" => finiteSCarrier →L[Complex] finiteSCarrier

/-! ## Cancellation on the whole-line carrier -/

/-- A whole-line `L²` vector fixed by a nonzero positive translation is zero.
The proof uses the already established weak escape of translation matrix
coefficients. -/
theorem eq_zero_of_cc20GlobalLogTranslation_eq_self
    (a : Real) (ha : 0 < a) (x : finiteSCarrier)
    (hfixed : cc20GlobalLogTranslation a x = x) :
    x = 0 := by
  have htranslate : ∀ N : Nat,
      cc20GlobalLogTranslation ((N : Real) * a) x = x := by
    intro N
    induction N with
    | zero =>
        simpa using cc20GlobalLogTranslation_zero_apply x
    | succ N ih =>
        calc
          cc20GlobalLogTranslation (((Nat.succ N : Nat) : Real) * a) x =
              cc20GlobalLogTranslation ((N : Real) * a + a) x := by
            congr 2
            push_cast
            ring
          _ = cc20GlobalLogTranslation ((N : Real) * a)
                (cc20GlobalLogTranslation a x) := by
            rw [cc20GlobalLogTranslation_add_apply]
          _ = cc20GlobalLogTranslation ((N : Real) * a) x := by
            rw [hfixed]
          _ = x := ih
  have hzero := inner_cc20GlobalLogTranslation_nat_mul_tendsto_zero
    a ha x x
  have hzero' : Tendsto (fun _ : Nat => inner Complex x x)
      atTop (nhds 0) := by
    simpa only [htranslate] using hzero
  have hconstant : Tendsto (fun _ : Nat => inner Complex x x)
      atTop (nhds (inner Complex x x)) := tendsto_const_nhds
  exact (inner_self_eq_zero.mp (tendsto_nhds_unique hconstant hzero'))

/-- The negative one-step translation coboundary has trivial kernel. -/
theorem negativeTranslationCoboundary_eq_zero_imp_eq_zero
    (a : Real) (ha : 0 < a) (x : finiteSCarrier)
    (hzero :
      (ContinuousLinearMap.id Complex finiteSCarrier -
        (cc20GlobalLogTranslation (-a)).toContinuousLinearMap) x = 0) :
    x = 0 := by
  have hnegative : x = cc20GlobalLogTranslation (-a) x := by
    apply sub_eq_zero.mp
    simpa only [ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply] using hzero
  have hpositive : cc20GlobalLogTranslation a x = x := by
    calc
      cc20GlobalLogTranslation a x =
          cc20GlobalLogTranslation a
            (cc20GlobalLogTranslation (-a) x) := by
        rw [← hnegative]
      _ = x := cc20GlobalLogTranslation_neg_apply a x
  exact eq_zero_of_cc20GlobalLogTranslation_eq_self a ha x hpositive

/-- Left composition by the negative one-step coboundary is cancellable. -/
theorem negativeTranslationCoboundary_injective
    (a : Real) (ha : 0 < a) :
    Function.Injective
      (ContinuousLinearMap.id Complex finiteSCarrier -
        (cc20GlobalLogTranslation (-a)).toContinuousLinearMap) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply negativeTranslationCoboundary_eq_zero_imp_eq_zero a ha
  simp only [map_sub, hxy, sub_self]

/-- Generic cancellation of a common injective left factor. -/
theorem comp_left_cancel_of_injective
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Complex E]
    [NormedAddCommGroup F] [NormedSpace Complex F]
    [NormedAddCommGroup G] [NormedSpace Complex G]
    (left : F →L[Complex] G) (hleft : Function.Injective left)
    {first second : E →L[Complex] F}
    (hcomp : left ∘L first = left ∘L second) :
    first = second := by
  apply ContinuousLinearMap.ext
  intro x
  apply hleft
  exact DFunLike.congr_fun hcomp x

/-! ## One-step times antiresonant step -/

/-- The two-step translation coboundary is the one-step coboundary followed
by the antiresonant factor. -/
theorem twoStepTranslationCoboundary_eq_oneStep_comp_add
    (a : Real) :
    ContinuousLinearMap.id Complex finiteSCarrier -
        (cc20GlobalLogTranslation (-2 * a)).toContinuousLinearMap =
      (ContinuousLinearMap.id Complex finiteSCarrier -
          (cc20GlobalLogTranslation (-a)).toContinuousLinearMap) ∘L
        (ContinuousLinearMap.id Complex finiteSCarrier +
          (cc20GlobalLogTranslation (-a)).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, map_add]
  change x - cc20GlobalLogTranslation (-2 * a) x =
    x - cc20GlobalLogTranslation (-a) x +
      (cc20GlobalLogTranslation (-a) x -
        cc20GlobalLogTranslation (-a)
          (cc20GlobalLogTranslation (-a) x))
  rw [cc20GlobalLogTranslation_add_apply]
  have hshift : -a + -a = -2 * a := by ring
  rw [hshift]
  module

private theorem star_inv_ofReal (scale : Real) :
    (starRingEnd Complex) ((scale : Complex)⁻¹) =
      ((scale : Complex)⁻¹) := by
  rw [map_inv₀, starRingEnd_apply, Complex.star_def,
    Complex.conj_ofReal]

/-- The scaled adjoint coboundary target is the injective one-step factor
applied to the scaled complete target adjoint. -/
theorem routeScaledPrimeLogAdjointCoboundaryTarget_eq_oneStep_comp_scaledAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    routeScaledPrimeLogAdjointCoboundaryTarget owner index =
      (ContinuousLinearMap.id Complex finiteSCarrier -
          (cc20GlobalLogTranslation
            (-Real.log index.prime)).toContinuousLinearMap) ∘L
        (((primeEulerAmbientLossScale index.prime : Complex)⁻¹) •
          (suffixActualBandCompleteCoupledAmbientTarget
            owner unitSoninScale index.prime index.suffix)†) := by
  rw [routeScaledPrimeLogAdjointCoboundaryTarget,
    routePrimeLogAdjointCoboundaryTarget]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_smul,
    star_inv_ofReal]

/-! ## Same-bound conversion of the two factor contracts -/

/-- Injectivity cancels Proof 656's common one-step coboundary. -/
theorem RouteScaledTwoStepCoboundaryFactorData.scaledAdjoint_factorization
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {index : RouteFiniteHorizonIndex} {bound : Real}
    (data : RouteScaledTwoStepCoboundaryFactorData owner index bound) :
    ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) •
        (suffixActualBandCompleteCoupledAmbientTarget
          owner unitSoninScale index.prime index.suffix)† =
      (ContinuousLinearMap.id Complex finiteSCarrier +
          (cc20GlobalLogTranslation
            (-Real.log index.prime)).toContinuousLinearMap) ∘L
        data.factor := by
  let oneStep : GlobalOp :=
    ContinuousLinearMap.id Complex finiteSCarrier -
      (cc20GlobalLogTranslation
        (-Real.log index.prime)).toContinuousLinearMap
  let addStep : GlobalOp :=
    ContinuousLinearMap.id Complex finiteSCarrier +
      (cc20GlobalLogTranslation
        (-Real.log index.prime)).toContinuousLinearMap
  have hprime : (1 : Real) < (index.prime : Real) := by
    exact_mod_cast index.prime.property
  have honeStep : Function.Injective oneStep := by
    simpa only [oneStep] using
      negativeTranslationCoboundary_injective
        (Real.log index.prime) (Real.log_pos hprime)
  apply comp_left_cancel_of_injective oneStep honeStep
  calc
    oneStep ∘L
          (((primeEulerAmbientLossScale index.prime : Complex)⁻¹) •
            (suffixActualBandCompleteCoupledAmbientTarget
              owner unitSoninScale index.prime index.suffix)†) =
        routeScaledPrimeLogAdjointCoboundaryTarget owner index := by
      rw [
        routeScaledPrimeLogAdjointCoboundaryTarget_eq_oneStep_comp_scaledAdjoint]
    _ = (ContinuousLinearMap.id Complex finiteSCarrier -
          (cc20GlobalLogTranslation
            (-2 * Real.log index.prime)).toContinuousLinearMap) ∘L
        data.factor := data.factorization
    _ = (oneStep ∘L addStep) ∘L data.factor := by
      rw [twoStepTranslationCoboundary_eq_oneStep_comp_add]
    _ = oneStep ∘L (addStep ∘L data.factor) := by
      simp only [ContinuousLinearMap.comp_assoc]

/-- A Proof 656 two-step factor is the actual complete ambient-loss quotient
with the same factor and the same norm bound after taking adjoints. -/
noncomputable def
    RouteScaledTwoStepCoboundaryFactorData.toAmbientLossFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {index : RouteFiniteHorizonIndex} {bound : Real}
    (data : RouteScaledTwoStepCoboundaryFactorData owner index bound) :
    SuffixCompleteCoupledAmbientLossFactorData owner index.prime
      index.suffix bound := by
  let scale := primeEulerAmbientLossScale index.prime
  let completeTarget := suffixActualBandCompleteCoupledAmbientTarget
    owner unitSoninScale index.prime index.suffix
  have hscale : 0 < scale := primeEulerAmbientLossScale_pos index.prime
  have hscaleComplex : (scale : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hscale.ne'
  have hscaled :=
    RouteScaledTwoStepCoboundaryFactorData.scaledAdjoint_factorization data
  have hlossFactor :
      primeEulerAmbientLossFactor index.prime ∘L data.factor =
        completeTarget† := by
    rw [primeEulerAmbientLossFactor]
    apply ContinuousLinearMap.ext
    intro x
    have hpoint := DFunLike.congr_fun hscaled x
    simp only [completeTarget, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply] at hpoint ⊢
    rw [← hpoint, smul_smul, mul_inv_cancel₀ hscaleComplex, one_smul]
  have hadjoint := congrArg ContinuousLinearMap.adjoint hlossFactor
  exact
    { bound_nonneg :=
        le_trans (norm_nonneg data.factor) data.factor_norm_le
      factor := data.factor†
      factor_norm_le := by
        calc
          ‖data.factor†‖ = ‖data.factor‖ :=
            ContinuousLinearMap.adjoint.norm_map data.factor
          _ ≤ bound := data.factor_norm_le
      factorization := by
        simpa only [ContinuousLinearMap.adjoint_comp,
          ContinuousLinearMap.adjoint_adjoint] using hadjoint }

/-- An ambient-loss quotient gives the scaled adjoint antiresonant factor
before the one-step coboundary is restored. -/
theorem
    SuffixCompleteCoupledAmbientLossFactorData.scaledAdjoint_factorization
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime} {bound : Real}
    (data : SuffixCompleteCoupledAmbientLossFactorData owner p S bound) :
    ((primeEulerAmbientLossScale p : Complex)⁻¹) •
        (suffixActualBandCompleteCoupledAmbientTarget
          owner unitSoninScale p S)† =
      (ContinuousLinearMap.id Complex finiteSCarrier +
          (cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap) ∘L
        data.factor† := by
  let scale := primeEulerAmbientLossScale p
  let completeTarget := suffixActualBandCompleteCoupledAmbientTarget
    owner unitSoninScale p S
  have hscale : 0 < scale := primeEulerAmbientLossScale_pos p
  have hscaleComplex : (scale : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hscale.ne'
  have hadjoint := congrArg ContinuousLinearMap.adjoint data.factorization
  have hlossFactor :
      primeEulerAmbientLossFactor p ∘L data.factor† = completeTarget† := by
    simpa only [completeTarget, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint] using hadjoint
  rw [primeEulerAmbientLossFactor] at hlossFactor
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := DFunLike.congr_fun hlossFactor x
  simp only [completeTarget, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply] at hpoint ⊢
  rw [← hpoint, smul_smul, inv_mul_cancel₀ hscaleComplex, one_smul]

/-- Conversely, an ambient-loss quotient is Proof 656's two-step factor with
the same adjoint factor and the same norm bound. -/
noncomputable def
    SuffixCompleteCoupledAmbientLossFactorData.toTwoStepFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {index : RouteFiniteHorizonIndex} {bound : Real}
    (data : SuffixCompleteCoupledAmbientLossFactorData owner index.prime
      index.suffix bound) :
    RouteScaledTwoStepCoboundaryFactorData owner index bound := by
  exact
    { factor := data.factor†
      factor_norm_le := by
        calc
          ‖data.factor†‖ = ‖data.factor‖ :=
            ContinuousLinearMap.adjoint.norm_map data.factor
          _ ≤ bound := data.factor_norm_le
      factorization := by
        rw [
          routeScaledPrimeLogAdjointCoboundaryTarget_eq_oneStep_comp_scaledAdjoint,
          SuffixCompleteCoupledAmbientLossFactorData.scaledAdjoint_factorization
            data,
          ← ContinuousLinearMap.comp_assoc,
          ← twoStepTranslationCoboundary_eq_oneStep_comp_add] }

/-! ## Route-uniform equivalence -/

/-- One complete ambient-loss quotient bound shared by every route-valid
prime and suffix. -/
def SuffixCompleteCoupledRouteUniformAmbientLossFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : Real) : Prop :=
  0 ≤ bound ∧ ∀ index : RouteFiniteHorizonIndex,
    Nonempty (SuffixCompleteCoupledAmbientLossFactorData owner index.prime
      index.suffix bound)

/-- The two-step and ambient-loss route factor gates are the same statement
with the same constant. -/
theorem routeUniformTwoStepFactor_iff_ambientLossFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : Real) :
    SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor
        owner bound ↔
      SuffixCompleteCoupledRouteUniformAmbientLossFactor owner bound := by
  constructor
  · rintro ⟨hbound, hfactor⟩
    refine ⟨hbound, ?_⟩
    intro index
    obtain ⟨data⟩ := hfactor index
    exact
      ⟨RouteScaledTwoStepCoboundaryFactorData.toAmbientLossFactorData data⟩
  · rintro ⟨hbound, hfactor⟩
    refine ⟨hbound, ?_⟩
    intro index
    obtain ⟨data⟩ := hfactor index
    exact
      ⟨SuffixCompleteCoupledAmbientLossFactorData.toTwoStepFactorData data⟩

/-- Existence of route-uniform two-step factors is exactly existence of one
route-uniform ambient antiresonant quotient bound. -/
theorem exists_routeUniformTwoStepFactor_iff_ambientLossFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (∃ bound : Real,
      SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor
        owner bound) ↔
      ∃ bound : Real,
        SuffixCompleteCoupledRouteUniformAmbientLossFactor owner bound := by
  constructor
  · rintro ⟨bound, data⟩
    exact ⟨bound,
      (routeUniformTwoStepFactor_iff_ambientLossFactor
        owner bound).mp data⟩
  · rintro ⟨bound, data⟩
    exact ⟨bound,
      (routeUniformTwoStepFactor_iff_ambientLossFactor
        owner bound).mpr data⟩

/-! ## The horizon-one gate is redundant -/

/-- A route-uniform two-step factor bound already supplies the scaled target
size gate with constant `2 * bound`. -/
theorem routeUniformScaledTargetBound_of_twoStepFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {bound : Real}
    (data :
      SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor
        owner bound) :
    SuffixCompleteCoupledRouteUniformScaledTargetBound owner (2 * bound) := by
  refine ⟨mul_nonneg (by norm_num) data.1, ?_⟩
  intro index
  obtain ⟨factorData⟩ := data.2 index
  let ambientData :=
    RouteScaledTwoStepCoboundaryFactorData.toAmbientLossFactorData factorData
  have hreadout :=
    uniformFiniteHorizonReadoutBound_of_ambientLossFactorData ambientData
  have hone := hreadout.2 1
  unfold suffixActualBandFiniteHorizonCoboundaryReadout at hone
  rw [finiteHorizonAntiresonantCoboundaryReadout_one] at hone
  simpa only [routeScaledCompleteCoupledAmbientTarget] using hone

/-- Proof 656's two-step factor gate alone bounds the paired envelope; its
separately supplied horizon-one premise is unnecessary. -/
theorem pairedAdjointCoboundaryEnvelopeBound_of_twoStepFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {bound : Real}
    (data :
      SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor
        owner bound) :
    SuffixCompleteCoupledRoutePairedAdjointCoboundaryEnvelopeBound owner :=
  pairedAdjointCoboundaryEnvelopeBound_of_size_and_twoStepFactor
    (routeUniformScaledTargetBound_of_twoStepFactor data) data

/-- The two-step factor gate alone reaches Proof 649's pointwise target. -/
theorem routePointwiseFiniteHorizonReadoutBound_of_twoStepFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {bound : Real}
    (data :
      SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor
        owner bound) :
    SuffixCompleteCoupledRoutePointwiseFiniteHorizonReadoutBound owner :=
  (routePairedAdjointCoboundaryEnvelope_iff_pointwiseFiniteHorizonReadout
    owner).mp (pairedAdjointCoboundaryEnvelopeBound_of_twoStepFactor data)

/-- The two-step factor gate alone reaches the raw Bone 1 consumer. -/
theorem exists_routeUniformRawAmbientDomination_of_twoStepFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {bound : Real}
    (data :
      SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor
        owner bound) :
    ∃ rawBound : Real,
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale rawBound :=
  exists_routeUniformRawAmbientDomination_of_pointwise
    (routePointwiseFiniteHorizonReadoutBound_of_twoStepFactor data)

/-- The same single gate reaches the renewed Bone 1 consumer. -/
theorem exists_routeUniformRenewedAmbientDomination_of_twoStepFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {bound : Real}
    (data :
      SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor
        owner bound) :
    ∃ renewedBound : Real,
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner unitSoninScale renewedBound :=
  exists_routeUniformRenewedAmbientDomination_of_pointwise
    (routePointwiseFiniteHorizonReadoutBound_of_twoStepFactor data)

end TwoStepFactorCollapse
end CCM25Concrete
end Source
end ConnesWeilRH
