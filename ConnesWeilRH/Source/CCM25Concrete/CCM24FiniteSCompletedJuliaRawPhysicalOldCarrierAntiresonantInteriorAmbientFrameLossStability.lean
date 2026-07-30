/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorTwoStepFactorCollapse

/-!
# Ambient frame-loss stability for the antiresonant interior

The raw Bone 1 estimate controls the signed interior only on the range of the
actual new suffix frame.  Proof 648's ambient quotient is stronger: after the
canonical ambient target applies the frame adjoint, the antiresonant loss must
still see the resulting frame projection.  The missing quantitative input is

```text
‖A_p F_S F_S† u‖ ≤ K ‖A_p u‖,
```

where `A_p = (primeEulerAmbientLossFactor p)†` and `F_S` is the actual
isometric suffix frame.

This module proves that a route-uniform raw Bone 1 constant `B` together with
this frame-loss stability constant `K` produces the full ambient quotient with
constant `B * K`.  Proof 669 then turns it into the two-step factor gate.

The final section gives an injective two-coordinate Hilbert-space model in
which the frame is isometric and the restricted estimate is exact with
constant one, while both ambient domination and frame-loss stability require
constants of order `epsilon⁻¹`.  Thus the new stability input is not a formal
consequence of injectivity or of the isometric-frame identities.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AmbientFrameLossStability

open Function
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSDouglasFactor
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCausalMarkov
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedCorrelationCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelColumnEquivalence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorTwoStepCoboundaryFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorUniformAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment
open TwoStepFactorCollapse

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The exact route bridge -/

/-- Uniform stability of the actual ambient antiresonant loss under the
orthogonal projection `F_S F_S†` onto the new suffix-frame range. -/
def SuffixCompleteCoupledRouteUniformAmbientFrameLossStability
    (bound : Real) : Prop :=
  0 ≤ bound ∧
    ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixRouteValidStep p S → ∀ u : finiteSCarrier,
        ‖((primeEulerAmbientLossFactor p)†)
            (newSuffixFrame unitSoninScale S
              (((newSuffixFrame unitSoninScale S)†) u))‖ ≤
          bound * ‖((primeEulerAmbientLossFactor p)†) u‖

/-- The squared raw Bone 1 predicate gives its unsquared same-vector norm
bound because both the constant and all norms are nonnegative. -/
theorem norm_signedInterior_le_rawColumn_of_routeUniformRawAmbientDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {bound : Real}
    (hraw :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale bound)
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (hvalid : SuffixRouteValidStep p S)
    (x : sourceSoninCarrier unitSoninScale) :
    ‖signedCompressedInteriorOwner owner unitSoninScale p S x‖ ≤
      bound * ‖newFrameAntiresonantColumn unitSoninScale p S x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hraw.1 (norm_nonneg _))).mp
  simpa only [mul_pow] using hraw.2 p S hvalid x

/-- Restricted Bone 1 plus frame-loss stability controls the canonical full
ambient target by the actual ambient loss with product constant `B * K`. -/
theorem norm_completeCoupledAmbientTarget_le_of_rawAmbientDomination_and_frameLossStability
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {rawBound stabilityBound : Real}
    (hraw :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale rawBound)
    (hstability :
      SuffixCompleteCoupledRouteUniformAmbientFrameLossStability
        stabilityBound)
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (hvalid : SuffixRouteValidStep p S)
    (u : finiteSCarrier) :
    ‖suffixActualBandCompleteCoupledAmbientTarget
        owner unitSoninScale p S u‖ ≤
      (rawBound * stabilityBound) *
        ‖((primeEulerAmbientLossFactor p)†) u‖ := by
  let frame := newSuffixFrame unitSoninScale S
  let loss := (primeEulerAmbientLossFactor p)†
  have hrestricted :=
    norm_signedInterior_le_rawColumn_of_routeUniformRawAmbientDomination
      hraw hvalid ((frame†) u)
  have hstable := hstability.2 p S hvalid u
  calc
    ‖suffixActualBandCompleteCoupledAmbientTarget
        owner unitSoninScale p S u‖ =
        ‖signedCompressedInteriorOwner owner unitSoninScale p S
          ((frame†) u)‖ := by
      rw [suffixActualBandCompleteCoupledAmbientTarget_eq_interior_comp_frameAdjoint]
      rfl
    _ ≤ rawBound *
        ‖newFrameAntiresonantColumn unitSoninScale p S ((frame†) u)‖ :=
      hrestricted
    _ = rawBound * ‖loss (frame ((frame†) u))‖ := by
      rfl
    _ ≤ rawBound *
        (stabilityBound * ‖loss u‖) :=
      mul_le_mul_of_nonneg_left hstable hraw.1
    _ = (rawBound * stabilityBound) * ‖loss u‖ := by ring

/-- Douglas upgrades the product norm bound to the full ambient factor for
one route-valid adjacent step. -/
noncomputable def completeCoupledAmbientLossFactorDataOfRawAmbientDominationAndFrameLossStability
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {rawBound stabilityBound : Real}
    (hraw :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale rawBound)
    (hstability :
      SuffixCompleteCoupledRouteUniformAmbientFrameLossStability
        stabilityBound)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hvalid : SuffixRouteValidStep p S) :
    SuffixCompleteCoupledAmbientLossFactorData owner p S
      (rawBound * stabilityBound) := by
  let witness := exists_factor_of_norm_le
    (suffixActualBandCompleteCoupledAmbientTarget
      owner unitSoninScale p S)
    ((primeEulerAmbientLossFactor p)†)
    (rawBound * stabilityBound)
    (mul_nonneg hraw.1 hstability.1)
    (norm_completeCoupledAmbientTarget_le_of_rawAmbientDomination_and_frameLossStability
      hraw hstability hvalid)
  let factor := Classical.choose witness
  have factorSpec := Classical.choose_spec witness
  exact
    { bound_nonneg := mul_nonneg hraw.1 hstability.1
      factor := factor
      factor_norm_le := factorSpec.1
      factorization := factorSpec.2 }

/-- The two uniform inputs produce Proof 648's full ambient-loss factor gate
with the product constant. -/
noncomputable def routeUniformAmbientLossFactorOfRawAmbientDominationAndFrameLossStability
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {rawBound stabilityBound : Real}
    (hraw :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale rawBound)
    (hstability :
      SuffixCompleteCoupledRouteUniformAmbientFrameLossStability
        stabilityBound) :
    SuffixCompleteCoupledRouteUniformAmbientLossFactor owner
      (rawBound * stabilityBound) := by
  refine ⟨mul_nonneg hraw.1 hstability.1, ?_⟩
  intro index
  exact
    ⟨completeCoupledAmbientLossFactorDataOfRawAmbientDominationAndFrameLossStability
      hraw hstability index.prime index.suffix index.valid⟩

/-- By Proof 669, the same product constant also supplies the route-uniform
two-step coboundary factor. -/
theorem routeUniformTwoStepFactorOfRawAmbientDominationAndFrameLossStability
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {rawBound stabilityBound : Real}
    (hraw :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale rawBound)
    (hstability :
      SuffixCompleteCoupledRouteUniformAmbientFrameLossStability
        stabilityBound) :
    SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor owner
      (rawBound * stabilityBound) :=
  (routeUniformTwoStepFactor_iff_ambientLossFactor
    owner (rawBound * stabilityBound)).mpr
      (routeUniformAmbientLossFactorOfRawAmbientDominationAndFrameLossStability
        hraw hstability)

/-- The bridge reaches Proof 656's paired finite-horizon envelope without a
separate horizon-one size premise. -/
theorem pairedAdjointCoboundaryEnvelopeBoundOfRawAmbientDominationAndFrameLossStability
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {rawBound stabilityBound : Real}
    (hraw :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale rawBound)
    (hstability :
      SuffixCompleteCoupledRouteUniformAmbientFrameLossStability
        stabilityBound) :
    SuffixCompleteCoupledRoutePairedAdjointCoboundaryEnvelopeBound owner :=
  pairedAdjointCoboundaryEnvelopeBound_of_twoStepFactor
    (routeUniformTwoStepFactorOfRawAmbientDominationAndFrameLossStability
      hraw hstability)

/-! ## Injective two-coordinate guard -/

/-- The Hilbert `L²` product used by the countermodel. -/
abbrev TwoCoordinateCarrier := WithLp 2 (Complex × Complex)

/-- The first-coordinate isometric frame `x ↦ (x, 0)`. -/
noncomputable def twoCoordinateFrame :
    Complex →L[Complex] TwoCoordinateCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 Complex Complex Complex).symm.toContinuousLinearMap ∘L
    ((ContinuousLinearMap.id Complex Complex).prod
      (0 : Complex →L[Complex] Complex))

/-- The first-coordinate readback. -/
noncomputable def twoCoordinateCoframe :
    TwoCoordinateCarrier →L[Complex] Complex :=
  WithLp.fstL 2 Complex Complex Complex

/-- The injective loss
`A_epsilon(x,z) = (x + z, epsilon z)`. -/
noncomputable def twoCoordinateLoss (epsilon : Real) :
    TwoCoordinateCarrier →L[Complex] TwoCoordinateCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 Complex Complex Complex).symm.toContinuousLinearMap ∘L
    ((WithLp.fstL 2 Complex Complex Complex +
        WithLp.sndL 2 Complex Complex Complex).prod
      ((epsilon : Complex) • WithLp.sndL 2 Complex Complex Complex))

/-- In this model the canonical ambient target is the frame coadjoint. -/
noncomputable def twoCoordinateAmbientTarget :
    TwoCoordinateCarrier →L[Complex] Complex :=
  twoCoordinateCoframe

@[simp]
theorem twoCoordinateFrame_apply (x : Complex) :
    twoCoordinateFrame x = WithLp.toLp 2 (x, 0) := by
  simp [twoCoordinateFrame]

@[simp]
theorem twoCoordinateCoframe_apply (u : TwoCoordinateCarrier) :
    twoCoordinateCoframe u = u.fst := by
  rfl

@[simp]
theorem twoCoordinateLoss_apply (epsilon : Real)
    (u : TwoCoordinateCarrier) :
    twoCoordinateLoss epsilon u =
      WithLp.toLp 2
        (u.fst + u.snd, (epsilon : Complex) * u.snd) := by
  simp [twoCoordinateLoss]

/-- The named coframe is exactly the Hilbert adjoint of the isometric frame. -/
theorem twoCoordinateFrame_adjoint :
    twoCoordinateFrame† = twoCoordinateCoframe := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    twoCoordinateCoframe twoCoordinateFrame).2
  intro u x
  simp [twoCoordinateCoframe, twoCoordinateFrame,
    WithLp.prod_inner_apply]

/-- The countermodel frame has the same adjoint-left-inverse identity as the
actual suffix frame. -/
theorem twoCoordinateFrame_adjoint_comp_self :
    twoCoordinateFrame† ∘L twoCoordinateFrame =
      ContinuousLinearMap.id Complex Complex := by
  rw [twoCoordinateFrame_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  simp

/-- Every nonzero `epsilon` gives an injective ambient loss. -/
theorem twoCoordinateLoss_injective
    {epsilon : Real} (hepsilon : epsilon ≠ 0) :
    Injective (twoCoordinateLoss epsilon) := by
  intro u v huv
  have hcoords :
      (u.fst + u.snd, (epsilon : Complex) * u.snd) =
        (v.fst + v.snd, (epsilon : Complex) * v.snd) := by
    simpa only [twoCoordinateLoss_apply] using congrArg
      (WithLp.prodContinuousLinearEquiv 2 Complex Complex Complex) huv
  have hepsilonComplex : (epsilon : Complex) ≠ 0 := by
    exact_mod_cast hepsilon
  have hsnd : u.snd = v.snd := by
    apply mul_left_cancel₀ hepsilonComplex
    exact congrArg Prod.snd hcoords
  have hfst : u.fst = v.fst := by
    have hfirst := congrArg Prod.fst hcoords
    simpa only [hsnd, add_left_inj] using hfirst
  apply (WithLp.prodContinuousLinearEquiv 2 Complex Complex Complex).injective
  ext
  · exact hfst
  · exact hsnd

/-- The restricted Bone 1 comparison is perfect: both sides are exactly the
norm of the source scalar. -/
theorem twoCoordinate_restricted_norm_eq
    (epsilon : Real) (x : Complex) :
    ‖twoCoordinateAmbientTarget (twoCoordinateFrame x)‖ =
      ‖twoCoordinateLoss epsilon (twoCoordinateFrame x)‖ := by
  rw [twoCoordinateFrame_apply, twoCoordinateLoss_apply]
  simp [twoCoordinateAmbientTarget, WithLp.norm_toLp_fst]

/-- The vector `(1, -1)` cancels the first loss coordinate. -/
noncomputable def twoCoordinateCancellationVector : TwoCoordinateCarrier :=
  WithLp.toLp 2 ((1 : Complex), -(1 : Complex))

@[simp]
theorem twoCoordinateAmbientTarget_cancellationVector :
    twoCoordinateAmbientTarget twoCoordinateCancellationVector = 1 := by
  rfl

theorem norm_twoCoordinateLoss_cancellationVector
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    ‖twoCoordinateLoss epsilon twoCoordinateCancellationVector‖ = epsilon := by
  rw [twoCoordinateLoss_apply]
  simp only [twoCoordinateCancellationVector, WithLp.toLp_fst,
    WithLp.toLp_snd, add_neg_cancel, mul_neg, mul_one]
  change ‖WithLp.toLp 2 ((0 : Complex), -(epsilon : Complex))‖ = epsilon
  rw [WithLp.norm_toLp_snd, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hepsilon]

/-- Projecting the cancellation vector back to the frame removes the
cancellation, so its loss norm is exactly one. -/
theorem norm_twoCoordinateLoss_frame_frameAdjoint_cancellationVector
    (epsilon : Real) :
    ‖twoCoordinateLoss epsilon
        (twoCoordinateFrame
          ((twoCoordinateFrame†) twoCoordinateCancellationVector))‖ = 1 := by
  rw [twoCoordinateFrame_adjoint]
  simp [twoCoordinateCancellationVector, WithLp.norm_toLp_fst]

/-- At a fixed positive `epsilon`, any frame-loss stability constant is at
least the reciprocal scale in the precise inequality `1 ≤ K * epsilon`. -/
theorem one_le_mul_epsilon_of_twoCoordinateFrameLossStability
    {epsilon bound : Real} (hepsilon : 0 < epsilon)
    (hstability : ∀ u : TwoCoordinateCarrier,
      ‖twoCoordinateLoss epsilon
          (twoCoordinateFrame ((twoCoordinateFrame†) u))‖ ≤
        bound * ‖twoCoordinateLoss epsilon u‖) :
    1 ≤ bound * epsilon := by
  have h := hstability twoCoordinateCancellationVector
  rw [norm_twoCoordinateLoss_frame_frameAdjoint_cancellationVector,
    norm_twoCoordinateLoss_cancellationVector hepsilon.le] at h
  exact h

/-- Injectivity, an isometric frame, and exact restricted control do not give
a frame-loss stability constant uniform in the injective parameter. -/
theorem not_exists_uniform_twoCoordinateFrameLossStability :
    ¬ ∃ bound : Real, 0 ≤ bound ∧
      ∀ epsilon : Real, 0 < epsilon → ∀ u : TwoCoordinateCarrier,
        ‖twoCoordinateLoss epsilon
            (twoCoordinateFrame ((twoCoordinateFrame†) u))‖ ≤
          bound * ‖twoCoordinateLoss epsilon u‖ := by
  rintro ⟨bound, hbound, hstability⟩
  let epsilon : Real := (bound + 1)⁻¹
  have hdenominator : 0 < bound + 1 := by linarith
  have hepsilon : 0 < epsilon := inv_pos.mpr hdenominator
  have hlower :=
    one_le_mul_epsilon_of_twoCoordinateFrameLossStability hepsilon
      (hstability epsilon hepsilon)
  have hupper : bound * epsilon < 1 := by
    change bound * (bound + 1)⁻¹ < 1
    rw [← div_eq_mul_inv]
    exact (div_lt_one hdenominator).2 (by linarith)
  exact (not_lt_of_ge hlower) hupper

/-- The same cancellation vector shows directly that no full ambient Douglas
domination constant can be uniform in `epsilon`. -/
theorem not_exists_uniform_twoCoordinateAmbientDomination :
    ¬ ∃ bound : Real, 0 ≤ bound ∧
      ∀ epsilon : Real, 0 < epsilon → ∀ u : TwoCoordinateCarrier,
        ‖twoCoordinateAmbientTarget u‖ ≤
          bound * ‖twoCoordinateLoss epsilon u‖ := by
  rintro ⟨bound, hbound, hdomination⟩
  let epsilon : Real := (bound + 1)⁻¹
  have hdenominator : 0 < bound + 1 := by linarith
  have hepsilon : 0 < epsilon := inv_pos.mpr hdenominator
  have hlower := hdomination epsilon hepsilon twoCoordinateCancellationVector
  rw [twoCoordinateAmbientTarget_cancellationVector, norm_one,
    norm_twoCoordinateLoss_cancellationVector hepsilon.le] at hlower
  have hupper : bound * epsilon < 1 := by
    change bound * (bound + 1)⁻¹ < 1
    rw [← div_eq_mul_inv]
    exact (div_lt_one hdenominator).2 (by linarith)
  exact (not_lt_of_ge hlower) hupper

end AmbientFrameLossStability
end CCM25Concrete
end Source
end ConnesWeilRH
