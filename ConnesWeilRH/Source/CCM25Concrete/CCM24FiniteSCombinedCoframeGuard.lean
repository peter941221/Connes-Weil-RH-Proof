/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawRemainderCommonPair

/-!
# Biorthogonal guard for the combined finite-S coframe

Proof 492 keeps the forward actual-band coframe and the raw metric coframe in
one physical Hilbert--Schmidt column.  This module identifies the exact
source-Sonin and off-Sonin parts of that combined coframe.

If `J` is the source inclusion, `R = J J^dagger`,
`V_S = B A_S J`, and `C_S` is the raw metric coframe, then

```text
D_S = V_S + C_S,
J^dagger D_S = I,
R D_S = J,
D_S = J + L_S,
L_S = (I-R)D_S = V_S + (I-R)C_S.
```

Thus every family-dependent component lies in the genuine off-Sonin column
`L_S`.  These identities do not imply that `D_S` or `L_S` is contractive.
The complete physical right leg must remain composed with `J + L_S` before
any Hilbert--Schmidt energy is estimated.

No norm estimate, Gate 3U bound, sign statement, or RH premise is introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCombinedCoframeGuard

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSInverseMetric
open CCM24FiniteSCoframeResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSRawRemainderCommonPair
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The forward coframe is purely off-Sonin -/

/-- The source Sonin projection annihilates the forward actual-band coframe.
This is the source-specific input that prevents the forward term from
changing the biorthogonal component. -/
theorem sourceSoninProjection_comp_sourceActualBandForwardCoframe_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L
        sourceActualBandForwardCoframe lambda family = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hzero := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator
        (normalizedFiniteEulerInverse family (sourceInclusion lambda u)))
    (sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda)
  simpa only [sourceActualBandForwardCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] using hzero

/-- The inclusion adjoint also annihilates the forward actual-band coframe. -/
theorem sourceInclusionAdjoint_comp_sourceActualBandForwardCoframe_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L
        sourceActualBandForwardCoframe lambda family = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have habsorb := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator (sourceActualBandForwardCoframe lambda family u))
    (sourceInclusionAdjoint_comp_sourceProjection lambda)
  have hzero := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator u)
    (sourceSoninProjection_comp_sourceActualBandForwardCoframe_eq_zero
      lambda family)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at habsorb hzero ⊢
  rw [← habsorb, hzero, map_zero]

/-! ## Biorthogonality of the combined coframe -/

/-- Adding the forward actual-band coframe preserves `J^dagger D_S = I`. -/
theorem sourceInclusionAdjoint_comp_sourceActualBandForwardEndpointCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L
        sourceActualBandForwardEndpointCoframe lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  apply ContinuousLinearMap.ext
  intro u
  have hforward := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => operator u)
    (sourceInclusionAdjoint_comp_sourceActualBandForwardCoframe_eq_zero
      lambda family)
  have hmetric := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => operator u)
    (sourceInclusionAdjoint_comp_metricCoframe lambda family)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.id_apply] at hforward hmetric
  simp only [sourceActualBandForwardEndpointCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, map_add,
    ContinuousLinearMap.id_apply]
  rw [hforward, hmetric, zero_add]

/-- The source Sonin compression of the combined coframe is exactly `J`. -/
theorem sourceSoninProjection_comp_sourceActualBandForwardEndpointCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L
        sourceActualBandForwardEndpointCoframe lambda family =
      sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  have hforward := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator u)
    (sourceSoninProjection_comp_sourceActualBandForwardCoframe_eq_zero
      lambda family)
  have hmetric := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator u)
    (sourceSoninProjection_comp_metricCoframe lambda family)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hforward hmetric
  simp only [sourceActualBandForwardEndpointCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, map_add]
  rw [hforward, hmetric, zero_add]

/-! ## The genuine off-Sonin leakage -/

/-- The complete off-Sonin part of the Proof 492 combined coframe. -/
noncomputable def sourceActualBandCombinedCoframeLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
    sourceActualBandForwardEndpointCoframe lambda family

theorem sourceActualBandCombinedCoframeLeakage_eq_combined_sub_inclusion
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandCombinedCoframeLeakage lambda family =
      sourceActualBandForwardEndpointCoframe lambda family -
        sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  have hcompression := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator u)
    (sourceSoninProjection_comp_sourceActualBandForwardEndpointCoframe
      lambda family)
  simp only [sourceActualBandCombinedCoframeLeakage,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply] at hcompression ⊢
  rw [hcompression]

/-- The combined coframe is the fixed inclusion plus its complete off-Sonin
leakage.  This is an affine decomposition, not a norm bound. -/
theorem sourceActualBandForwardEndpointCoframe_eq_inclusion_add_leakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandForwardEndpointCoframe lambda family =
      sourceInclusion lambda +
        sourceActualBandCombinedCoframeLeakage lambda family := by
  rw [sourceActualBandCombinedCoframeLeakage_eq_combined_sub_inclusion]
  abel

/-- The family-dependent leakage is the coherent sum of the forward
actual-band coframe and the raw metric-coframe leakage. -/
theorem sourceActualBandCombinedCoframeLeakage_eq_forward_add_metricLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandCombinedCoframeLeakage lambda family =
      sourceActualBandForwardCoframe lambda family +
        sourceSoninCoframeLeakage lambda family := by
  rw [sourceActualBandCombinedCoframeLeakage_eq_combined_sub_inclusion,
    sourceActualBandForwardEndpointCoframe,
    sourceSoninCoframeLeakage_eq_coframe_sub_inclusion]
  abel

/-- The inclusion adjoint annihilates the complete combined leakage. -/
theorem sourceInclusionAdjoint_comp_sourceActualBandCombinedCoframeLeakage_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L
        sourceActualBandCombinedCoframeLeakage lambda family = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hcombined := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => operator u)
    (sourceInclusionAdjoint_comp_sourceActualBandForwardEndpointCoframe
      lambda family)
  have hinclusion := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => operator u)
    (sourceInclusion_adjoint_comp_self lambda)
  rw [sourceActualBandCombinedCoframeLeakage_eq_combined_sub_inclusion]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    map_sub, ContinuousLinearMap.zero_apply] at hcombined hinclusion ⊢
  rw [hcombined, hinclusion, sub_self]

/-- The source Sonin projection annihilates the complete combined leakage. -/
theorem sourceSoninProjection_comp_sourceActualBandCombinedCoframeLeakage_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L
        sourceActualBandCombinedCoframeLeakage lambda family = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hcombined := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator u)
    (sourceSoninProjection_comp_sourceActualBandForwardEndpointCoframe
      lambda family)
  have hinclusion := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator u)
    (sourceSoninProjection_comp_sourceInclusion_eq_self lambda)
  rw [sourceActualBandCombinedCoframeLeakage_eq_combined_sub_inclusion]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    map_sub, ContinuousLinearMap.zero_apply] at hcombined hinclusion ⊢
  rw [hcombined, hinclusion, sub_self]

/-! ## Preserve the complete physical column -/

/-- Any bounded physical right leg sees the combined coframe as the single
column `M (J + L_S)`.  The theorem deliberately does not distribute `M` over
the sum, because that distribution is not a valid uniform energy estimate. -/
theorem postcomp_sourceActualBandForwardEndpointCoframe_eq_inclusion_add_leakage
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (rightLeg : finiteSCarrier →L[ℂ] G)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    rightLeg ∘L sourceActualBandForwardEndpointCoframe lambda family =
      rightLeg ∘L
        (sourceInclusion lambda +
          sourceActualBandCombinedCoframeLeakage lambda family) := by
  rw [sourceActualBandForwardEndpointCoframe_eq_inclusion_add_leakage]

/-- The actual first coordinate of Proof 492 has the guarded form
`M (J + L_S)` before Hilbert--Schmidt energy is taken. -/
theorem sourceActualBandForwardEndpointPairData_right_apply_eq_guardedCoframe
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (u : sourceSoninCarrier lambda) :
    (sourceActualBandForwardEndpointPairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).right u =
        (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
          ((sourceInclusion lambda +
            sourceActualBandCombinedCoframeLeakage lambda family) u) := by
  rw [sourceActualBandForwardEndpointPairData_right_apply,
    sourceActualBandForwardEndpointCoframe_eq_inclusion_add_leakage]

end CCM24FiniteSCombinedCoframeGuard
end CCM25Concrete
end Source
end ConnesWeilRH
