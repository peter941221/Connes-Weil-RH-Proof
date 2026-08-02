/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalPrefixFullKernelPairing
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSourceFirstJetSupportBound

/-!
# Physical-leakage reduction for the finite-S Gate trace

The forward conjugate pair in the physical Gate response is exactly the
already controlled actual finite-Euler first jet.  The remaining summand is
the complete physical coframe leakage, equivalently the negative source band
Gram response.

This file works at the ordinary-trace level.  It does not turn the existing
first-jet trace bound into a bound for every ordered finite prefix.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalLeakageTraceReduction

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSActualBandFirstJetTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSSourceFirstJetSupportBound
open CCM24FiniteSGatePhysicalDetectorNormalForm
open CCM24FiniteSGatePhysicalSignedDiagonal
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawRemainderCommonPair
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The Gate's forward conjugate pair is the actual finite-Euler first jet
pulled back to the source Sonin carrier. -/
theorem sourceGatePhysicalForwardSymmetricResponse_eq_firstJet
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceGatePhysicalForwardSymmetricResponse owner lambda family =
      sourceActualBandFiniteEulerSoninResponse owner lambda family := by
  rw [sourceGatePhysicalForwardSymmetricResponse,
    sourceActualBandFiniteEulerSoninResponse,
    sourceActualBandFiniteEulerPairedResponse_eq_rawDetector,
    sourceActualBandForwardCoframe_adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  have hright := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator u)
    (sourceSoninProjection_comp_sourceInclusion_eq_self lambda)
  have hleft (x : finiteSCarrier) :
      ((sourceInclusion lambda)†) (sourceSoninProjection lambda x) =
        ((sourceInclusion lambda)†) x := by
    exact congrArg
      (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
        operator x)
      (sourceInclusionAdjoint_comp_sourceProjection lambda)
  simp only [actualBandDetectorPairedResponse,
    sourceActualBandForwardCoframe, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, map_add]
  rw [show sourceSoninProjection lambda (sourceInclusion lambda u) =
      sourceInclusion lambda u by
    simpa only [ContinuousLinearMap.comp_apply] using hright,
    hleft, hleft]

/-- The complete physical leakage crossing is the negative source band Gram
response.  No physical branch is separated in this identity. -/
theorem sourceGatePhysicalLeakageCrossingResponse_eq_neg_sourceBandGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceGatePhysicalLeakageCrossingResponse owner lambda family =
      -sourceBandGramResponse owner lambda family := by
  rw [sourceGatePhysicalLeakageCrossingResponse,
    sourceBandGramResponse_eq_neg_physical_leakage]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, neg_neg]

/-- The leakage trace is exactly the negative source band Gram trace. -/
theorem ordinaryTraceAlong_leakage_eq_neg_sourceBandGram
    {ρ : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong sourceBasis
        (sourceGatePhysicalLeakageCrossingResponse owner lambda family) =
      -ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family) := by
  rw [sourceGatePhysicalLeakageCrossingResponse_eq_neg_sourceBandGramResponse,
    CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_neg]

/-- The forward Gate pair inherits the existing first-jet trace legality. -/
theorem sourceGatePhysicalForwardSymmetricResponse_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ ρ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong sourceBasis
      (sourceGatePhysicalForwardSymmetricResponse owner lambda family) := by
  rw [sourceGatePhysicalForwardSymmetricResponse_eq_firstJet]
  exact sourceActualBandFiniteEulerSoninResponse_isTraceClassAlong owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor

/-- The complete physical leakage crossing is trace legal for every fixed
finite family. -/
theorem sourceGatePhysicalLeakageCrossingResponse_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ ρ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong sourceBasis
      (sourceGatePhysicalLeakageCrossingResponse owner lambda family) := by
  rw [sourceGatePhysicalLeakageCrossingResponse_eq_neg_sourceBandGramResponse]
  exact CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_neg
    sourceBasis _
    (sourceBandGramResponse_isTraceClassAlong owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor)

/-- Once the two summands are trace legal, the complete Gate trace is the
controlled first-jet trace plus one physical leakage trace. -/
theorem ordinaryTraceAlong_lowerFactorGaugedResponse_eq_firstJet_add_leakage
    {ρ : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfirst : IsTraceClassAlong sourceBasis
      (sourceActualBandFiniteEulerSoninResponse owner lambda family))
    (hleakage : IsTraceClassAlong sourceBasis
      (sourceGatePhysicalLeakageCrossingResponse owner lambda family)) :
    ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family) =
      ordinaryTraceAlong sourceBasis
          (sourceActualBandFiniteEulerSoninResponse owner lambda family) +
        ordinaryTraceAlong sourceBasis
          (sourceGatePhysicalLeakageCrossingResponse owner lambda family) := by
  rw [lowerFactorGaugedResponse_eq_detectorOffDiagonal,
    sourceGatePhysicalDetectorOffDiagonalResponse_eq_forward_add_leakage,
    sourceGatePhysicalForwardSymmetricResponse_eq_firstJet]
  exact ordinaryTraceAlong_add sourceBasis _ _ hfirst hleakage

/-- The known support bound controls the first-jet part of the Gate trace.
Only one complete physical leakage scalar remains to be bounded. -/
theorem lowerFactorGaugedResponse_trace_norm_le_supportEnergy_add_leakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ ρ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (leakageBound : ℝ)
    (hleakageBound :
      ‖ordinaryTraceAlong sourceBasis
        (sourceGatePhysicalLeakageCrossingResponse owner lambda family)‖ ≤
          leakageBound) :
    ‖ordinaryTraceAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)‖ ≤
      (12 + 4 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) +
        leakageBound := by
  have hfirstClass := sourceActualBandFiniteEulerSoninResponse_isTraceClassAlong
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  have hleakageClass :=
    sourceGatePhysicalLeakageCrossingResponse_isTraceClassAlong owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have htrace :=
    ordinaryTraceAlong_lowerFactorGaugedResponse_eq_firstJet_add_leakage
      owner lambda family sourceBasis hfirstClass hleakageClass
  have hfirstBound :=
    sourceActualBandFiniteEulerSoninTrace_norm_le_supportEnergy owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  rw [htrace]
  exact (norm_add_le _ _).trans (add_le_add hfirstBound hleakageBound)

/-- Uniform boundedness of the complete Gate trace over all finite families is
equivalent to uniform boundedness of the one physical leakage trace.  The
conversion cost is precisely the already proved family-independent first-jet
support bound. -/
theorem exists_uniform_lowerFactorGaugedTraceBound_iff_leakageTraceBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ ρ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤ bound) ↔
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (sourceGatePhysicalLeakageCrossingResponse
          owner lambda family)‖ ≤ bound) := by
  let firstBound :=
    (12 + 4 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
      (globalBasis i)‖ ^ 2)) *
      ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2)
  constructor
  · rintro ⟨gateBound, hgate⟩
    refine ⟨gateBound + firstBound, ?_⟩
    intro family
    have hfirstClass :=
      sourceActualBandFiniteEulerSoninResponse_isTraceClassAlong owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
    have hleakageClass :=
      sourceGatePhysicalLeakageCrossingResponse_isTraceClassAlong owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis hfactor
    have htrace :=
      ordinaryTraceAlong_lowerFactorGaugedResponse_eq_firstJet_add_leakage
        owner lambda family sourceBasis hfirstClass hleakageClass
    have hfirstBound :=
      sourceActualBandFiniteEulerSoninTrace_norm_le_supportEnergy owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
    calc
      ‖ordinaryTraceAlong sourceBasis
          (sourceGatePhysicalLeakageCrossingResponse
            owner lambda family)‖ =
          ‖ordinaryTraceAlong sourceBasis
              (lowerFactorGaugedActualBandCompletedRelativeResponse
                owner lambda family) -
            ordinaryTraceAlong sourceBasis
              (sourceActualBandFiniteEulerSoninResponse
                owner lambda family)‖ := by
        rw [htrace]
        congr 1
        abel
      _ ≤ ‖ordinaryTraceAlong sourceBasis
              (lowerFactorGaugedActualBandCompletedRelativeResponse
                owner lambda family)‖ +
            ‖ordinaryTraceAlong sourceBasis
              (sourceActualBandFiniteEulerSoninResponse
                owner lambda family)‖ := norm_sub_le _ _
      _ ≤ gateBound + firstBound := by
        exact add_le_add (hgate family)
          (by simpa only [firstBound] using hfirstBound)
  · rintro ⟨leakageBound, hleakage⟩
    refine ⟨firstBound + leakageBound, ?_⟩
    intro family
    simpa only [firstBound] using
      (lowerFactorGaugedResponse_trace_norm_le_supportEnergy_add_leakage
        owner lambda family a c hac hsupp negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis pairedBoundaryBasis
        sourceBasis hfactor leakageBound (hleakage family))

end CCM24FiniteSGatePhysicalLeakageTraceReduction
end CCM25Concrete
end Source
end ConnesWeilRH
