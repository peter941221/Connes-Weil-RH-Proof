/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawCompletedGaugeOwner

/-!
# Common physical pair for the raw finite-S remainder

The old source-remainder pair puts the actual first jet and the raw Gram
endpoint in orthogonal `L2` coordinates.  That construction proves trace
legality, but its Hilbert--Schmidt energy cannot see their signed cancellation.

This module combines the forward first-jet coframe and the raw metric coframe
inside one right Hilbert--Schmidt leg.  Only the genuinely opposite first-jet
orientation remains in a second coordinate.  The resulting pair owns the
complete raw remainder and hence the lower-factor-gauged owner from Proof 490.

No norm estimate, Gate 3U bound, sign statement, or RH premise is introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRawRemainderCommonPair

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSInverseMetric
open CCM24FiniteSCoframeResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSTwoSidedRootRecombination
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSActualBandFirstJetTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24SourceProlateTrace

/-! ## Generic common-left recombination -/

/-- Precompose two copies of one Hilbert--Schmidt pair by the same left map
and add their right legs before any Hilbert--Schmidt energy is evaluated. -/
noncomputable def boundedPrecompAddRight
    {iota kappa mu H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {sourceBasis : HilbertBasis iota ℂ H}
    (targetBasis : HilbertBasis kappa ℂ G)
    (newSourceBasis : HilbertBasis mu ℂ K)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (commonLeft firstRight secondRight : K →L[ℂ] H) :
    BasisHilbertSchmidtPairData (G := G) newSourceBasis :=
  let first := data.boundedPrecomp targetBasis newSourceBasis commonLeft
    firstRight
  let second := data.boundedPrecomp targetBasis newSourceBasis commonLeft
    secondRight
  first.addOfLeftEq second (by rfl)

theorem boundedPrecompAddRight_left_eq
    {iota kappa mu H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {sourceBasis : HilbertBasis iota ℂ H}
    (targetBasis : HilbertBasis kappa ℂ G)
    (newSourceBasis : HilbertBasis mu ℂ K)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (commonLeft firstRight secondRight : K →L[ℂ] H) :
    (boundedPrecompAddRight targetBasis newSourceBasis data commonLeft
      firstRight secondRight).left = data.left ∘L commonLeft := by
  rfl

/-- The right leg contains the signed/coherent sum itself, not an orthogonal
pair of the two inputs. -/
theorem boundedPrecompAddRight_right_eq
    {iota kappa mu H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {sourceBasis : HilbertBasis iota ℂ H}
    (targetBasis : HilbertBasis kappa ℂ G)
    (newSourceBasis : HilbertBasis mu ℂ K)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (commonLeft firstRight secondRight : K →L[ℂ] H) :
    (boundedPrecompAddRight targetBasis newSourceBasis data commonLeft
      firstRight secondRight).right =
        data.right ∘L (firstRight + secondRight) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [boundedPrecompAddRight,
    BasisHilbertSchmidtPairData.addOfLeftEq,
    BasisHilbertSchmidtPairData.boundedPrecomp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, map_add]

theorem boundedPrecompAddRight_traceProduct_eq
    {iota kappa mu H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {sourceBasis : HilbertBasis iota ℂ H}
    (targetBasis : HilbertBasis kappa ℂ G)
    (newSourceBasis : HilbertBasis mu ℂ K)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (commonLeft firstRight secondRight : K →L[ℂ] H) :
    (boundedPrecompAddRight targetBasis newSourceBasis data commonLeft
      firstRight secondRight).traceProduct =
        commonLeft† ∘L data.traceProduct ∘L
          (firstRight + secondRight) := by
  rw [boundedPrecompAddRight,
    BasisHilbertSchmidtPairData.addOfLeftEq_traceProduct_eq,
    BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
    BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    map_add]

/-! ## The exact physical coframes -/

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-- The forward actual-band coframe `B A_S J`. -/
noncomputable def sourceActualBandForwardCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  sourceBandProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
    sourceInclusion lambda

theorem sourceActualBandForwardCoframe_adjoint_eq
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceActualBandForwardCoframe lambda family)† =
      (sourceInclusion lambda)† ∘L
        (normalizedFiniteEulerInverse family)† ∘L
          sourceBandProjection lambda := by
  rw [sourceActualBandForwardCoframe, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp]
  have hBand :=
    (sourceBandProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq
  rw [hBand]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The forward first jet and raw endpoint share this one right coframe. -/
noncomputable def sourceActualBandForwardEndpointCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  sourceActualBandForwardCoframe lambda family +
    finiteEulerMetricCoframe lambda family

/-! ## Algebraic alignment with the physical three-branch ledger -/

variable {A : Type*} [Ring A]

/-- Replacing the fixed commutator by its compressed three-branch ledger keeps
the two actual first-jet orientations in their correct order. -/
theorem pairedFixedResponse_eq_threeBranch
    (inner band transport transportAdjoint support ledger fixed : A)
    (hFixed : fixed = -(support * ledger * support))
    (hInnerSupport : inner * support = inner)
    (hSupportBand : support * band = band)
    (hBandSupport : band * support = band)
    (hSupportInner : support * inner = inner) :
    -(inner * fixed * band * transport * inner) +
        inner * transportAdjoint * band * fixed * inner =
      inner * ledger * band * transport * inner -
        inner * transportAdjoint * band * ledger * inner := by
  rw [hFixed]
  calc
    -(inner * (-(support * ledger * support)) * band * transport * inner) +
          inner * transportAdjoint * band *
            (-(support * ledger * support)) * inner =
        (inner * support) * ledger * (support * band) * transport * inner -
          inner * transportAdjoint * (band * support) * ledger *
            (support * inner) := by
              noncomm_ring
    _ = inner * ledger * band * transport * inner -
        inner * transportAdjoint * band * ledger * inner := by
      rw [hInnerSupport, hSupportBand, hBandSupport, hSupportInner]

theorem sourceActualBandFiniteEulerPairedResponse_eq_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandFiniteEulerPairedResponse owner lambda family =
      sourceSoninProjection lambda ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          sourceBandProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          sourceSoninProjection lambda -
        sourceSoninProjection lambda ∘L
          (normalizedFiniteEulerInverse family)† ∘L
          sourceBandProjection lambda ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          sourceSoninProjection lambda := by
  let band := sourceBandProjection lambda
  let inner := sourceSoninProjection lambda
  let detector := compressedDetector (radialSupportProjection lambda)
    (detectorOperator owner)
  let transport := normalizedFiniteEulerInverse family
  let transportAdjoint := (normalizedFiniteEulerInverse family)†
  let fixed := fixedPhysicalCommutator (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda) (sourceProlateRemainder lambda)
    (detectorOperator owner)
  have hdecomp :
      sourceActualBandFiniteEulerPairedResponse owner lambda family =
        -(inner ∘L fixed ∘L band ∘L transport ∘L inner) +
          inner ∘L transportAdjoint ∘L band ∘L fixed ∘L inner := by
    rw [sourceActualBandFiniteEulerPairedResponse]
    rw [← actualBandCommutatorPairedResponse_eq_detector band inner detector
      transport transportAdjoint
      (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
      (by simpa only [band, inner, ContinuousLinearMap.mul_def] using
        sourceBandProjection_comp_sourceSoninProjection_eq_zero lambda)
      (by simpa only [band, inner, ContinuousLinearMap.mul_def] using
        sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda)]
    unfold actualBandCommutatorPairedResponse
    rw [← fixedPhysicalCommutator_eq_sourceCompressedCommutator owner lambda]
    rfl
  rw [hdecomp]
  simpa only [band, inner, transport, transportAdjoint, fixed,
      ContinuousLinearMap.mul_def] using
    (pairedFixedResponse_eq_threeBranch
      (sourceSoninProjection lambda) (sourceBandProjection lambda)
      (normalizedFiniteEulerInverse family)
      ((normalizedFiniteEulerInverse family)†)
      (radialSupportProjection lambda)
      (cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner))
      (fixedPhysicalCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner))
      (by simpa only [ContinuousLinearMap.mul_def] using
        (fixedPhysicalCommutator_eq_neg_compressedThreeBranch
          (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner)
          (radialSupportProjection_isStarProjection lambda).isIdempotentElem
          (radialSupportProjection_comp_sourceProlateRemainder lambda)
          (sourceProlateRemainder_comp_radialSupportProjection lambda)))
      (by simpa only [ContinuousLinearMap.mul_def] using
        sourceSoninProjection_comp_radialSupportProjection lambda)
      (by simpa only [ContinuousLinearMap.mul_def] using
        radialSupportProjection_comp_sourceBandProjection_eq_self lambda)
      (by simpa only [ContinuousLinearMap.mul_def] using
        sourceBandProjection_comp_radialSupportProjection_eq_self lambda)
      (by simpa only [ContinuousLinearMap.mul_def] using
        radialSupportProjection_comp_sourceSoninProjection lambda))

/-- Source pullback of the actual first jet through the same physical ledger.
The adjoint normalized inverse remains in the reverse orientation. -/
theorem sourceActualBandFiniteEulerSoninResponse_eq_commonPhysicalFirstJet
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandFiniteEulerSoninResponse owner lambda family =
      (sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          sourceActualBandForwardCoframe lambda family -
        (sourceActualBandForwardCoframe lambda family)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          sourceInclusion lambda := by
  rw [sourceActualBandFiniteEulerSoninResponse,
    sourceActualBandFiniteEulerPairedResponse_eq_threeBranch,
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
  simp only [sourceActualBandForwardCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  rw [show sourceSoninProjection lambda (sourceInclusion lambda u) =
      sourceInclusion lambda u by
    simpa only [ContinuousLinearMap.comp_apply] using hright,
    hleft, hleft]

theorem sourceBandGramResponse_eq_neg_commonPhysicalEndpoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandGramResponse owner lambda family =
      -((sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        finiteEulerMetricCoframe lambda family) := by
  rw [sourceBandGramResponse_eq_neg_threeBranch]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The raw remainder written as one common forward/endpoint physical pairing
and the genuinely opposite first-jet orientation. -/
noncomputable def sourceActualBandRawRemainderCommonPhysicalResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  (sourceInclusion lambda)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      sourceActualBandForwardEndpointCoframe lambda family -
    (sourceActualBandForwardCoframe lambda family)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      sourceInclusion lambda

theorem sourceActualBandRawRemainderCommonPhysicalResponse_eq_remainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandRawRemainderCommonPhysicalResponse owner lambda family =
      sourceActualBandFiniteEulerRemainderResponse owner lambda family := by
  rw [sourceActualBandFiniteEulerRemainderResponse,
    sourceActualBandFiniteEulerSoninResponse_eq_commonPhysicalFirstJet,
    sourceBandGramResponse_eq_neg_commonPhysicalEndpoint]
  apply ContinuousLinearMap.ext
  intro u
  simp only [sourceActualBandRawRemainderCommonPhysicalResponse,
    sourceActualBandForwardEndpointCoframe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, map_add]
  abel

/-! ## One common Hilbert--Schmidt owner -/

/-- The forward first jet and raw endpoint are combined through their exact
common left leg `base.left ∘ J`. -/
noncomputable def sourceActualBandForwardEndpointPairData
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData
      (G := commonBoundaryCarrier a c) sourceBasis :=
  boundedPrecompAddRight boundaryBasis sourceBasis
    (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor)
    (sourceInclusion lambda)
    (sourceActualBandForwardCoframe lambda family)
    (finiteEulerMetricCoframe lambda family)

theorem sourceActualBandForwardEndpointPairData_right_apply
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
          (sourceActualBandForwardEndpointCoframe lambda family u) := by
  rw [sourceActualBandForwardEndpointPairData,
    boundedPrecompAddRight_right_eq]
  rfl

/-- The completed common pair has two coordinates.  The first contains the
forward/endpoint coframe sum; the second is the reverse first jet. -/
noncomputable def sourceActualBandRawRemainderCommonPairData
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData
      (G := WithLp 2
        (commonBoundaryCarrier a c × commonBoundaryCarrier a c)) sourceBasis :=
  BasisHilbertSchmidtPairData.l2Sum
    (sourceActualBandForwardEndpointPairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor)
    ((BasisHilbertSchmidtPairData.boundedPrecomp boundaryBasis sourceBasis
      (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis hfactor)
      (sourceActualBandForwardCoframe lambda family)
      (sourceInclusion lambda)).smulRight (-1))

theorem sourceActualBandForwardEndpointPairData_traceProduct_eq
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceActualBandForwardEndpointPairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).traceProduct =
        (sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          sourceActualBandForwardEndpointCoframe lambda family := by
  rw [sourceActualBandForwardEndpointPairData,
    boundedPrecompAddRight_traceProduct_eq,
    sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]
  rfl

theorem sourceActualBandRawRemainderCommonPairData_traceProduct_eq
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceActualBandRawRemainderCommonPairData owner lambda family a c hac
      hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).traceProduct =
        sourceActualBandRawRemainderCommonPhysicalResponse
          owner lambda family := by
  rw [sourceActualBandRawRemainderCommonPairData,
    BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    sourceActualBandForwardEndpointPairData_traceProduct_eq owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor,
    BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
    sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]
  apply ContinuousLinearMap.ext
  intro u
  simp only [sourceActualBandRawRemainderCommonPhysicalResponse,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    neg_smul, one_smul, ContinuousLinearMap.neg_apply,
    sub_eq_add_neg]

theorem sourceActualBandRawRemainderCommonPairData_traceProduct_eq_remainder
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceActualBandRawRemainderCommonPairData owner lambda family a c hac
      hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).traceProduct =
        sourceActualBandFiniteEulerRemainderResponse owner lambda family := by
  rw [sourceActualBandRawRemainderCommonPairData_traceProduct_eq,
    sourceActualBandRawRemainderCommonPhysicalResponse_eq_remainder]

theorem sourceActualBandRawRemainderCommonPairData_traceProduct_eq_gauged
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceActualBandRawRemainderCommonPairData owner lambda family a c hac
      hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).traceProduct =
        lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family := by
  rw [sourceActualBandRawRemainderCommonPairData_traceProduct_eq_remainder,
    ← lowerFactorGaugedActualBandCompletedRelativeResponse_eq_sourceRemainder]

theorem sourceActualBandRawRemainderCommonPairData_isTraceClassAlong
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong sourceBasis
      (sourceActualBandRawRemainderCommonPhysicalResponse
        owner lambda family) := by
  rw [← sourceActualBandRawRemainderCommonPairData_traceProduct_eq owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  exact (sourceActualBandRawRemainderCommonPairData owner lambda family a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor).traceProduct_isTraceClassAlong

end CCM24FiniteSRawRemainderCommonPair
end CCM25Concrete
end Source
end ConnesWeilRH
