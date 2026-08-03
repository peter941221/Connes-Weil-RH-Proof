/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalHardyProlateCompletedHermitianTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalLowerFactorPersistence

/-!
# Lower-factor-square form of the completed Hardy--prolate trace

Proof 784 identifies the canonical real Gate with the norm of one completed
Hardy--prolate physical trace.  Proof 787 identifies the normalized source
trace with the raw source trace multiplied by the square of the finite Euler
lower factor.

This module combines those two statements without adding an estimate: the
normalized real source trace is exactly the lower-factor-square scaling of
the same completed Hardy--prolate Hermitian trace.  Thus the remaining Gate 3U
producer is a lower-factor-square bound for that single completed signed
physical trace, not a branchwise bound and not a merely uniform normalized
estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalLowerFactorCompletedTrace

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSCanonicalRealGate
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalCanonicalCompletedKernelTraceLegality
open CCM24FiniteSGatePhysicalHardyProlateCompletedBoundaryKernel
open CCM24FiniteSGatePhysicalHardyProlateCompletedHermitianTrace
open CCM24FiniteSGatePhysicalLowerFactorPersistence
open CCM24FiniteSGatePhysicalTargetHermitianPrefix
open CCM24FiniteSGramResponse
open CCM24FiniteSNormalizedPhysicalResponse
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The normalized real source trace is the norm of the same completed
Hardy--prolate Hermitian trace after multiplying by the lower-factor square.
This is an identity of readouts only; it supplies no uniform estimate. -/
theorem norm_lowerFactorSq_completePhysicalHermitianTrace_eq_abs_normalizedSourceBandRealTrace
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu : Type*}
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
    ‖((finiteEulerLowerFactor family.visiblePrimes) ^ 2 : ℂ) *
        ∑' i, ((finiteEulerCausalHardyProlateCompletePhysicalBoundaryPairing
          owner lambda family a c hac hsupp reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
          (sourceBasis i) (sourceBasis i)).re : ℂ)‖ =
      |(ordinaryTraceAlong sourceBasis
        (normalizedSourceBandGramResponse owner lambda family)).re| := by
  have hcomplete :=
    ordinaryTraceAlong_targetHermitianResponse_eq_completePhysicalBoundaryPairing_re
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis sourceBasis hfactor
  have htargetClass :=
    finiteEulerTargetCommutatorResponse_isTraceClassAlong_completedKernel
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hhermitian :=
    ordinaryTraceAlong_targetHermitianResponse_eq_target_re owner lambda family
      sourceBasis htargetClass
  have hnormalized :=
    normalizedSourceBandGramRealTrace_eq_lowerFactorSq_mul_raw owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  rw [← hcomplete, hhermitian,
    ordinaryTraceAlong_targetCommutator_re_eq_neg_sourceBand_re owner lambda
      family sourceBasis,
    hnormalized]
  rw [Complex.ofReal_neg]
  let lower := finiteEulerLowerFactor family.visiblePrimes
  let raw :=
    (ordinaryTraceAlong sourceBasis
      (CCM24FiniteSBandTrace.sourceBandGramResponse owner lambda family)).re
  change ‖(lower : ℂ) ^ 2 * -(raw : ℂ)‖ = |lower ^ 2 * raw|
  have hscalar : (lower : ℂ) ^ 2 * -(raw : ℂ) =
      (-(lower ^ 2 * raw) : ℂ) := by
    ring
  rw [hscalar, norm_neg]
  rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow]

/-- The canonical real Gate can be tested by the lower-factor-square scaling
of the single completed Hardy--prolate physical trace.  Equivalently, a
successful producer must prove this scaled trace is bounded by
lowerFactor^2 * bound. -/
theorem canonicalRealGate3UAt_iff_lowerFactorSq_completePhysicalHermitianTraceBound
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu : Type*}
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
    (bound : ℝ) :
    canonicalRealGate3UAt owner lambda sourceBasis bound ↔
      ‖((finiteEulerLowerFactor (canonicalFamily owner).visiblePrimes) ^ 2 : ℂ) *
          ∑' i, ((finiteEulerCausalHardyProlateCompletePhysicalBoundaryPairing
            owner lambda (canonicalFamily owner) a c hac hsupp
            reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
            globalBasis hfactor (sourceBasis i) (sourceBasis i)).re : ℂ)‖ ≤
        (finiteEulerLowerFactor (canonicalFamily owner).visiblePrimes) ^ 2 *
          bound := by
  have htrace :=
    finiteEulerTargetCommutatorResponse_isTraceClassAlong_completedKernel
      owner lambda (canonicalFamily owner) a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor
  rw [canonicalRealGate3UAt_iff_completePhysicalHermitianBoundaryTraceBound
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis sourceBasis hfactor bound htrace]
  have hlowerSq :
      0 < (finiteEulerLowerFactor (canonicalFamily owner).visiblePrimes) ^ 2 :=
    sq_pos_of_pos
      (finiteEulerLowerFactor_pos (canonicalFamily owner).visiblePrimes)
  have hlower :
      0 < finiteEulerLowerFactor (canonicalFamily owner).visiblePrimes :=
    finiteEulerLowerFactor_pos (canonicalFamily owner).visiblePrimes
  have hscalarNorm :
      ‖(finiteEulerLowerFactor
          (canonicalFamily owner).visiblePrimes : ℂ) ^ 2‖ =
        (finiteEulerLowerFactor (canonicalFamily owner).visiblePrimes) ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlower]
  rw [norm_mul, hscalarNorm]
  exact (mul_le_mul_iff_right₀ hlowerSq).symm

/-- A lower-factor-square bound for the completed Hardy--prolate trace closes
the canonical real Gate directly. -/
theorem canonicalRealGate3UAt_of_lowerFactorSq_completePhysicalHermitianTraceBound
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu : Type*}
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
    (bound : ℝ)
    (hbound :
      ‖((finiteEulerLowerFactor (canonicalFamily owner).visiblePrimes) ^ 2 : ℂ) *
          ∑' i, ((finiteEulerCausalHardyProlateCompletePhysicalBoundaryPairing
            owner lambda (canonicalFamily owner) a c hac hsupp
            reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
            globalBasis hfactor (sourceBasis i) (sourceBasis i)).re : ℂ)‖ ≤
        (finiteEulerLowerFactor (canonicalFamily owner).visiblePrimes) ^ 2 *
          bound) :
    canonicalRealGate3UAt owner lambda sourceBasis bound :=
  (canonicalRealGate3UAt_iff_lowerFactorSq_completePhysicalHermitianTraceBound
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor bound).mpr hbound

end CCM24FiniteSGatePhysicalLowerFactorCompletedTrace
end CCM25Concrete
end Source
end ConnesWeilRH
