/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalNormalizedAnomalyBoundaryReadout

/-!
# Real trace reduction of the normalized physical Gate

Proofs 749 and 750 retain the genuine pure-imaginary Gram-order anomaly.
This module removes that anomaly only after applying the real scalar readout.
It does not set the complex anomaly to zero.

For the complete target trace and the support-first full-kernel scalar, Lean
proves

`Tr(Symmetric_S) = (Re Tr(Target_S) : C) = (Re FullKernelTrace_S : C)`.

The outer, reflected second-support, and prolate branches remain combined in
`FullKernelTrace_S` before the real part is taken.  This gives a precise
real-trace interface.  It does not prove that this weaker interface suffices
for the existing complex-norm Gate 3U consumer.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalNormalizedRealTraceReduction

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalLeakageTraceReduction
open CCM24FiniteSGatePhysicalNormalizedAnomalyBoundaryReadout
open CCM24FiniteSGatePhysicalNormalizedAnomalyTrace
open CCM24FiniteSGatePhysicalNormalizedGradedCoboundary
open CCM24FiniteSGatePhysicalObliqueShearKernelReduction
open CCM24FiniteSGatePhysicalTargetCommutatorReduction
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private theorem half_mul_sub_star_re_eq_zero (z : ℂ) :
    ((1 / 2 : ℂ) * (z - star z)).re = 0 := by
  rw [Complex.star_def]
  norm_num [Complex.mul_re]

private theorem neg_half_mul_add_star_eq_star_neg_re (z : ℂ) :
    -(1 / 2 : ℂ) * (z + star z) = ((star (-z)).re : ℂ) := by
  rw [Complex.star_def]
  apply Complex.ext
  · norm_num [Complex.mul_re]
    ring
  · norm_num [Complex.mul_im]

section FixedFamily

variable (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
variable (lambda : CCM24SoninScale)
variable (family : FinitePrimePowerFamily)
variable (a c : ℝ) (hac : a ≤ c)
variable (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
variable {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
variable (negativeBasis : HilbertBasis iota ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
variable (positiveBasis : HilbertBasis kappa ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
variable (outputBasis : HilbertBasis tau ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
variable (reflectedNegativeBasis : HilbertBasis iotaR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
variable (reflectedPositiveBasis : HilbertBasis kappaR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
variable (reflectedOutputBasis : HilbertBasis tauR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
variable (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
variable (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
variable (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
variable (hfactor : Summable fun i =>
  ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)

include a c hac hsupp negativeBasis positiveBasis outputBasis
  reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
  globalBasis boundaryBasis sourceBasis hfactor

/-- The normalized Gram-similarity anomaly has zero real trace.  Its
imaginary trace is retained. -/
theorem ordinaryTraceAlong_normalizedGramSimilarityAnomaly_re_eq_zero :
    (ordinaryTraceAlong sourceBasis
      (finiteEulerNormalizedGramSimilarityAnomaly
        owner lambda family)).re = 0 := by
  rw [ordinaryTraceAlong_normalizedGramSimilarityAnomaly_eq owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  exact half_mul_sub_star_re_eq_zero _

/-- The trace of the normalized symmetric response is exactly the real part
of the complete target trace, embedded back into `C`. -/
theorem ordinaryTraceAlong_normalizedSymmetricBoundaryResponse_eq_target_re :
    ordinaryTraceAlong sourceBasis
        (finiteEulerNormalizedSymmetricBoundaryResponse
          owner lambda family) =
      ((ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family)).re : ℂ) := by
  rw [ordinaryTraceAlong_normalizedSymmetricBoundaryResponse_eq owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  rw [ordinaryTraceAlong_targetCommutator_eq_star_leakage,
    ordinaryTraceAlong_leakage_eq_neg_sourceBandGram]
  exact neg_half_mul_add_star_eq_star_neg_re _

/-- The symmetric trace is real without asserting that the combined target
trace is real. -/
theorem ordinaryTraceAlong_normalizedSymmetricBoundaryResponse_im_eq_zero :
    (ordinaryTraceAlong sourceBasis
      (finiteEulerNormalizedSymmetricBoundaryResponse
        owner lambda family)).im = 0 := by
  rw [ordinaryTraceAlong_normalizedSymmetricBoundaryResponse_eq_target_re
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  exact Complex.ofReal_im _

/-- The same real trace is the real part of the one complete physical
full-kernel scalar.  Compact-root support acts before this real readout. -/
theorem ordinaryTraceAlong_normalizedSymmetricBoundaryResponse_eq_fullKernel_re :
    ordinaryTraceAlong sourceBasis
        (finiteEulerNormalizedSymmetricBoundaryResponse
          owner lambda family) =
      ((finiteEulerObliqueShearFullKernelTrace owner lambda family a c
        sourceBasis).re : ℂ) := by
  rw [ordinaryTraceAlong_normalizedSymmetricBoundaryResponse_eq_target_re
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  rw [ordinaryTraceAlong_targetCommutator_eq_obliqueShearFullKernelTrace
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis sourceBasis hfactor]

/-- Norm of the symmetric trace is precisely the absolute real full-kernel
scalar; no triangle inequality over physical branches occurs. -/
theorem norm_ordinaryTraceAlong_normalizedSymmetricBoundaryResponse_eq_abs_fullKernel_re :
    ‖ordinaryTraceAlong sourceBasis
      (finiteEulerNormalizedSymmetricBoundaryResponse owner lambda family)‖ =
      |(finiteEulerObliqueShearFullKernelTrace owner lambda family a c
        sourceBasis).re| := by
  rw [ordinaryTraceAlong_normalizedSymmetricBoundaryResponse_eq_fullKernel_re
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  simp only [Complex.norm_real, Real.norm_eq_abs]

/-- Proof 750's ambient physical anomaly readout also has zero real trace.
The theorem uses the legal source-to-ambient rectangular cycle. -/
theorem ordinaryTraceAlong_normalizedPhysicalAnomalyBoundaryReadout_re_eq_zero :
    (ordinaryTraceAlong globalBasis
      (finiteEulerNormalizedPhysicalAnomalyBoundaryReadout
        owner lambda family)).re = 0 := by
  have htrace := congrArg Complex.re
    (ordinaryTraceAlong_normalizedGramSimilarityAnomaly_eq_physicalBoundary
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor)
  rw [ordinaryTraceAlong_normalizedGramSimilarityAnomaly_re_eq_zero owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor] at htrace
  exact htrace.symm

end FixedFamily

section UniformFamily

variable (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
variable (lambda : CCM24SoninScale)
variable (a c : ℝ) (hac : a ≤ c)
variable (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
variable {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
variable (negativeBasis : HilbertBasis iota ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
variable (positiveBasis : HilbertBasis kappa ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
variable (outputBasis : HilbertBasis tau ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
variable (reflectedNegativeBasis : HilbertBasis iotaR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
variable (reflectedPositiveBasis : HilbertBasis kappaR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
variable (reflectedOutputBasis : HilbertBasis tauR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
variable (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
variable (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
variable (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
variable (hfactor : Summable fun i =>
  ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)

include a c hac hsupp negativeBasis positiveBasis outputBasis
  reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
  globalBasis boundaryBasis sourceBasis hfactor

/-- Family-uniform boundedness of the normalized symmetric trace is exactly
boundedness of the real part of the same complete full-kernel scalar.  This is
a real-trace interface, not the existing full complex-norm Gate 3U theorem. -/
theorem exists_uniform_normalizedSymmetricTraceBound_iff_fullKernelRealBound :
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (finiteEulerNormalizedSymmetricBoundaryResponse
          owner lambda family)‖ ≤ bound) ↔
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      |(finiteEulerObliqueShearFullKernelTrace owner lambda family a c
        sourceBasis).re| ≤ bound) := by
  constructor
  · rintro ⟨bound, hbound⟩
    refine ⟨bound, fun family => ?_⟩
    rw [←
      norm_ordinaryTraceAlong_normalizedSymmetricBoundaryResponse_eq_abs_fullKernel_re
        owner lambda family a c hac hsupp negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor]
    exact hbound family
  · rintro ⟨bound, hbound⟩
    refine ⟨bound, fun family => ?_⟩
    rw [
      norm_ordinaryTraceAlong_normalizedSymmetricBoundaryResponse_eq_abs_fullKernel_re
        owner lambda family a c hac hsupp negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor]
    exact hbound family

end UniformFamily

end CCM24FiniteSGatePhysicalNormalizedRealTraceReduction
end CCM25Concrete
end Source
end ConnesWeilRH
