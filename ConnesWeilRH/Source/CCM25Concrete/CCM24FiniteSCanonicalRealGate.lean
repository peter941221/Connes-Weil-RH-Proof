/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalTargetHermitianPrefix
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalCanonicalCompletedKernelPhysicalTraceLegality
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandSelfAdjointTrace

/-!
# Canonical-family real Gate contract

The historical Gate interface asks for a complex trace bound over every finite
prime-power family.  The route-selected arithmetic owner uses only
`canonicalFamily owner`, and its Hermitian endpoint consumes only the real
part of the trace.

This module records that smaller contract without making it vacuous.  The
bound is supplied explicitly, or by a supplied owner-dependent majorant; it
is never existentially chosen after fixing one scalar.  Fixed-family trace
legality remains supplied by Proofs 758 and 759.

The exact source identity is

`Tr(Target_S) = -star (Tr(SourceBand_S))`.

Thus the canonical real target, the real source-band endpoint, the Hermitian
target trace, and the completed physical full-kernel real trace are the same
scalar bound.  A source-to-ambient endpoint trace cycle is kept as an explicit
premise: this file does not infer it from diagonal summability.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCanonicalRealGate

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalCanonicalCompletedKernelPhysicalTraceLegality
open CCM24FiniteSGatePhysicalObliqueShearKernelReduction
open CCM24FiniteSGatePhysicalTargetHermitianPrefix
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSMovingBandSelfAdjointTrace
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The non-vacuous pointwise real Gate 3U contract.  The caller supplies the
bound before the canonical trace is inspected. -/
noncomputable def canonicalRealGate3UAt
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (bound : ℝ) : Prop :=
  |(ordinaryTraceAlong sourceBasis
    (finiteEulerTargetCommutatorResponse owner lambda
      (canonicalFamily owner))).re| ≤ bound

/-- A support-coupled Gate contract over a specified class of selected owners.
The majorant may depend on the support radius and Sobolev energy of the same
owner, but not on an unrelated finite prime family. -/
noncomputable def canonicalRealGate3UOn
    {rho : Type*} (owners : Set SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (majorant : SelectedWeilSquare.SelectedWeilSquareOwner → ℝ) : Prop :=
  ∀ owner ∈ owners,
    canonicalRealGate3UAt owner lambda sourceBasis (majorant owner)

/-- The actual target trace is the negative conjugate of the right-ordered
source-band trace.  This is an operator-order identity, not a trace cycle. -/
theorem ordinaryTraceAlong_targetCommutator_eq_neg_star_sourceBand
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) =
      -star (ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)) := by
  have htrace := congrArg (ordinaryTraceAlong sourceBasis)
    (leftOrderedSourceBandGramResponse_eq_neg_targetCommutator
      owner lambda family)
  rw [ordinaryTraceAlong_leftOrderedSourceBandGramResponse_eq_star,
    PositiveTrace.ordinaryTraceAlong_neg] at htrace
  calc
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) =
      -(-ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family)) := by ring
    _ = -star (ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)) := by rw [← htrace]

/-- Consequently the two real traces differ only by sign. -/
theorem ordinaryTraceAlong_targetCommutator_re_eq_neg_sourceBand_re
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    (ordinaryTraceAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda family)).re =
      -(ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)).re := by
  rw [ordinaryTraceAlong_targetCommutator_eq_neg_star_sourceBand]
  simp only [Complex.star_def, Complex.neg_re, Complex.conj_re]

/-- Absolute real trace size is exactly invariant under the target/source
order reversal. -/
theorem abs_re_ordinaryTraceAlong_targetCommutator_eq_sourceBand
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    |(ordinaryTraceAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda family)).re| =
      |(ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)).re| := by
  rw [ordinaryTraceAlong_targetCommutator_re_eq_neg_sourceBand_re, abs_neg]

/-- The canonical real Gate is exactly the real source-band endpoint bound. -/
theorem canonicalRealGate3UAt_iff_sourceBandRealBound
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (bound : ℝ) :
    canonicalRealGate3UAt owner lambda sourceBasis bound ↔
      |(ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda (canonicalFamily owner))).re| ≤
          bound := by
  unfold canonicalRealGate3UAt
  rw [abs_re_ordinaryTraceAlong_targetCommutator_eq_sourceBand]

/-- The Hermitian target trace norm is exactly the absolute real target trace.
Trace legality is explicit because the equality uses trace additivity. -/
theorem norm_ordinaryTraceAlong_targetHermitian_eq_abs_target_re
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (htrace : IsTraceClassAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda family)) :
    ‖ordinaryTraceAlong sourceBasis
      (finiteEulerTargetHermitianResponse owner lambda family)‖ =
      |(ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family)).re| := by
  rw [ordinaryTraceAlong_targetHermitianResponse_eq_target_re owner lambda
    family sourceBasis htrace]
  simp only [Complex.norm_real, Real.norm_eq_abs]

/-- Under the already available fixed-family legality witness, the canonical
real Gate is exactly a norm bound for the self-adjoint target owner. -/
theorem canonicalRealGate3UAt_iff_targetHermitianTraceBound
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (bound : ℝ)
    (htrace : IsTraceClassAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda
        (canonicalFamily owner))) :
    canonicalRealGate3UAt owner lambda sourceBasis bound ↔
      ‖ordinaryTraceAlong sourceBasis
        (finiteEulerTargetHermitianResponse owner lambda
          (canonicalFamily owner))‖ ≤ bound := by
  unfold canonicalRealGate3UAt
  rw [norm_ordinaryTraceAlong_targetHermitian_eq_abs_target_re owner lambda
    (canonicalFamily owner) sourceBasis htrace]

/-- The same canonical contract is the real trace bound for the one completed
outer/reflected-second-support/prolate physical scalar. -/
theorem canonicalRealGate3UAt_iff_fullKernelRealBound
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
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
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ) :
    canonicalRealGate3UAt owner lambda sourceBasis bound ↔
      |(finiteEulerObliqueShearFullKernelTrace owner lambda
        (canonicalFamily owner) a c sourceBasis).re| ≤ bound := by
  unfold canonicalRealGate3UAt
  rw [ordinaryTraceAlong_targetCommutator_eq_obliqueShearFullKernelTrace
    owner lambda (canonicalFamily owner) a c hac hsupp negativeBasis
    positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis sourceBasis hfactor]

/-- A complex trace bound over every unrelated family is sufficient for the
canonical real contract, but no converse is asserted. -/
theorem canonicalRealGate3UAt_of_allFamilyComplexTargetBound
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (bound : ℝ)
    (hbound : ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family)‖ ≤ bound) :
    canonicalRealGate3UAt owner lambda sourceBasis bound := by
  unfold canonicalRealGate3UAt
  exact (Complex.abs_re_le_norm _).trans (hbound (canonicalFamily owner))

/-- Restricting the owner class weakens the support-coupled contract in the
expected direction. -/
theorem canonicalRealGate3UOn_mono
    {rho : Type*} {first second : Set
      SelectedWeilSquare.SelectedWeilSquareOwner}
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (majorant : SelectedWeilSquare.SelectedWeilSquareOwner → ℝ)
    (hsubset : first ⊆ second)
    (hgate : canonicalRealGate3UOn second lambda sourceBasis majorant) :
    canonicalRealGate3UOn first lambda sourceBasis majorant := by
  intro owner howner
  exact hgate owner (hsubset howner)

/-- If a legal source-to-ambient endpoint cycle is supplied, the canonical
real target size is exactly the trace norm of the self-adjoint ambient band
response.  The cycle is deliberately not inferred here. -/
theorem norm_rootSandwichedBandResponse_eq_abs_target_re_of_endpointCycle
    {rho nu : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (hcycle : ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family) =
      ordinaryTraceAlong globalBasis
        (rootSandwichedBandResponse owner lambda family)) :
    ‖ordinaryTraceAlong globalBasis
      (rootSandwichedBandResponse owner lambda family)‖ =
      |(ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family)).re| := by
  rw [ordinaryTraceAlong_rootSandwichedBandResponse_eq_re]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [← hcycle]
  exact (abs_re_ordinaryTraceAlong_targetCommutator_eq_sourceBand
    owner lambda family sourceBasis).symm

/-- The canonical real Gate therefore feeds the self-adjoint endpoint once
the separate source-to-ambient trace cycle has been established. -/
theorem canonicalRootSandwichedTraceBound_of_realGate_and_endpointCycle
    {rho nu : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier) (bound : ℝ)
    (hgate : canonicalRealGate3UAt owner lambda sourceBasis bound)
    (hcycle : ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda (canonicalFamily owner)) =
      ordinaryTraceAlong globalBasis
        (rootSandwichedBandResponse owner lambda (canonicalFamily owner))) :
    ‖ordinaryTraceAlong globalBasis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner))‖ ≤
        bound := by
  rw [norm_rootSandwichedBandResponse_eq_abs_target_re_of_endpointCycle
    owner lambda (canonicalFamily owner) sourceBasis globalBasis hcycle]
  exact hgate

end CCM24FiniteSCanonicalRealGate
end CCM25Concrete
end Source
end ConnesWeilRH
