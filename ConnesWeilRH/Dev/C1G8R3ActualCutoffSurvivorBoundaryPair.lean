/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ActualCutoffPairedCrossTrace

/-!
# Actual-cutoff survivor/boundary channel pair

The two mixed survivor/boundary channels in the G8 metric ledger are adjoints
at every literal cutoff. Their ordinary-trace sum is therefore real and is
exactly twice either orientation's real trace. This is an algebraic pairing;
it supplies no cutoff limit or `qw` readback.
-/

namespace ConnesWeilRH
namespace Dev

open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.C1G8AdjointShearGram
open Source.C1G8P1MetricChannels
open scoped InnerProduct InnerProductSpace Topology

noncomputable local instance actualCutoffSurvivorBoundarySoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Normalizing four nested adjoints through the coframe channel needs this budget.
/-- At every actual cutoff, the survivor/boundary channel is the adjoint of
the boundary/survivor channel for the same selected detector and source leg. -/
theorem g8MetricCutoffSurvivorBoundaryChannel_eq_adjoint
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : ℕ) :
    g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
        (g8MetricSurvivorCoframe lambda family)
        (g8MetricVisibleBoundaryCoframe lambda family) =
      (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
        (g8MetricVisibleBoundaryCoframe lambda family)
        (g8MetricSurvivorCoframe lambda family)).adjoint := by
  let C := (sourceInclusion lambda).adjoint ∘L
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  let S := g8MetricSurvivorCoframe lambda family
  let B := g8MetricVisibleBoundaryCoframe lambda family
  let D := detectorOperator owner
  have hD : D.adjoint = D := (detectorOperator_isSelfAdjoint owner).adjoint_eq
  change C.adjoint ∘L S.adjoint ∘L D ∘L B ∘L C =
    (C.adjoint ∘L B.adjoint ∘L D ∘L S ∘L C).adjoint
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hD,
    ContinuousLinearMap.comp_assoc]

set_option maxHeartbeats 1000000 in
-- The two trace-class witnesses and adjoint trace readback need this budget.
/-- The two mixed metric-channel traces at a finite cutoff sum to twice the
real part of either ordered trace. -/
theorem ordinaryTraceAlong_g8MetricCutoffSurvivorBoundaryPair_eq_two_re
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : ℕ) :
    ordinaryTraceAlong sourceBasis
        (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricSurvivorCoframe lambda family)
          (g8MetricVisibleBoundaryCoframe lambda family) +
         g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricVisibleBoundaryCoframe lambda family)
          (g8MetricSurvivorCoframe lambda family)) =
      ((2 * (ordinaryTraceAlong sourceBasis
        (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricVisibleBoundaryCoframe lambda family)
          (g8MetricSurvivorCoframe lambda family))).re : ℝ) : ℂ) := by
  let SB := g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
    (g8MetricSurvivorCoframe lambda family)
    (g8MetricVisibleBoundaryCoframe lambda family)
  let BS := g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
    (g8MetricVisibleBoundaryCoframe lambda family)
    (g8MetricSurvivorCoframe lambda family)
  have hSB : PositiveTrace.IsTraceClassAlong sourceBasis SB := by
    exact g8MetricCutoffChannel_isTraceClassAlong owner lambda family
      globalBasis sourceBasis n (g8MetricSurvivorCoframe lambda family)
      (g8MetricVisibleBoundaryCoframe lambda family)
  have hBS : PositiveTrace.IsTraceClassAlong sourceBasis BS := by
    exact g8MetricCutoffChannel_isTraceClassAlong owner lambda family
      globalBasis sourceBasis n (g8MetricVisibleBoundaryCoframe lambda family)
      (g8MetricSurvivorCoframe lambda family)
  have htraceSum : ordinaryTraceAlong sourceBasis (SB + BS) =
      ordinaryTraceAlong sourceBasis SB + ordinaryTraceAlong sourceBasis BS :=
    ordinaryTraceAlong_add sourceBasis SB BS hSB hBS
  have hpair : SB = BS.adjoint := by
    simpa only [SB, BS] using
      g8MetricCutoffSurvivorBoundaryChannel_eq_adjoint owner lambda family
        globalBasis sourceBasis n
  rw [show ordinaryTraceAlong sourceBasis (SB + BS) =
        ordinaryTraceAlong sourceBasis SB + ordinaryTraceAlong sourceBasis BS
      from htraceSum]
  rw [hpair, ordinaryTraceAlong_adjoint, Complex.star_def]
  rw [add_comm]
  rw [Complex.add_conj]

end Dev
end ConnesWeilRH
