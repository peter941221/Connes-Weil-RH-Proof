/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleStrictAngle
import ConnesWeilRH.Dev.C1SelectedDetectorSemiLocalEulerBoundary
import ConnesWeilRH.Dev.C1ProlateResponseTraceLegalityUnitScale
import ConnesWeilRH.Dev.C1ProlateRootCommutatorPairOwner

/-!
# C1: single-contract reduction for F1' at unit scale (record 1066)

The two remaining analytic contracts of the detector-weighted prolate legality
F1' are related by pure bounded-precomposition plumbing.  This leaf records that
relation as three usable theorems plus the termwise diagonal identity they share:

```text
S2-FK-HS : Summable fun i => |F_K (globalBasis i)|^2        (owner-free)
    ==> S1 : Summable fun i => |(F_K oL C)(globalBasis i)|^2
          via summable_normSq_precomp, one line.
```

and the retired raw-F1 series is IDENTICAL to S2-FK-HS term by term:

```text
((|F_K e_i|^2 : R) : C) = <e_i, K_S e_i> .
```

Consequence (the third theorem): F1' at unit scale follows from the single
contract `targetProlateRemainderFactorSummable` alone.  No production of that
contract is claimed here; record 1063's operational guard on it carries over, since
it IS numerically the flagged raw-F1 series (see docs/proofs/1066).

No positivity, remainder sign, or RH-facing statement is asserted in this leaf.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ProlateSingleContractReduction

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24SourceProlateTrace
open CCM25Concrete.CCM24UnitScaleProlateTraceReduction
open C1SelectedDetectorSemiLocalEulerBoundary
open C1ProlateResponseTraceLegalityUnitScale
open C1ProlateRootCommutatorPairOwner

noncomputable section

/-- The retired raw-F1 diagonal identity under its record-1063 factor name: the
named-basis Hilbert--Schmidt weight of `F_K` is exactly one term of the finite-S
remainder's named-basis diagonal series. -/
theorem targetProlateRemainderFactor_unit_diagonal_eq_targetRemainder
    (family : FinitePrimePowerFamily) {ν : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) (i : ν) :
    ((‖targetProlateRemainderFactor unitSoninScale family (globalBasis i)‖ ^ 2 : ℝ) : ℂ) =
      inner ℂ (globalBasis i)
        (targetProlateRemainder unitSoninScale family (globalBasis i)) := by
  have hsq := targetProlateRemainderFactor_adjoint_comp_self unitSoninScale family
  rw [← hsq, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The S1 smoothing contract is the bounded-precomposition shadow of the single
prolate-factor Hilbert--Schmidt contract: precomposing `F_K` by the convolution
root never leaves the HS ideal. -/
theorem targetProlateDetectorRightSmoothingFactorSummable_of_remainderFactorSummable
    {ν : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    targetProlateDetectorRightSmoothingFactorSummable owner family globalBasis := by
  unfold targetProlateDetectorRightSmoothingFactorSummable
    targetProlateDetectorRightSmoothingFactor
  exact summable_normSq_precomp globalBasis globalBasis globalBasis
      (targetProlateRemainderFactor unitSoninScale family)
      (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner) hfactor

/-- The single prolate-factor Hilbert--Schmidt contract is termwise the retired
raw-F1 statement: summing the HS weights of `F_K` along a named basis is exactly
the trace-class legality of the finite-S remainder along that basis. -/
theorem targetProlateRemainderFactorSummable_iff_unitIsTraceClassAlong
    {ν : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (family : FinitePrimePowerFamily) :
    targetProlateRemainderFactorSummable family globalBasis ↔
      IsTraceClassAlong globalBasis (targetProlateRemainder unitSoninScale family) := by
  rw [IsTraceClassAlong, targetProlateRemainderFactorSummable]
  have hpointwise : ∀ i,
      ‖(inner ℂ (globalBasis i)
          ((targetProlateRemainder unitSoninScale family) (globalBasis i)))‖ =
        ‖(targetProlateRemainderFactor unitSoninScale family) (globalBasis i)‖ ^ 2 := by
    intro i
    rw [← targetProlateRemainderFactor_unit_diagonal_eq_targetRemainder
      family globalBasis i]
    exact Complex.norm_of_nonneg (sq_nonneg _)
  constructor
  · intro h
    have habs : Summable fun i =>
        ‖(inner ℂ (globalBasis i)
            ((targetProlateRemainder unitSoninScale family) (globalBasis i)))‖ :=
      h.congr (fun i => (hpointwise i).symm)
    exact habs.of_norm
  · intro htrace
    have hnorm : Summable fun i =>
        ‖(inner ℂ (globalBasis i)
            ((targetProlateRemainder unitSoninScale family) (globalBasis i)))‖ :=
      htrace.norm
    exact hnorm.congr hpointwise

/-- F1' at unit scale follows from the single prolate-factor Hilbert--Schmidt
contract alone: S1 is its bounded-precomposition shadow and the root-commutator
legality is brick 1065's pair owner. -/
theorem targetProlateRemainderDetectorWeightedTraceLegality_of_remainderFactorSummable
    {ν κ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (factorBasis : HilbertBasis κ ℂ (WithLp 2 (finiteSCarrier × finiteSCarrier)))
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    targetProlateRemainderDetectorWeightedTraceLegality owner family globalBasis := by
  have hright := targetProlateDetectorRightSmoothingFactorSummable_of_remainderFactorSummable
      owner family globalBasis hfactor
  exact targetProlateRemainderDetectorWeightedTraceLegality_of_rightSmoothing_and_remainderFactorSummable
      globalBasis factorBasis owner family hright hfactor

end

end C1ProlateSingleContractReduction
end Source
end ConnesWeilRH
