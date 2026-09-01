/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleStrictAngle
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal
import ConnesWeilRH.Dev.C1SelectedDetectorSemiLocalEulerBoundary
import ConnesWeilRH.Dev.C1ProlateResponseTraceLegalityUnitScale
import ConnesWeilRH.Dev.C1ProlateRootCommutatorBalancedLegOwner

/-!
# C1: balanced-leg S2 contract reduction (record 1094)

Record 1093 (`C1ProlateRootCommutatorBalancedLegOwner`) closed S2 through three named
column-sum contracts, one per leg of the two balanced per-term pairs:

```text
  #1  targetProlateRootFactorHS          : Summable ‖C e_i‖^2        (KC right leg)
  #2  targetProlateRootFactorAdjointHS   : Summable ‖C^dagger e_i‖^2 (CK left leg)
  #3  targetProlateRemainderHS           : Summable ‖K_S e_i‖^2      (both CK + KC legs)

  C   := rootConvolution owner         (a bare Fourier multiplier, bounded)
  K_S := targetProlateRemainder ...    (= F_K^dagger . F_K, self-adjoint)
```

This module reduces that contract set and pinpoints what is genuinely owed:

1. **`#2` follows from `#1`.** The Hilbert--Schmidt column sum is adjoint-invariant
   (`summable_adjoint_normSq`, read on the same global basis), so the CK left-leg contract is
   not independent of the KC right-leg one.  S2 therefore needs only TWO named contracts,
   `#1` and `#3`, via `..._of_twoContractBalancedPairData`.

2. **At the Hilbert--Schmidt level, only `#3` is structurally required.** Each commutator term
   `C o K_S` (postcomposition) and `K_S o C` (precomposition) is col-summable from `#3` plus the
   boundedness of `C` alone - the committed two-sided HS ideal property.  So the bare-root legs
   that #1/#2 control follow from the remainder contract - no extra input at this level.

3. **What remains owed is PER-TERM NUCLEARITY** (named below as
   `targetProlateCommutatorTermNuclearity`): each commutator term has a
   summable DIAGONAL along the global basis - strictly stronger than being
   Hilbert--Schmidt (items 1 and 2) - PROBE-P2's flat O(1).

A bare multiplier bounded below on a positive-measure set is not compact, so
contracts #1/#2 hold only in the finite-grid model.  The duty past `#3` is the
nuclearity of each term, which this module NAMES but does not yet discharge.

Honesty ledger: items 1 and 2 are proven from committed machinery alone; the
item-3 nuclearity contract is the producer's target.  RH unclaimed; GATE 1
mainline untouched.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ProlateRootCommutatorBalancedLegContractReduction

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24SourceProlateTrace
open CCM25Concrete.CCM24UnitScaleProlateTraceReduction
open C1SelectedDetectorSemiLocalEulerBoundary
open C1ProlateResponseTraceLegalityUnitScale
open C1ProlateRootCommutatorBalancedLegOwner

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

noncomputable section

/-- The CK left-leg contract `#2` (`C^dagger in HS`) follows from the KC right-leg contract
`#1` (`C in HS`): the Hilbert--Schmidt column sum is adjoint-invariant, read on the SAME global
basis.  This collapses record 1093's two root contracts to a single one. -/
theorem targetProlateRootFactorAdjointHS_of_HS
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) {ν : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hc : targetProlateRootFactorHS owner globalBasis) :
    targetProlateRootFactorAdjointHS owner globalBasis := by
  exact BasisHilbertSchmidtPairData.summable_adjoint_normSq
      globalBasis globalBasis
        (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner) hc

/-- The first commutator term `C o K_S` is Hilbert--Schmidt on the global basis from the remainder
contract `#3` alone: the root is a bounded Fourier multiplier, so postcomposition preserves column-
summability (the committed HS ideal property) - no bare-root contract is needed at this level. -/
theorem targetProlateRootLeftTermHS_of_RemainderHS
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) {ν : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (family : FinitePrimePowerFamily)
    (hK : targetProlateRemainderHS family globalBasis) :
    Summable fun i =>
      ‖(CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner ∘L
        targetProlateRemainder unitSoninScale family) (globalBasis i)‖ ^ 2 := by
  exact summable_normSq_postcomp globalBasis
      (targetProlateRemainder unitSoninScale family)
      (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner) hK

/-- The second commutator term `K_S o C` is Hilbert--Schmidt on the global basis from the remainder
contract `#3` alone: precomposition by a bounded map preserves column-summability (the committed
two-sided ideal property, proven through the adjoint).  Again no bare-root contract is required. -/
theorem targetProlateRemainderRightTermHS_of_RemainderHS
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) {ν : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (family : FinitePrimePowerFamily)
    (hK : targetProlateRemainderHS family globalBasis) :
    Summable fun i =>
      ‖(targetProlateRemainder unitSoninScale family ∘L
        CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner) (globalBasis i)‖ ^ 2 := by
  exact summable_normSq_precomp globalBasis globalBasis globalBasis
      (targetProlateRemainder unitSoninScale family)
      (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner) hK

/-- PER-TERM NUCLEARITY: the owed analytic contract for S2 past `#3`.  Each
   commutator term has a summable DIAGONAL along the global basis, strictly
   stronger than being Hilbert--Schmidt (the two lemmas above) and equal to
   PROBE-P2's flat O(1).  On the continuum carrier it does not reduce to a bare
   root HS contract (#1/#2), which fail for a generic Schwartz symbol.  So this,
   not #1, is what producers discharge. -/
noncomputable def targetProlateCommutatorTermNuclearity
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : Prop :=
  IsTraceClassAlong globalBasis
      (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner ∘L
        targetProlateRemainder unitSoninScale family) ∧
  IsTraceClassAlong globalBasis
      (targetProlateRemainder unitSoninScale family ∘L
        CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)

/-- S2 closes from just TWO named HS contracts, a root `#1` and a remainder
   `#3`, not record 1093's three.  The adjoint-invariance lemma derives `#2`
   from `#1`; its AdjointHS assumption is thus discharged. -/
theorem targetProlateDetectorRootCommutatorTraceLegality_of_twoContractBalancedPairData
    {ν κ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (factorBasis : HilbertBasis κ ℂ (WithLp 2 (finiteSCarrier × finiteSCarrier)))
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hc : targetProlateRootFactorHS owner globalBasis)
    (hK : targetProlateRemainderHS family globalBasis) :
    targetProlateDetectorRootCommutatorTraceLegality owner family globalBasis := by
  have hcAdj : targetProlateRootFactorAdjointHS owner globalBasis :=
    targetProlateRootFactorAdjointHS_of_HS owner globalBasis hc
  exact targetProlateDetectorRootCommutatorTraceLegality_of_balancedPairData
      globalBasis factorBasis owner family hcAdj hK hc

end

end C1ProlateRootCommutatorBalancedLegContractReduction
end Source
end ConnesWeilRH
