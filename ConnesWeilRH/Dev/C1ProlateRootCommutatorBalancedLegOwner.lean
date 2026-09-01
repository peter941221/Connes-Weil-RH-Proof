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

/-!
# C1: balanced-leg root-commutator pair owner for S2 at unit scale (record 1093)

This is the second re-shape of the record-1065 brick, closing task #8.  The goal set by
`docs/proofs/1091_p2_s2_brick_leg_design.md` was to DROP record 1065's one analytic premise:
the bare prolate factor `F_K = Q_S (E - R_S)` is itself Hilbert--Schmidt (`...FactorSummable`).
Record 1067 measured it growing like `xi^0.4` for `{2,3,5}`, so it FAILS there.

The balanced-leg argument uses only NAMED operators as legs:

```text
  C   := rootConvolution owner               (selected convolution root; a Fourier multiplier)
  K_S := targetProlateRemainder unitSoninScale family    (= F_K^dagger . F_K, self-adjoint)

  pairData_CK : left = C^dagger , right = K_S   traceProduct = C o K_S
  pairData_KC : left = K_S      , right = C     traceProduct = K_S o C   (K_S self-adjoint)
```

Each commutator term is a product of two HS operators, hence trace-class; it factors as
`(HS-leg)^dagger . (HS-leg)` with every leg drawn from `{C, C^dagger, K_S}` - no bare `F_K` leg.
So record 1065's premise disappears entirely.

The three named contracts this owner consumes (each a plain column-norm sum):

```text
  targetProlateRootFactorHS         : Summable ‖C e_i‖^2        (KC right leg)
  targetProlateRootFactorAdjointHS  : Summable ‖C^dagger e_i‖^2 (CK left leg)
  targetProlateRemainderHS          : Summable ‖K_S e_i‖^2      (CK + KC legs; = Tr(K_S^2))
```

`...RootFactorHS`, and its adjoint twin, state the same fact - HS norms are
adjoint-invariant.  They stay two explicit sums because each pairData field asks
for its own leg's column sum.

The third contract, `targetProlateRemainderHS`, is PROBE-P2's control row
(record 1090 s4a): it is finite per window and WEAKER than the 1065 premise -
`K_S`'s eigenvalues lie in `[0,1]`, so `{Tr(K_S) < inf}` implies that
`{Tr(K_S^2) < inf}`.

Honesty ledger (what this draft proves vs what is owed):
- PROVEN here: traceProduct identities for both balanced per-term owners (the KC side uses `K_S`
  self-adjointness, derived inline from `..._adjoint_comp_self`).  They reassemble to `[C, K_S]`,
  and close S2 through the UNCHANGED generic consumer `_of_pairData`.
- STILL OWED (to producers): discharge the three column-sum contracts above.
  Each is as well-supported by the model as record 1065's premise was - `C in HS`
  holds for any Schwartz symbol, and `K_S in HS` is PROBE-P2's finite control row -
  but none is yet a Lean proof of summability.

No positivity of the remainder, no RH-facing statement, and no F1' closure is asserted
until those contracts are discharged by producers.  It SUPERSEDES record 1092's absorbed-leg
`...PerTermPairOwner`: it drops the failing premise at the cost of two extra, weaker
named contracts.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ProlateRootCommutatorBalancedLegOwner

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24SourceProlateTrace
open CCM25Concrete.CCM24UnitScaleProlateTraceReduction
open C1SelectedDetectorSemiLocalEulerBoundary
open C1ProlateResponseTraceLegalityUnitScale

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

noncomputable section

/-- Named-basis Hilbert--Schmidt summability of the selected convolution root `C` itself.  This is
the KC right-leg contract; for a Fourier-multiplier root it equals the L2 norm of the symbol and is
flat (independent of the frequency window) for any Schwartz symbol. -/
noncomputable def targetProlateRootFactorHS
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) {ν : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) : Prop :=
  Summable fun i =>
    ‖CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner (globalBasis i)‖ ^ 2

/-- Named-basis Hilbert--Schmidt summability of the ADJOINT `C^dagger` of the convolution root.
The CK left-leg contract; in content identical to `targetProlateRootFactorHS`, since the HS norm is
adjoint-invariant, but stated on its own leg's column sum so no equivalence lemma is owed here. -/
noncomputable def targetProlateRootFactorAdjointHS
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) {ν : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) : Prop :=
  Summable fun i =>
    ‖(CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner).adjoint (globalBasis i)‖ ^ 2

/-- Named-basis HS summability of `K_S` itself; the CK right-leg and KC left-leg contract.
It IS PROBE-P2's control row `Tr(K_S^2)` (record 1090 s4a), strictly weaker than the 1065 premise.
The reason: `K_S`'s eigenvalues lie in `[0,1]`, so the sum of squares is at most the plain sum. -/
noncomputable def targetProlateRemainderHS
    (family : FinitePrimePowerFamily) {ν : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) : Prop :=
  Summable fun i =>
    ‖targetProlateRemainder unitSoninScale family (globalBasis i)‖ ^ 2

/-- The `C o K_S` balanced per-term pair owner: left leg is the ADJOINT root, right leg is the
remainder itself.  Neither leg is the bare prolate factor `F_K`, so record 1065's premise drops
out; the two legs are each controlled by their own named HS contract. -/
noncomputable def targetProlateRootLeftTermBalancedPairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hcAdj : targetProlateRootFactorAdjointHS owner globalBasis)
    (hK : targetProlateRemainderHS family globalBasis) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis where
  left := (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner).adjoint
  right := targetProlateRemainder unitSoninScale family
  left_summable_normSq := hcAdj
  right_summable_normSq := hK

/-- The `C o K_S` balanced trace product is the root applied on the LEFT of the remainder, with no
assumption that the root or the remainder is self-adjoint: `(C^dagger)^dagger = C`, so the adjoint
of the left leg reproduces `C`. -/
theorem targetProlateRootLeftTermBalancedPairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hcAdj : targetProlateRootFactorAdjointHS owner globalBasis)
    (hK : targetProlateRemainderHS family globalBasis) :
    (targetProlateRootLeftTermBalancedPairData globalBasis owner family hcAdj hK).traceProduct =
      CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner ∘L
        targetProlateRemainder unitSoninScale family := by
  unfold targetProlateRootLeftTermBalancedPairData BasisHilbertSchmidtPairData.traceProduct
  -- (C^dagger)^dagger = C ; the remainder leg is untouched.
  simp only [ContinuousLinearMap.adjoint_adjoint]

/-- The `K_S o C` balanced per-term pair owner: left leg is the remainder itself, right leg is the
selected convolution root.  Mirrors `targetProlateRootLeftTermBalancedPairData` with roles swapped;
the trace product relies on `K_S` being self-adjoint (it is, as `F_K^dagger . F_K`). -/
noncomputable def targetProlateRemainderRightTermBalancedPairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hK : targetProlateRemainderHS family globalBasis)
    (hc : targetProlateRootFactorHS owner globalBasis) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis where
  left := targetProlateRemainder unitSoninScale family
  right := CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner
  left_summable_normSq := hK
  right_summable_normSq := hc

/-- The `K_S o C` balanced trace product puts the root on the RIGHT of the remainder:
the left leg's adjoint equals `K_S` because it is self-adjoint as `F_K^dagger . F_K`. -/
theorem targetProlateRemainderRightTermBalancedPairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hK : targetProlateRemainderHS family globalBasis)
    (hc : targetProlateRootFactorHS owner globalBasis) :
    (targetProlateRemainderRightTermBalancedPairData globalBasis owner family hK hc).traceProduct =
      targetProlateRemainder unitSoninScale family ∘L
        CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner := by
  unfold targetProlateRemainderRightTermBalancedPairData BasisHilbertSchmidtPairData.traceProduct
  -- K_S is self-adjoint: (K_S)^dagger = ((F_K^dagger . F_K))^dagger = F_K^dagger . F_K = K_S.
  have hKself :
      (targetProlateRemainder unitSoninScale family).adjoint =
        targetProlateRemainder unitSoninScale family := by
    rw [← targetProlateRemainderFactor_adjoint_comp_self]
    simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  -- Use the self-adjointness as a rewrite so (K_S)^dagger becomes K_S on the left of the root.
  simp only [hKself]

/-- The signed-difference owner for the complete root commutator: the two balanced per-term owners
combined over the `L2` product carrier, with the minus sign kept in the second right leg. -/
noncomputable def targetProlateRootCommutatorBalancedPairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hcAdj : targetProlateRootFactorAdjointHS owner globalBasis)
    (hK : targetProlateRemainderHS family globalBasis)
    (hc : targetProlateRootFactorHS owner globalBasis) :
    BasisHilbertSchmidtPairData
      (G := WithLp 2 (finiteSCarrier × finiteSCarrier)) globalBasis :=
  BasisHilbertSchmidtPairData.l2Sum
    (targetProlateRootLeftTermBalancedPairData globalBasis owner family hcAdj hK)
    (CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight
      (targetProlateRemainderRightTermBalancedPairData globalBasis owner family hK hc) (-1))

/-- The signed-difference trace product is exactly the root commutator. -/
theorem targetProlateRootCommutatorBalancedPairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hcAdj : targetProlateRootFactorAdjointHS owner globalBasis)
    (hK : targetProlateRemainderHS family globalBasis)
    (hc : targetProlateRootFactorHS owner globalBasis) :
    (targetProlateRootCommutatorBalancedPairData globalBasis owner family
      hcAdj hK hc).traceProduct = cc20Commutator
      (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)
        (targetProlateRemainder unitSoninScale family) := by
  unfold targetProlateRootCommutatorBalancedPairData
  rw [BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    targetProlateRootLeftTermBalancedPairData_traceProduct_eq,
    targetProlateRemainderRightTermBalancedPairData_traceProduct_eq]
  simp only [sub_eq_add_neg, neg_one_smul, cc20Commutator]

/-- S2 closes from the three balanced-leg HS contracts, via the balanced per-term owner.
The `factorBasis` over the `L2` product carrier is an existence-side argument required by the
trace-legality machinery; it carries no analytic content of its own. -/
theorem targetProlateDetectorRootCommutatorTraceLegality_of_balancedPairData
    {ν κ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (factorBasis : HilbertBasis κ ℂ (WithLp 2 (finiteSCarrier × finiteSCarrier)))
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hcAdj : targetProlateRootFactorAdjointHS owner globalBasis)
    (hK : targetProlateRemainderHS family globalBasis)
    (hc : targetProlateRootFactorHS owner globalBasis) :
    targetProlateDetectorRootCommutatorTraceLegality owner family globalBasis := by
  exact targetProlateDetectorRootCommutatorTraceLegality_of_pairData
      globalBasis factorBasis owner family
      (targetProlateRootCommutatorBalancedPairData globalBasis owner family hcAdj hK hc)
      (targetProlateRootCommutatorBalancedPairData_traceProduct_eq
        globalBasis owner family hcAdj hK hc)

end

end C1ProlateRootCommutatorBalancedLegOwner
end Source
end ConnesWeilRH
