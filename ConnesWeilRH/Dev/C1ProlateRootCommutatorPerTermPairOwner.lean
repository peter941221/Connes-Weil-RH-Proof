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
import ConnesWeilRH.Dev.C1ProlateRootCommutatorPairOwner

/-!
# C1: per-term root-commutator pair owner for S2 at unit scale (record 1091)

This is the D-weighted re-shape of the record-1065 brick, pinned by the recon note
`docs/proofs/1091_p2_s2_brick_leg_design.md`.  The committed brick factors `[C, K_S]` through
ONE shared base pair `(F_K, F_K)` and places the root on either side with `boundedSandwich`; its
sole analytic premise is record 1065's bare-prolate-factor contract, i.e. that the bare prolate
factor `F_K = Q_S (E - R_S)` itself is Hilbert--Schmidt.  Record 1067 measured `Tr(K_S)_model`
growing like `xi^0.4` for `{2,3,5}`, so that premise FAILS for the deciding family even though
the S2 conclusion holds: PROBE-P2 (record 1090) showed each NAMED term `C o K_S` and `K_S o C`
is individually nuclear with a flat O(1) norm (~4.63, decreasing), because the root's decaying
symbol absorbs the prolate mass that bare `F_K` cannot.

This leaf therefore owns the two terms SEPARATELY - one pairData with trace product
`C o K_S`, one with trace product `K_S o C` - built DIRECTLY from explicit analytic legs rather
than through 1065's shared base + sandwich.  Each term carries ONE root-absorbed leg (the prolate
factor pre-composed with the root, `F_K . C^dagger` or `F_K . C`) whose columns are O(1) per
PROBE-P2; that absorbed leg is defined under its own name so the owed "balanced nuclear leg"
helper can later replace the remaining bare `F_K` leg and drop 1065's premise entirely.  The
signed difference is reassembled with the committed `l2Sum` + scalar `-1`, then closes S2 through
the EXISTING generic consumer `targetProlateDetectorRootCommutatorTraceLegality_of_pairData`.

Honesty ledger (what this draft proves vs what is owed):
- PROVEN here: exact trace-product identities for both per-term owners (root OUTSIDE, no root
  self-adjointness assumed - the same adjoint algebra `boundedSandwich_traceProduct_eq` uses), and
  that they reassemble to `[C, K_S]` and close S2 through the unchanged `_of_pairData`.
- STILL OWED: this draft rests on the committed bare-prolate-factor contract (record 1065's), i.e.
  `F_K in HS`, for the un-weighted leg of each term - exactly record 1065's premise.  The balanced
  nuclear leg helper will exhibit that bare leg's replacement so neither leg is bare `F_K`, at which
  point the root-absorbed leg contracts below (O(1) per PROBE-P2) become the only obligations.

No positivity of the remainder, no RH-facing statement, and no F1' closure are asserted until the
per-term leg contracts are discharged by producers.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ProlateRootCommutatorPerTermPairOwner

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24SourceProlateTrace
open CCM25Concrete.CCM24UnitScaleProlateTraceReduction
open C1SelectedDetectorSemiLocalEulerBoundary
open C1ProlateResponseTraceLegalityUnitScale
open C1ProlateRootCommutatorPairOwner

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

noncomputable section

/-- The root-absorbed left leg of the `C o K_S` term: the prolate factor pre-composed with the
adjoint of the selected convolution root.  In xi-basis this weights the prolate kernel's COLUMNS by
the decaying root symbol, which is precisely the O(1) row/column weighting PROBE-P2 measured flat;
it is named separately so the owed balanced-nuclear-leg helper can weight that bare leg too. -/
noncomputable def targetProlateRootLeftTermAbsorbedLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : Op :=
  targetProlateRemainderFactor unitSoninScale family ∘L
    (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner).adjoint

/-- The root-absorbed right leg of the `K_S o C` term: the prolate factor post-composed with the
selected convolution root.  Symmetric to `targetProlateRootLeftTermAbsorbedLeg`; together they carry
the root's decay into both commutator terms so that neither needs bare `F_K in HS`. -/
noncomputable def targetProlateRemainderRightTermAbsorbedLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : Op :=
  targetProlateRemainderFactor unitSoninScale family ∘L
    CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner

/-- The `C o K_S` per-term pair owner: root-absorbed left leg, bare prolate right leg. -/
noncomputable def targetProlateRootLeftTermPairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis where
  left := targetProlateRootLeftTermAbsorbedLeg owner family
  right := targetProlateRemainderFactor unitSoninScale family
  left_summable_normSq := by
    -- The absorbed leg is a bounded precomposition of the HS prolate factor, so it inherits
    -- column-summability from `hfactor` (the committed ideal property).
    exact summable_normSq_precomp globalBasis globalBasis globalBasis
      (targetProlateRemainderFactor unitSoninScale family)
      ((CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner).adjoint)
      hfactor
  right_summable_normSq := hfactor

/-- The `C o K_S` per-term trace product is the root applied on the LEFT of the remainder, with no
assumption that the root is self-adjoint: `(F_K . C^dagger)^dagger = C . F_K^dagger`, so the adjoint
of the absorbed leg reproduces `C` and cancels to give exactly `C o K_S`. -/
theorem targetProlateRootLeftTermPairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    (targetProlateRootLeftTermPairData globalBasis owner family hfactor).traceProduct =
      CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner ∘L
        targetProlateRemainder unitSoninScale family := by
  unfold targetProlateRootLeftTermPairData targetProlateRootLeftTermAbsorbedLeg
    BasisHilbertSchmidtPairData.traceProduct
  -- (F_K . C^dagger)^dagger = C . F_K^dagger ; regroup so the self-product is a subterm;
  -- then F_K^dagger . F_K = K_S.
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  rw [ContinuousLinearMap.comp_assoc,
    targetProlateRemainderFactor_adjoint_comp_self unitSoninScale family]

/-- The `K_S o C` per-term pair owner: bare prolate left leg, root-absorbed right leg. -/
noncomputable def targetProlateRemainderRightTermPairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis where
  left := targetProlateRemainderFactor unitSoninScale family
  right := targetProlateRemainderRightTermAbsorbedLeg owner family
  left_summable_normSq := hfactor
  right_summable_normSq := by
    exact summable_normSq_precomp globalBasis globalBasis globalBasis
      (targetProlateRemainderFactor unitSoninScale family)
      (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)
      hfactor

/-- The `K_S o C` per-term trace product is the root applied on the RIGHT of the remainder:
`F_K^dagger . (F_K . C) = K_S . C`. -/
theorem targetProlateRemainderRightTermPairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    (targetProlateRemainderRightTermPairData globalBasis owner family hfactor).traceProduct =
      targetProlateRemainder unitSoninScale family ∘L
        CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner := by
  unfold targetProlateRemainderRightTermPairData targetProlateRemainderRightTermAbsorbedLeg
    BasisHilbertSchmidtPairData.traceProduct
  -- F_K^dagger . (F_K . C) = (F_K^dagger . F_K) . C = K_S . C.
  rw [← ContinuousLinearMap.comp_assoc,
    targetProlateRemainderFactor_adjoint_comp_self unitSoninScale family]

/-- The signed-difference owner for the complete root commutator: the two per-term owners combined
over the `L2` product carrier, with the minus sign kept in the second right leg. -/
noncomputable def targetProlateRootCommutatorPerTermPairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    BasisHilbertSchmidtPairData
      (G := WithLp 2 (finiteSCarrier × finiteSCarrier)) globalBasis :=
  BasisHilbertSchmidtPairData.l2Sum
    (targetProlateRootLeftTermPairData globalBasis owner family hfactor)
    (CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight
      (targetProlateRemainderRightTermPairData globalBasis owner family hfactor) (-1))

/-- The signed-difference trace product is exactly the root commutator. -/
theorem targetProlateRootCommutatorPerTermPairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    (targetProlateRootCommutatorPerTermPairData globalBasis owner family hfactor).traceProduct =
      cc20Commutator (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)
        (targetProlateRemainder unitSoninScale family) := by
  unfold targetProlateRootCommutatorPerTermPairData
  rw [BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    targetProlateRootLeftTermPairData_traceProduct_eq,
    targetProlateRemainderRightTermPairData_traceProduct_eq]
  simp only [sub_eq_add_neg, neg_one_smul, cc20Commutator]

/-- S2 closes from the single prolate-factor Hilbert--Schmidt contract via the per-term owner. The
`factorBasis` over the `L2` product carrier is an existence-side argument required by the
trace-legality machinery; it carries no analytic content of its own. -/
theorem targetProlateDetectorRootCommutatorTraceLegality_of_perTermPairData
    {ν κ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (factorBasis : HilbertBasis κ ℂ (WithLp 2 (finiteSCarrier × finiteSCarrier)))
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateRemainderFactorSummable family globalBasis) :
    targetProlateDetectorRootCommutatorTraceLegality owner family globalBasis := by
  exact targetProlateDetectorRootCommutatorTraceLegality_of_pairData
      globalBasis factorBasis owner family
      (targetProlateRootCommutatorPerTermPairData globalBasis owner family hfactor)
      (targetProlateRootCommutatorPerTermPairData_traceProduct_eq
        globalBasis owner family hfactor)

end

end C1ProlateRootCommutatorPerTermPairOwner
end Source
end ConnesWeilRH
