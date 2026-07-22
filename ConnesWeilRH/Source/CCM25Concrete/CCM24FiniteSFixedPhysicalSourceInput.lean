/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedSourceInput
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedPhysicalEnergyBound

/-!
# Fixed compact-root source input

The complete outer, reflected-outer, second-support, and prolate pair is first
pulled back through the literal source Sonin inclusion on both sides.  Its
positive Gram square root is then a single Hilbert--Schmidt endomorphism of the
source carrier.  The construction uses the exact square-energy identity for
the Gram square root; no Douglas readout or family-dependent factor is used.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedPhysicalSourceInput

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSFixedPhysicalEnergyBound
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSFixedSourceInput
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The fixed physical pair on the actual source Sonin carrier.  It is
independent of every finite prime-power family. -/
noncomputable def fixedSourceThreeBranchPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
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
  BasisHilbertSchmidtPairData.boundedPrecomp boundaryBasis sourceBasis
    (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor)
    (sourceInclusion lambda) (sourceInclusion lambda)

/-- The one fixed source-carrier input used by the completed physical history.
Its definition contains no finite Euler family. -/
noncomputable def fixedPhysicalSourceInput
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
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
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  pairSourceGramSqrt
    (fixedSourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor)

theorem fixedPhysicalSourceInput_summable_normSq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
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
    Summable fun i =>
      ‖fixedPhysicalSourceInput owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor
        (sourceBasis i)‖ ^ 2 := by
  exact pairSourceGramSqrt_summable_normSq
    (fixedSourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor)

/-- Compact support gives a fixed Hilbert--Schmidt budget for the source input.
The bound is independent of the finite visible-prime family. -/
theorem fixedPhysicalSourceInput_basisEnergy_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
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
    (∑' i, ‖fixedPhysicalSourceInput owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor
      (sourceBasis i)‖ ^ 2) ≤
        2 * fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
    positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis hfactor
  let pair := fixedSourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  let majorant := fixedPhysicalEnergyMajorant owner lambda a c globalBasis
  have hinclusion : ‖sourceInclusion lambda‖ ≤ 1 :=
    Submodule.norm_subtypeL_le _
  have hleftBase : (∑' i, ‖base.left (globalBasis i)‖ ^ 2) ≤ majorant := by
    dsimp only [base, majorant]
    exact sourceThreeBranchPairData_left_basisEnergy_le_fixedMajorant
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor
  have hrightBase : (∑' i, ‖base.right (globalBasis i)‖ ^ 2) ≤ majorant := by
    dsimp only [base, majorant]
    exact sourceThreeBranchPairData_right_basisEnergy_le_fixedMajorant
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor
  have hleft : (∑' i, ‖pair.left (sourceBasis i)‖ ^ 2) ≤ majorant := by
    dsimp only [pair, fixedSourceThreeBranchPairData]
    exact (boundedPrecomp_left_tsum_le_of_norm_le_one boundaryBasis sourceBasis
      base (sourceInclusion lambda) (sourceInclusion lambda) hinclusion).trans
        hleftBase
  have hright : (∑' i, ‖pair.right (sourceBasis i)‖ ^ 2) ≤ majorant := by
    dsimp only [pair, fixedSourceThreeBranchPairData]
    exact (boundedPrecomp_right_tsum_le_of_norm_le_one boundaryBasis sourceBasis
      base (sourceInclusion lambda) (sourceInclusion lambda) hinclusion).trans
        hrightBase
  calc
    (∑' i, ‖fixedPhysicalSourceInput owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor (sourceBasis i)‖ ^ 2) =
        ∑' i, (‖pair.left (sourceBasis i)‖ ^ 2 +
          ‖pair.right (sourceBasis i)‖ ^ 2) := by
      apply tsum_congr
      intro i
      simpa only [fixedPhysicalSourceInput, pair] using
        pairSourceGramSqrt_normSq_eq pair (sourceBasis i)
    _ = (∑' i, ‖pair.left (sourceBasis i)‖ ^ 2) +
        ∑' i, ‖pair.right (sourceBasis i)‖ ^ 2 := by
      exact pair.left_summable_normSq.tsum_add pair.right_summable_normSq
    _ ≤ majorant + majorant := add_le_add hleft hright
    _ = 2 * fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
      dsimp only [majorant]
      ring

end CCM24FiniteSFixedPhysicalSourceInput
end CCM25Concrete
end Source
end ConnesWeilRH
