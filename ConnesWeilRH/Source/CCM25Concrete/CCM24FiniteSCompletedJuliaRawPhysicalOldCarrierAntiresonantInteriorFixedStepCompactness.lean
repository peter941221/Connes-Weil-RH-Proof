/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CompactApproximateKernel
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRenewalDeviation
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawLocalTraceFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleStrictAngle

/-!
# Fixed-step compactness exclusion for the Bone 1 quotient

At unit Sonin scale the complete reverse-intertwining defect is compact for
every fixed prime and suffix.  The renewal-deviation denominator is injective.
Consequently a bounded sequence on the actual source Sonin carrier cannot
make the denominator tend to zero while the fixed-step numerator stays away
from zero.

This leaves open both a rate obstruction at one fixed step and every
non-uniform obstruction in which the prime or suffix varies with the sequence.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFixedStepCompactness

open MeasureTheory
open Filter Function Set Topology
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactApproximateKernel
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentBoundaryResponse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorReverseIntertwining
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelKernel
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRenewalDeviation
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurMarkovPairing
open CCM24SourceProlateTrace
open CCM24UnitScaleProlateAlignment
open CCM24UnitScaleProlateTraceReduction

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable local instance commonBoundaryTwoCopyTopologicalSpace
    (a c : ℝ) : TopologicalSpace
      (WithLp 2
        (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c) ×
          WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c))) :=
  WithLp.instProdTopologicalSpace 2 _ _

private noncomputable def chooseHilbertBasisIndex
    (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] : Set G :=
  Classical.choose (exists_hilbertBasis ℂ G)

private noncomputable def chooseHilbertBasis
    (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] : HilbertBasis (chooseHilbertBasisIndex G) ℂ G :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ G))

/-! ## Injective denominator -/

/-- The normalized renewal-deviation column has trivial kernel, just like the
renewed antiresonant column from Proof 629. -/
theorem suffixEulerFrameRenewalDeviationColumn_injective
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    Function.Injective (suffixEulerFrameRenewalDeviationColumn lambda p S) := by
  intro x y hxy
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one p.property)
  have hq : 0 < ccm24PrimeEulerCoefficient p := by
    unfold ccm24PrimeEulerCoefficient
    exact div_pos zero_lt_one (Real.sqrt_pos.2 hp0)
  have hscale : (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 hq))
  rw [suffixEulerFrameRenewalDeviationColumn_eq_sqrtCoefficient_smul_renewedColumn]
    at hxy
  simp only [ContinuousLinearMap.smul_apply] at hxy
  apply suffixEulerFrameRenewedAntiresonantColumn_injective lambda p S
  rw [← sub_eq_zero]
  apply (smul_eq_zero.mp ?_).resolve_left hscale
  rw [smul_sub, hxy, sub_self]

/-! ## Compact numerator -/

/-- Any Hilbert--Schmidt pair owner for the local raw defect makes the complete
reverse-intertwining defect compact.  The paired reverse transition recovers
the complete defect with only a nonzero scalar rescaling. -/
theorem completeBoundaryReverseIntertwiningDefect_isCompactOperator_of_localPairOwner
    {iota kappa G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (sourceBasis : HilbertBasis iota ℂ (sourceSoninCarrier lambda))
    (targetBasis : HilbertBasis kappa ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (hdata : data.traceProduct =
      suffixActualBandLocalRawDefect owner lambda p S) :
    IsCompactOperator
      (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
        owner lambda p S) := by
  have hlocalAdjoint : IsCompactOperator
      (suffixActualBandLocalRawDefect owner lambda p S).adjoint := by
    rw [← hdata]
    exact data.traceProduct_adjoint_isCompactOperator targetBasis
  have hcofactor :=
    completeBoundaryReverseIntertwiningDefect_comp_transitionAdjoint_eq_neg_localRawDefectAdjoint
      owner lambda p S
  have hcompactCofactor : IsCompactOperator
      (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S ∘L
        (suffixEulerFrameTransition lambda p S).adjoint) := by
    rw [hcofactor]
    exact hlocalAdjoint.neg
  have hcompactScaled : IsCompactOperator
      ((suffixActualBandCompleteBoundaryReverseIntertwiningDefect
            owner lambda p S ∘L
          (suffixEulerFrameTransition lambda p S).adjoint) ∘L
        (suffixEulerFrameReverseTransition lambda p S).adjoint) := by
    simpa only [ContinuousLinearMap.comp_apply, Function.comp_apply] using
      hcompactCofactor.comp_clm
        (suffixEulerFrameReverseTransition lambda p S).adjoint
  have hpair :=
    suffixEulerFrameTransitionAdjoint_comp_reverseTransitionAdjoint_eq_scalar
      lambda p S
  have hscaled :
      (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S ∘L
        (suffixEulerFrameTransition lambda p S).adjoint) ∘L
          (suffixEulerFrameReverseTransition lambda p S).adjoint =
        (primeSchurMarkovScalar p : ℂ) •
          suffixActualBandCompleteBoundaryReverseIntertwiningDefect
            owner lambda p S := by
    rw [ContinuousLinearMap.comp_assoc, hpair]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul]
  rw [hscaled] at hcompactScaled
  have hrho : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  exact (IsCompactOperator.smul_iff₀ hrho).mp hcompactScaled

/-- At unit Sonin scale the existing physical pair data and strict prolate
angle make the complete reverse-intertwining defect unconditionally compact.
-/
theorem suffixActualBandCompleteBoundaryReverseIntertwiningDefect_unit_isCompactOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    IsCompactOperator
      (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
        owner unitSoninScale p S) := by
  classical
  obtain ⟨R0, hR0⟩ := owner.sourceTest.compactSupport.isBounded.exists_norm_le
  let R : ℝ := max R0 0
  have hRnonneg : 0 ≤ R := le_max_right R0 0
  have hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc (-R) R := by
    intro x hx
    have hxtsupport : x ∈ tsupport owner.sourceTest.test :=
      subset_tsupport _ hx
    have habs : |x| ≤ R := by
      simpa only [Real.norm_eq_abs, R] using
        (hR0 x hxtsupport).trans (le_max_left R0 0)
    exact abs_le.mp habs
  have hac : -R ≤ R := by linarith
  let negativeBasis := chooseHilbertBasis
    (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-R) R)))
  let positiveBasis := chooseHilbertBasis
    (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-R) R)))
  let outputBasis := chooseHilbertBasis
    (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-R) R)))
  let reflectedNegativeBasis := chooseHilbertBasis
    (Lp ℂ 2
      (volume : Measure (BoundaryNegativeInputInterval (-R) (-(-R)))))
  let reflectedPositiveBasis := chooseHilbertBasis
    (Lp ℂ 2
      (volume : Measure (BoundaryPositiveInputInterval (-R) (-(-R)))))
  let reflectedOutputBasis := chooseHilbertBasis
    (Lp ℂ 2
      (volume : Measure (BoundaryOutputInterval (-R) (-(-R)))))
  let globalBasis := chooseHilbertBasis finiteSCarrier
  let boundaryBasis := chooseHilbertBasis (commonBoundaryCarrier (-R) R)
  let sourceBasis := chooseHilbertBasis (sourceSoninCarrier unitSoninScale)
  let pairedBoundaryBasis := chooseHilbertBasis
    (WithLp 2
      (commonBoundaryCarrier (-R) R × commonBoundaryCarrier (-R) R))
  let data := suffixActualBandLocalRawDefectPairData owner unitSoninScale p S
    (-R) R hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis pairedBoundaryBasis
    (sourceProlateHilbertSchmidtFactor_unit_summable globalBasis)
  let targetBasis := chooseHilbertBasis
    (WithLp 2
      (WithLp 2
          (commonBoundaryCarrier (-R) R × commonBoundaryCarrier (-R) R) ×
        WithLp 2
          (commonBoundaryCarrier (-R) R × commonBoundaryCarrier (-R) R)))
  exact
    completeBoundaryReverseIntertwiningDefect_isCompactOperator_of_localPairOwner
      owner unitSoninScale p S sourceBasis targetBasis data
        (suffixActualBandLocalRawDefectPairData_traceProduct_eq owner
          unitSoninScale p S (-R) R hac hsupp negativeBasis positiveBasis
          outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis boundaryBasis sourceBasis
          pairedBoundaryBasis
          (sourceProlateHilbertSchmidtFactor_unit_summable globalBasis))

/-! ## Fixed-step exclusion -/

/-- For a fixed `(p,S)`, bounded approximate kernels of the actual renewal
deviation have vanishing complete reverse-intertwining output. -/
theorem completeBoundaryReverseIntertwiningDefect_unit_tendsto_zero_of_renewalDeviation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : ℕ → sourceSoninCarrier unitSoninScale)
    (hbounded : Bornology.IsBounded (Set.range x))
    (hzero : Tendsto
      (fun n ↦ suffixEulerFrameRenewalDeviationColumn
        unitSoninScale p S (x n)) atTop (nhds 0)) :
    Tendsto
      (fun n ↦ suffixActualBandCompleteBoundaryReverseIntertwiningDefect
        owner unitSoninScale p S (x n)) atTop (nhds 0) := by
  exact compact_output_tendsto_zero_of_injective_approximate_kernel
    (suffixEulerFrameRenewalDeviationColumn unitSoninScale p S)
    (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
      owner unitSoninScale p S)
    (suffixEulerFrameRenewalDeviationColumn_injective unitSoninScale p S)
    (suffixActualBandCompleteBoundaryReverseIntertwiningDefect_unit_isCompactOperator
      owner p S)
    x hbounded hzero

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFixedStepCompactness
end CCM25Concrete
end Source
end ConnesWeilRH
