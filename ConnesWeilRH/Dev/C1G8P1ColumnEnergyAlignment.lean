/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8P1SchurBoundaryAntiresonantFactorization
import ConnesWeilRH.Dev.C1G8P1RadialCommutatorChannelLedger
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace

/-!
# G8 P1 column energy alignment

Both P1 boundary channels eat the same composite input

```text
B(p,S) = antiresonantColumn ∘L newFrame† ∘L oldFrame,
```

up to the two closed channel constants `√q_p` (metric side) and
`32 ‖q_p⁻¹‖` (radial side).  This record aligns their energies: from the
single full-carrier column-energy premise of the radial energy transport,

```text
∑_i ‖antiresonantColumn(newFrame† u_i)‖² < ∞   along any carrier basis,
```

it deduces

* summability of the metric boundary composite basis energy
  `∑_j ‖B b_j‖²` along any source basis `{b_j}`,
* the same-input radial ledger `‖radial(oldFrame x)‖ ≤ 32 ‖q_p⁻¹‖ ‖B x‖`,
  hence summability of `∑_j ‖radial(oldFrame b_j)‖²`,
* an explicit owning pair for the positive boundary energy operator
  `B† B`, trace-class along the source basis.

The engine is a generic two-line lemma: Hilbert-Schmidt summability
survives precomposition with a contraction, obtained by applying the
existing adjoint-summability theorem twice (`C` HS along `{u_i}` gives
`C†` HS along `{u_i}`; the composite adjoint `pull† ∘L C†` is then
dominated pointwise because `‖pull‖ ≤ 1`, and a second application
reads the result on any source basis).

This is an energy alignment only.  The full-carrier column-energy
premise is NOT proved here — it is the shared analytic input carried
open by the radial energy transport record.  No vanishing, no sign, and
no RH-facing claim is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1ColumnEnergyAlignment

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryColumnBridge
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryColumnFullCarrierExtension
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryCauchyPairProducer
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryCauchyDefect
open CCM25Concrete.AntiresonantFrameLossRadialBoundarySplit
open CCM25Concrete.AntiresonantFrameLossCommutator
open CCM25Concrete.CCM24FiniteSActualSchurCascade
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM25Concrete.CCM24FiniteSFrameGramCalculus
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSFixedSourcePolar
open CCM25Concrete.CCM24FiniteSJuliaCausal
open CCM25Concrete.CCM24UnitScaleProlateAlignment
open C1G8P1SchurBoundaryAntiresonantFactorization
open C1G8P1RadialCommutatorChannelLedger

/-- Local copy of the source-carrier completeness instance (the Schur
cascade declares it `local`, so it is not exported). -/
noncomputable local instance sourceSoninCarrierCompleteSpaceColumnEnergy
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Generic engine: Hilbert-Schmidt survives a contractive pull -/

/-- Hilbert-Schmidt summability is preserved under precomposition with a
contraction.  The proof applies the existing adjoint-summability theorem
twice and never touches a Fubini exchange directly. -/
theorem summable_comp_normSq_of_contractive_pull
    {ι κ H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (sourceBasis : HilbertBasis κ ℂ H₁) (carrierBasis : HilbertBasis ι ℂ H₂)
    (pull : H₁ →L[ℂ] H₂) (hpull : ‖pull‖ ≤ 1)
    (column : H₂ →L[ℂ] H₂)
    (hcolumn : Summable fun i => ‖column (carrierBasis i)‖ ^ 2) :
    Summable fun j => ‖(column ∘L pull) (sourceBasis j)‖ ^ 2 := by
  have hCadj : Summable fun i => ‖column.adjoint (carrierBasis i)‖ ^ 2 :=
    BasisHilbertSchmidtPairData.summable_adjoint_normSq carrierBasis
      carrierBasis column hcolumn
  have hDadj : Summable fun i =>
      ‖(column ∘L pull).adjoint (carrierBasis i)‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) hCadj
    rw [ContinuousLinearMap.adjoint_comp]
    simp only [ContinuousLinearMap.comp_apply]
    have h2 : ‖pull.adjoint (column.adjoint (carrierBasis i))‖
        ≤ ‖column.adjoint (carrierBasis i)‖ := by
      have h1 : ‖pull.adjoint (column.adjoint (carrierBasis i))‖
          ≤ ‖pull‖ * ‖column.adjoint (carrierBasis i)‖ := by
        refine le_trans
          (ContinuousLinearMap.le_opNorm pull.adjoint
            (column.adjoint (carrierBasis i))) ?_
        rw [ContinuousLinearMap.adjoint.norm_map]
      calc ‖pull.adjoint (column.adjoint (carrierBasis i))‖
          ≤ ‖pull‖ * ‖column.adjoint (carrierBasis i)‖ := h1
        _ ≤ 1 * ‖column.adjoint (carrierBasis i)‖ :=
            mul_le_mul_of_nonneg_right hpull (norm_nonneg _)
        _ = ‖column.adjoint (carrierBasis i)‖ := one_mul _
    exact sq_le_sq'
      (by linarith [norm_nonneg (column.adjoint (carrierBasis i)),
        norm_nonneg (pull.adjoint (column.adjoint (carrierBasis i)))]) h2
  have hfinal := BasisHilbertSchmidtPairData.summable_adjoint_normSq carrierBasis
    sourceBasis ((column ∘L pull).adjoint) hDadj
  rw [ContinuousLinearMap.adjoint_adjoint] at hfinal
  exact hfinal

/-! ## Metric boundary composite energy from the full-carrier premise -/

/-- The metric boundary composite
`antiresonantColumn ∘L newFrame† ∘L oldFrame` has summable basis energy
along any source basis, conditional on the same full-carrier column-energy
premise as the radial side. -/
theorem summable_metricBoundaryComposite_normSq_of_fullCarrierColumnEnergy
    {ι κ : Type*}
    (sourceBasis : HilbertBasis κ ℂ (sourceSoninCarrier unitSoninScale))
    (carrierBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcolumn : Summable fun i =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (carrierBasis i))‖ ^ 2) :
    Summable fun j =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ ^ 2 := by
  refine Summable.congr
    (summable_comp_normSq_of_contractive_pull sourceBasis carrierBasis
      (oldSuffixFrame unitSoninScale p S) (norm_oldSuffixFrame_le_one p S)
      (newFrameAntiresonantColumn unitSoninScale p S ∘L
        ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S))
      hcolumn) (fun j => ?_)
  rfl

/-! ## Same-input radial ledger -/

/-- The radial boundary channel evaluated on the old-frame image of a
source vector costs at most the canonical `32 ‖q_p⁻¹‖` times the metric
boundary composite norm at the same input. -/
theorem norm_radialSoninBoundaryCrossing_apply_oldSuffixFrame_le
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier unitSoninScale) :
    ‖radialSoninBoundaryCrossing p S
        (oldSuffixFrame unitSoninScale p S x)‖ ≤
      (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) *
        ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
            (oldSuffixFrame unitSoninScale p S x))‖ :=
  norm_radialSoninBoundaryCrossing_apply_le_canonical_antiresonantColumn
    p S _

/-- The radial crossing composed with the old frame has summable basis
energy along any source basis, from the same full-carrier premise. -/
theorem summable_radialCrossingAfterOldFrame_normSq_of_fullCarrierColumnEnergy
    {ι κ : Type*}
    (sourceBasis : HilbertBasis κ ℂ (sourceSoninCarrier unitSoninScale))
    (carrierBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcolumn : Summable fun i =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (carrierBasis i))‖ ^ 2) :
    Summable fun j =>
      ‖radialSoninBoundaryCrossing p S
        (oldSuffixFrame unitSoninScale p S (sourceBasis j))‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
    (Summable.mul_left ((32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2)
      (summable_metricBoundaryComposite_normSq_of_fullCarrierColumnEnergy
        sourceBasis carrierBasis p S hcolumn))
  have h := norm_radialSoninBoundaryCrossing_apply_oldSuffixFrame_le p S
    (sourceBasis j)
  have hA : 0 ≤ ‖radialSoninBoundaryCrossing p S
      (oldSuffixFrame unitSoninScale p S (sourceBasis j))‖ :=
    norm_nonneg _
  have hB : 0 ≤ (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) *
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ :=
    mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _)
  calc ‖radialSoninBoundaryCrossing p S
        (oldSuffixFrame unitSoninScale p S (sourceBasis j))‖ ^ 2
      ≤ ((32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) *
          ‖newFrameAntiresonantColumn unitSoninScale p S
            (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
              (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖) ^ 2 :=
        sq_le_sq' (by linarith) h
    _ = (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2 *
        ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
            (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ ^ 2 := by
        ring

/-! ## Owning pair for the positive boundary energy operator -/

/-- The positive metric boundary energy operator `B† B`. -/
noncomputable def metricBoundaryColumnEnergyOperator
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier unitSoninScale →L[ℂ] sourceSoninCarrier unitSoninScale :=
  ContinuousLinearMap.adjoint
      (newFrameAntiresonantColumn unitSoninScale p S ∘L
        ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) ∘L
          oldSuffixFrame unitSoninScale p S) ∘L
    (newFrameAntiresonantColumn unitSoninScale p S ∘L
      ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) ∘L
        oldSuffixFrame unitSoninScale p S)

/-- The metric boundary pair with two equal legs `B`. -/
noncomputable def metricBoundaryCauchyPairData
    {ι κ : Type*}
    (sourceBasis : HilbertBasis κ ℂ (sourceSoninCarrier unitSoninScale))
    (carrierBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcolumn : Summable fun i =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (carrierBasis i))‖ ^ 2) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) sourceBasis :=
  { left := newFrameAntiresonantColumn unitSoninScale p S ∘L
      ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) ∘L
        oldSuffixFrame unitSoninScale p S
    right := newFrameAntiresonantColumn unitSoninScale p S ∘L
      ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) ∘L
        oldSuffixFrame unitSoninScale p S
    left_summable_normSq :=
      summable_metricBoundaryComposite_normSq_of_fullCarrierColumnEnergy
        sourceBasis carrierBasis p S hcolumn
    right_summable_normSq :=
      summable_metricBoundaryComposite_normSq_of_fullCarrierColumnEnergy
        sourceBasis carrierBasis p S hcolumn }

/-- The pair's trace product is exactly the positive boundary energy
operator. -/
theorem metricBoundaryCauchyPairData_traceProduct_eq_energyOperator
    {ι κ : Type*}
    (sourceBasis : HilbertBasis κ ℂ (sourceSoninCarrier unitSoninScale))
    (carrierBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcolumn : Summable fun i =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (carrierBasis i))‖ ^ 2) :
    (metricBoundaryCauchyPairData sourceBasis carrierBasis p S hcolumn).traceProduct =
      metricBoundaryColumnEnergyOperator p S := by
  rfl

/-- The positive metric boundary energy operator is trace-class along the
source basis, conditional on the single full-carrier column-energy
premise. -/
theorem metricBoundaryColumnEnergyOperator_isTraceClassAlong
    {ι κ : Type*}
    (sourceBasis : HilbertBasis κ ℂ (sourceSoninCarrier unitSoninScale))
    (carrierBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcolumn : Summable fun i =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (carrierBasis i))‖ ^ 2) :
    IsTraceClassAlong sourceBasis
      (metricBoundaryColumnEnergyOperator p S) := by
  rw [← metricBoundaryCauchyPairData_traceProduct_eq_energyOperator
    sourceBasis carrierBasis p S hcolumn]
  exact (metricBoundaryCauchyPairData sourceBasis carrierBasis p S
    hcolumn).traceProduct_isTraceClassAlong

end C1G8P1ColumnEnergyAlignment
end Source
end ConnesWeilRH
