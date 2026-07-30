/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryCorePairSupport

/-!
# Positive Cauchy defect for the radial boundary channel

Proof 691 records the exact positive operator behind the bare radial
boundary crossing.  If

```text
E = radialSupportProjection unitSoninScale
P = newSuffixRangeProjection unitSoninScale S
U = cc20GlobalLogTranslation (log p)
C = (I - E) U P,
```

then

```text
C† C = P - P U† E U P.
```

The module also turns any supplied Hilbert--Schmidt pair `C = A† B` into a
new pair whose trace product is `C† C`.  This is a producer reduction only:
it does not construct the missing pair for the bare radial crossing and does
not provide a finite-S-uniform estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialBoundaryCauchyDefect

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialBoundaryCorePairSupport
open AntiresonantFrameLossRadialBoundaryColumnFullCarrierExtension
open AntiresonantFrameLossRadialBoundaryAdjointSupport
open AntiresonantFrameLossRadialPhysicalOwnerCommonRootPairData
open AntiresonantFrameLossRadialPhysicalOwnerCompression
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

/-! ## A generic Cauchy pair -/

/-- Repackage a pair `A† B` as a pair for the positive operator
`(A† B)† (A† B) = B† (A A†) B`.  The right leg is obtained by bounded
postcomposition, so its Hilbert--Schmidt square sum is inherited from `B`.
-/
noncomputable def cauchyPair
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] {ι : Type*}
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis) :
    BasisHilbertSchmidtPairData (G := G) sourceBasis :=
  { left := data.right
    right := (data.left ∘L data.left.adjoint) ∘L data.right
    left_summable_normSq := data.right_summable_normSq
    right_summable_normSq := summable_normSq_postcomp sourceBasis data.right
      (data.left ∘L data.left.adjoint) data.right_summable_normSq }

/-- The Cauchy pair owns the positive Gram operator exactly. -/
theorem cauchyPair_traceProduct_eq
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] {ι : Type*}
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis) :
    (cauchyPair data).traceProduct =
      data.traceProduct.adjoint ∘L data.traceProduct := by
  change data.right† ∘L
      ((data.left ∘L data.left†) ∘L data.right) =
    (data.left† ∘L data.right)† ∘L
      (data.left† ∘L data.right)
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

/-! ## The radial positive defect -/

/-- The positive Cauchy energy of the bare radial boundary crossing. -/
noncomputable def radialSoninBoundaryCauchyDefect
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (radialSoninBoundaryCrossing p S)† ∘L
    radialSoninBoundaryCrossing p S

/-- The radial boundary energy is the compressed complementary-support
defect `P - P U† E U P`. -/
theorem radialSoninBoundaryCauchyDefect_eq_complementCompression
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    radialSoninBoundaryCauchyDefect p S =
      newSuffixRangeProjection unitSoninScale S -
        newSuffixRangeProjection unitSoninScale S ∘L
          (cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap ∘L
          radialSupportProjection unitSoninScale ∘L
          (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap ∘L
          newSuffixRangeProjection unitSoninScale S := by
  have hR :
      radialComplement unitSoninScale ∘L radialComplement unitSoninScale =
        radialComplement unitSoninScale := by
    simpa only [ContinuousLinearMap.mul_def, radialComplement] using
      (radialSupportProjection_isStarProjection unitSoninScale).one_sub.isIdempotentElem
  have hP := newSuffixRangeProjection_comp_self_eq S
  have hU :
      (cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap ∘L
          (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ finiteSCarrier := by
    apply ContinuousLinearMap.ext
    intro u
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, neg_neg] using
      (cc20GlobalLogTranslation_neg_apply (-Real.log p) u)
  apply ContinuousLinearMap.ext
  intro u
  rw [radialSoninBoundaryCauchyDefect, radialSoninBoundaryCrossing_adjoint_eq_reverse]
  simp only [ContinuousLinearMap.comp_apply, radialSoninBoundaryCrossing]
  have hR' := DFunLike.congr_fun hR
    ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
      (newSuffixRangeProjection unitSoninScale S u))
  have hP' := DFunLike.congr_fun hP u
  have hU' := DFunLike.congr_fun hU
    (newSuffixRangeProjection unitSoninScale S u)
  simp only [ContinuousLinearMap.comp_apply] at hR' hP' hU'
  simp only [ContinuousLinearMap.id_apply] at hU'
  rw [hR']
  simp only [radialComplement, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  rw [hU']
  rw [hP']
  simp only [ContinuousLinearMap.comp_apply]

/-- The Cauchy defect is positive because it is an adjoint-composition square.
-/
theorem radialSoninBoundaryCauchyDefect_isPositive
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    ContinuousLinearMap.IsPositive (radialSoninBoundaryCauchyDefect p S) := by
  exact ContinuousLinearMap.isPositive_adjoint_comp_self
    (radialSoninBoundaryCrossing p S)

/-! ## Conditional transfer from a boundary pair -/

/-- Any supplied boundary pair yields a Hilbert--Schmidt pair for the positive
Cauchy defect.  The missing boundary pair itself is intentionally left as a
source premise. -/
noncomputable def RadialSignedPhysicalOwnerPairData.boundaryCauchyPair
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (data : RadialSignedPhysicalOwnerPairData
      (K := K) (G := G) p family sourceBasis) :
    BasisHilbertSchmidtPairData (G := G) sourceBasis :=
  cauchyPair data.boundaryData

theorem RadialSignedPhysicalOwnerPairData.boundaryCauchyPair_traceProduct_eq
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (data : RadialSignedPhysicalOwnerPairData
      (K := K) (G := G) p family sourceBasis) :
    (boundaryCauchyPair data).traceProduct =
      (data.boundaryData.traceProduct).adjoint ∘L
        data.boundaryData.traceProduct := by
  exact cauchyPair_traceProduct_eq data.boundaryData

theorem RadialSignedPhysicalOwnerPairData.boundaryCauchyPair_traceProduct_eq_defect
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (data : RadialSignedPhysicalOwnerPairData
      (K := K) (G := G) p family sourceBasis) :
    (boundaryCauchyPair data).traceProduct =
      radialSoninBoundaryCauchyDefect p family.visiblePrimes := by
  rw [boundaryCauchyPair_traceProduct_eq data,
    data.boundary_traceProduct_eq,
    radialSoninBoundaryCauchyDefect]

end AntiresonantFrameLossRadialBoundaryCauchyDefect
end CCM25Concrete
end Source
end ConnesWeilRH
