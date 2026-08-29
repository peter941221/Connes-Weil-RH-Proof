/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Stage3ProjectionResponseBridge

/-!
# C1 projection-square order guard

The active Stage-3 kernel is not merely positive.  It is a positive
contraction:

```text
0 <= K_S <= I.
```

The upper bound is structural.  `K_S` is the positive difference between a
compression of two orthogonal projections and the target Sonin projection.
It prevents a cutoff finite part obtained by subtracting the identity bulk
from inheriting its sign from `K_S >= 0` alone.

This file proves only the operator-order fact.  It makes no trace, cutoff,
finite-part, or RH assertion.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1ProjectionSquareOrderGuard

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open C1Stage3ProjectionKernel
open C1Stage3ProjectionResponseBridge
open C1PositiveTraceWindowProducer
open MeasureTheory

noncomputable section

abbrev projectionCarrier := cc20GlobalLogCrossingL2

/-- The Stage-3 projection-square kernel is bounded above by the identity in
the Loewner order on bounded operators. -/
theorem stage3ProjectionKernel_le_id
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    stage3ProjectionKernel lambda S <=
      ContinuousLinearMap.id Complex projectionCarrier := by
  let E : projectionCarrier →L[ℂ] projectionCarrier :=
    (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
  let Q : projectionCarrier →L[ℂ] projectionCarrier :=
    (ccm24SemilocalFourierSupportClosedSubspace lambda S).toSubmodule.starProjection
  let R : projectionCarrier →L[ℂ] projectionCarrier :=
    (concreteCCM24SoninTransportData lambda S).gramCorrectedTargetSoninProjection
  have hE : IsStarProjection E := by
    dsimp [E]
    exact isStarProjection_starProjection
  have hQ : IsStarProjection Q := by
    dsimp [Q]
    exact isStarProjection_starProjection
  have hR : R.IsPositive := by
    dsimp [R]
    exact ContinuousLinearMap.IsPositive.of_isStarProjection
      (concreteCCM24SoninTransportData lambda S).gramCorrectedTargetSoninProjection_isStarProjection
  have hKernel : stage3ProjectionKernel lambda S = E ∘L Q ∘L E - R := by
    rfl
  have hEadj : ContinuousLinearMap.adjoint E = E :=
    hE.isSelfAdjoint.adjoint_eq
  have hEE : E ∘L E = E := by
    change E * E = E
    exact hE.isIdempotentElem
  have hKernel_le_compression : stage3ProjectionKernel lambda S <= E ∘L Q ∘L E := by
    rw [ContinuousLinearMap.le_def, hKernel]
    have hcancel : E ∘L Q ∘L E - (E ∘L Q ∘L E - R) = R := by
      abel
    rw [hcancel]
    exact hR
  have hQcomplement :
      (ContinuousLinearMap.id Complex projectionCarrier - Q).IsPositive := by
    exact ContinuousLinearMap.IsPositive.of_isStarProjection hQ.one_sub
  have hCompression_complement :
      E ∘L (ContinuousLinearMap.id ℂ projectionCarrier - Q) ∘L E =
        E - E ∘L Q ∘L E := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply]
    rw [map_sub]
    have hEE_apply : E (E x) = E x := by
      change (E ∘L E) x = E x
      rw [hEE]
    rw [hEE_apply]
  have hCompression_le_E : E ∘L Q ∘L E <= E := by
    rw [ContinuousLinearMap.le_def]
    have hpositive := hQcomplement.adjoint_conj E
    rw [hEadj] at hpositive
    rwa [hCompression_complement] at hpositive
  have hE_le_id : E <= ContinuousLinearMap.id Complex projectionCarrier := by
    rw [ContinuousLinearMap.le_def]
    exact ContinuousLinearMap.IsPositive.of_isStarProjection hE.one_sub
  exact hKernel_le_compression.trans (hCompression_le_E.trans hE_le_id)

/-- Equivalently, the complement of the Stage-3 kernel is positive. -/
theorem stage3ProjectionKernel_complement_isPositive
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (ContinuousLinearMap.id Complex projectionCarrier -
      stage3ProjectionKernel lambda S).IsPositive := by
  exact (ContinuousLinearMap.le_def _ _).mp
    (stage3ProjectionKernel_le_id lambda S)

/-- Compressing the positive contraction to a finite output window remains a
positive contraction. -/
theorem outputCompressedStage3Kernel_le_id
    (a c : Real) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    outputCompressedStage3Kernel a c lambda S <=
      ContinuousLinearMap.id Complex
        (Lp Complex 2 (volume : Measure (BoundaryOutputInterval a c))) := by
  let Z := fullBoundaryOutputZeroExtension a c
  have hcomplement := stage3ProjectionKernel_complement_isPositive lambda S
  have hpositive := hcomplement.adjoint_conj Z
  have hrewrite :
      Z.adjoint ∘L
          (ContinuousLinearMap.id Complex projectionCarrier -
            stage3ProjectionKernel lambda S) ∘L Z =
        ContinuousLinearMap.id Complex
          (Lp Complex 2 (volume : Measure (BoundaryOutputInterval a c))) -
          outputCompressedStage3Kernel a c lambda S := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply]
    rw [map_sub]
    have hZ : Z.adjoint (Z u) = u := by
      rw [← ContinuousLinearMap.comp_apply,
        fullBoundaryOutputZeroExtension_adjoint_comp,
        ContinuousLinearMap.id_apply]
    rw [hZ]
    change u - Z.adjoint (stage3ProjectionKernel lambda S (Z u)) =
      u - Z.adjoint (stage3ProjectionKernel lambda S (Z u))
    rfl
  rw [ContinuousLinearMap.le_def]
  rw [← hrewrite]
  exact hpositive

/-- The first Stage-3 defect has the fixed nonpositive sign.  Thus it cannot
be used as a positive correction after subtracting the identity bulk. -/
theorem kernelInsertionDefect_le_zero
    (a c : Real) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    kernelInsertionDefect a c lambda S <= 0 := by
  have hcompression := outputCompressedStage3Kernel_le_id a c lambda S
  rw [ContinuousLinearMap.le_def] at hcompression ⊢
  simpa only [kernelInsertionDefect, zero_sub, neg_sub] using hcompression

end

end C1ProjectionSquareOrderGuard
end Dev
end Source
end ConnesWeilRH
