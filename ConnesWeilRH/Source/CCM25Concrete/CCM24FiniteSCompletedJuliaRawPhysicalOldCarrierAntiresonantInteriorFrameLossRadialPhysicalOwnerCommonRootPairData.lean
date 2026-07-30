/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerRootSandwichFiniteSEndpointAlignment
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair

/-!
# Pair-data producer for the signed radial owner

Proof 683 packages the exact source premises needed to turn the finite-S
signed radial owner into one common `A†B` pair.  One pair owns the positive
three-branch term and a second pair owns the radial boundary term; `l2Sum`
places their signed sum in orthogonal coordinates before any root estimate.

The boundary pair is deliberately an explicit field.  The existing radial
boundary transport owns compact detector crossings, not the bare positive
translation channel, so this module does not manufacture that field.  The
resulting common-root producer inherits the bookkeeping Julia row from
`commonRootS2ProducerOfPairData`; it is an ownership bridge, not a Gate 3U
producer.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialPhysicalOwnerCommonRootPairData

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialPhysicalOwner
open AntiresonantFrameLossRadialPhysicalOwnerRootSandwich
open AntiresonantFrameLossRadialPhysicalOwnerFiniteSEndpointAlignment
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

noncomputable def targetThreeBranch
    (p : CCM24VisiblePrime) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  cc20ThreeBranchCommutator
    (radialSupportProjection unitSoninScale)
    (targetFourierSupportProjection unitSoninScale family)
    (targetProlateRemainder unitSoninScale family)
    (radialCompressedPositiveTranslation p)

/-! ## The two source pair premises -/

/-- Pair-data premises for the two signed channels of the finite-S radial
owner.  The first trace product is the positive three-branch commutator; the
minus sign is inserted only when the two coordinates are packed. -/
structure RadialSignedPhysicalOwnerPairData
    (p : CCM24VisiblePrime) (family : FinitePrimePowerFamily)
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ finiteSCarrier) where
  threeBranchData : BasisHilbertSchmidtPairData
    (G := K) sourceBasis
  boundaryData : BasisHilbertSchmidtPairData
    (G := G) sourceBasis
  threeBranch_traceProduct_eq :
    threeBranchData.traceProduct = targetThreeBranch p family
  boundary_traceProduct_eq :
    boundaryData.traceProduct =
      radialSoninBoundaryCrossing p family.visiblePrimes

/-! ## Orthogonal signed packing -/

/-- The signed two-channel pair, with the negative three-branch term and the
positive radial boundary term kept in orthogonal `L2` coordinates. -/
noncomputable def RadialSignedPhysicalOwnerPairData.signedPairData
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (data : RadialSignedPhysicalOwnerPairData
      (K := K) (G := G) p family sourceBasis) :
    BasisHilbertSchmidtPairData
      (G := WithLp 2 (K × G)) sourceBasis :=
  let first := data.threeBranchData.smulRight (-1)
  let second := data.boundaryData
  { left :=
      (WithLp.prodContinuousLinearEquiv 2 ℂ K G).symm.toContinuousLinearMap ∘L
        first.left.prod second.left
    right :=
      (WithLp.prodContinuousLinearEquiv 2 ℂ K G).symm.toContinuousLinearMap ∘L
        first.right.prod second.right
    left_summable_normSq := by
      apply (first.left_summable_normSq.add second.left_summable_normSq).congr
      intro i
      change ‖first.left (sourceBasis i)‖ ^ 2 +
          ‖second.left (sourceBasis i)‖ ^ 2 =
        ‖WithLp.toLp 2
          (first.left (sourceBasis i), second.left (sourceBasis i))‖ ^ 2
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp
    right_summable_normSq := by
      apply (first.right_summable_normSq.add second.right_summable_normSq).congr
      intro i
      change ‖first.right (sourceBasis i)‖ ^ 2 +
          ‖second.right (sourceBasis i)‖ ^ 2 =
        ‖WithLp.toLp 2
          (first.right (sourceBasis i), second.right (sourceBasis i))‖ ^ 2
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp }

/-- The packed pair owns the complete signed radial owner exactly. -/
theorem RadialSignedPhysicalOwnerPairData.signedPairData_traceProduct_eq_owner
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (data : RadialSignedPhysicalOwnerPairData
      (K := K) (G := G) p family sourceBasis) :
    data.signedPairData.traceProduct =
      radialSignedPhysicalOwner p family.visiblePrimes := by
  let first := data.threeBranchData.smulRight (-1)
  let second := data.boundaryData
  have htrace : data.signedPairData.traceProduct =
      first.traceProduct + second.traceProduct := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    unfold RadialSignedPhysicalOwnerPairData.signedPairData
      BasisHilbertSchmidtPairData.traceProduct
    simp [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, WithLp.prod_inner_apply]
    rw [inner_add_right, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_right]
  rw [htrace, BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    data.threeBranch_traceProduct_eq, data.boundary_traceProduct_eq]
  simpa only [neg_one_smul, targetThreeBranch] using
    (radialSignedPhysicalOwner_one_eq_targetThreeBranch_add_boundary
      p family).symm

/-! ## Common-root construction after a bounded sandwich -/

/-- A pair-data owner yields the common-root producer used by Proof 680 once
the target Hilbert basis for the packed coordinate is supplied.  The boundary
pair equality remains a real source premise; no estimate is inferred here. -/
noncomputable def radialSignedOwnerRootS2ProducerOfPairData
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι κ K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (data : RadialSignedPhysicalOwnerPairData
      (K := K) (G := G) p family sourceBasis)
    (targetBasis : HilbertBasis κ ℂ (WithLp 2 (K × G)))
    (leftSandwich rightSandwich : finiteSCarrier →L[ℂ] finiteSCarrier) :
    RadialSignedOwnerRootS2Producer
      (K := WithLp 2 (WithLp 2 (K × G) × WithLp 2 (K × G)))
      (G := WithLp 2 (WithLp 2 (K × G) × WithLp 2 (K × G))) sourceBasis := by
  let sandwiched := BasisHilbertSchmidtPairData.boundedSandwich
    (H := finiteSCarrier) (G := WithLp 2 (K × G)) targetBasis
    data.signedPairData leftSandwich rightSandwich
  let base := commonRootS2ProducerOfPairData
    (H := finiteSCarrier) (G := WithLp 2 (K × G)) sandwiched
  refine
    { p := p
      S := family.visiblePrimes
      base := base
      leftSandwich := leftSandwich
      rightSandwich := rightSandwich
      response_eq_owner := ?_ }
  rw [show base.response = sandwiched.traceProduct by
      exact commonRootS2ProducerOfPairData_response_eq sandwiched,
    BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
    data.signedPairData_traceProduct_eq_owner]

end AntiresonantFrameLossRadialPhysicalOwnerCommonRootPairData
end CCM25Concrete
end Source
end ConnesWeilRH
