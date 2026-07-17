/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.PositiveTrace

/-!
# Hilbert--Schmidt ideal calculus for named bases

The project represents trace-class operators by two Hilbert--Schmidt factors
with a named source basis.  This module proves that bounded precomposition and
postcomposition preserve that summability, then transports a complete
`A^dagger B` trace-product owner through arbitrary bounded left and right
factors.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace PositiveTrace

open scoped InnerProduct InnerProductSpace

variable {H G K L : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

omit [CompleteSpace H] [CompleteSpace G] [CompleteSpace K] in
/-- Hilbert--Schmidt basis summability is preserved by bounded
postcomposition. -/
theorem summable_normSq_postcomp
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (operator : H →L[ℂ] G) (bounded : G →L[ℂ] K)
    (hoperator : Summable fun i => ‖operator (basis i)‖ ^ 2) :
    Summable fun i => ‖(bounded ∘L operator) (basis i)‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun i => sq_nonneg ‖(bounded ∘L operator) (basis i)‖)
    (fun i => ?_)
    (hoperator.mul_left (‖bounded‖ ^ 2))
  rw [ContinuousLinearMap.comp_apply]
  calc
    ‖bounded (operator (basis i))‖ ^ 2 ≤
        (‖bounded‖ * ‖operator (basis i)‖) ^ 2 := by
      gcongr
      exact bounded.le_opNorm (operator (basis i))
    _ = ‖bounded‖ ^ 2 * ‖operator (basis i)‖ ^ 2 := by ring

/-- Hilbert--Schmidt basis summability is preserved by bounded
precomposition.  The proof passes to the adjoint, where precomposition
becomes postcomposition, and then returns to the requested source basis. -/
theorem summable_normSq_precomp
    {ι κ ν : Type*}
    (sourceBasis : HilbertBasis ι ℂ H)
    (targetBasis : HilbertBasis κ ℂ G)
    (newSourceBasis : HilbertBasis ν ℂ K)
    (operator : H →L[ℂ] G) (bounded : K →L[ℂ] H)
    (hoperator : Summable fun i => ‖operator (sourceBasis i)‖ ^ 2) :
    Summable fun k => ‖(operator ∘L bounded) (newSourceBasis k)‖ ^ 2 := by
  have hadjoint : Summable fun j =>
      ‖operator.adjoint (targetBasis j)‖ ^ 2 :=
    BasisHilbertSchmidtPairData.summable_adjoint_normSq
      sourceBasis targetBasis operator hoperator
  have hpost : Summable fun j =>
      ‖(bounded.adjoint ∘L operator.adjoint) (targetBasis j)‖ ^ 2 :=
    summable_normSq_postcomp targetBasis operator.adjoint bounded.adjoint
      hadjoint
  have hreturn :=
    BasisHilbertSchmidtPairData.summable_adjoint_normSq
      targetBasis newSourceBasis
      (bounded.adjoint ∘L operator.adjoint) hpost
  simpa only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint] using hreturn

omit [CompleteSpace H] [CompleteSpace G] in
/-- The sum of two Hilbert--Schmidt factors is Hilbert--Schmidt in the same
named basis.  This is the analytic step used to recombine signed boundary
branches before taking a trace. -/
theorem summable_normSq_add
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (left right : H →L[ℂ] G)
    (hleft : Summable fun i => ‖left (basis i)‖ ^ 2)
    (hright : Summable fun i => ‖right (basis i)‖ ^ 2) :
    Summable fun i => ‖(left + right) (basis i)‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun i => sq_nonneg ‖(left + right) (basis i)‖)
    (fun i => ?_)
    ((hleft.add hright).mul_left 2)
  rw [ContinuousLinearMap.add_apply]
  calc
    ‖left (basis i) + right (basis i)‖ ^ 2 ≤
        (‖left (basis i)‖ + ‖right (basis i)‖) ^ 2 := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 2 * (‖left (basis i)‖ ^ 2 +
        ‖right (basis i)‖ ^ 2) := by
      nlinarith [sq_nonneg (‖left (basis i)‖ - ‖right (basis i)‖)]

omit [CompleteSpace H] in
/-- Named-basis trace legality is closed under subtraction without rewriting
through a scalar action. -/
theorem isTraceClassAlong_sub
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (left right : H →L[ℂ] H)
    (hleft : IsTraceClassAlong basis left)
    (hright : IsTraceClassAlong basis right) :
    IsTraceClassAlong basis (left - right) := by
  rw [IsTraceClassAlong] at hleft hright ⊢
  simpa only [ContinuousLinearMap.sub_apply, inner_sub_right] using
    hleft.sub hright

omit [CompleteSpace H] in
/-- The ordinary named-basis trace is additive across subtraction when both
diagonal series are summable. -/
theorem ordinaryTraceAlong_sub
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (left right : H →L[ℂ] H)
    (hleft : IsTraceClassAlong basis left)
    (hright : IsTraceClassAlong basis right) :
    ordinaryTraceAlong basis (left - right) =
      ordinaryTraceAlong basis left - ordinaryTraceAlong basis right := by
  rw [ordinaryTraceAlong, ordinaryTraceAlong, ordinaryTraceAlong]
  rw [IsTraceClassAlong] at hleft hright
  simpa only [ContinuousLinearMap.sub_apply, inner_sub_right] using
    hleft.tsum_sub hright

namespace BasisHilbertSchmidtPairData

/-- Swap the two Hilbert--Schmidt legs.  The resulting trace product is the
Hilbert-space adjoint of the original product. -/
noncomputable def swap
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis) :
    BasisHilbertSchmidtPairData (G := G) sourceBasis where
  left := data.right
  right := data.left
  left_summable_normSq := data.right_summable_normSq
  right_summable_normSq := data.left_summable_normSq

theorem swap_traceProduct_eq_adjoint
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis) :
    data.swap.traceProduct = data.traceProduct.adjoint := by
  unfold swap traceProduct
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- Multiply the right Hilbert--Schmidt leg by a scalar without changing the
factor space or the named source basis. -/
noncomputable def smulRight
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (scalar : ℂ) :
    BasisHilbertSchmidtPairData (G := G) sourceBasis where
  left := data.left
  right := scalar • data.right
  left_summable_normSq := data.left_summable_normSq
  right_summable_normSq := by
    simpa only [ContinuousLinearMap.smul_apply, norm_smul, mul_pow] using
      data.right_summable_normSq.mul_left (‖scalar‖ ^ 2)

theorem smulRight_traceProduct_eq
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (scalar : ℂ) :
    (data.smulRight scalar).traceProduct = scalar • data.traceProduct := by
  unfold smulRight traceProduct
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul]

/-- Recombine two pair owners that have the same left leg.  The signed or
weighted cancellation remains inside the single right factor. -/
noncomputable def addOfLeftEq
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (first second : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (_hleft : first.left = second.left) :
    BasisHilbertSchmidtPairData (G := G) sourceBasis where
  left := first.left
  right := first.right + second.right
  left_summable_normSq := first.left_summable_normSq
  right_summable_normSq := summable_normSq_add sourceBasis
    first.right second.right first.right_summable_normSq
      second.right_summable_normSq

theorem addOfLeftEq_traceProduct_eq
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (first second : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (hleft : first.left = second.left) :
    (first.addOfLeftEq second hleft).traceProduct =
      first.traceProduct + second.traceProduct := by
  unfold addOfLeftEq traceProduct
  rw [← hleft]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add]

/-- Subtraction is addition after retaining the minus sign inside the shared
Hilbert--Schmidt right leg. -/
noncomputable def subOfLeftEq
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (first second : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (hleft : first.left = second.left) :
    BasisHilbertSchmidtPairData (G := G) sourceBasis :=
  first.addOfLeftEq (second.smulRight (-1)) (by simpa using hleft)

theorem subOfLeftEq_traceProduct_eq
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (first second : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (hleft : first.left = second.left) :
    (first.subOfLeftEq second hleft).traceProduct =
      first.traceProduct - second.traceProduct := by
  rw [subOfLeftEq, addOfLeftEq_traceProduct_eq,
    smulRight_traceProduct_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.add_apply,
    neg_smul, one_smul, sub_eq_add_neg]

/-- Push a complete Hilbert--Schmidt pair through bounded left and right
operators while retaining one same-object trace-product owner. -/
noncomputable def boundedSandwich
    {ι κ : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (leftBounded rightBounded : H →L[ℂ] H) :
    BasisHilbertSchmidtPairData (G := G) sourceBasis where
  left := data.left ∘L leftBounded.adjoint
  right := data.right ∘L rightBounded
  left_summable_normSq :=
    summable_normSq_precomp sourceBasis targetBasis sourceBasis
      data.left leftBounded.adjoint data.left_summable_normSq
  right_summable_normSq :=
    summable_normSq_precomp sourceBasis targetBasis sourceBasis
      data.right rightBounded data.right_summable_normSq

/-- The transported pair really owns the bounded sandwich of the original
trace product. -/
theorem boundedSandwich_traceProduct_eq
    {ι κ : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (leftBounded rightBounded : H →L[ℂ] H) :
    (data.boundedSandwich targetBasis leftBounded rightBounded).traceProduct =
      leftBounded ∘L data.traceProduct ∘L rightBounded := by
  unfold boundedSandwich traceProduct
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- Any bounded sandwich of a pair-owned trace product has a summable
diagonal in the same named source basis. -/
theorem boundedSandwich_isTraceClassAlong
    {ι κ : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (leftBounded rightBounded : H →L[ℂ] H) :
    IsTraceClassAlong sourceBasis
      (leftBounded ∘L data.traceProduct ∘L rightBounded) := by
  rw [← data.boundedSandwich_traceProduct_eq
    targetBasis leftBounded rightBounded]
  exact (data.boundedSandwich targetBasis leftBounded rightBounded)
    |>.traceProduct_isTraceClassAlong

end BasisHilbertSchmidtPairData
end PositiveTrace
end CC20Concrete
end Source
end ConnesWeilRH
