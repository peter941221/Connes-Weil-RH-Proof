/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

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

/-!
The preceding theorem gives only summability.  For the normalized causal
owner we also need the quantitative ideal inequality: precomposition by a
bounded map costs at most its operator norm in Hilbert--Schmidt energy.

The proof deliberately changes basis through the legal `A†A`/`AA†` trace
cycle.  A pointwise estimate on the original source basis would be false in
general; the basis change is the step that preserves the full square sum.
-/
theorem tsum_normSq_precomp_le
    {ι κ ν : Type*}
    (sourceBasis : HilbertBasis ι ℂ H)
    (targetBasis : HilbertBasis κ ℂ G)
    (newSourceBasis : HilbertBasis ν ℂ K)
    (operator : H →L[ℂ] G) (bounded : K →L[ℂ] H)
    (hoperator : Summable fun i => ‖operator (sourceBasis i)‖ ^ 2) :
    ∑' k, ‖(operator ∘L bounded) (newSourceBasis k)‖ ^ 2 ≤
      ‖bounded‖ ^ 2 * (∑' i, ‖operator (sourceBasis i)‖ ^ 2) := by
  have hcomposed : Summable fun k =>
      ‖(operator ∘L bounded) (newSourceBasis k)‖ ^ 2 :=
    summable_normSq_precomp sourceBasis targetBasis newSourceBasis operator
      bounded hoperator
  have hoperatorAdjoint : Summable fun j =>
      ‖operator.adjoint (targetBasis j)‖ ^ 2 :=
    BasisHilbertSchmidtPairData.summable_adjoint_normSq sourceBasis targetBasis
      operator hoperator
  have hcomposedAdjoint : Summable fun j =>
      ‖(operator ∘L bounded).adjoint (targetBasis j)‖ ^ 2 :=
    BasisHilbertSchmidtPairData.summable_adjoint_normSq newSourceBasis
      targetBasis (operator ∘L bounded) hcomposed
  have hoperatorCycle :=
    BasisHilbertSchmidtPairData.ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
      sourceBasis targetBasis operator operator hoperator hoperator
  have hoperatorEnergyComplex :
      (∑' i, ((‖operator (sourceBasis i)‖ ^ 2 : ℝ) : ℂ)) =
        ∑' j, ((‖operator.adjoint (targetBasis j)‖ ^ 2 : ℝ) : ℂ) := by
    calc
      (∑' i, ((‖operator (sourceBasis i)‖ ^ 2 : ℝ) : ℂ)) =
          ordinaryTraceAlong sourceBasis
            (operator.adjoint ∘L operator) := by
        rw [ordinaryTraceAlong]
        apply tsum_congr
        intro i
        rw [ContinuousLinearMap.comp_apply, operator.adjoint_inner_right,
          inner_self_eq_norm_sq_to_K]
        norm_cast
      _ = ordinaryTraceAlong targetBasis
          (operator ∘L operator.adjoint) := hoperatorCycle
      _ = ∑' j, ((‖operator.adjoint (targetBasis j)‖ ^ 2 : ℝ) : ℂ) := by
        rw [ordinaryTraceAlong]
        apply tsum_congr
        intro j
        rw [ContinuousLinearMap.comp_apply, ← operator.adjoint_inner_left,
          inner_self_eq_norm_sq_to_K]
        norm_cast
  have hoperatorEnergy :
      (∑' i, ‖operator (sourceBasis i)‖ ^ 2) =
        ∑' j, ‖operator.adjoint (targetBasis j)‖ ^ 2 := by
    refine Complex.ofReal_injective ?_
    calc
      Complex.ofRealCLM (∑' i, ‖operator (sourceBasis i)‖ ^ 2) =
          ∑' i, ((‖operator (sourceBasis i)‖ ^ 2 : ℝ) : ℂ) := by
        simpa only [Complex.ofRealCLM_apply] using
          (Complex.ofRealCLM.map_tsum hoperator)
      _ = ∑' j, ((‖operator.adjoint (targetBasis j)‖ ^ 2 : ℝ) : ℂ) :=
        hoperatorEnergyComplex
      _ = Complex.ofRealCLM (∑' j, ‖operator.adjoint (targetBasis j)‖ ^ 2) := by
        symm
        simpa only [Complex.ofRealCLM_apply] using
          (Complex.ofRealCLM.map_tsum hoperatorAdjoint)
  have hcomposedCycle :=
    BasisHilbertSchmidtPairData.ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
      newSourceBasis targetBasis (operator ∘L bounded) (operator ∘L bounded)
      hcomposed hcomposed
  have hcomposedEnergyComplex :
      (∑' k, ((‖(operator ∘L bounded) (newSourceBasis k)‖ ^ 2 : ℝ) : ℂ)) =
        ∑' j, ((‖(operator ∘L bounded).adjoint (targetBasis j)‖ ^ 2 : ℝ) : ℂ) := by
    calc
      (∑' k, ((‖(operator ∘L bounded) (newSourceBasis k)‖ ^ 2 : ℝ) : ℂ)) =
          ordinaryTraceAlong newSourceBasis
            ((operator ∘L bounded).adjoint ∘L (operator ∘L bounded)) := by
        rw [ordinaryTraceAlong]
        apply tsum_congr
        intro k
        change ((‖(operator ∘L bounded) (newSourceBasis k)‖ ^ 2 : ℝ) : ℂ) =
          ⟪newSourceBasis k,
            (operator ∘L bounded).adjoint
              ((operator ∘L bounded) (newSourceBasis k))⟫_ℂ
        rw [(operator ∘L bounded).adjoint_inner_right,
          inner_self_eq_norm_sq_to_K]
        norm_cast
      _ = ordinaryTraceAlong targetBasis
          ((operator ∘L bounded) ∘L (operator ∘L bounded).adjoint) :=
        hcomposedCycle
      _ = ∑' j, ((‖(operator ∘L bounded).adjoint (targetBasis j)‖ ^ 2 : ℝ) : ℂ) := by
        rw [ordinaryTraceAlong]
        apply tsum_congr
        intro j
        change
          ⟪targetBasis j,
            (operator ∘L bounded)
              ((operator ∘L bounded).adjoint (targetBasis j))⟫_ℂ =
            ((‖(operator ∘L bounded).adjoint (targetBasis j)‖ ^ 2 : ℝ) : ℂ)
        rw [← (operator ∘L bounded).adjoint_inner_left,
          inner_self_eq_norm_sq_to_K]
        norm_cast
  have hcomposedEnergy :
      (∑' k, ‖(operator ∘L bounded) (newSourceBasis k)‖ ^ 2) =
        ∑' j, ‖(operator ∘L bounded).adjoint (targetBasis j)‖ ^ 2 := by
    refine Complex.ofReal_injective ?_
    calc
      Complex.ofRealCLM
          (∑' k, ‖(operator ∘L bounded) (newSourceBasis k)‖ ^ 2) =
          ∑' k, ((‖(operator ∘L bounded) (newSourceBasis k)‖ ^ 2 : ℝ) : ℂ) := by
        simpa only [Complex.ofRealCLM_apply] using
          (Complex.ofRealCLM.map_tsum hcomposed)
      _ = ∑' j,
          ((‖(operator ∘L bounded).adjoint (targetBasis j)‖ ^ 2 : ℝ) : ℂ) :=
        hcomposedEnergyComplex
      _ = Complex.ofRealCLM
          (∑' j, ‖(operator ∘L bounded).adjoint (targetBasis j)‖ ^ 2) := by
        symm
        simpa only [Complex.ofRealCLM_apply] using
          (Complex.ofRealCLM.map_tsum hcomposedAdjoint)
  have hpoint : ∀ j, ‖(operator ∘L bounded).adjoint
      (targetBasis j)‖ ^ 2 ≤
      ‖bounded‖ ^ 2 * ‖operator.adjoint (targetBasis j)‖ ^ 2 := by
    intro j
    rw [ContinuousLinearMap.adjoint_comp]
    change ‖bounded.adjoint (operator.adjoint (targetBasis j))‖ ^ 2 ≤ _
    calc
      ‖bounded.adjoint (operator.adjoint (targetBasis j))‖ ^ 2 ≤
          (‖bounded.adjoint‖ * ‖operator.adjoint (targetBasis j)‖) ^ 2 := by
        gcongr
        exact bounded.adjoint.le_opNorm _
      _ = ‖bounded‖ ^ 2 * ‖operator.adjoint (targetBasis j)‖ ^ 2 := by
        rw [ContinuousLinearMap.adjoint.norm_map]
        ring
  have hmajorant : Summable (fun j =>
      ‖bounded‖ ^ 2 * ‖operator.adjoint (targetBasis j)‖ ^ 2) :=
    hoperatorAdjoint.mul_left (‖bounded‖ ^ 2)
  have hcomposedEnergy_le :
      (∑' j, ‖(operator ∘L bounded).adjoint (targetBasis j)‖ ^ 2) ≤
        ‖bounded‖ ^ 2 * (∑' j, ‖operator.adjoint (targetBasis j)‖ ^ 2) :=
    (hcomposedAdjoint.tsum_le_tsum hpoint hmajorant).trans_eq (by
      rw [tsum_mul_left])
  calc
    ∑' k, ‖(operator ∘L bounded) (newSourceBasis k)‖ ^ 2 =
        ∑' j, ‖(operator ∘L bounded).adjoint (targetBasis j)‖ ^ 2 :=
      hcomposedEnergy
    _ ≤ ‖bounded‖ ^ 2 * (∑' j, ‖operator.adjoint (targetBasis j)‖ ^ 2) :=
      hcomposedEnergy_le
    _ = ‖bounded‖ ^ 2 *
        (∑' i, ‖operator (sourceBasis i)‖ ^ 2) := by
      rw [hoperatorEnergy]

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

/-- A summable diagonal for the exact positive square `A† A` forces `A` to
be Hilbert--Schmidt in the same named basis.

This implication is deliberately restricted to a positive square.  The
project's `IsTraceClassAlong` predicate records only one diagonal series and
is not, for a general operator, a Schatten `S1` witness.  Here every diagonal
entry is exactly the nonnegative real number `‖A e_i‖²`, so no cyclicity or
basis-independence is being inferred. -/
theorem summable_normSq_of_isTraceClassAlong_adjoint_comp_self
    {ι : Type*} (basis : HilbertBasis ι ℂ H) (operator : H →L[ℂ] G)
    (hoperator : IsTraceClassAlong basis
      (operator.adjoint ∘L operator)) :
    Summable fun i => ‖operator (basis i)‖ ^ 2 := by
  rw [IsTraceClassAlong] at hoperator
  have habsolute := hoperator.norm
  exact habsolute.congr fun i => by
    rw [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    rw [norm_pow]
    exact congrArg (fun value : ℝ => value ^ 2)
      (Complex.norm_of_nonneg (norm_nonneg (operator (basis i))))

/-- A strict contraction is Hilbert--Schmidt when its canonical positive
defect has a Hilbert--Schmidt square root.

If `A† A = K`, the displayed defect is `K - K† K`.  The strict norm bound
gives

`(1 - ‖A‖²) ‖A e‖² ≤ ‖D e‖²`

on every basis vector.  This is the abstract angle-gap step in the prolate
trace reduction; it does not assert the required strict bound for any
particular pair of projections. -/
theorem summable_normSq_of_strictContraction_of_defect
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (operator : H →L[ℂ] G) (defect : H →L[ℂ] K)
    (hnorm : ‖operator‖ < 1)
    (hdefect : defect.adjoint ∘L defect =
      operator.adjoint ∘L operator -
        (operator.adjoint ∘L operator).adjoint ∘L
          (operator.adjoint ∘L operator))
    (hdefectSummable : Summable fun i => ‖defect (basis i)‖ ^ 2) :
    Summable fun i => ‖operator (basis i)‖ ^ 2 := by
  let gram : H →L[ℂ] H := operator.adjoint ∘L operator
  let gap : ℝ := 1 - ‖operator‖ ^ 2
  have hgap : 0 < gap := by
    dsimp only [gap]
    nlinarith [norm_nonneg operator]
  apply Summable.of_nonneg_of_le
    (fun i => sq_nonneg ‖operator (basis i)‖)
    (fun i => ?_)
    (hdefectSummable.mul_left gap⁻¹)
  have hgramBound :
      ‖gram (basis i)‖ ≤ ‖operator‖ * ‖operator (basis i)‖ := by
    calc
      ‖gram (basis i)‖ =
          ‖operator.adjoint (operator (basis i))‖ := by
        rfl
      _ ≤ ‖operator.adjoint‖ * ‖operator (basis i)‖ :=
        operator.adjoint.le_opNorm _
      _ = ‖operator‖ * ‖operator (basis i)‖ := by
        rw [LinearIsometryEquiv.norm_map]
  have hgramSq :
      ‖gram (basis i)‖ ^ 2 ≤
        ‖operator‖ ^ 2 * ‖operator (basis i)‖ ^ 2 := by
    calc
      ‖gram (basis i)‖ ^ 2 ≤
          (‖operator‖ * ‖operator (basis i)‖) ^ 2 := by
        gcongr
      _ = ‖operator‖ ^ 2 * ‖operator (basis i)‖ ^ 2 := by
        ring
  have hdiagonal :
      ‖defect (basis i)‖ ^ 2 =
        ‖operator (basis i)‖ ^ 2 - ‖gram (basis i)‖ ^ 2 := by
    have hop := congrArg
      (fun map : H →L[ℂ] H => inner ℂ (basis i) (map (basis i)))
      hdefect
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, inner_sub_right,
      ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K] at hop
    norm_cast at hop
  have hscaled :
      gap * ‖operator (basis i)‖ ^ 2 ≤
        ‖defect (basis i)‖ ^ 2 := by
    rw [hdiagonal]
    dsimp only [gap]
    nlinarith
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hgap).2 (by
    simpa only [mul_comm] using hscaled)

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

/-!
The fixed signed boundary ledger has factors with different compact output
carriers.  A Cartesian product with the `L2` norm is the canonical way to
combine those carriers: the two coordinates remain orthogonal, so the square
sum of the combined Hilbert--Schmidt column is exactly the sum of the two
square sums.  This is a genuine one-pair owner, rather than a list of
trace-class claims.
-/
noncomputable def l2Sum
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (first : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (second : BasisHilbertSchmidtPairData (G := K) sourceBasis) :
    BasisHilbertSchmidtPairData
      (G := WithLp 2 (G × K)) sourceBasis where
  left :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ G K).symm.toContinuousLinearMap ∘L
      first.left.prod second.left
  right :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ G K).symm.toContinuousLinearMap ∘L
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
    simp

theorem l2Sum_traceProduct_eq_add
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (first : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (second : BasisHilbertSchmidtPairData (G := K) sourceBasis) :
    (l2Sum first second).traceProduct =
      first.traceProduct + second.traceProduct := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  unfold l2Sum BasisHilbertSchmidtPairData.traceProduct
  simp [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, WithLp.prod_inner_apply]
  rw [inner_add_right, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]

/-!
Precompose both Hilbert--Schmidt legs by possibly different bounded maps from
a new source carrier.  The target carrier and its basis are retained only for
the summability transfer; the resulting trace product acts on the new source
carrier.
-/
noncomputable def boundedPrecomp
    {ι κ μ : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (newSourceBasis : HilbertBasis μ ℂ K)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (leftBounded rightBounded : K →L[ℂ] H) :
    BasisHilbertSchmidtPairData (G := G) newSourceBasis where
  left := data.left ∘L leftBounded
  right := data.right ∘L rightBounded
  left_summable_normSq := summable_normSq_precomp sourceBasis targetBasis
    newSourceBasis data.left leftBounded data.left_summable_normSq
  right_summable_normSq := summable_normSq_precomp sourceBasis targetBasis
    newSourceBasis data.right rightBounded data.right_summable_normSq

theorem boundedPrecomp_traceProduct_eq
    {ι κ μ : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (newSourceBasis : HilbertBasis μ ℂ K)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (leftBounded rightBounded : K →L[ℂ] H) :
    (boundedPrecomp targetBasis newSourceBasis data leftBounded rightBounded).traceProduct =
      leftBounded† ∘L data.traceProduct ∘L rightBounded := by
  unfold boundedPrecomp traceProduct
  rw [ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro x
  rfl

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

/-!
Package the signed commutator of a pair-owned crossing after arbitrary bounded
left/right dressing.  The adjoint and forward orientations are placed in two
orthogonal `L2` coordinates; the minus sign stays in the second right leg.
This is the reusable owner for an oriented boundary difference.
-/
noncomputable def boundedAdjointSub
    {ι κ : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (leftBounded rightBounded : H →L[ℂ] H) :
    BasisHilbertSchmidtPairData
      (G := WithLp 2 (G × G)) sourceBasis :=
  l2Sum
    (data.swap.boundedSandwich targetBasis leftBounded rightBounded)
    ((data.boundedSandwich targetBasis leftBounded rightBounded).smulRight (-1))

theorem boundedAdjointSub_traceProduct_eq
    {ι κ : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (leftBounded rightBounded : H →L[ℂ] H) :
    (boundedAdjointSub targetBasis data leftBounded rightBounded).traceProduct =
      leftBounded ∘L data.traceProduct.adjoint ∘L rightBounded -
        leftBounded ∘L data.traceProduct ∘L rightBounded := by
  rw [boundedAdjointSub, l2Sum_traceProduct_eq_add,
    smulRight_traceProduct_eq,
    boundedSandwich_traceProduct_eq,
    boundedSandwich_traceProduct_eq,
    swap_traceProduct_eq_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  simp [ContinuousLinearMap.comp_apply]
  abel

end BasisHilbertSchmidtPairData
end PositiveTrace
end CC20Concrete
end Source
end ConnesWeilRH
