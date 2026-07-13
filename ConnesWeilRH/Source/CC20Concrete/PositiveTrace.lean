/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Ordinary positive trace from Hilbert-Schmidt data

This module defines the ordinary trace as a diagonal series, independently of
the Hilbert-Schmidt norm. For an operator whose squared norms are summable on
one Hilbert basis, the adjoint composition has a summable diagonal and its
ordinary trace equals that norm square.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace PositiveTrace

open scoped ComplexConjugate InnerProduct InnerProductSpace

variable {ι H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The diagonal-series trace in a named Hilbert basis. -/
noncomputable def ordinaryTraceAlong
    (basis : HilbertBasis ι ℂ H) (operator : H →L[ℂ] H) : ℂ :=
  ∑' i, ⟪basis i, operator (basis i)⟫_ℂ

/-- Trace-class legality for the named diagonal series. -/
def IsTraceClassAlong
    (basis : HilbertBasis ι ℂ H) (operator : H →L[ℂ] H) : Prop :=
  Summable fun i => ⟪basis i, operator (basis i)⟫_ℂ

/-- Taking the Hilbert-space adjoint conjugates the diagonal-series trace in
the same Hilbert basis. This identity does not require a separate summability
premise because complex conjugation commutes with `tsum`. -/
theorem ordinaryTraceAlong_adjoint
    (basis : HilbertBasis ι ℂ H) (operator : H →L[ℂ] H) :
    ordinaryTraceAlong basis operator.adjoint =
      star (ordinaryTraceAlong basis operator) := by
  rw [ordinaryTraceAlong, ordinaryTraceAlong, tsum_star]
  apply tsum_congr
  intro i
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (𝕜 := ℂ) (operator (basis i)) (basis i)).symm

/-- Trace-class legality is preserved by the Hilbert-space adjoint. -/
theorem isTraceClassAlong_adjoint
    (basis : HilbertBasis ι ℂ H) (operator : H →L[ℂ] H)
    (hoperator : IsTraceClassAlong basis operator) :
    IsTraceClassAlong basis operator.adjoint := by
  rw [IsTraceClassAlong] at hoperator ⊢
  apply Summable.of_norm
  exact hoperator.norm.congr fun i => by
    rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]

omit [CompleteSpace H] in
theorem isTraceClassAlong_zero (basis : HilbertBasis ι ℂ H) :
    IsTraceClassAlong basis (0 : H →L[ℂ] H) := by
  rw [IsTraceClassAlong]
  simpa using (summable_zero : Summable fun _ : ι => (0 : ℂ))

omit [CompleteSpace H] in
theorem isTraceClassAlong_add
    (basis : HilbertBasis ι ℂ H) (left right : H →L[ℂ] H)
    (hleft : IsTraceClassAlong basis left)
    (hright : IsTraceClassAlong basis right) :
    IsTraceClassAlong basis (left + right) := by
  rw [IsTraceClassAlong] at hleft hright ⊢
  simpa only [ContinuousLinearMap.add_apply, inner_add_right] using
    hleft.add hright

omit [CompleteSpace H] in
theorem isTraceClassAlong_smul
    (basis : HilbertBasis ι ℂ H) (scalar : ℂ) (operator : H →L[ℂ] H)
    (hoperator : IsTraceClassAlong basis operator) :
    IsTraceClassAlong basis (scalar • operator) := by
  rw [IsTraceClassAlong] at hoperator ⊢
  simpa only [ContinuousLinearMap.smul_apply, inner_smul_right] using
    hoperator.mul_left scalar

omit [CompleteSpace H] in
/-- Additivity of the ordinary diagonal trace, with both summability premises
kept explicit. -/
theorem ordinaryTraceAlong_add
    (basis : HilbertBasis ι ℂ H) (left right : H →L[ℂ] H)
    (hleft : IsTraceClassAlong basis left)
    (hright : IsTraceClassAlong basis right) :
    ordinaryTraceAlong basis (left + right) =
      ordinaryTraceAlong basis left + ordinaryTraceAlong basis right := by
  rw [ordinaryTraceAlong, ordinaryTraceAlong, ordinaryTraceAlong]
  rw [IsTraceClassAlong] at hleft hright
  simpa only [ContinuousLinearMap.add_apply, inner_add_right] using
    hleft.tsum_add hright

omit [CompleteSpace H] in
/-- Complex homogeneity of the ordinary diagonal trace, under an explicit
summability premise. -/
theorem ordinaryTraceAlong_smul
    (basis : HilbertBasis ι ℂ H) (scalar : ℂ) (operator : H →L[ℂ] H)
    (hoperator : IsTraceClassAlong basis operator) :
    ordinaryTraceAlong basis (scalar • operator) =
      scalar * ordinaryTraceAlong basis operator := by
  rw [ordinaryTraceAlong, ordinaryTraceAlong]
  rw [IsTraceClassAlong] at hoperator
  simpa only [ContinuousLinearMap.smul_apply, inner_smul_right] using
    hoperator.tsum_mul_left scalar

omit [CompleteSpace H] in
theorem isTraceClassAlong_finset_sum
    {α : Type*} (basis : HilbertBasis ι ℂ H)
    (terms : Finset α) (operator : α → H →L[ℂ] H)
    (hoperator : ∀ term ∈ terms,
      IsTraceClassAlong basis (operator term)) :
    IsTraceClassAlong basis (∑ term ∈ terms, operator term) := by
  classical
  induction terms using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using isTraceClassAlong_zero basis
  | @insert term terms hnotmem ih =>
      rw [Finset.sum_insert hnotmem]
      apply isTraceClassAlong_add
      · exact hoperator term (Finset.mem_insert_self term terms)
      · exact ih fun other hother =>
          hoperator other (Finset.mem_insert_of_mem hother)

omit [CompleteSpace H] in
/-- The ordinary trace commutes with a finite operator sum once every summand
has an explicit trace-class witness in the same Hilbert basis. -/
theorem ordinaryTraceAlong_finset_sum
    {α : Type*} (basis : HilbertBasis ι ℂ H)
    (terms : Finset α) (operator : α → H →L[ℂ] H)
    (hoperator : ∀ term ∈ terms,
      IsTraceClassAlong basis (operator term)) :
    ordinaryTraceAlong basis (∑ term ∈ terms, operator term) =
      ∑ term ∈ terms, ordinaryTraceAlong basis (operator term) := by
  classical
  induction terms using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, ordinaryTraceAlong]
      simp
  | @insert term terms hnotmem ih =>
      rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem]
      rw [ordinaryTraceAlong_add basis]
      · exact congrArg
          (fun value => ordinaryTraceAlong basis (operator term) + value)
          (ih fun other hother =>
            hoperator other (Finset.mem_insert_of_mem hother))
      · exact hoperator term (Finset.mem_insert_self term terms)
      · exact isTraceClassAlong_finset_sum basis terms operator
          (fun other hother =>
            hoperator other (Finset.mem_insert_of_mem hother))

omit [CompleteSpace H] in
theorem isCompactOperator_finset_sum
    {α : Type*} (terms : Finset α) (operator : α → H →L[ℂ] H)
    (hoperator : ∀ term ∈ terms, IsCompactOperator (operator term)) :
    IsCompactOperator
      ((∑ term ∈ terms, operator term : H →L[ℂ] H) : H → H) := by
  classical
  induction terms using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (isCompactOperator_zero :
          IsCompactOperator (0 : H →L[ℂ] H))
  | @insert term terms hnotmem ih =>
      rw [Finset.sum_insert hnotmem]
      exact (hoperator term (Finset.mem_insert_self term terms)).add
        (ih fun other hother =>
          hoperator other (Finset.mem_insert_of_mem hother))

/-- A Hilbert-Schmidt summability witness tied to one operator and one basis. -/
structure BasisHilbertSchmidtData (basis : HilbertBasis ι ℂ H) where
  operator : H →L[ℂ] H
  summable_normSq : Summable fun i => ‖operator (basis i)‖ ^ 2

namespace BasisHilbertSchmidtData

noncomputable def hsNormSq
    {basis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtData basis) : ℝ :=
  ∑' i, ‖data.operator (basis i)‖ ^ 2

noncomputable def positiveComposition
    {basis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtData basis) : H →L[ℂ] H :=
  data.operator† ∘L data.operator

theorem positiveComposition_diagonal
    {basis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtData basis) (i : ι) :
    ⟪basis i, data.positiveComposition (basis i)⟫_ℂ =
      ((‖data.operator (basis i)‖ ^ 2 : ℝ) : ℂ) := by
  rw [positiveComposition, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem positiveComposition_isTraceClassAlong
    {basis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtData basis) :
    IsTraceClassAlong basis data.positiveComposition := by
  rw [IsTraceClassAlong]
  simpa only [data.positiveComposition_diagonal] using
    Complex.ofRealCLM.summable data.summable_normSq

omit [CompleteSpace H] in
theorem hsNormSq_nonnegative
    {basis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtData basis) :
    0 ≤ data.hsNormSq := by
  exact tsum_nonneg fun i => sq_nonneg ‖data.operator (basis i)‖

/-- The ordinary trace of `A†A` is the Hilbert-Schmidt norm square. -/
theorem ordinaryTrace_positiveComposition
    {basis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtData basis) :
    ordinaryTraceAlong basis data.positiveComposition =
      (data.hsNormSq : ℂ) := by
  rw [ordinaryTraceAlong]
  simp_rw [data.positiveComposition_diagonal]
  simpa only [Complex.ofRealCLM_apply, hsNormSq] using
    (Complex.ofRealCLM.map_tsum data.summable_normSq).symm

theorem ordinaryTrace_positiveComposition_im_eq_zero
    {basis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtData basis) :
    (ordinaryTraceAlong basis data.positiveComposition).im = 0 := by
  rw [data.ordinaryTrace_positiveComposition]
  simp

theorem ordinaryTrace_positiveComposition_re_nonnegative
    {basis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtData basis) :
    0 ≤ (ordinaryTraceAlong basis data.positiveComposition).re := by
  rw [data.ordinaryTrace_positiveComposition]
  simpa using data.hsNormSq_nonnegative

end BasisHilbertSchmidtData

/-- Two Hilbert-Schmidt operators with a common source basis. Their target
space may differ from the source, as required by crossing factorizations. -/
structure BasisHilbertSchmidtPairData
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (basis : HilbertBasis ι ℂ H) where
  left : H →L[ℂ] G
  right : H →L[ℂ] G
  left_summable_normSq : Summable fun i => ‖left (basis i)‖ ^ 2
  right_summable_normSq : Summable fun i => ‖right (basis i)‖ ^ 2

namespace BasisHilbertSchmidtPairData

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace G]

noncomputable def traceProduct
    {basis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtPairData (G := G) basis) : H →L[ℂ] H :=
  data.left† ∘L data.right

theorem traceProduct_diagonal
    {basis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtPairData (G := G) basis) (i : ι) :
    ⟪basis i, data.traceProduct (basis i)⟫_ℂ =
      ⟪data.left (basis i), data.right (basis i)⟫_ℂ := by
  rw [traceProduct, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

theorem summable_traceProduct_diagonal
    {basis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtPairData (G := G) basis) :
    Summable fun i => ⟪basis i, data.traceProduct (basis i)⟫_ℂ := by
  rw [show (fun i => ⟪basis i, data.traceProduct (basis i)⟫_ℂ) =
      (fun i => ⟪data.left (basis i), data.right (basis i)⟫_ℂ) by
    funext i
    exact data.traceProduct_diagonal i]
  apply Summable.of_norm_bounded
    ((data.left_summable_normSq.add data.right_summable_normSq).mul_left
      (1 / 2 : ℝ))
  intro i
  have hinner := norm_inner_le_norm (𝕜 := ℂ)
    (data.left (basis i)) (data.right (basis i))
  have hsq :
      ‖data.left (basis i)‖ * ‖data.right (basis i)‖ ≤
        (1 / 2 : ℝ) *
          (‖data.left (basis i)‖ ^ 2 + ‖data.right (basis i)‖ ^ 2) := by
    nlinarith [sq_nonneg
      (‖data.left (basis i)‖ - ‖data.right (basis i)‖)]
  exact hinner.trans hsq

theorem traceProduct_isTraceClassAlong
    {basis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtPairData (G := G) basis) :
    IsTraceClassAlong basis data.traceProduct :=
  data.summable_traceProduct_diagonal

omit [CompleteSpace H] [CompleteSpace G] in
/-- The matrix coefficients used to cycle `A†B` are absolutely summable on
the product of any source and target Hilbert bases. This is the analytic
justification for exchanging the two basis sums. -/
theorem summable_cyclicCoefficients
    {κ : Type*}
    (sourceBasis : HilbertBasis ι ℂ H) (targetBasis : HilbertBasis κ ℂ G)
    (left right : H →L[ℂ] G)
    (hleft : Summable fun i => ‖left (sourceBasis i)‖ ^ 2)
    (hright : Summable fun i => ‖right (sourceBasis i)‖ ^ 2) :
    Summable (fun ij : ι × κ =>
      inner ℂ (left (sourceBasis ij.1)) (targetBasis ij.2) *
        inner ℂ (targetBasis ij.2) (right (sourceBasis ij.1))) := by
  let majorant : ι × κ → ℝ := fun ij =>
    (1 / 2 : ℝ) *
      (‖inner ℂ (targetBasis ij.2) (left (sourceBasis ij.1))‖ ^ 2 +
        ‖inner ℂ (targetBasis ij.2) (right (sourceBasis ij.1))‖ ^ 2)
  have hmajorant_nonneg : 0 ≤ majorant := by
    intro ij
    exact mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hmajorant : Summable majorant := by
    rw [summable_prod_of_nonneg hmajorant_nonneg]
    constructor
    · intro i
      exact (((targetBasis.orthonormal.inner_products_summable
          (x := left (sourceBasis i))).add
        (targetBasis.orthonormal.inner_products_summable
          (x := right (sourceBasis i)))).mul_left (1 / 2 : ℝ))
    · apply Summable.of_nonneg_of_le
        (fun i => tsum_nonneg fun j => hmajorant_nonneg (i, j))
        (fun i => ?_) ((hleft.add hright).mul_left (1 / 2 : ℝ))
      calc
        (∑' j, majorant (i, j)) =
            (1 / 2 : ℝ) *
              ((∑' j, ‖inner ℂ (targetBasis j) (left (sourceBasis i))‖ ^ 2) +
                ∑' j, ‖inner ℂ (targetBasis j) (right (sourceBasis i))‖ ^ 2) := by
          rw [tsum_mul_left]
          rw [(targetBasis.orthonormal.inner_products_summable
              (x := left (sourceBasis i))).tsum_add
            (targetBasis.orthonormal.inner_products_summable
              (x := right (sourceBasis i)))]
        _ ≤ (1 / 2 : ℝ) *
            (‖left (sourceBasis i)‖ ^ 2 + ‖right (sourceBasis i)‖ ^ 2) := by
          gcongr
          · exact targetBasis.orthonormal.tsum_inner_products_le
              (left (sourceBasis i))
          · exact targetBasis.orthonormal.tsum_inner_products_le
              (right (sourceBasis i))
  apply Summable.of_norm_bounded hmajorant
  intro ij
  calc
    ‖inner ℂ (left (sourceBasis ij.1)) (targetBasis ij.2) *
        inner ℂ (targetBasis ij.2) (right (sourceBasis ij.1))‖ =
        ‖inner ℂ (targetBasis ij.2) (left (sourceBasis ij.1))‖ *
          ‖inner ℂ (targetBasis ij.2) (right (sourceBasis ij.1))‖ := by
      rw [norm_mul, norm_inner_symm]
    _ ≤ majorant ij := by
      dsimp [majorant]
      nlinarith [sq_nonneg
        (‖inner ℂ (targetBasis ij.2) (left (sourceBasis ij.1))‖ -
          ‖inner ℂ (targetBasis ij.2) (right (sourceBasis ij.1))‖)]

/-- Hilbert--Schmidt summability is preserved by taking the adjoint and may be
read on any Hilbert basis of the target. The proof uses the same absolutely
summable two-basis coefficient matrix as trace cyclicity. -/
theorem summable_adjoint_normSq
    {κ : Type*}
    (sourceBasis : HilbertBasis ι ℂ H) (targetBasis : HilbertBasis κ ℂ G)
    (operator : H →L[ℂ] G)
    (hoperator : Summable fun i => ‖operator (sourceBasis i)‖ ^ 2) :
    Summable fun j => ‖operator.adjoint (targetBasis j)‖ ^ 2 := by
  let coefficient : ι → κ → ℂ := fun i j =>
    inner ℂ (operator (sourceBasis i)) (targetBasis j) *
      inner ℂ (targetBasis j) (operator (sourceBasis i))
  have hcoeff : Summable (Function.uncurry coefficient) :=
    summable_cyclicCoefficients sourceBasis targetBasis
      operator operator hoperator hoperator
  have houter := hcoeff.prod_symm.prod
  change Summable (fun j => ∑' i, coefficient i j) at houter
  have hinner : Summable fun j =>
      inner ℂ (operator.adjoint (targetBasis j))
        (operator.adjoint (targetBasis j)) := by
    apply houter.congr
    intro j
    rw [← sourceBasis.tsum_inner_mul_inner
      (operator.adjoint (targetBasis j))
      (operator.adjoint (targetBasis j))]
    apply tsum_congr
    intro i
    dsimp only [coefficient]
    rw [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
    ring
  have hreal := Complex.reCLM.summable hinner
  apply hreal.congr
  intro j
  exact inner_self_eq_norm_sq (𝕜 := ℂ)
    (operator.adjoint (targetBasis j))

/-- The target-basis rank-one term in the nuclear expansion of `A†B`. -/
noncomputable def traceProductNuclearTerm
    {κ : Type*}
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (j : κ) : H →L[ℂ] H :=
  InnerProductSpace.rankOne ℂ
    (data.left.adjoint (targetBasis j))
    (data.right.adjoint (targetBasis j))

theorem traceProductNuclearTerm_isCompactOperator
    {κ : Type*}
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (j : κ) :
    IsCompactOperator (traceProductNuclearTerm targetBasis data j) := by
  rw [traceProductNuclearTerm, InnerProductSpace.rankOne_def']
  exact
    (isCompactOperator_of_locallyCompactSpace_dom
      (innerSL ℂ (data.right.adjoint (targetBasis j)))).clm_comp
        (ContinuousLinearMap.toSpanSingleton ℂ
          (data.left.adjoint (targetBasis j)))

theorem summable_norm_traceProductNuclearTerm
    {κ : Type*}
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis) :
    Summable fun j => ‖traceProductNuclearTerm targetBasis data j‖ := by
  have hleft := summable_adjoint_normSq sourceBasis targetBasis data.left
    data.left_summable_normSq
  have hright := summable_adjoint_normSq sourceBasis targetBasis data.right
    data.right_summable_normSq
  apply Summable.of_nonneg_of_le
    (fun j => norm_nonneg (traceProductNuclearTerm targetBasis data j))
    (fun j => ?_) ((hleft.add hright).mul_left (1 / 2 : ℝ))
  rw [traceProductNuclearTerm, InnerProductSpace.norm_rankOne]
  nlinarith [sq_nonneg
    (‖data.left.adjoint (targetBasis j)‖ -
      ‖data.right.adjoint (targetBasis j)‖)]

theorem traceProduct_eq_tsum_nuclearTerm
    {κ : Type*}
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis) :
    data.traceProduct = ∑' j, traceProductNuclearTerm targetBasis data j := by
  have hsummable : Summable fun j =>
      traceProductNuclearTerm targetBasis data j :=
    Summable.of_norm (summable_norm_traceProductNuclearTerm targetBasis data)
  apply ContinuousLinearMap.ext
  intro x
  have hnuclear := hsummable.hasSum.mapL
    (ContinuousLinearMap.apply ℂ H x)
  have hproduct : HasSum
      (fun j => traceProductNuclearTerm targetBasis data j x)
      (data.traceProduct x) := by
    rw [traceProduct, ContinuousLinearMap.comp_apply]
    refine HasSum.congr_fun (data.left.adjoint.hasSum
      (targetBasis.hasSum_repr (data.right x))) (fun j => ?_)
    change (InnerProductSpace.rankOne ℂ
        (data.left.adjoint (targetBasis j))
        (data.right.adjoint (targetBasis j))) x =
      data.left.adjoint
        (targetBasis.repr (data.right x) j • targetBasis j)
    rw [InnerProductSpace.rankOne_apply, map_smul]
    rw [targetBasis.repr_apply_apply]
    rw [ContinuousLinearMap.adjoint_inner_left]
  exact hproduct.unique hnuclear

theorem traceProduct_isCompactOperator
    {κ : Type*}
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis) :
    IsCompactOperator data.traceProduct := by
  classical
  have hsummable : Summable fun j =>
      traceProductNuclearTerm targetBasis data j :=
    Summable.of_norm (summable_norm_traceProductNuclearTerm targetBasis data)
  rw [traceProduct_eq_tsum_nuclearTerm targetBasis data]
  apply isCompactOperator_of_tendsto hsummable.hasSum
  filter_upwards with terms
  change IsCompactOperator
    (∑ j ∈ terms, traceProductNuclearTerm targetBasis data j : H →L[ℂ] H)
  induction terms using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (isCompactOperator_zero :
          IsCompactOperator (0 : H →L[ℂ] H))
  | @insert j terms hnotmem ih =>
      rw [Finset.sum_insert hnotmem]
      exact (traceProductNuclearTerm_isCompactOperator
        targetBasis data j).add ih

theorem traceProduct_adjoint_isCompactOperator
    {κ : Type*}
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis) :
    IsCompactOperator data.traceProduct.adjoint := by
  let swapped : BasisHilbertSchmidtPairData (G := G) sourceBasis :=
    { left := data.right
      right := data.left
      left_summable_normSq := data.right_summable_normSq
      right_summable_normSq := data.left_summable_normSq }
  have hcompact := swapped.traceProduct_isCompactOperator targetBasis
  have heq : swapped.traceProduct = data.traceProduct.adjoint := by
    dsimp only [swapped, traceProduct]
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  rw [← heq]
  exact hcompact

/-- Genuine Hilbert--Schmidt cyclicity: if `A` and `B` are square summable on
one source basis, then the diagonal traces of `A†B` and `BA†` agree. -/
theorem ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
    {κ : Type*}
    (sourceBasis : HilbertBasis ι ℂ H) (targetBasis : HilbertBasis κ ℂ G)
    (left right : H →L[ℂ] G)
    (hleft : Summable fun i => ‖left (sourceBasis i)‖ ^ 2)
    (hright : Summable fun i => ‖right (sourceBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis (left.adjoint ∘L right) =
      ordinaryTraceAlong targetBasis (right ∘L left.adjoint) := by
  let coefficient : ι → κ → ℂ := fun i j =>
    inner ℂ (left (sourceBasis i)) (targetBasis j) *
      inner ℂ (targetBasis j) (right (sourceBasis i))
  have hcoeff : Summable (Function.uncurry coefficient) :=
    summable_cyclicCoefficients sourceBasis targetBasis left right hleft hright
  rw [ordinaryTraceAlong, ordinaryTraceAlong]
  calc
    (∑' i, inner ℂ (sourceBasis i)
        ((left.adjoint ∘L right) (sourceBasis i))) =
        ∑' i, inner ℂ (left (sourceBasis i)) (right (sourceBasis i)) := by
      apply tsum_congr
      intro i
      rw [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right]
    _ = ∑' i, ∑' j, coefficient i j := by
      apply tsum_congr
      intro i
      exact (targetBasis.tsum_inner_mul_inner
        (left (sourceBasis i)) (right (sourceBasis i))).symm
    _ = ∑' j, ∑' i, coefficient i j := hcoeff.tsum_comm.symm
    _ = ∑' j, inner ℂ (targetBasis j)
        ((right ∘L left.adjoint) (targetBasis j)) := by
      apply tsum_congr
      intro j
      rw [ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left]
      rw [← sourceBasis.tsum_inner_mul_inner
        (right.adjoint (targetBasis j)) (left.adjoint (targetBasis j))]
      apply tsum_congr
      intro i
      dsimp [coefficient]
      rw [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.adjoint_inner_right]
      ring

/-- Cycle a three-factor trace through a common Hilbert space when both cuts
are backed by Hilbert--Schmidt pairs. This is the rectangular trace-class
form needed to compare a compressed trace with a whole-space trace. -/
theorem ordinaryTraceAlong_three_comp_eq_cycle
    {κ ν : Type*}
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K]
    (sourceBasis : HilbertBasis ι ℂ H)
    (factorBasis : HilbertBasis κ ℂ K)
    (globalBasis : HilbertBasis ν ℂ G)
    (boundary : G →L[ℂ] H)
    (leftFactor : K →L[ℂ] G)
    (rightFactor : H →L[ℂ] K)
    (hBoundaryLeft : Summable fun k =>
      ‖(boundary ∘L leftFactor) (factorBasis k)‖ ^ 2)
    (hRight : Summable fun i => ‖rightFactor (sourceBasis i)‖ ^ 2)
    (hLeft : Summable fun k => ‖leftFactor (factorBasis k)‖ ^ 2)
    (hRightBoundary : Summable fun j =>
      ‖(rightFactor ∘L boundary) (globalBasis j)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        ((boundary ∘L leftFactor) ∘L rightFactor) =
      ordinaryTraceAlong globalBasis
        (leftFactor ∘L (rightFactor ∘L boundary)) := by
  have hcycleSource := ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
    sourceBasis factorBasis (boundary ∘L leftFactor).adjoint rightFactor
      (summable_adjoint_normSq factorBasis sourceBasis
        (boundary ∘L leftFactor) hBoundaryLeft)
      hRight
  rw [ContinuousLinearMap.adjoint_adjoint] at hcycleSource
  have hcycleGlobal := ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
    globalBasis factorBasis leftFactor.adjoint (rightFactor ∘L boundary)
      (summable_adjoint_normSq factorBasis globalBasis leftFactor hLeft)
      hRightBoundary
  rw [ContinuousLinearMap.adjoint_adjoint] at hcycleGlobal
  have hassoc :
      rightFactor ∘L (boundary ∘L leftFactor) =
        (rightFactor ∘L boundary) ∘L leftFactor := by
    apply ContinuousLinearMap.ext
    intro u
    rfl
  calc
    _ = ordinaryTraceAlong factorBasis
        (rightFactor ∘L (boundary ∘L leftFactor)) := hcycleSource
    _ = ordinaryTraceAlong factorBasis
        ((rightFactor ∘L boundary) ∘L leftFactor) :=
      congrArg (ordinaryTraceAlong factorBasis) hassoc
    _ = _ := hcycleGlobal.symm

/-- Cycle the trace product stored by a pair-data owner onto any Hilbert basis
of its target space. -/
theorem ordinaryTraceAlong_traceProduct_eq_cyclic
    {κ : Type*}
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis) :
    ordinaryTraceAlong sourceBasis data.traceProduct =
      ordinaryTraceAlong targetBasis (data.right ∘L data.left.adjoint) := by
  exact ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
    sourceBasis targetBasis data.left data.right
      data.left_summable_normSq data.right_summable_normSq

end BasisHilbertSchmidtPairData
end PositiveTrace
end CC20Concrete
end Source
end ConnesWeilRH
