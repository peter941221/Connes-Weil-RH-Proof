/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
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

end BasisHilbertSchmidtPairData
end PositiveTrace
end CC20Concrete
end Source
end ConnesWeilRH
