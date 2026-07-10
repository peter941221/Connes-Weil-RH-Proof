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
end PositiveTrace
end CC20Concrete
end Source
end ConnesWeilRH
