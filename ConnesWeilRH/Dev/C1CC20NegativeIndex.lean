/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20OperatorGap
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The codimension-one form of the CC20 endpoint obstruction

This leaf isolates the non-numerical linear-algebra content of Gate 1.  If a
real quadratic functional is nonnegative on the kernel of one complex linear
functional, then every subspace on which it is strictly negative has complex
dimension at most one.  No eigenvalue approximation or finite matrix enters.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20NegativeIndex

open C1CC20OperatorGap

/-- A subspace is strictly negative for `q` when every nonzero vector in it
has negative quadratic value. -/
def IsStrictlyNegativeSubspace {H : Type*} [AddCommGroup H] [Module Complex H]
    (q : H -> Real) (V : Submodule Complex H) : Prop :=
  forall x : V, x ≠ 0 -> q x < 0

/-- Kernel positivity for one linear functional forces every strictly
negative subspace to have dimension at most one.  The restriction of `ell` to
that subspace is injective: a nonzero kernel vector would have both signs. -/
theorem finrank_strictlyNegativeSubspace_le_one
    {H : Type*} [AddCommGroup H] [Module Complex H]
    (q : H -> Real) (ell : H →ₗ[Complex] Complex)
    (hker : forall x : H, ell x = 0 -> 0 <= q x)
    (V : Submodule Complex H) (hnegative : IsStrictlyNegativeSubspace q V) :
    Module.finrank Complex V <= 1 := by
  let restricted : V →ₗ[Complex] Complex := ell.domRestrict V
  have hinjective : Function.Injective restricted := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hxne
    have hneg : q x < 0 := hnegative x hxne
    have hnonneg : 0 <= q x := hker x hx
    linarith
  calc
    Module.finrank Complex V <= Module.finrank Complex Complex :=
      restricted.finrank_le_finrank_of_injective hinjective
    _ = 1 := Module.finrank_self Complex

/-- Operator-level CC20 specialization.  Once the endpoint defect form is
nonnegative on the vanishing hyperplane, its negative index is at most one in
the precise subspace sense used above. -/
theorem cc20Endpoint_negativeIndex_le_one_of_kernel_nonnegative
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    (kf : H →L[Complex] H) (ell : H →ₗ[Complex] Complex)
    (hker : forall xi : H, ell xi = 0 ->
      0 <= cc20DefectQuadraticForm kf xi)
    (V : Submodule Complex H)
    (hnegative : IsStrictlyNegativeSubspace
      (cc20DefectQuadraticForm kf) V) :
    Module.finrank Complex V <= 1 :=
  finrank_strictlyNegativeSubspace_le_one
    (cc20DefectQuadraticForm kf) ell hker V hnegative

/-- Riesz-functional form of the endpoint statement.  This is the exact
codimension-one bad direction used in the CC20 rank-one repair. -/
theorem cc20Endpoint_negativeIndex_le_one_of_inner_kernel_nonnegative
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    (kf : H →L[Complex] H) (psi : H)
    (hker : forall xi : H, inner Complex psi xi = 0 ->
      0 <= cc20DefectQuadraticForm kf xi)
    (V : Submodule Complex H)
    (hnegative : IsStrictlyNegativeSubspace
      (cc20DefectQuadraticForm kf) V) :
    Module.finrank Complex V <= 1 := by
  apply cc20Endpoint_negativeIndex_le_one_of_kernel_nonnegative kf
    (innerSL Complex psi).toLinearMap
  · simpa only using hker
  · exact hnegative

end C1CC20NegativeIndex
end Source
end ConnesWeilRH
