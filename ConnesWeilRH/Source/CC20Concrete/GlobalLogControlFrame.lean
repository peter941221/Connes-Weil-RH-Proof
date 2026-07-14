/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogKernel
import ConnesWeilRH.Source.CC20Concrete.CompactBadSpace

/-!
# Dense control rows across the Haar/log window equivalence

The finite-window regular operator has two exact carriers: the source Haar
space and the restricted logarithmic `L2` space.  This module transports the
finite dense-span control selector across the existing linear isometry.  The
transport keeps the row vectors, the operator conjugacy, and the shifted
quadratic form on the same object.

It does not identify the route's global Mellin evaluations with the finite
window carrier.  That separate mismatch remains an explicit obligation.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set
open scoped InnerProduct InnerProductSpace

/-- The preimage of a complete logarithmic basis is complete on the exact Haar
window.  This is stated explicitly so later finite-row producers can use the
same index set on both carriers. -/
theorem dense_span_cc20GlobalLogWindowRestrictedL2HaarPreimageBasis
    (lambda : ℝ) (hlambda : 1 < lambda)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)))) :
    Dense (Submodule.span ℂ
      (Set.range (cc20GlobalLogWindowRestrictedL2HaarPreimageBasis
        lambda hlambda basis)) : Set
          (Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda))) := by
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (cc20GlobalLogWindowRestrictedL2HaarPreimageBasis
      lambda hlambda basis).dense_span

/-- A finite logarithmic-basis selector for the compact remainder transports to
the same finite row indices on the Haar carrier.  The proof uses the exact
operator conjugacy, rather than merely comparing two independently compact
operators. -/
theorem exists_finite_cc20WindowHaarRegularRemainder_nonpositive_on_logBasis_rows
    (lambda : ℝ) (hlambda : 1 < lambda)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)))) :
    ∃ rowIndices : Finset ι,
      FiniteDimensional ℂ
          (Submodule.span ℂ
            ((cc20GlobalLogWindowRestrictedL2HaarPreimageBasis
              lambda hlambda basis) '' (rowIndices : Set ι))) ∧
        ∀ x : Lp ℂ 2 (cc20WindowHaarMeasure lambda hlambda),
          (∀ i ∈ rowIndices,
            inner ℂ x
              (cc20GlobalLogWindowRestrictedL2HaarPreimageBasis
                lambda hlambda basis i) = 0) →
            (inner ℂ x
              (cc20WindowHaarComplexL2Operator lambda hlambda x -
                (2 : ℂ) • x)).re ≤ 0 := by
  let e := cc20WindowHaarRestrictedLogL2IsometryEquiv lambda hlambda
  let basisH :=
    cc20GlobalLogWindowRestrictedL2HaarPreimageBasis lambda hlambda basis
  obtain ⟨rowIndices, _hfiniteLog, hsignLog⟩ :=
    CompactBadSpace.exists_finite_hilbertBasis_controlRowIndices
      (cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda)
      (isCompactOperator_cc20GlobalLogWindowRestrictedL2Endomorphism
        lambda hlambda)
      basis
      (by norm_num : (0 : ℝ) < 2)
  refine ⟨rowIndices,
    FiniteDimensional.span_of_finite ℂ
      (rowIndices.finite_toSet.image basisH), ?_⟩
  intro x hrows
  let y := e x
  have hyrows : ∀ i ∈ rowIndices, inner ℂ y (basis i) = 0 := by
    intro i hi
    have hrow := hrows i hi
    have hrow' : inner ℂ x (e.symm (basis i)) = 0 := by
      simpa [basisH,
        cc20GlobalLogWindowRestrictedL2HaarPreimageBasis_apply]
        using hrow
    have hinner : inner ℂ (e x) (basis i) =
        inner ℂ x (e.symm (basis i)) := by
      calc
        inner ℂ (e x) (basis i) =
            inner ℂ (e x) (e (e.symm (basis i))) := by
              rw [e.apply_symm_apply]
        _ = inner ℂ x (e.symm (basis i)) := e.inner_map_map _ _
    simpa [y] using hinner.symm ▸ hrow'
  have hlog := hsignLog y hyrows
  have hoperator :
      e (cc20WindowHaarComplexL2Operator lambda hlambda x) =
        cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda y := by
    rw [cc20GlobalLogWindowRestrictedL2Endomorphism_eq_conjugatedHaarOperator]
    simp [cc20GlobalLogWindowRestrictedL2ConjugatedHaarOperator, e, y]
  have hshift :
      e (cc20WindowHaarComplexL2Operator lambda hlambda x -
          (2 : ℂ) • x) =
        cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda y -
          (2 : ℂ) • y := by
    rw [map_sub, map_smul, hoperator]
  have hinner := e.inner_map_map x
    (cc20WindowHaarComplexL2Operator lambda hlambda x - (2 : ℂ) • x)
  rw [hshift] at hinner
  rw [← hinner]
  exact hlog

end CC20Concrete
end Source
end ConnesWeilRH
