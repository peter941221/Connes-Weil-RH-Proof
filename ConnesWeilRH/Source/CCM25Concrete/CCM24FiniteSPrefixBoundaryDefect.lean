/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandPrefixCompression

/-!
# Boundary defects of finite Hilbert-basis compressions

A finite basis compression preserves addition but not operator composition.
This module names the exact product defect.  Finite-dimensional trace
cyclicity then removes only the internal matrix commutator and leaves the two
boundary defects explicit.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSPrefixBoundaryDefect

open scoped InnerProduct InnerProductSpace Matrix
open CCM24FiniteSMovingBandPrefixCompression

/-- Failure of the first-`N` matrix compression to preserve composition. -/
noncomputable def basisPrefixProductDefect
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ)
    (left right : H →L[ℂ] H) : Matrix (Fin N) (Fin N) ℂ :=
  basisPrefixMatrix basis N (left * right) -
    basisPrefixMatrix basis N left * basisPrefixMatrix basis N right

theorem basisPrefixMatrix_sub
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ)
    (left right : H →L[ℂ] H) :
    basisPrefixMatrix basis N (left - right) =
      basisPrefixMatrix basis N left - basisPrefixMatrix basis N right := by
  ext i j
  simp [basisPrefixMatrix, inner_sub_right]

/-- The compressed operator commutator is an internal matrix commutator plus
the antisymmetrized boundary defect. -/
theorem basisPrefixMatrix_commutator_eq_internal_add_boundaryDefect
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ)
    (left right : H →L[ℂ] H) :
    basisPrefixMatrix basis N (left * right - right * left) =
      (basisPrefixMatrix basis N left * basisPrefixMatrix basis N right -
        basisPrefixMatrix basis N right * basisPrefixMatrix basis N left) +
      (basisPrefixProductDefect basis N left right -
        basisPrefixProductDefect basis N right left) := by
  rw [basisPrefixMatrix_sub]
  unfold basisPrefixProductDefect
  noncomm_ring

/-- Finite trace cyclicity kills only the internal matrix commutator.  The
remaining trace is exactly the physical prefix-boundary defect. -/
theorem trace_basisPrefixMatrix_commutator_eq_trace_boundaryDefect
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ)
    (left right : H →L[ℂ] H) :
    Matrix.trace
        (basisPrefixMatrix basis N (left * right - right * left)) =
      Matrix.trace
        (basisPrefixProductDefect basis N left right -
          basisPrefixProductDefect basis N right left) := by
  rw [basisPrefixMatrix_commutator_eq_internal_add_boundaryDefect]
  rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_mul_comm]
  simp

end CCM24FiniteSPrefixBoundaryDefect
end CCM25Concrete
end Source
end ConnesWeilRH
