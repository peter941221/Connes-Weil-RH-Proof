/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandExhaustionTrace
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite compression traces for ordered Hilbert-basis prefixes

The ordered `Finset.range N` diagonal prefix is represented by the ordinary
matrix trace of the `Fin N` compression of an operator in a fixed Hilbert
basis.  This is only a finite-dimensional identification; it does not assert
an infinite-dimensional trace cycle or any limit in `N`.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMovingBandPrefixCompression

open CC20Concrete
open MeasureTheory
open scoped InnerProduct InnerProductSpace
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSMovingBandExhaustionTrace
open CCM24FiniteSRootSandwichedMovingFlow

/-- Matrix of the first `N` basis vectors against an operator. -/
noncomputable def basisPrefixMatrix {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ) (operator : H →L[ℂ] H) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ⟪basis (i : ℕ), operator (basis (j : ℕ))⟫_ℂ

/-- The finite compression trace is exactly the ordered diagonal prefix. -/
theorem trace_basisPrefixMatrix_eq_rangeDiagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ) (operator : H →L[ℂ] H) :
    Matrix.trace (basisPrefixMatrix basis N operator) =
      ∑ i ∈ Finset.range N,
        ⟪basis i, operator (basis i)⟫_ℂ := by
  change (∑ i : Fin N,
    ⟪basis (i : ℕ), operator (basis (i : ℕ))⟫_ℂ) = _
  exact Fin.sum_univ_eq_sum_range
    (fun i => ⟪basis i, operator (basis i)⟫_ℂ) N

theorem trace_basisPrefixMatrix_re_eq_rangeDiagonal_re
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ) (operator : H →L[ℂ] H) :
    (Matrix.trace (basisPrefixMatrix basis N operator)).re =
      ∑ i ∈ Finset.range N,
        (⟪basis i, operator (basis i)⟫_ℂ).re := by
  rw [trace_basisPrefixMatrix_eq_rangeDiagonal]
  exact map_sum Complex.reCLM _ _

/-- A signed integral bound for finite compression traces feeds the ordered
exhaustion consumer without requiring bounds for arbitrary finite subsets. -/
theorem ordinaryTraceAlong_norm_le_of_prefixCompressionIntegralBound
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (C : ℝ)
    (htrace : PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedBandResponse owner lambda family))
    (hbound : ∀ N : ℕ,
      |∫ alpha : ℝ in 0..1,
        (Matrix.trace (basisPrefixMatrix basis N
          (actualMovingSoninRootFlow owner lambda alpha
            family.visiblePrimes))).re| ≤ C) :
    ‖PositiveTrace.ordinaryTraceAlong basis
      (rootSandwichedBandResponse owner lambda family)‖ ≤ C := by
  apply ordinaryTraceAlong_norm_le_of_rangeDiagonalIntegralBound
    basis owner lambda family C htrace
  intro N
  simpa only [trace_basisPrefixMatrix_re_eq_rangeDiagonal_re] using hbound N

theorem canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_prefixCompressionBound
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (htrace : PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner)))
    (hbound : ∀ N : ℕ,
      |∫ alpha : ℝ in 0..1,
        (Matrix.trace (basisPrefixMatrix basis N
          (actualMovingSoninRootFlow owner lambda alpha
            (canonicalFamily owner).visiblePrimes))).re| ≤
        2 * (owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3)) :
    ‖PositiveTrace.ordinaryTraceAlong basis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner))‖ ≤
      2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3) := by
  exact ordinaryTraceAlong_norm_le_of_prefixCompressionIntegralBound
    basis owner lambda (canonicalFamily owner)
      (2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3)) htrace hbound

end CCM24FiniteSMovingBandPrefixCompression
end CCM25Concrete
end Source
end ConnesWeilRH
