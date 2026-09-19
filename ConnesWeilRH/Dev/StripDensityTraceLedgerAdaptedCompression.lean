/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.StripDensityTraceLedger

/-!
# The compression obligation for adapted bases

`StripDensityTraceLedger.StripDensityCompressionObligation` — the trace-level
compression inequality `re Tr(P T P) <= re Tr(T)` for `T` positive — was
filed as a named obligation because its standard proof factors `T` through an
operator square root, which the tree's layer lacks (and because the naive
operator sandwich `P T P <= T` is false as stated; the audit companion
carries the explicit two-dimensional counterexample).

This module discharges the obligation in the case that matters for the
applications: when the basis is **adapted to** `P` in the sense that every
basis vector is either fixed by `P` or killed by it.  No square root is
needed — the pointwise diagonal bound is pure positivity bookkeeping:

  `re << basis i, (P - T - P) (basis i) >>`
    = `re << P (basis i), T (P (basis i)) >>`
    = `re << basis i, T (basis i) >>`   (if `P (basis i) = basis i`)
    = 0                                  (if `P (basis i) = 0`),

and `T` positive makes every undone diagonal nonnegative, so
`tsum_le_tsum` finishes.  Only self-adjointness of `P` is used.

The two intended instances: the carrier basis is adapted to the carrier
projection (each basis vector satisfies `R_0 e_i = e_i`), and any Hilbert
basis split into a basis of `range P` and one of `ker P` is adapted.
-/

namespace ConnesWeilRH
namespace Dev
namespace StripDensityTraceLedgerAdaptedCompression

open scoped ComplexConjugate InnerProduct InnerProductSpace
open ConnesWeilRH.Source.CC20Concrete.PositiveTrace

variable {ι H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The diagonal of `P T P` at a basis vector, folded through `P`'s
self-adjointness.  (No `omit`: `P.adjoint` itself needs the completeness
instance, since Riesz representation is where it lives.) -/
theorem re_diagonal_PTP_eq (basis : HilbertBasis ι ℂ H)
    {P T : H →L[ℂ] H} (hPadj : P.adjoint = P) (i : ι) :
    (⟪basis i, (P ∘L T ∘L P) (basis i)⟫_ℂ).re
      = (⟪P (basis i), T (P (basis i))⟫_ℂ).re := by
  simp only [ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← hPadj]
  rw [ContinuousLinearMap.adjoint_inner_right, hPadj]

/-- **The compression inequality for `P`-adapted bases.**  If every basis
vector is fixed or killed by the self-adjoint operator `P`, then for every
positive `T` whose diagonal series converges along the basis,

  `re Tr(P T P) <= re Tr(T)`.

This discharges `StripDensityCompressionObligation` for adapted bases and
repairs the middle step of record 1625 section 2's chain at the same level
of generality its applications use. -/
theorem ordinaryTraceAlong_re_PTP_le_of_adaptedBasis
    (basis : HilbertBasis ι ℂ H)
    {P T : H →L[ℂ] H} (hPadj : P.adjoint = P)
    (hTpos : T.IsPositive)
    (hPsum : IsTraceClassAlong basis (P ∘L T ∘L P))
    (hTsum : IsTraceClassAlong basis T)
    (hadapted : ∀ i, P (basis i) = basis i ∨ P (basis i) = 0) :
    (ordinaryTraceAlong basis (P ∘L T ∘L P)).re
      ≤ (ordinaryTraceAlong basis T).re := by
  rw [ConnesWeilRH.Dev.StripDensityTraceLedger.re_ordinaryTraceAlong_eq_tsum_re
      basis _ hPsum,
    ConnesWeilRH.Dev.StripDensityTraceLedger.re_ordinaryTraceAlong_eq_tsum_re
      basis T hTsum]
  refine (hPsum.mapL Complex.reCLM).tsum_le_tsum (fun i => ?_)
    (hTsum.mapL Complex.reCLM)
  rw [re_diagonal_PTP_eq basis hPadj i]
  rcases hadapted i with h | h
  · rw [h]
  · rw [h, inner_zero_left]
    exact hTpos.re_inner_nonneg_right (basis i)

/-- The adapted-basis instance of the named compression obligation. -/
theorem stripDensityCompressionObligation_of_adaptedBasis
    (basis : HilbertBasis ι ℂ H)
    {P T : H →L[ℂ] H} (hPadj : P.adjoint = P)
    (hTpos : T.IsPositive)
    (hPsum : IsTraceClassAlong basis (P ∘L T ∘L P))
    (hTsum : IsTraceClassAlong basis T)
    (hadapted : ∀ i, P (basis i) = basis i ∨ P (basis i) = 0) :
    ConnesWeilRH.Dev.StripDensityTraceLedger.StripDensityCompressionObligation
      basis P T :=
  ordinaryTraceAlong_re_PTP_le_of_adaptedBasis basis hPadj hTpos hPsum hTsum
    hadapted

end StripDensityTraceLedgerAdaptedCompression
end Dev
end ConnesWeilRH
