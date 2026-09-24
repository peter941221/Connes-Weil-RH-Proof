/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1P2SpanProfileMatrix

/-!
# Aggregate physical readback for the four-point span owner

The per-node four-channel expansion is useful only when it is attached to the
actual finite visible-prime set of the span owner.  This leaf performs that
finite aggregation without replacing the owner by the original orbit test or
by an ambient cutoff.
-/

namespace ConnesWeilRH
namespace Source
namespace C1FourPointAggregatePhysicalReadback

open C1GateMatrixRepresentation
open C1P2BilateralProfile
open C1P2SignedBudget
open C1P2SpanProfileMatrix
open C1SameOwnerWeil
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

theorem finitePrimeSum_twoSpan_eq_four_pair_profiles
    (A B : CompactLogTest) (lam : ℝ) :
    finitePrimeSum (spanObj ![A, B] ![(1 : ℝ), -lam]).convolutionSquare =
      ∑ n ∈ globalPrimeIndexSet (spanObj ![A, B] ![(1 : ℝ), -lam]).convolutionSquare,
        ((ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (bilateralProfile (pairTest ![A, B] 0 0) (Real.log n)).re) -
          lam * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (bilateralProfile (pairTest ![A, B] 0 1) (Real.log n)).re) -
          lam * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (bilateralProfile (pairTest ![A, B] 1 0) (Real.log n)).re) +
          lam ^ 2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (bilateralProfile (pairTest ![A, B] 1 1) (Real.log n)).re)) := by
  rw [finitePrimeSum_eq_bilateralProfile_weighted_sum]
  exact Finset.sum_congr
    (s₁ := globalPrimeIndexSet (spanObj ![A, B] ![(1 : ℝ), -lam]).convolutionSquare)
    (s₂ := globalPrimeIndexSet (spanObj ![A, B] ![(1 : ℝ), -lam]).convolutionSquare)
    rfl (fun n hn => by
    simpa [signedProfileTerm, div_eq_mul_inv] using
      signedProfileTerm_twoSpan_eq_four_pair_profiles A B lam n)

theorem finitePrimeSum_twoSpan_eq_four_pair_physical_integrals
    (A B : CompactLogTest) (lam : ℝ) :
    finitePrimeSum (spanObj ![A, B] ![(1 : ℝ), -lam]).convolutionSquare =
      ∑ n ∈ globalPrimeIndexSet (spanObj ![A, B] ![(1 : ℝ), -lam]).convolutionSquare,
        ((ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (((∫ t : ℝ, star (A.test (-t)) * A.test (Real.log n - t)) +
              ∫ t : ℝ, star (A.test (-t)) * A.test (-Real.log n - t))).re) -
          lam * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (((∫ t : ℝ, star (A.test (-t)) * B.test (Real.log n - t)) +
              ∫ t : ℝ, star (A.test (-t)) * B.test (-Real.log n - t))).re) -
          lam * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (((∫ t : ℝ, star (B.test (-t)) * A.test (Real.log n - t)) +
              ∫ t : ℝ, star (B.test (-t)) * A.test (-Real.log n - t))).re) +
          lam ^ 2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (((∫ t : ℝ, star (B.test (-t)) * B.test (Real.log n - t)) +
              ∫ t : ℝ, star (B.test (-t)) * B.test (-Real.log n - t))).re)) := by
  rw [finitePrimeSum_eq_bilateralProfile_weighted_sum]
  exact Finset.sum_congr
    (s₁ := globalPrimeIndexSet (spanObj ![A, B] ![(1 : ℝ), -lam]).convolutionSquare)
    (s₂ := globalPrimeIndexSet (spanObj ![A, B] ![(1 : ℝ), -lam]).convolutionSquare)
    rfl (fun n hn => by
    simpa [signedProfileTerm, div_eq_mul_inv] using
      signedProfileTerm_twoSpan_eq_four_pair_physical_integrals A B lam n)

end C1FourPointAggregatePhysicalReadback
end Source
end ConnesWeilRH
