import ConnesWeilRH.Dev.C1P2SignedBudget
import ConnesWeilRH.Dev.C1GateMatrixRepresentation

/-!
# Finite-span readback of the selected prime profile

The signed-budget observable is evaluated on a convolution square, not on
the root test itself.  This leaf expands one actual prime-log profile term of
a finite root span into the pair-basis quadratic form.  It is an exact
same-owner algebraic interface; it proves no sign or RH statement.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2SpanProfileMatrix

open C1GateMatrixRepresentation
open C1P2BilateralProfile
open C1P2SignedBudget
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

noncomputable section

theorem signedProfileTerm_spanObj_eq_pair_profile_quadratic
    {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ) (n : ℕ) :
    signedProfileTerm (spanObj w y) n =
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
        (∑ i ∈ (Finset.univ : Finset (Fin k)),
          ∑ j ∈ (Finset.univ : Finset (Fin k)),
            ((y i * y j : ℝ) : ℂ) *
              bilateralProfile (pairTest w i j) (Real.log n)).re := by
  unfold signedProfileTerm bilateralProfile
  rw [convolutionSquare_spanObj_apply, convolutionSquare_spanObj_apply]
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]

end
end C1P2SpanProfileMatrix
end Source
end ConnesWeilRH
