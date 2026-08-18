import ConnesWeilRH.Dev.C1XiCenterTwoGammaTailEstimate

/-!
# C1XiCenterTwoGammaPrefixTailConsumer - coupled sign consumer

This module consumes the exact constant/prefix/tail decomposition and the
absolute tail estimate.  It does not produce the finite constrained-prefix
inequality; it records the final order argument once that inequality is
supplied by a later owner.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoGammaPrefixTailConsumer

open C1SameOwnerWeil
open C1XiCenterTwoGammaSummedKernel
open C1XiCenterTwoGammaTailEstimate
open CCM25Concrete.CompactLogConvolution

noncomputable section

private theorem profileTail_re_le_tailNorm
    (F : CompactLogTest) (N : Nat) :
    (gammaRArchProfileTail F N).re ≤ gammaRArchProfileTailNorm F N := by
  exact (Complex.re_le_norm _).trans
    (norm_gammaRArchProfileTail_le_tailNorm F N)

/-- A finite-prefix upper bound and an absolute tail budget imply the full
archimedean term is nonpositive.  The budget is deliberately an abstract real
number so later producers can choose their own mass normalization. -/
theorem archimedeanTerm_nonpos_of_profilePrefix_bound_and_tailNorm_bound
    (F : CompactLogTest) (N : Nat) (budget : Real)
    (hprefix :
      ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
          F.test 0).re) +
        (∑ n ∈ Finset.range N, gammaRArchProfileIntegral F n).re ≤ -budget)
    (htail : gammaRArchProfileTailNorm F N ≤ budget) :
    C1SameOwnerWeil.archimedeanTerm F ≤ 0 := by
  rw [archimedeanTerm_eq_constant_add_profilePrefix_add_tail_re F N]
  have htailRe : (gammaRArchProfileTail F N).re ≤ budget :=
    (profileTail_re_le_tailNorm F N).trans htail
  linarith

/-- A strict finite-prefix margin survives an absolute tail budget. -/
theorem archimedeanTerm_neg_of_profilePrefix_bound_and_tailNorm_bound
    (F : CompactLogTest) (N : Nat) (budget delta : Real)
    (hdelta : 0 < delta)
    (hprefix :
      ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
          F.test 0).re) +
        (∑ n ∈ Finset.range N, gammaRArchProfileIntegral F n).re ≤
          -(budget + delta))
    (htail : gammaRArchProfileTailNorm F N ≤ budget) :
    C1SameOwnerWeil.archimedeanTerm F < 0 := by
  rw [archimedeanTerm_eq_constant_add_profilePrefix_add_tail_re F N]
  have htailRe : (gammaRArchProfileTail F N).re ≤ budget :=
    (profileTail_re_le_tailNorm F N).trans htail
  linarith

end
end C1XiCenterTwoGammaPrefixTailConsumer
end Source
end ConnesWeilRH
