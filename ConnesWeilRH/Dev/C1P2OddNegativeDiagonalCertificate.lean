import ConnesWeilRH.Dev.C1LaneRNarrowArch
import ConnesWeilRH.Dev.C1P2EvenOddGateDecomposition

/-!
# P2 odd negative diagonal certificate

The narrow Archimedean budget applies directly to an odd owner.  If its
convolution square stays inside the open log-2 window and has positive mass,
then the complete same-owner gate is strictly negative because the visible
prime sum vanishes.  This is the parity-compatible negative diagonal socket
for the even/odd two-span consumer; nodal and detector-preservation data are
separate obligations.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2OddNegativeDiagonalCertificate

open C1LaneRNarrowArch
open C1P2EvenOddGateDecomposition
open C1LocalConfigurationDomination
open C1SameOwnerWeil
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open Set

theorem odd_ICgate_neg_of_narrow_budget
    (g : CompactLogTest)
    (hodd : ∀ x : ℝ, g.test (-x) = -g.test x)
    (R : ℝ)
    (hRpos : 0 < R) (hRlt : R < 1) (hRlog2 : R < Real.log 2)
    (hsupport : Function.support g.convolutionSquare.test ⊆ Ioo (-R) R)
    (hbudget :
      Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + R -
          (1 / 2 : ℝ) * Real.log (1 / R) < 0)
    (hmass : 0 < (g.convolutionSquare.test 0).re) :
    ICgate g.convolutionSquare < 0 := by
  have harch := archimedeanTerm_neg_of_narrow_budget
    g R hRpos hRlt hsupport hbudget hmass
  have hopen : Function.support g.convolutionSquare.test ⊆
      Ioo (-Real.log 2) (Real.log 2) := by
    intro x hx
    rcases hsupport hx with ⟨hlower, hupper⟩
    constructor <;> linarith
  have hprime := finitePrimeSum_eq_zero_of_support_subset_open_log_two
    g.convolutionSquare hopen
  unfold ICgate
  rw [hprime]
  simpa using harch

end C1P2OddNegativeDiagonalCertificate
end Source
end ConnesWeilRH
