import ConnesWeilRH.Dev.C1LaneRStrictness
import ConnesWeilRH.Dev.C1LocalConfigurationDomination

/-!
# P2 negative diagonal certificate

The narrow D3 root has a strict negative Archimedean term when its seed has a
nonzero Laplace value at `2`.  Its square is prime-free on the same support,
so the complete gate is strictly negative.  This is an actual owner-preserving
negative diagonal candidate for the parity/two-span consumers; it does not
control a mixed cross gate or claim RH.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2NegativeDiagonalCertificate

open C1LaneRStrictness
open C1LaneRNarrowArch
open C1LocalConfigurationDomination
open C1SameOwnerWeil
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.CompactLogConvolution.CompactLogTest

theorem tripleVanishingRoot_ICgate_neg_of_narrow_base_of_laplaceAt_two_ne_zero
    (h : CompactLogTest)
    (hsupport : Function.support h.test ⊆
      Set.Icc (-narrowArchBaseWidth) narrowArchBaseWidth)
    (hlap : CompactLogTest.laplaceAt h (2 : ℂ) ≠ 0) :
    ICgate (C1LaneRD3Root.tripleVanishingRoot h).convolutionSquare < 0 := by
  have harch :=
    tripleVanishingRoot_archimedeanTerm_neg_of_narrow_base_of_laplaceAt_two_ne_zero
      h hsupport hlap
  have hprime :=
    finitePrimeSum_eq_zero_of_support_subset_open_log_two
      (C1LaneRD3Root.tripleVanishingRoot h).convolutionSquare
      (C1LaneRD3Root.tripleVanishingRoot_square_support_subset_open_log_two_of_Icc
        h hsupport (by
          dsimp [narrowArchBaseWidth]
          nlinarith [narrowArchRadius_lt_one]))
  unfold ICgate
  rw [hprime]
  simpa using harch

end C1P2NegativeDiagonalCertificate
end Source
end ConnesWeilRH
