import ConnesWeilRH.Dev.C1P2EvenOddGateDecomposition
import ConnesWeilRH.Dev.C1LaneRNarrowArch

/-!
# P2 narrow diagonal consumer

This leaf identifies a concrete sufficient condition for the two diagonal
gates exposed by the even/odd decomposition.  If each square stays in a
prime-free narrow interval and satisfies the existing archimedean budget,
then each diagonal gate is nonpositive and the summed detector has
nonnegative `qw`.  The narrow support hypotheses remain explicit: no theorem
here transfers the larger orbit detector into this class.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2NarrowDiagonalConsumer

open C1HealthyDetectorArchRescue
open C1HealthyYoshidaDetector
open C1LaneRNarrowArch
open C1LocalConfigurationDomination
open C1P2EvenOddGateDecomposition
open C1OrbitWindowSemiLocalGate
open C1SameOwnerWeil
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution

noncomputable section

theorem diagonalICgate_nonpos_of_primeFree_archimedean_nonpos
    (F : CompactLogTest)
    (hsupport : Function.support F.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2))
    (harch : archimedeanTerm F ≤ 0) :
    ICgate F ≤ 0 := by
  unfold ICgate
  rw [finitePrimeSum_eq_zero_of_support_subset_open_log_two F hsupport]
  linarith

theorem not_both_diagonalICgate_nonpos_of_primeFree_positive_arch_sum
    (f g : CompactLogTest)
    (hsf : Function.support f.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2))
    (hsg : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2))
    (harch : archimedeanTerm f.convolutionSquare +
      archimedeanTerm g.convolutionSquare > 0) :
    ¬ (ICgate f.convolutionSquare ≤ 0 ∧ ICgate g.convolutionSquare ≤ 0) := by
  intro hpair
  unfold ICgate at hpair
  rw [finitePrimeSum_eq_zero_of_support_subset_open_log_two
      f.convolutionSquare hsf,
    finitePrimeSum_eq_zero_of_support_subset_open_log_two
      g.convolutionSquare hsg] at hpair
  linarith

theorem diagonalICgate_nonpos_of_narrowBudget
    (F : CompactLogTest) (R : ℝ)
    (hRpos : 0 < R) (hRlt : R < 1)
    (hRlog2 : R < Real.log 2)
    (hsupport : Function.support F.convolutionSquare.test ⊆ Set.Ioo (-R) R)
    (hbudget :
      Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + R -
          (1 / 2 : ℝ) * Real.log (1 / R) ≤ 0) :
    ICgate F.convolutionSquare ≤ 0 := by
  apply diagonalICgate_nonpos_of_primeFree_archimedean_nonpos
    F.convolutionSquare
  · exact Set.Subset.trans hsupport
      (Set.Ioo_subset_Ioo (neg_lt_neg hRlog2).le hRlog2.le)
  · exact archimedeanTerm_nonpos_of_narrow_budget F R hRpos hRlt
      hsupport hbudget

theorem cc20TripleVanishes_of_even_odd_nodal
    (f g : CompactLogTest)
    (hg : ∀ x : ℝ, g.test (-x) = -g.test x)
    (hf0 : CompactLogTest.laplaceAt f 0 = 0)
    (hhalf : CompactLogTest.laplaceAt f (1 / 2 : ℂ) +
      CompactLogTest.laplaceAt g (1 / 2 : ℂ) = 0)
    (hone : CompactLogTest.laplaceAt f 1 +
      CompactLogTest.laplaceAt g 1 = 0) :
    CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet (sumTest f g) := by
  intro p _hp
  change CompactLogTest.laplaceAt (sumTest f g)
    (criticalVanishingPointValue p) = 0
  rw [laplaceAt_sumTest]
  cases p
  · have hv : criticalVanishingPointValue CriticalVanishingPoint.zero = 0 := rfl
    rw [hv, hf0, laplaceAt_eq_zero_of_test_odd g hg]
    simp
  · have hv : criticalVanishingPointValue CriticalVanishingPoint.half =
      (1 / 2 : ℂ) := rfl
    rw [hv]
    exact hhalf
  · have hv : criticalVanishingPointValue CriticalVanishingPoint.one = 1 := rfl
    rw [hv]
    exact hone

theorem qw_nonneg_of_even_odd_narrow_diagonal
    (f g : CompactLogTest)
    (hf : ∀ x : ℝ, f.test (-x) = f.test x)
    (hg : ∀ x : ℝ, g.test (-x) = -g.test x)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet (sumTest f g))
    (Rf Rg : ℝ)
    (hRfpos : 0 < Rf) (hRgpos : 0 < Rg)
    (hRf_lt : Rf < 1) (hRg_lt : Rg < 1)
    (hRf_log2 : Rf < Real.log 2) (hRg_log2 : Rg < Real.log 2)
    (hsf : Function.support f.convolutionSquare.test ⊆ Set.Ioo (-Rf) Rf)
    (hsg : Function.support g.convolutionSquare.test ⊆ Set.Ioo (-Rg) Rg)
    (hbf :
      Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + Rf -
          (1 / 2 : ℝ) * Real.log (1 / Rf) ≤ 0)
    (hbg :
      Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + Rg -
          (1 / 2 : ℝ) * Real.log (1 / Rg) ≤ 0) :
    0 ≤ qw (sumTest f g) := by
  apply qw_nonneg_of_diagonal_gate_nonpos_of_even_odd_of_vanishes
    f g hf hg hvanishes
  · exact diagonalICgate_nonpos_of_narrowBudget f Rf
      hRfpos hRf_lt hRf_log2 hsf hbf
  · exact diagonalICgate_nonpos_of_narrowBudget g Rg
      hRgpos hRg_lt hRg_log2 hsg hbg

theorem qw_nonneg_of_even_odd_nodal_narrow_diagonal
    (f g : CompactLogTest)
    (hf : ∀ x : ℝ, f.test (-x) = f.test x)
    (hg : ∀ x : ℝ, g.test (-x) = -g.test x)
    (hf0 : CompactLogTest.laplaceAt f 0 = 0)
    (hhalf : CompactLogTest.laplaceAt f (1 / 2 : ℂ) +
      CompactLogTest.laplaceAt g (1 / 2 : ℂ) = 0)
    (hone : CompactLogTest.laplaceAt f 1 +
      CompactLogTest.laplaceAt g 1 = 0)
    (Rf Rg : ℝ)
    (hRfpos : 0 < Rf) (hRgpos : 0 < Rg)
    (hRf_lt : Rf < 1) (hRg_lt : Rg < 1)
    (hRf_log2 : Rf < Real.log 2) (hRg_log2 : Rg < Real.log 2)
    (hsf : Function.support f.convolutionSquare.test ⊆ Set.Ioo (-Rf) Rf)
    (hsg : Function.support g.convolutionSquare.test ⊆ Set.Ioo (-Rg) Rg)
    (hbf :
      Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + Rf -
          (1 / 2 : ℝ) * Real.log (1 / Rf) ≤ 0)
    (hbg :
      Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + Rg -
          (1 / 2 : ℝ) * Real.log (1 / Rg) ≤ 0) :
    0 ≤ qw (sumTest f g) := by
  apply qw_nonneg_of_even_odd_narrow_diagonal f g hf hg
    (cc20TripleVanishes_of_even_odd_nodal f g hg hf0 hhalf hone)
    Rf Rg hRfpos hRgpos hRf_lt hRg_lt hRf_log2 hRg_log2 hsf hsg hbf hbg

end
end C1P2NarrowDiagonalConsumer
end Source
end ConnesWeilRH
