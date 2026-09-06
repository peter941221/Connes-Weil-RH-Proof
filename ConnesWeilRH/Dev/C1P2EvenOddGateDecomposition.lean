import ConnesWeilRH.Dev.C1P2BilateralProfile
import ConnesWeilRH.Dev.C1HealthyDetectorArchRescue

/-!
# P2 even/odd gate decomposition

The even/odd correction family has an exact gate-level diagonalization.  The
polarized cross of an even and an odd test is odd, so its bilateral profile
and its complete finite-prime sum vanish.  The existing archimedean odd-kill
then removes the other cross channel.  This is an exact structural identity,
not a positivity assertion.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2EvenOddGateDecomposition

open C1HealthyDetectorArchRescue
open C1P2BilateralProfile
open C1LocalConfigurationDomination
open C1HealthyYoshidaDetector
open C1SameOwnerWeil
open CCM25Concrete.CompactLogConvolution

noncomputable section

private theorem finitePrimeTerm_eq_zero_of_not_mem
    (F : CompactLogTest) {n : ℕ}
    (hn : n ∉ globalPrimeIndexSet F) :
    finitePrimeTerm F n = 0 := by
  have hzero : finitePrimeTermComplex F n = 0 := by
    by_contra hne
    exact hn ((mem_globalPrimeIndexSet_iff F n).2
      ⟨finitePrimeTermComplex_nonzero_primePower F hne, hne⟩)
  unfold finitePrimeTerm
  rw [hzero]
  rfl

theorem finitePrimeSum_congr {F G : CompactLogTest}
    (h : F.test = G.test) :
    finitePrimeSum F = finitePrimeSum G := by
  have hFG : F = G := CompactLogTest.ext h
  subst hFG
  rfl

theorem finitePrimeTermComplex_sumTest_add
    (F G : CompactLogTest) (n : ℕ) :
    finitePrimeTermComplex (sumTest F G) n =
      finitePrimeTermComplex F n + finitePrimeTermComplex G n := by
  unfold finitePrimeTermComplex
  simp only [sumTest_apply, add_mul]
  ring

theorem finitePrimeTerm_sumTest_add
    (F G : CompactLogTest) (n : ℕ) :
    finitePrimeTerm (sumTest F G) n =
      finitePrimeTerm F n + finitePrimeTerm G n := by
  unfold finitePrimeTerm
  rw [finitePrimeTermComplex_sumTest_add]
  exact Complex.add_re _ _

theorem globalPrimeIndexSet_sumTest_subset_union
    (F G : CompactLogTest) :
    globalPrimeIndexSet (sumTest F G) ⊆
      globalPrimeIndexSet F ∪ globalPrimeIndexSet G := by
  intro n hn
  have hsum : finitePrimeTermComplex (sumTest F G) n ≠ 0 :=
    (mem_globalPrimeIndexSet_iff (sumTest F G) n).mp hn |>.2
  have hprime : IsPrimePow n :=
    (mem_globalPrimeIndexSet_iff (sumTest F G) n).mp hn |>.1
  by_contra hnot
  have hF : finitePrimeTermComplex F n = 0 := by
    by_contra hne
    exact hnot (Finset.mem_union.mpr (Or.inl
      ((mem_globalPrimeIndexSet_iff F n).2 ⟨hprime, hne⟩)))
  have hG : finitePrimeTermComplex G n = 0 := by
    by_contra hne
    exact hnot (Finset.mem_union.mpr (Or.inr
      ((mem_globalPrimeIndexSet_iff G n).2 ⟨hprime, hne⟩)))
  apply hsum
  rw [finitePrimeTermComplex_sumTest_add, hF, hG]
  simp

theorem finitePrimeSum_sumTest_add
    (F G : CompactLogTest) :
    finitePrimeSum (sumTest F G) =
      finitePrimeSum F + finitePrimeSum G := by
  let S : Finset ℕ :=
    globalPrimeIndexSet (sumTest F G) ∪
      (globalPrimeIndexSet F ∪ globalPrimeIndexSet G)
  have hsum :
      ∑ n ∈ globalPrimeIndexSet (sumTest F G), finitePrimeTerm (sumTest F G) n =
        ∑ n ∈ S, finitePrimeTerm (sumTest F G) n := by
    apply Finset.sum_subset
    · exact Finset.subset_union_left
    · intro n hn hnot
      exact finitePrimeTerm_eq_zero_of_not_mem (sumTest F G) hnot
  have hF :
      ∑ n ∈ globalPrimeIndexSet F, finitePrimeTerm F n =
        ∑ n ∈ S, finitePrimeTerm F n := by
    apply Finset.sum_subset
    · exact Finset.Subset.trans Finset.subset_union_left
        Finset.subset_union_right
    · intro n hn hnot
      exact finitePrimeTerm_eq_zero_of_not_mem F hnot
  have hG :
      ∑ n ∈ globalPrimeIndexSet G, finitePrimeTerm G n =
        ∑ n ∈ S, finitePrimeTerm G n := by
    apply Finset.sum_subset
    · exact Finset.Subset.trans Finset.subset_union_right
        Finset.subset_union_right
    · intro n hn hnot
      exact finitePrimeTerm_eq_zero_of_not_mem G hnot
  unfold finitePrimeSum
  rw [hsum, hF, hG]
  calc
    (∑ n ∈ S, finitePrimeTerm (sumTest F G) n) =
        ∑ n ∈ S, (finitePrimeTerm F n + finitePrimeTerm G n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact finitePrimeTerm_sumTest_add F G n
    _ = (∑ n ∈ S, finitePrimeTerm F n) +
          ∑ n ∈ S, finitePrimeTerm G n := Finset.sum_add_distrib

theorem finitePrimeSum_crossTest_eq_zero_of_even_odd
    (f g : CompactLogTest)
    (hf : ∀ x : ℝ, f.test (-x) = f.test x)
    (hg : ∀ x : ℝ, g.test (-x) = -g.test x) :
    finitePrimeSum (crossTest f g) = 0 := by
  exact finitePrimeSum_eq_zero_of_test_odd (crossTest f g)
    (test_neg_crossTest_of_even_odd f g hf hg)

theorem finitePrimeSum_convolutionSquare_sumTest_eq_add_of_even_odd
    (f g : CompactLogTest)
    (hf : ∀ x : ℝ, f.test (-x) = f.test x)
    (hg : ∀ x : ℝ, g.test (-x) = -g.test x) :
    finitePrimeSum (sumTest f g).convolutionSquare =
      finitePrimeSum f.convolutionSquare +
        finitePrimeSum g.convolutionSquare := by
  have howner :
      (sumTest f g).convolutionSquare =
        sumTest (sumTest f.convolutionSquare g.convolutionSquare)
          (crossTest f g) := by
    apply CompactLogTest.ext
    ext y
    rw [convolutionSquare_sumTest_apply f g y]
    simp [sumTest_apply]
  calc
    finitePrimeSum (sumTest f g).convolutionSquare =
        finitePrimeSum
          (sumTest (sumTest f.convolutionSquare g.convolutionSquare)
            (crossTest f g)) := by rw [howner]
    _ = finitePrimeSum (sumTest f.convolutionSquare g.convolutionSquare) +
          finitePrimeSum (crossTest f g) :=
      finitePrimeSum_sumTest_add _ _
    _ = (finitePrimeSum f.convolutionSquare +
          finitePrimeSum g.convolutionSquare) + 0 := by
      rw [finitePrimeSum_sumTest_add,
        finitePrimeSum_crossTest_eq_zero_of_even_odd f g hf hg]
    _ = finitePrimeSum f.convolutionSquare +
          finitePrimeSum g.convolutionSquare := by ring

/-- The full same-owner gate diagonalizes on the even/odd correction class.
The cross term is killed independently on the archimedean and arithmetic
sides; no sign is asserted. -/
theorem ICgate_convolutionSquare_sumTest_eq_add_of_even_odd
    (f g : CompactLogTest)
    (hf : ∀ x : ℝ, f.test (-x) = f.test x)
    (hg : ∀ x : ℝ, g.test (-x) = -g.test x) :
    ICgate (sumTest f g).convolutionSquare =
      ICgate f.convolutionSquare + ICgate g.convolutionSquare := by
  unfold ICgate
  rw [archimedeanTerm_convolutionSquare_sumTest_of_even_odd f g hf hg,
    finitePrimeSum_convolutionSquare_sumTest_eq_add_of_even_odd f g hf hg]
  ring

theorem qw_eq_neg_diagonal_gate_sum_of_even_odd_of_vanishes
    (f g : CompactLogTest)
    (hf : ∀ x : ℝ, f.test (-x) = f.test x)
    (hg : ∀ x : ℝ, g.test (-x) = -g.test x)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet (sumTest f g)) :
    C1SameOwnerWeil.qw (sumTest f g) =
      -(ICgate f.convolutionSquare + ICgate g.convolutionSquare) := by
  have hgate := ICgate_convolutionSquare_sumTest_eq_add_of_even_odd
    f g hf hg
  rw [qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple
    (sumTest f g) hvanishes, ← hgate]
  unfold ICgate
  ring

theorem qw_nonneg_of_diagonal_gate_nonpos_of_even_odd_of_vanishes
    (f g : CompactLogTest)
    (hf : ∀ x : ℝ, f.test (-x) = f.test x)
    (hg : ∀ x : ℝ, g.test (-x) = -g.test x)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet (sumTest f g))
    (hfGate : ICgate f.convolutionSquare ≤ 0)
    (hgGate : ICgate g.convolutionSquare ≤ 0) :
    0 ≤ C1SameOwnerWeil.qw (sumTest f g) := by
  rw [qw_eq_neg_diagonal_gate_sum_of_even_odd_of_vanishes
    f g hf hg hvanishes]
  linarith

end
end C1P2EvenOddGateDecomposition
end Source
end ConnesWeilRH
