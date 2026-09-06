import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.C1P2DefectZeroSumIdentity

/-!
# P2 prime-point matching

This leaf isolates an exact cancellation target for the Line-C producer.
The finite-prime part of the same-owner Weil functional reads the square test
at the finitely many visible points `± log n`; it does not read the Mellin
values used by the interpolation construction.  Matching those square point
values on the union of the two visible sets therefore cancels the complete
finite-prime sum, without assuming any sign or P2 conclusion.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2PrimePointMatching

open C1SameOwnerWeil
open C1HealthyYoshidaDetector
open C1LocalConfigurationDomination
open C1P2DefectZeroSumIdentity
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

/-- Matching a pair of real square-test values at every visible index of
either owner.  The union is intentional: the two owners may expose different
prime-power sets before matching. -/
def PrimePointMatch (F G : CompactLogTest) : Prop :=
  ∀ n ∈ globalPrimeIndexSet F ∪ globalPrimeIndexSet G,
    F.test (Real.log n) = G.test (Real.log n) ∧
      F.test (-Real.log n) = G.test (-Real.log n)

private theorem finitePrimeTermComplex_eq_of_point_match
    (F G : CompactLogTest) {n : Nat}
    (hmatch : F.test (Real.log n) = G.test (Real.log n) ∧
      F.test (-Real.log n) = G.test (-Real.log n)) :
    finitePrimeTermComplex F n = finitePrimeTermComplex G n := by
  unfold finitePrimeTermComplex
  rw [hmatch.1, hmatch.2]

private theorem finitePrimeTerm_eq_of_point_match
    (F G : CompactLogTest) {n : Nat}
    (hmatch : F.test (Real.log n) = G.test (Real.log n) ∧
      F.test (-Real.log n) = G.test (-Real.log n)) :
    finitePrimeTerm F n = finitePrimeTerm G n := by
  unfold finitePrimeTerm
  rw [finitePrimeTermComplex_eq_of_point_match F G hmatch]

private theorem finitePrimeTerm_eq_zero_of_not_mem
    (F : CompactLogTest) {n : Nat}
    (hn : n ∉ globalPrimeIndexSet F) :
    finitePrimeTerm F n = 0 := by
  have hzero : finitePrimeTermComplex F n = 0 := by
    by_contra hne
    apply hn
    exact (mem_globalPrimeIndexSet_iff F n).2
      ⟨finitePrimeTermComplex_nonzero_primePower F hne, hne⟩
  unfold finitePrimeTerm
  rw [hzero]
  rfl

/-- Exact finite-prime cancellation from pointwise matching on the union of
the visible prime-power owners.  This is the concrete finite target that a
future Line-C correction may try to enforce; it carries no archimedean sign
and no `qw` positivity. -/
theorem finitePrimeSum_eq_of_primePointMatch
    (F G : CompactLogTest)
    (hmatch : PrimePointMatch F G) :
    finitePrimeSum F = finitePrimeSum G := by
  let S : Finset Nat := globalPrimeIndexSet F ∪ globalPrimeIndexSet G
  have hF : ∑ n ∈ globalPrimeIndexSet F, finitePrimeTerm F n =
      ∑ n ∈ S, finitePrimeTerm F n := by
    dsimp [S]
    apply Finset.sum_subset (Finset.subset_union_left)
    intro n hn hnot
    exact finitePrimeTerm_eq_zero_of_not_mem F hnot
  have hG : ∑ n ∈ globalPrimeIndexSet G, finitePrimeTerm G n =
      ∑ n ∈ S, finitePrimeTerm G n := by
    dsimp [S]
    apply Finset.sum_subset (Finset.subset_union_right)
    intro n hn hnot
    exact finitePrimeTerm_eq_zero_of_not_mem G hnot
  unfold finitePrimeSum
  rw [hF, hG]
  apply Finset.sum_congr rfl
  intro n hn
  exact finitePrimeTerm_eq_of_point_match F G
    (hmatch n (by simpa [S] using hn))

/-- On triple-vanishing root owners, prime-point matching removes the entire
finite-prime part of the one-window defect gate.  The exact defect identity
therefore reduces to a difference of archimedean terms; no sign is asserted. -/
theorem defectGate_eq_archimedean_sub_of_primePointMatch
    (g W : CompactLogTest)
    (hgv : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (hWv : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet W)
    (hmatch : PrimePointMatch g.convolutionSquare W.convolutionSquare) :
    ICgate (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1)) =
      archimedeanTerm g.convolutionSquare -
        archimedeanTerm W.convolutionSquare := by
  rw [defectGate_eq_qw_sub g W hgv hWv,
    qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple
      g hgv,
    qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple
      W hWv,
    finitePrimeSum_eq_of_primePointMatch g.convolutionSquare
      W.convolutionSquare hmatch]
  ring

end C1P2PrimePointMatching
end Source
end ConnesWeilRH
