import ConnesWeilRH.Dev.C1CrossingCommonCarrier
import ConnesWeilRH.Dev.C1SameOwnerWeil
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# C1CrossingEulerLogReadback - finite Euler-log readback on one carrier

Stage 2 of the positive-trace producer keeps the common-carrier owner from
Stage 1 and inserts the exact Euler-log coefficient for each prime power.
The results here are finite algebraic readbacks only.  They do not assert
positivity, a cutoff limit, or the still-open pole/archimedean reorganization.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CrossingEulerLogReadback

open CCM25Concrete.SelectedCrossingKernel
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedWeilSquare
open C1CrossingCommonCarrier
open C1SameOwnerWeil
open scoped BigOperators

noncomputable section

/- The coefficient is kept in Complex form because the crossing trace is
   Complex-valued; the real Weil term is obtained only after the finite sum. -/
noncomputable def eulerLogWeightedCarrierPairTrace
    {h : ℝ → ℂ} {hh : Continuous h} {a c : ℝ} {S : Finset ℝ}
    (data : CrossingCommonCarrierData h hh a c S)
    (p m : ℕ) : ℂ :=
  (((1 / Real.sqrt ((p ^ m : ℕ) : ℝ)) / (m : ℝ) : ℝ) : ℂ) *
    (data.carrierPairTrace ((m : ℝ) * Real.log (p : ℝ)) +
      data.carrierReversePairTrace ((m : ℝ) * Real.log (p : ℝ)))

theorem eulerLogWeightedCarrierPairTrace_eq_finitePrimeTerm_pow
    (owner : SelectedWeilSquareOwner)
    (a c : ℝ) (S : Finset ℝ)
    (data : CrossingCommonCarrierData owner.sourceTest.test
      owner.sourceTest.test.continuous a c S)
    {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hmem : (m : ℝ) * Real.log (p : ℝ) ∈ S) :
    eulerLogWeightedCarrierPairTrace data p m =
      owner.finitePrimeTerm (p ^ m) := by
  unfold eulerLogWeightedCarrierPairTrace
  rw [data.carrier_pair_trace _ hmem,
    data.carrier_reverse_pair_trace _ hmem]
  exact eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow
    owner a c hp hm hsupp (data.intervalBasis _)

theorem eulerLogWeightedCarrierPairTrace_sum_eq_finitePrimeTerm_pow_sum
    (owner : SelectedWeilSquareOwner)
    (a c : ℝ) (S : Finset ℝ)
    (data : CrossingCommonCarrierData owner.sourceTest.test
      owner.sourceTest.test.continuous a c S)
    (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    (hnonzero : ∀ pm ∈ terms, pm.2 ≠ 0)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hmem : ∀ pm ∈ terms,
      (pm.2 : ℝ) * Real.log (pm.1 : ℝ) ∈ S) :
    (∑ pm ∈ terms, eulerLogWeightedCarrierPairTrace data pm.1 pm.2) =
      ∑ pm ∈ terms, owner.finitePrimeTerm (pm.1 ^ pm.2) := by
  apply Finset.sum_congr rfl
  intro pm hpm
  exact eulerLogWeightedCarrierPairTrace_eq_finitePrimeTerm_pow
    owner a c S data (hprime pm hpm) (hnonzero pm hpm) hsupp (hmem pm hpm)

theorem eulerLogWeightedCarrierPairTrace_sum_re_eq_finitePrimeTerm_pow_sum_re
    (owner : SelectedWeilSquareOwner)
    (a c : ℝ) (S : Finset ℝ)
    (data : CrossingCommonCarrierData owner.sourceTest.test
      owner.sourceTest.test.continuous a c S)
    (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    (hnonzero : ∀ pm ∈ terms, pm.2 ≠ 0)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hmem : ∀ pm ∈ terms,
      (pm.2 : ℝ) * Real.log (pm.1 : ℝ) ∈ S) :
    (∑ pm ∈ terms, eulerLogWeightedCarrierPairTrace data pm.1 pm.2).re =
      ∑ pm ∈ terms, (owner.finitePrimeTerm (pm.1 ^ pm.2)).re := by
  rw [eulerLogWeightedCarrierPairTrace_sum_eq_finitePrimeTerm_pow_sum
    owner a c S data terms hprime hnonzero hsupp hmem]
  simp

/- The active C1 owner indexes visible terms by naturals.  This canonical
   conversion records the unique prime/exponent coordinates without importing
   the frozen finite-S family. -/
noncomputable def canonicalPrimePowerTerm (n : ℕ) : ℕ × ℕ :=
  (n.minFac, n.factorization n.minFac)

theorem canonicalPrimePowerTerm_prime
    (owner : SelectedWeilSquareOwner) {n : ℕ}
    (hn : n ∈ (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet) :
    (canonicalPrimePowerTerm n).1.Prime := by
  have hnprime : IsPrimePow n :=
    ((SelectedFinitePrimeSupportData.ofOwner owner).globalExact n).mp hn |>.1
  exact Nat.minFac_prime (ne_of_gt hnprime.one_lt)

theorem canonicalPrimePowerTerm_exponent_ne_zero
    (owner : SelectedWeilSquareOwner) {n : ℕ}
    (hn : n ∈ (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet) :
    (canonicalPrimePowerTerm n).2 ≠ 0 := by
  have hnprime : IsPrimePow n :=
    ((SelectedFinitePrimeSupportData.ofOwner owner).globalExact n).mp hn |>.1
  intro hexponent
  have hpow := hnprime.minFac_pow_factorization_eq
  rw [show n.factorization n.minFac = 0 by
    simpa [canonicalPrimePowerTerm] using hexponent, pow_zero] at hpow
  exact (ne_of_gt hnprime.one_lt) hpow.symm

theorem canonicalPrimePowerTerm_pow_eq
    (owner : SelectedWeilSquareOwner) {n : ℕ}
    (hn : n ∈ (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet) :
    (canonicalPrimePowerTerm n).1 ^ (canonicalPrimePowerTerm n).2 = n := by
  have hnprime : IsPrimePow n :=
    ((SelectedFinitePrimeSupportData.ofOwner owner).globalExact n).mp hn |>.1
  simpa [canonicalPrimePowerTerm] using hnprime.minFac_pow_factorization_eq

noncomputable def canonicalPrimePowerTerms
    (owner : SelectedWeilSquareOwner) : Finset (ℕ × ℕ) :=
  (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet.attach.image
    fun n => canonicalPrimePowerTerm n.1

theorem canonicalPrimePowerTerms_prime
    (owner : SelectedWeilSquareOwner) {pm : ℕ × ℕ}
    (hpm : pm ∈ canonicalPrimePowerTerms owner) :
    pm.1.Prime := by
  rw [canonicalPrimePowerTerms, Finset.mem_image] at hpm
  obtain ⟨n, _hn, rfl⟩ := hpm
  exact canonicalPrimePowerTerm_prime owner n.2

theorem canonicalPrimePowerTerms_exponent_ne_zero
    (owner : SelectedWeilSquareOwner) {pm : ℕ × ℕ}
    (hpm : pm ∈ canonicalPrimePowerTerms owner) :
    pm.2 ≠ 0 := by
  rw [canonicalPrimePowerTerms, Finset.mem_image] at hpm
  obtain ⟨n, _hn, rfl⟩ := hpm
  exact canonicalPrimePowerTerm_exponent_ne_zero owner n.2

theorem canonicalPrimePowerTerms_sum_eq_selectedFinitePrimeTerm_sum
    (owner : SelectedWeilSquareOwner) :
    (∑ pm ∈ canonicalPrimePowerTerms owner,
      owner.finitePrimeTerm (pm.1 ^ pm.2)) =
      ∑ n ∈ (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet,
        owner.finitePrimeTerm n := by
  have hinj : Set.InjOn
      (fun n : {n // n ∈
        (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet} =>
          canonicalPrimePowerTerm n.1)
      (↑((SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet.attach) : Set _) := by
    intro x _hx y _hy hxy
    apply Subtype.ext
    calc
      x.1 = (canonicalPrimePowerTerm x.1).1 ^
          (canonicalPrimePowerTerm x.1).2 :=
        (canonicalPrimePowerTerm_pow_eq owner x.2).symm
      _ = (canonicalPrimePowerTerm y.1).1 ^
          (canonicalPrimePowerTerm y.1).2 :=
        congrArg (fun pm : ℕ × ℕ => pm.1 ^ pm.2) hxy
      _ = y.1 := canonicalPrimePowerTerm_pow_eq owner y.2
  rw [canonicalPrimePowerTerms, Finset.sum_image hinj]
  calc
    (∑ n ∈ (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet.attach,
        owner.finitePrimeTerm
          ((canonicalPrimePowerTerm n.1).1 ^ (canonicalPrimePowerTerm n.1).2)) =
        ∑ n ∈ (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet.attach,
          owner.finitePrimeTerm n.1 := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact congrArg owner.finitePrimeTerm
        (canonicalPrimePowerTerm_pow_eq owner n.2)
    _ = ∑ n ∈ (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet,
          owner.finitePrimeTerm n :=
      Finset.sum_attach _ _

noncomputable def canonicalCrossingLengthSet
    (owner : SelectedWeilSquareOwner) : Finset ℝ :=
  (canonicalPrimePowerTerms owner).image
    fun pm => (pm.2 : ℝ) * Real.log (pm.1 : ℝ)

theorem canonicalCrossingLength_mem
    (owner : SelectedWeilSquareOwner) {pm : ℕ × ℕ}
    (hpm : pm ∈ canonicalPrimePowerTerms owner) :
    (pm.2 : ℝ) * Real.log (pm.1 : ℝ) ∈
      canonicalCrossingLengthSet owner := by
  exact Finset.mem_image.mpr ⟨pm, hpm, rfl⟩

theorem canonicalEulerLogCarrierPairTrace_sum_re_eq_selectedFinitePrimeTerm_sum
    (owner : SelectedWeilSquareOwner)
    (a c : ℝ)
    (data : CrossingCommonCarrierData owner.sourceTest.test
      owner.sourceTest.test.continuous a c (canonicalCrossingLengthSet owner))
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c) :
    (∑ pm ∈ canonicalPrimePowerTerms owner,
      eulerLogWeightedCarrierPairTrace data pm.1 pm.2).re =
      ∑ n ∈ (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet,
        owner.finitePrimeTermReal n := by
  rw [eulerLogWeightedCarrierPairTrace_sum_eq_finitePrimeTerm_pow_sum
    owner a c (canonicalCrossingLengthSet owner) data
      (canonicalPrimePowerTerms owner)
      (fun pm hpm => canonicalPrimePowerTerms_prime owner hpm)
      (fun pm hpm => canonicalPrimePowerTerms_exponent_ne_zero owner hpm)
      hsupp
      (fun pm hpm => canonicalCrossingLength_mem owner hpm)]
  rw [canonicalPrimePowerTerms_sum_eq_selectedFinitePrimeTerm_sum]
  simp [SelectedWeilSquareOwner.finitePrimeTermReal]

theorem canonicalEulerLogCarrierPairTrace_sum_re_eq_finitePrimeSum
    (g : CompactLogTest)
    (a c : ℝ)
    (data : CrossingCommonCarrierData
      (SelectedWeilSquareOwner.ofCompactLogTest g).sourceTest.test
      (SelectedWeilSquareOwner.ofCompactLogTest g).sourceTest.test.continuous
      a c (canonicalCrossingLengthSet
        (SelectedWeilSquareOwner.ofCompactLogTest g)))
    (hsupp : Function.support
      (SelectedWeilSquareOwner.ofCompactLogTest g).sourceTest.test ⊆ Set.Icc a c) :
    (∑ pm ∈ canonicalPrimePowerTerms (SelectedWeilSquareOwner.ofCompactLogTest g),
      eulerLogWeightedCarrierPairTrace data pm.1 pm.2).re =
      finitePrimeSum g.convolutionSquare := by
  rw [canonicalEulerLogCarrierPairTrace_sum_re_eq_selectedFinitePrimeTerm_sum
    (SelectedWeilSquareOwner.ofCompactLogTest g) a c data hsupp]
  exact (finitePrimeSum_square_eq_selected g).symm

theorem qw_eq_pole_sub_archimedean_sub_canonicalEulerLogCarrierTrace
    (g : CompactLogTest)
    (a c : ℝ)
    (data : CrossingCommonCarrierData
      (SelectedWeilSquareOwner.ofCompactLogTest g).sourceTest.test
      (SelectedWeilSquareOwner.ofCompactLogTest g).sourceTest.test.continuous
      a c (canonicalCrossingLengthSet
        (SelectedWeilSquareOwner.ofCompactLogTest g)))
    (hsupp : Function.support
      (SelectedWeilSquareOwner.ofCompactLogTest g).sourceTest.test ⊆ Set.Icc a c) :
    qw g =
      poleTerm g.convolutionSquare - archimedeanTerm g.convolutionSquare -
        (∑ pm ∈ canonicalPrimePowerTerms
            (SelectedWeilSquareOwner.ofCompactLogTest g),
          eulerLogWeightedCarrierPairTrace data pm.1 pm.2).re := by
  rw [qw_eq_psi_square, psi_eq_components]
  rw [← canonicalEulerLogCarrierPairTrace_sum_re_eq_finitePrimeSum
    g a c data hsupp]

end
end C1CrossingEulerLogReadback
end Source
end ConnesWeilRH
