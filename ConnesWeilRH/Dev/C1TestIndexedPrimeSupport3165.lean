import ConnesWeilRH.Dev.C1SameOwnerWeil

/-!
# 3165 - test-indexed finite-prime support boundary

This is a development-only interface for the Route A owner. It records the
finite prime support as a function of the formula test, matching the existing
compact-support proof. It does not alter the fixed-index CCM25 API and does
not claim a source producer or RH.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1TestIndexedPrimeSupport3165

open C1SameOwnerWeil
open CCM25Concrete.CompactLogConvolution

structure TestIndexedFinitePrimeSupport where
  globalIndexSet : CompactLogTest -> Finset Nat
  restrictedIndexSet : Real -> CompactLogTest -> Finset Nat
  globalMem_iff :
    ∀ (F : CompactLogTest) (n : Nat),
      n ∈ globalIndexSet F ↔
        IsPrimePow n ∧ finitePrimeTermComplex F n ≠ 0
  restrictedMem_iff :
    ∀ (lambda : Real) (F : CompactLogTest) (n : Nat),
      n ∈ restrictedIndexSet lambda F ↔
        n ∈ globalIndexSet F ∧ 1 < n ∧ (n : Real) ≤ lambda ^ 2

noncomputable def c1TestIndexedFinitePrimeSupport :
    TestIndexedFinitePrimeSupport where
  globalIndexSet := C1SameOwnerWeil.globalPrimeIndexSet
  restrictedIndexSet := fun lambda F =>
    (C1SameOwnerWeil.globalPrimeIndexSet F).filter
      (fun n => 1 < n ∧ (n : Real) ≤ lambda ^ 2)
  globalMem_iff := by
    intro F n
    exact C1SameOwnerWeil.mem_globalPrimeIndexSet_iff F n
  restrictedMem_iff := by
    intro lambda F n
    simp [C1SameOwnerWeil.globalPrimeIndexSet]

theorem c1_visible_index_is_prime_power
    (F : CompactLogTest) {n : Nat}
    (hvisible : finitePrimeTermComplex F n ≠ 0) :
    IsPrimePow n := by
  exact C1SameOwnerWeil.finitePrimeTermComplex_nonzero_primePower F hvisible

theorem c1_visible_index_is_in_global_set
    (F : CompactLogTest) {n : Nat}
    (hvisible : finitePrimeTermComplex F n ≠ 0) :
    n ∈ c1TestIndexedFinitePrimeSupport.globalIndexSet F := by
  exact (c1TestIndexedFinitePrimeSupport.globalMem_iff F n).mpr
    ⟨c1_visible_index_is_prime_power F hvisible, hvisible⟩

theorem c1_restricted_index_readback
    (lambda : Real) (F : CompactLogTest) (n : Nat) :
    n ∈ c1TestIndexedFinitePrimeSupport.restrictedIndexSet lambda F ↔
      IsPrimePow n ∧ finitePrimeTermComplex F n ≠ 0 ∧
        1 < n ∧ (n : Real) ≤ lambda ^ 2 := by
  rw [c1TestIndexedFinitePrimeSupport.restrictedMem_iff]
  rw [c1TestIndexedFinitePrimeSupport.globalMem_iff]
  constructor
  · rintro ⟨⟨hprime, hterm⟩, hOne, hCutoff⟩
    exact ⟨hprime, hterm, hOne, hCutoff⟩
  · rintro ⟨hprime, hterm, hOne, hCutoff⟩
    exact ⟨⟨hprime, hterm⟩, hOne, hCutoff⟩

#print axioms c1TestIndexedFinitePrimeSupport
#print axioms c1_visible_index_is_prime_power
#print axioms c1_restricted_index_readback

end C1TestIndexedPrimeSupport3165
end Dev
end Source
end ConnesWeilRH
