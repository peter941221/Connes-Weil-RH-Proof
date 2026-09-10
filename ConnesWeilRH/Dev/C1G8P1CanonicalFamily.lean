import ConnesWeilRH.Dev.C1G8P1FinitePrimeAssembly
import ConnesWeilRH.Dev.C1CrossingEulerLogReadback
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalFamily

/-!
# G8 P1 canonical exact-support family

The visible-prime assembly is now specialized to the exact finite support of
the selected Weil square.  This keeps the finite arithmetic endpoint tied to
the same healthy `CompactLog` owner that supplies the detector; no arbitrary
prime family or support enlargement is introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1CanonicalFamily

open CC20Concrete
open CCM25Concrete
open CCM25Concrete.SelectedWeilSquare
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSProjectionTrace.FinitePrimePowerFamily
open CCM25Concrete.SelectedCrossingOperatorBridge
open CC20Concrete.PositiveTrace
open C1G8P1FinitePrimeAssembly
open C1CrossingEulerLogReadback
open C1SelectedDetectorSemiLocalEulerBoundary
open scoped BigOperators

noncomputable section

noncomputable def g8CanonicalFamily
    (owner : SelectedWeilSquareOwner) : FinitePrimePowerFamily :=
  ofSelectedOwner owner

theorem g8CanonicalFamily_pow_mem_iff
    (owner : SelectedWeilSquareOwner) (n : ℕ) :
    (∃ pm ∈ (g8CanonicalFamily owner).terms, pm.1 ^ pm.2 = n) ↔
      IsPrimePow n ∧ owner.finitePrimeTerm n ≠ 0 := by
  exact exists_mem_ofSelectedOwner_pow_eq_iff owner n

theorem g8CanonicalFamily_visiblePrime_iff
    (owner : SelectedWeilSquareOwner) (p : CCM24VisiblePrime) :
    p ∈ (g8CanonicalFamily owner).visiblePrimes ↔
      p.1.Prime ∧ ∃ m : ℕ, owner.finitePrimeTerm (p.1 ^ m) ≠ 0 := by
  constructor
  · intro hp
    obtain ⟨m, hpm⟩ := (g8CanonicalFamily owner).exists_term_of_mem_visiblePrimes hp
    exact ⟨(g8CanonicalFamily owner).prime (p.1, m) hpm,
      ⟨m, finitePrimeTerm_pow_ne_zero_of_mem_ofSelectedOwner owner hpm⟩⟩
  · rintro ⟨hp, m, hm⟩
    have hm0 : m ≠ 0 := by
      intro hmzero
      subst hmzero
      simp at hm
    have hprimepow : IsPrimePow (p.1 ^ m) :=
      ⟨p.1, m, Nat.prime_iff.mp hp, Nat.pos_of_ne_zero hm0, rfl⟩
    have hvisible := minFac_mem_visiblePrimes_of_finitePrimeTerm_ne_zero
      owner hprimepow hm
    have hminfac : (p.1 ^ m).minFac = p.1 := hp.pow_minFac hm0
    simpa [hminfac] using hvisible

theorem g8CanonicalFamily_visiblePrime_lt_globalIndexBound
    (owner : SelectedWeilSquareOwner) {p : CCM24VisiblePrime}
    (hp : p ∈ (g8CanonicalFamily owner).visiblePrimes) :
    p.1 < owner.globalIndexBound := by
  exact visiblePrime_lt_globalIndexBound_ofSelectedOwner owner hp

theorem ordinaryTraceAlong_g8CanonicalFamilyVisibleBoundary_eq_selectedSupport_sum
    (owner : SelectedWeilSquareOwner)
    (a c : ℝ)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {nu : Type*}
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ (g8CanonicalFamily owner).terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    ordinaryTraceAlong globalBasis
        (selectedEulerLogBoundaryPairOperatorSum owner
          (familyVisiblePrimePowerTerms (g8CanonicalFamily owner))) =
      ∑ n ∈ (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet,
        owner.finitePrimeTerm n := by
  have htrace := ordinaryTraceAlong_g8FamilyVisibleBoundary_eq_finitePrimeTerm_sum
    owner a c (g8CanonicalFamily owner) hsupp globalBasis basisData
  rw [htrace]
  have hterms : (g8CanonicalFamily owner).terms = canonicalPrimePowerTerms owner := by
    ext pm
    simp [g8CanonicalFamily, FinitePrimePowerFamily.ofSelectedOwner,
      FinitePrimePowerFamily.ofSelectedExactSupport, canonicalPrimePowerTerms,
      canonicalTerm, canonicalPrimePowerTerm]
  rw [hterms]
  exact canonicalPrimePowerTerms_sum_eq_selectedFinitePrimeTerm_sum owner

end
end C1G8P1CanonicalFamily
end Source
end ConnesWeilRH
