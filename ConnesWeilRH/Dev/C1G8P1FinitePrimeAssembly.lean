import ConnesWeilRH.Dev.C1SelectedDetectorSemiLocalEulerBoundary
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace

/-!
# G8 P1 finite-prime assembly

The G8 family owns both its natural prime-power terms and the deduplicated
visible-prime list used by the finite Euler geometry.  This leaf converts the
family to the visible-place boundary assembly and proves that the existing
semi-local trace theorem reads that assembly back to the original finite
prime-power sum.  It is an arithmetic-side P1 consumer only; it does not
identify the assembly with the metric Schur boundary maps or assert a cutoff
limit.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1FinitePrimeAssembly

open CCM25Concrete
open CC20Concrete
open C1SelectedDetectorSemiLocalEulerBoundary
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.SelectedCrossingOperatorBridge
open CC20Concrete.PositiveTrace
open scoped BigOperators InnerProduct InnerProductSpace

noncomputable section

private def familyTermEmbedding (family : FinitePrimePowerFamily) :
    {pm : ℕ × ℕ // pm ∈ family.terms} ↪ VisiblePrimePower where
  toFun pm :=
    (⟨pm.1.1, (family.prime pm.1 pm.2).one_lt⟩, pm.1.2)
  inj' x y h := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : VisiblePrimePower => z.1.1) h
    · exact congrArg (fun z : VisiblePrimePower => z.2) h

noncomputable def familyVisiblePrimePowerTerms
    (family : FinitePrimePowerFamily) :
    VisiblePrimePowerTerms family.visiblePrimes :=
  { terms := family.terms.attach.map (familyTermEmbedding family)
    visible := by
      intro pm hpm
      rcases Finset.mem_map.1 hpm with ⟨q, hq, rfl⟩
      simpa only [familyTermEmbedding] using
        (FinitePrimePowerFamily.mem_visiblePrimes_of_mem family q.2)
    prime := by
      intro pm hpm
      rcases Finset.mem_map.1 hpm with ⟨q, hq, hqpm⟩
      subst hqpm
      simpa only [familyTermEmbedding] using family.prime q.1 q.2
    exponent_ne_zero := by
      intro pm hpm
      rcases Finset.mem_map.1 hpm with ⟨q, hq, hqpm⟩
      subst hqpm
      simpa only [familyTermEmbedding] using family.exponent_ne_zero q.1 q.2 }

theorem familyVisiblePrimePowerTerms_natTerms_eq
    (family : FinitePrimePowerFamily) :
    (familyVisiblePrimePowerTerms family).natTerms = family.terms := by
  ext pm
  constructor
  · intro hpm
    rcases Finset.mem_map.1 hpm with ⟨v, hv, hmap⟩
    rcases Finset.mem_map.1 hv with ⟨q, hq, hqv⟩
    subst hqv
    have hqpm : pm = q.1 := by
      simpa only [visiblePrimePowerToNatPair, familyTermEmbedding] using hmap.symm
    rw [hqpm]
    exact q.2
  · intro hpm
    let q : {pm : ℕ × ℕ // pm ∈ family.terms} := ⟨pm, hpm⟩
    have hterms : familyTermEmbedding family q ∈
        (familyVisiblePrimePowerTerms family).terms := by
      rw [familyVisiblePrimePowerTerms]
      exact Finset.mem_map.2 ⟨q, Finset.mem_attach _ _, rfl⟩
    apply Finset.mem_map.2
    refine ⟨familyTermEmbedding family q, hterms, ?_⟩
    rfl

theorem ordinaryTraceAlong_g8FamilyVisibleBoundary_eq_finitePrimeTerm_sum
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (family : FinitePrimePowerFamily)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {nu : Type*}
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ family.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
        (selectedEulerLogBoundaryPairOperatorSum owner
          (familyVisiblePrimePowerTerms family)) =
      ∑ pm ∈ family.terms, owner.finitePrimeTerm (pm.1 ^ pm.2) := by
  have htrace :=
    ordinaryTraceAlong_selectedEulerLogBoundaryPairOperatorSum_eq_finitePrimeTerm_sum
      owner a c (familyVisiblePrimePowerTerms family) hsupp globalBasis (by
        intro pm
        have hmem : pm.1 ∈
            family.terms.attach.map (familyTermEmbedding family) := by
          simpa only [familyVisiblePrimePowerTerms] using pm.2
        let hpre : ∃ q : {pm : ℕ × ℕ // pm ∈ family.terms},
            q ∈ family.terms.attach ∧ familyTermEmbedding family q = pm.1 :=
          Finset.mem_map.1 hmem
        let q : {pm : ℕ × ℕ // pm ∈ family.terms} := Classical.choose hpre
        have hq := Classical.choose_spec hpre
        have hp : q.1.1 = pm.1.1.1 := by
          exact congrArg (fun z : VisiblePrimePower => z.1.1) hq.2
        have hm : q.1.2 = pm.1.2 := by
          exact congrArg (fun z : VisiblePrimePower => z.2) hq.2
        simpa only [hp, hm] using basisData q)
  rw [htrace]
  rw [familyVisiblePrimePowerTerms]
  rw [Finset.sum_map]
  simpa [familyTermEmbedding] using
    (Finset.sum_attach (s := family.terms)
      (f := fun pm : ℕ × ℕ => owner.finitePrimeTerm (pm.1 ^ pm.2)))

end
end C1G8P1FinitePrimeAssembly
end Source
end ConnesWeilRH
