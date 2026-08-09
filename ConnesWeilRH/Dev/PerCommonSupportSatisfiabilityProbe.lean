import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.AnalyticCoreBase
import ConnesWeilRH.Dev.SchwartzAmbientOwnerProbe

/-!
# Per-common source finite-prime support: satisfiability after forward narrowing

`docs/proofs/907` (§7j/7k) and `H2FullCarrierImpossible.universal_impossible`
showed that the OLD forward row
`sourceVisibleGlobalIndex : ∀ n, ∀ F, term n F ≠ 0 → n ∈ index` is
carrier-agnostically unsatisfiable: it quantifies over every test, so a
bump-nonzero prime is forced into the finite `globalIndexSet` for all the
infinitely many primes.

Commit `1bcf203` removed this wall by narrowing the forward rows to the single
`common` test:

    sourceVisibleGlobalIndex : ∀ n, term n common ≠ 0 → n ∈ globalIndexSet

This probe verifies the narrowing restores *satisfiability*: the structure now
has a model on the ambient Schwartz carrier, with `common = 0` and empty index
sets.  Because `term n 0 = 0` for every `n` on the ambient carrier, both
forward and reverse rows are vacuously witnessed by the empty index sets.

ARCHITECTURE check only — it confirms the pre-`1bcf203` gap is gone. It does not
claim a non-degenerate carrier: exhibiting a single prime `p` visible at a
non-zero `common` still requires real analysis.  RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace PerCommonSupportProbe

open AnalyticCore

/-- The concrete evaluation data on the ambient carrier (empty structure,
explicitly constructed via `mk`). -/
noncomputable def ambientEval :
    SourceEvaluationData ambientSourceAlgebra :=
  SourceEvaluationData.mk (A := ambientSourceAlgebra)

/-- The `valueAt (0:Test) x = ‖0 x‖ = 0` on the ambient carrier (legacy is the
identity, so the encoded zero is the zero Schwartz map). -/
lemma valueAt_zero_ambient (x : ℝ) :
    ambientEval.valueAt (0 : TestFunction) x = 0 := by
  rw [SourceEvaluationData.valueAt_eq_norm]
  simp [ambientSourceAlgebra, ambientLegacy]

/-- The zero test has zero finite-prime term at every index. -/
lemma sourceFinitePrimeTerm_zero_ambient (n : ℕ) :
    ambientEval.sourceFinitePrimeTerm n (0 : TestFunction) = 0 := by
  rw [SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt]
  rw [valueAt_zero_ambient (n : ℝ)]
  rw [valueAt_zero_ambient (((n : ℝ)⁻¹ : ℝ))]
  norm_num

/-- The zero ambient test is not visible at any index. -/
lemma zero_term_not_visible {n : ℕ}
    (h : ambientEval.sourceFinitePrimeTerm n (0 : TestFunction) ≠ 0) : False :=
  h (sourceFinitePrimeTerm_zero_ambient n)

/-- The narrowed `PerCommonSourceFinitePrimeSupport` has a model on the ambient
carrier with `common = 0` and empty index sets: all rows vacuous. -/
noncomputable def zeroAmbientSupport :
    PerCommonSourceFinitePrimeSupport ambientSourceAlgebra ambientEval
      (0 : TestFunction) where
  globalIndexSet := ∅
  restrictedIndexSet := fun _ => (∅ : Finset ℕ)
  sourceVisibleGlobalIndex := by
    intro n hn
    exact False.elim (zero_term_not_visible hn)
  sourceVisibleRestrictedIndex := by
    intro lambda n hn hOne hle
    exact False.elim (zero_term_not_visible hn)
  commonGlobalIndex := by
    intro n hn
    simp at hn
  commonRestrictedIndex := by
    intro lambda n hn
    simp at hn

/-- The narrowed structure is satisfiable (has a model). -/
theorem perCommonSupport_nonempty_ambient :
    Nonempty (PerCommonSourceFinitePrimeSupport ambientSourceAlgebra ambientEval
      (0 : TestFunction)) :=
  ⟨zeroAmbientSupport⟩

end PerCommonSupportProbe
end Dev
end Source
end ConnesWeilRH