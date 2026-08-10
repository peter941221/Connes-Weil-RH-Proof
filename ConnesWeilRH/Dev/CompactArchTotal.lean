import ConnesWeilRH.Dev.CompactLogArchimedeanLift
import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

/-!
# CompactArchTotal — a TOTAL archimedean term on `TestFunction`

lane-B wall-A (docs/947 sub-step 1.2) needs an `archimedeanTerm : TestFunction -> R`
defined on ALL Schwartz tests (healthy carrier uses `Test = TestFunction`) yet equal
to the CCM25 Eq.3.7 value where a compact-log representation exists. This module
picks the classical total extension: on a test carrying a `CompactLogTest`
representation it returns `compactLogArchimedeanTerm` there, else `0`.

HONEST scope: this is the *definitional front* of the total-arch wall; it does not
prove the Weil explicit-formula identity. It gives `totalArchimedean : TestFunction ->
R` and the match theorem `totalArchimedean_eq_compact` on compact inputs.

RH NOT claimed.
-/
namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CompactArchTotal

open CompactLogConvolution
open CompactLogArchimedeanLift

/-- The compact-log arch term only reads the underlying test; two compact tests
with equal `.test` give equal terms. -/
theorem compactLogArchimedean_test_congr
    {g f : CompactLogTest} (hg : g.test = f.test) :
    compactLogArchimedeanTerm g = compactLogArchimedeanTerm f := by
  cases g with
  | mk gt gtc =>
    cases f with
    | mk ft ftc =>
      cases hg
      rfl

/-- The classical total extension of the compact archimedean term: on any
   `F : TestFunction` with a compact-log representation it reads the Eq.3.7
   term there, otherwise `0`. -/
noncomputable def totalArchimedean (F : TestFunction) : ℝ := by
  classical
  exact if h : Nonempty { g : CompactLogTest // g.test = F } then
    compactLogArchimedeanTerm (Classical.choice h).val
  else 0

/-- The total extension returns `compactLogArchimedeanTerm f` on any compact
   input `f`, by definition of the representation. -/
theorem totalArchimedean_eq_compact (f : CompactLogTest) :
    totalArchimedean f.test = compactLogArchimedeanTerm f := by
  unfold totalArchimedean
  classical
  by_cases h : Nonempty { g : CompactLogTest // g.test = f.test }
  · rw [dif_pos h]
    apply compactLogArchimedean_test_congr
    exact (Classical.choice h).2
  · rw [dif_neg h]
    exfalso
    exact h ⟨⟨f, rfl⟩⟩

/-- The total extension is fixed on the compact-log subcarrier. -/
theorem totalArchimedean_eq_compactTerm (f : CompactLogTest) :
    totalArchimedean f.test = compactLogArchimedeanTerm f :=
  totalArchimedean_eq_compact f

end CompactArchTotal
end CCM25Concrete
end Source
end ConnesWeilRH