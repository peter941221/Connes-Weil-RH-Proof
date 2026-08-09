import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.CC20YoshidaMellin
import ConnesWeilRH.Source.AnalyticCoreBase
import ConnesWeilRH.Dev.SchwartzAmbientOwnerProbe
import ConnesWeilRH.Dev.AmbientPrimeVisibleProbe

/-!
# The 536 ambient datum, wired into a full non-degenerate `SourceWeilFormData`

`AmbientPrimeVisibleProbe` built `nonDegenerateSupport`, a
`PerCommonSourceFinitePrimeSupport ambientSourceAlgebra ambientEval commonBump`
whose exact global index set is `{2}` (the prime `2` is visible:
`sourceFinitePrimeTerm 2 commonBump ≠ 0`).  That support object sits EXACTLY on
the `SourceFinitePrimeData` seam (`SourceFinitePrimeData`'s only field is
`support : PerCommonSourceFinitePrimeSupport A E common`).  So the whole
non-degenerate carrier `SourceWeilFormData ambientSourceAlgebra` is now a live,
constructible, axiom-clean object — the first real (non-zero) carrier datum on
the ambient carrier, wired all the way up to `WeilFormSymbols` global index
`{2}`.

This is a pure seam / wiring probe: it does NOT redo any real analysis in 536,
it only lifts the already-proven per-common support into the full
`SourceWeilFormData` record and records the downstream exactness facts.  RH is
NOT claimed.  Zero `sorry`, `#print axioms` stays `[propext, Classical.choice,
Quot.sound]`.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace AmbientSeam

open AnalyticCore
open CC20YoshidaInterpolationNode

-- Reuse the ambient carrier data from the 536 probe.
open AmbientPrimeProbe

/-- The `SourceFinitePrimeData` on the ambient carrier carried by the 536
per-common support. -/
noncomputable def ambientFinitePrimeData :
    AnalyticCore.SourceFinitePrimeData ambientSourceAlgebra
      ambientEval commonBump :=
{ support := nonDegenerateSupport }

/-- A NON-DEGENERATE `SourceWeilFormData` on the ambient carrier: the
`commonBump`'s prime `2` is visible (term ≠ 0) and the index set is `{2}`. -/
noncomputable def ambientWeilForm :
    AnalyticCore.SourceWeilFormData ambientSourceAlgebra :=
{ evaluation := ambientEval
  common := commonBump
  finitePrime := ambientFinitePrimeData
  archimedeanTerm := fun _ => 0 }

/-- The global prime index of the ambient non-degenerate form is exactly the
single prime `2`. -/
lemma ambientWeilForm_globalIndex :
    ambientWeilForm.finitePrime.globalPrimeIndexSet = ({2} : Finset ℕ) := by
  rfl

/-- 2 is a member of the ambient form's global prime index set. -/
lemma ambientWeilForm_two_mem :
    2 ∈ ambientWeilForm.finitePrime.globalPrimeIndexSet := by
  rw [ambientWeilForm_globalIndex]
  simp

/-- The finite-prime term of the live form at the prime `2` is non-zero:
the carrier datum is genuinely visible. -/
lemma ambientWeilForm_term_two_ne_zero :
    ambientWeilForm.finitePrime.finitePrimeTerm 2 commonBump ≠ 0 := by
  change ambientEval.sourceFinitePrimeTerm 2 commonBump ≠ 0
  exact term_two_ne_zero

/-- `globalExact` applied to the live form: 2 ∈ index `⟺` visible at the
common, and the common term is non-zero. -/
lemma ambientWeilForm_globalExact_two :
    2 ∈ ambientWeilForm.finitePrime.globalPrimeIndexSet ↔
      IsPrimePow 2 ∧
        ambientEval.sourceFinitePrimeTerm 2 commonBump ≠ 0 :=
  AnalyticCore.SourceFinitePrimeData.globalExact ambientFinitePrimeData 2

/-- The live `SourceWeilFormData` exists (nonempty) on the ambient carrier. -/
theorem ambientWeilForm_nonempty :
    Nonempty (AnalyticCore.SourceWeilFormData ambientSourceAlgebra) :=
  ⟨ambientWeilForm⟩

end AmbientSeam
end Dev
end Source
end ConnesWeilRH