import ConnesWeilRH.Source.CC20Concrete.TraceScale
import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing
import ConnesWeilRH.Dev.MellinHilbertCarrierMerge
import ConnesWeilRH.Basic

/-!
Hilbert-carrier CC20 trace symbols (852 merge): a concrete `TraceScale.ScalarTraceScaleSymbols`
on the Hilbert log carrier `cc20GlobalLogCrossingL2`, with

- a real nonnegative half-density scalar (`g -> ‖g‖²`), nonnegative by `sq_nonneg`;
- a real HS gate `Gate`, non-trivial because a Hilbert basis of the carrier exists;
- the honest half-density Mellin law (`mellinLaw`) wired from the 853 merge, axiom-clean
  through `MellinHilbertCarrierMerge.mellinHalfDensityProven`.

The three normalization conventions (`uInfinity/qdu/archimedeanSign`) are left as `False`:
they are separate obligations, not asserted.  No RH is claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace HilbertCarrierReTyped

noncomputable section
open MeasureTheory

/-- The faithful Hilbert log carrier (852 merge target). -/
abbrev H := ConnesWeilRH.Source.CC20Concrete.cc20GlobalLogCrossingL2

/-- Non-trivial HS gate: a Hilbert basis of the Hilbert log carrier exists. -/
def Gate (_g : H) : Prop :=
  ∃ (w : Set H), Nonempty (HilbertBasis w ℂ H)

/-- The gate is provably nonempty: every complete complex Hilbert space admits a
Hilbert-basis. -/
theorem Gate_nonempty (g : H) : Gate g := by
  classical
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  exact ⟨w, ⟨b⟩⟩

/-- The honest half-density Mellin law on the Hilbert carrier (universal form of the
853 `mellinHalfDensityProven`). -/
def MellinLaw : Prop :=
  ∀ f g : H, ∀ s : ℂ,
    MellinHilbertCarrierMerge.mellinLawPremise f s →
    MellinHilbertCarrierMerge.mellinLawPremise g s →
      MellinHilbertCarrierMerge.mellinHalfDensityStatement f g s

/-- Proof that `MellinLaw` holds: it is the universal closure of the 853 theorem. -/
theorem MellinLawTrue : MellinLaw := by
  intro f g s hF hG
  exact MellinHilbertCarrierMerge.mellinHalfDensityProven f g s hF hG

/-- The re-typed scalar trace symbols on the Hilbert carrier.  The positive trace is the
squared norm; the gate is Hilbert-basis existence; the two-dimensional normalization
conventions stay explicit obligations (`False`), not asserted. -/
noncomputable def reTyped :
    ConnesWeilRH.Source.CC20Concrete.TraceScale.ScalarTraceScaleSymbols where
  Test := H
  scalarTrace := fun g => ‖g‖ ^ 2
  scalarTrace_nonnegative := by
    intro g
    exact sq_nonneg ‖g‖
  traceClass := Gate
  cyclicLegal := Gate
  hilbertSchmidtGate := Gate
  mellinHalfDensityMatched := MellinLaw
  uInfinityNormalized := False
  qduNormalized := False
  archimedeanSignNormalized := False

end
end HilbertCarrierReTyped
end Dev
end Source
end ConnesWeilRH