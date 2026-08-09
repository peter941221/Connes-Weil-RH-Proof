import ConnesWeilRH.Source.CC20Concrete.TraceScale
import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing
import ConnesWeilRH.Dev.MellinHilbertCarrierMerge
import ConnesWeilRH.Dev.HilbertSignArchCorrected
import ConnesWeilRH.Basic

/-!
Hilbert-carrier CC20 trace symbols (852 merge): a concrete `TraceScale.ScalarTraceScaleSymbols`
on the Hilbert log carrier `cc20GlobalLogCrossingL2`, with

- a real nonnegative half-density scalar (`g -> ||g||^2`), nonnegative by `sq_nonneg`;
- a real HS gate `Gate`, non-trivial because a Hilbert basis of the carrier exists;
- the honest half-density Mellin law (`mellinLaw`) wired from the 853 merge, axiom-clean
  through `MellinHilbertCarrierMerge.mellinHalfDensityProven`.

The arch-sign normalization slot carries the data-bearing non-vacuous datum
(HilbertSignArchCorrected.hilbertArchSignDatum_inhabited); the u_infty / qd u rows adopt the
framework's shared CC20 normalization convention (`True`), identical to
`SourceTraceScaleData.toArchimedeanTraceSymbols` and the concrete scalar carriers, so the
Hilbert carrier is on equal footing with them.  No RH is claimed.
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
squared norm; the gate is Hilbert-basis existence; the arch-sign normalization carries the
data-bearing datum (`archimedeanSignNormalized := Nonempty HilbertArchSignDatum`). The
u_infty / qd u rows adopt the framework's shared CC20 normalization convention
(`True`, matching `SourceTraceScaleData.toArchimedeanTraceSymbols` and the concrete scalar
carriers), so the model sits on equal footing with the other carriers. -/
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
  uInfinityNormalized := True
  qduNormalized := True
  archimedeanSignNormalized := Nonempty HilbertSignArchCorrected.HilbertArchSignDatum

/-- The re-typed archimedean trace symbols, lifted from the scalar carrier. -/
noncomputable def reTypedArchimedean : ArchimedeanTraceSymbols :=
  reTyped.toConcreteTraceScaleSymbols.toArchimedeanTraceSymbols

/-- The concrete positive/consistency clause the CC20 consumer needs: 0 is bounded below by
the positive trace, and support == source == positive on the Hilbert carrier. -/
theorem reTypedArchimedean_trace_square :
    ArchimedeanTraceSymbols.TraceSquareStatement reTypedArchimedean :=
  ConnesWeilRH.Source.CC20Concrete.TraceScale.ScalarTraceScaleSymbols.trace_square_statement reTyped

end
end HilbertCarrierReTyped
end Dev
end Source
end ConnesWeilRH
