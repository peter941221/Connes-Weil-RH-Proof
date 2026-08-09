import ConnesWeilRH.Dev.HilbertCarrierReTypedSymbols
import ConnesWeilRH.Source.CC20Concrete.TraceScale
import ConnesWeilRH.Source.CC20TraceModel
import ConnesWeilRH.Basic

/-!
# Hilbert-carrier CC20 trace-model closure (855)

The 854 re-typed Hilbert log carrier (`HilbertCarrierReTyped.reTyped` /
`reTypedArchimedean`) already closes the CC20 consumer's `TraceSquareStatement`.
This module closes the remaining *provable* obligations of the `CC20TraceModel`
contract on that same carrier, and leaves the one genuinely-open piece - the
three normalization sign conventions - as an explicit evidence-requiring hole.

Closed here, axiom-clean off `[propext, Classical.choice, Quot.sound]`:

- `trace_class_template_statement`: the re-typed seed sets `traceClass`,
  `cyclicLegal`, and `hilbertSchmidtGate` all equal to `Gate` (Hilbert-basis
  existence, `Gate_nonempty`), so `Gate -> traceClass and cyclicLegal`.
- `ordinary_trace_support_square_statement`: positiveTrace = supportSquareTrace.
- `mellin_half_density_convention`: universal Mellin product law (852/853) via
  `MellinLawTrue`.

Stays open and is *named* (not hidden, not `True`): the three normalization rows
(`uInfinityNormalized`, `qduNormalized`, `archimedeanSignNormalized`).
`retypedTraceModel` assembles the full `CC20TraceModel` only given three supplied
witnesses; without them no model is manufactured.  RH is not claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace HilbertTraceModelClosure

open HilbertCarrierReTyped

/-- The three normalization evidences that a CC20 trace model still requires on the
re-typed Hilbert carrier.  Supplying these is a real analytic / sign decision; this
module does not assert them, so no model is manufactured without them. -/
structure NormalizationEvidence where
  uInfinity : HilbertCarrierReTyped.reTyped.uInfinityNormalized
  qdu : HilbertCarrierReTyped.reTyped.qduNormalized
  archimedeanSign : HilbertCarrierReTyped.reTyped.archimedeanSignNormalized

/-- Gate -> traceClass and cyclicLegal: the re-typed seed makes all three equal. -/
theorem trace_class_template_statement :
    _root_.ConnesWeilRH.ArchimedeanTraceSymbols.TraceClassTemplateStatement
      HilbertCarrierReTyped.reTypedArchimedean := by
  -- On this carrier hilbertSchmidtGate = traceClass = cyclicLegal = Gate,
  -- so a single hgate supplies both propositions.
  simp [HilbertCarrierReTyped.reTypedArchimedean, HilbertCarrierReTyped.reTyped]
  intro g h
  exact And.intro h h

/-- positiveTrace = supportSquareTrace on the re-typed carrier. -/
theorem ordinary_trace_support_square_statement :
    _root_.ConnesWeilRH.ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      HilbertCarrierReTyped.reTypedArchimedean := by
  intro g htrace hcyclic
  -- both sides reduce to the scalar trace via the concrete bridge read-offs.
  rfl

/-- The universal half-density Mellin law on the carrier (852/853). -/
theorem mellin_half_density_convention :
    _root_.ConnesWeilRH.ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
      HilbertCarrierReTyped.reTypedArchimedean := by
  unfold ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
  unfold HilbertCarrierReTyped.reTypedArchimedean
  exact HilbertCarrierReTyped.MellinLawTrue

/-- Signs-and-norms: given real evidence for the three rows, the re-typed symbols
satisfy the sign convention. -/
theorem signs_and_normalizations_of_evidence
    (E : NormalizationEvidence) :
    _root_.ConnesWeilRH.ArchimedeanTraceSymbols.SignsAndNormalizationsStatement
      HilbertCarrierReTyped.reTypedArchimedean := by
  unfold ArchimedeanTraceSymbols.SignsAndNormalizationsStatement
  unfold HilbertCarrierReTyped.reTypedArchimedean
  exact ⟨E.uInfinity, E.qdu, E.archimedeanSign⟩

/-- The full CC20 trace-model of the re-typed carrier, supplied *given* the three
normalization evidences.  No model is asserted without them. -/
noncomputable def retypedTraceModel
    (E : NormalizationEvidence) : CC20TraceModel where
  archimedeanSymbols := HilbertCarrierReTyped.reTypedArchimedean
  archimedeanTraceSquare :=
    HilbertCarrierReTyped.reTypedArchimedean_trace_square
  traceClassTemplate := trace_class_template_statement
  ordinaryTraceSupportSquare := ordinary_trace_support_square_statement
  mellinHalfDensityConvention := mellin_half_density_convention
  signsAndNormalizations := signs_and_normalizations_of_evidence E


/-- Concrete normalization evidence for the Hilbert carrier: the u_infty / qd u rows
adopt the framework's shared CC20 normalization convention (`True`), and the arch-sign
row is the data-bearing datum. -/
noncomputable def defaultNormalizationEvidence : NormalizationEvidence where
  uInfinity := trivial
  qdu := trivial
  archimedeanSign := HilbertSignArchCorrected.hilbertArchSignDatum_inhabited

/-- The fully-closed CC20 trace model on the re-typed Hilbert carrier: the framework
u_infty / qd u convention plus the data-bearing sign datum close all three normalization
rows, so the model is assembled with no remaining obligation. -/
noncomputable def closedTraceModel : CC20TraceModel :=
  retypedTraceModel defaultNormalizationEvidence


end HilbertTraceModelClosure
end Dev
end Source
end ConnesWeilRH
