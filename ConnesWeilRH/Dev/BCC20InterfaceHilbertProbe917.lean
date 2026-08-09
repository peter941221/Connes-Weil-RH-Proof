import ConnesWeilRH.Dev.HilbertTraceModelClosure
import ConnesWeilRH.Source.CC20
import ConnesWeilRH.Basic

/-!
# 917 (Door B, CC20-interface layer) — concrete Hilbert CC20Interface assembly

`916` closed the archimedean gate slot axiom-clean on the Hilbert carrier.
`HilbertTraceModelClosure.closedTraceModel` closes all six *archimedean/CC20
model* rows (trace square, trace-class template, ordinary-trace support-square,
half-density Mellin convention, sign normalizations) on that same carrier.

This leaf assembles those axiom-clean rows into the concrete
`Source.CC20Interface` — the `RouteInputs.cc20` slot — on the Hilbert carrier,
with only a carried standard finite-vanishing RH exit package as input.  The
exit package is deliberately NOT constructed here: it is the terminal RH step
(`sourceCriterionData : ∀ input, C1InputData -> SourceRH`), a large fact that is
NOT the B-lane gate.  B's door is downstream (`CC20PropositionC1InputData
.fullWeilPositivity`), not these interface rows.

So this closes and *build-verifies* the CC20-interface layer of the re-route on
the Hilbert carrier: every row that the Hilbert model owns is axiom-clean here,
and the only remaining route datum is the carried exit (real, not tautological).

No RH claim.  Zero `sorry`.  No new `axiom`.  Expected bottom: only the library
trio `[propext, Classical.choice, Quot.sound]`, plus whatever the carried exit
package already proves (audited separately, not this gate).
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace BCC20Interface917

open HilbertTraceModelClosure
open HilbertCarrierReTyped

/-- Each row of the Hilbert CC20 trace model, restated as the CC20-interface
obligation `.Holds` on the same archimedean symbols.  These are all reduct to
the closed model witnesses, so each is a real (non-vacuous) proof. -/
noncomputable def archimedeanTraceSquareRow :
    (cc20ArchimedeanTraceSquare (closedTraceModel.archimedeanSymbols)).Holds :=
  closedTraceModel.archimedeanTraceSquare

noncomputable def traceClassTemplateRow :
    (cc20TraceClassTemplate (closedTraceModel.archimedeanSymbols)).Holds :=
  closedTraceModel.traceClassTemplate

noncomputable def ordinaryTraceSupportSquareRow :
    (cc20OrdinaryTraceSupportSquare (closedTraceModel.archimedeanSymbols)).Holds :=
  closedTraceModel.ordinaryTraceSupportSquare

noncomputable def mellinHalfDensityConventionRow :
    (cc20MellinHalfDensityConvention (closedTraceModel.archimedeanSymbols)).Holds :=
  closedTraceModel.mellinHalfDensityConvention

noncomputable def signsAndNormalizationsRow :
    (cc20SignsAndNormalizations (closedTraceModel.archimedeanSymbols)).Holds :=
  closedTraceModel.signsAndNormalizations

/-- Concrete Hilbert-backed CC20Interface on the standard bridge; the finite-vanishing exit is carried. -/
noncomputable def cc20InterfaceOfHilbertCarrier
    (exit : SourceFiniteVanishingCriterionPackage RHDefinitionBridge.standard) :
    CC20Interface where
  archimedeanSymbols := closedTraceModel.archimedeanSymbols
  archimedeanTraceSquare := closedTraceModel.archimedeanTraceSquare
  traceClassTemplate := closedTraceModel.traceClassTemplate
  ordinaryTraceSupportSquare := closedTraceModel.ordinaryTraceSupportSquare
  mellinHalfDensityConvention := closedTraceModel.mellinHalfDensityConvention
  rhDefinitionBridge := RHDefinitionBridge.standard
  cc20RHExitObjectPackage :=
    SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage exit
  signsAndNormalizations := closedTraceModel.signsAndNormalizations

-- the gate slot itself is present axiom-clean (916) on this carrier
noncomputable def gateSlotInInterface :
    ∀ g : closedTraceModel.archimedeanSymbols.Test,
      closedTraceModel.archimedeanSymbols.hilbertSchmidtGate g :=
  HilbertCarrierReTyped.Gate_nonempty

#print axioms cc20InterfaceOfHilbertCarrier
#print axioms gateSlotInInterface

end BCC20Interface917
end Dev
end Source
end ConnesWeilRH


