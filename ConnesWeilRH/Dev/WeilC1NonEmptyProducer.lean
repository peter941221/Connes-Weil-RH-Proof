/-
Concrete non-empty C1 / Weil-positivity input on the healthy CompactLog HS carrier.

Objective it closes: there exists a concrete C1 input whose full
Weil-positivity Sort (the C1 / Weil state) is inhabited.  The RH-exit
axiom `normalizedCoreCC20PropositionC1SourceCriterionRoot` requires, per
input, the data `CC20PropositionC1InputData ... input` whose load-bearing
witness is `input.fullWeilPositivity`.  A nonempty `fullWeilPositivity` is
exactly the non-empty producer the finite-S Weil sign discharge needs on
the concrete carrier.

Here the C1/Weil state is the strictly positive Hilbert diagonal of the PSD
convolution-square operator at the concrete nonzero compact-log test.
`healthy_strict_positive_diagonal` (Dev/Wall1HealthyPositive.lean) inhabits
the underlying existential, so the subtype is nonempty.

RH NOT claimed: this only supplies the concrete nonempty producer for the
C1/Weil input.  The finite-S sign discharge of every such input stays open.
-/
import ConnesWeilRH.Dev.Wall1HealthyPositive
import ConnesWeilRH.Basic
import ConnesWeilRH.Source.ZetaHalfNonvanishing
import ConnesWeilRH.Source.CC20RHExit

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace WeilC1NonEmptyProducer

open CC20Concrete
open A3NonzeroCompactLogGateProbe
open Wall1HealthyPositive
open scoped InnerProduct InnerProductSpace ComplexConjugate

/-- The concrete C1/Weil-state type. -/
noncomputable def weilPositivePredicate
    (u : cc20GlobalLogCrossingL2) : Prop :=
  0 < (⟪u, cc20GlobalConvolutionPositive nonzeroTest.test u⟫_ℂ).re

@[reducible]
noncomputable def WeilPositiveState : Type :=
  { u : cc20GlobalLogCrossingL2 // weilPositivePredicate u }

/-- The Weil-state Sort is nonempty. -/
noncomputable def weilStateNonempty : Nonempty WeilPositiveState := by
  rcases healthy_strict_positive_diagonal with ⟨u, hu⟩
  exact ⟨⟨u, hu⟩⟩

/-- The concrete C1 input. -/
noncomputable def concreteWeilInput : WeilPositivityInput where
  tripleVanishing := True
  fullWeilPositivity := WeilPositiveState

theorem concreteWeilInput_triple : concreteWeilInput.tripleVanishing :=
  True.intro

theorem concreteWeilInput_nonempty :
    Nonempty concreteWeilInput.fullWeilPositivity :=
  weilStateNonempty

theorem concrete_c1_input_nonempty_exists :
    ∃ input : WeilPositivityInput,
      input.tripleVanishing ∧ Nonempty input.fullWeilPositivity :=
  ⟨concreteWeilInput, concreteWeilInput_triple, concreteWeilInput_nonempty⟩


/-- Real C1 input data for the standard bridge at the concrete C1 input. -/
noncomputable def concreteC1InputData :
    Source.CC20PropositionC1InputData
      (Source.RHDefinitionBridge.standard)
      Source.cc20TripleFiniteVanishingSet
      concreteWeilInput :=
{ finiteSetIsTriple := Source.cc20_triple_finite_set_is_triple
  finiteSetDisjointFromNontrivialZeros :=
    Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros
  tripleVanishingMatchesMellin := concreteWeilInput_triple
  fullWeilPositivity := Classical.choice weilStateNonempty }



/-- Real C1 *route* input at the standard bridge: the concrete C1 input data
with the standard-bridge finite-set fields already justified (zeta-half
disjointness, full Weil witness). -/
noncomputable def concreteC1RouteInputData :
    Source.CC20PropositionC1RouteInputData
      Source.RHDefinitionBridge.standard
      Source.cc20TripleFiniteVanishingSet
      concreteWeilInput
      concreteWeilInput_triple
      (Classical.choice weilStateNonempty) :=
{ c1InputData := concreteC1InputData
  tripleVanishing_eq_input := rfl
  fullWeilPositivity_eq_input := rfl }

end WeilC1NonEmptyProducer
end Dev
end Source
end ConnesWeilRH

