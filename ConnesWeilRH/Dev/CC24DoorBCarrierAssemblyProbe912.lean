import ConnesWeilRH.Basic
import ConnesWeilRH.Source.CC20RHExit
import ConnesWeilRH.Source.ZetaHalfNonvanishing
import ConnesWeilRH.Source.DirichletEta

/-!
# 912 (Door B): assemble the CC20 per-F rows axiom-clean; the FULL positivity
#   witness is the single remaining slot

A-lane closure (911) reduced the A-lane to exactly one wall, the generic-lambda
prolate Hilbert--Schmidt summability.  The B-lane route for the finite-vanishing
CC20 exit passes through `CC20PropositionC1InputData`, whose four fields are:

    finiteSetIsTriple : RouteFiniteVanishingSetIsCC20Triple F
    finiteSetDisjointFromNontrivialZeros : SourceFiniteSetDisjointFromNontrivialZeros B F
    tripleVanishingMatchesMellin : RouteTripleVanishingMatchesCC20Mellin F input
    fullWeilPositivity : input.fullWeilPositivity

Axiom status of the first three on the concrete triple (this file, via
`#print axioms`, confirming 849):

    finiteSetIsTriple                  : rfl-class (cc20_triple_finite_set_admissibility)
    finiteSetDisjointFromNontrivialZeros: CLOSED (cc20_triple_disjoint_..._nontrivial_zeros,
                                       via riemannZeta_half_ne_zero / Dirichlet-eta identity)
    tripleVanishingMatchesMellin       : definitionally input.tripleVanishing

So the ONLY per-f row that is not sourced from the admissible/disjointness
arithmetic is `fullWeilPositivity`, and for the refuted finite-vanishing input
    fullWeilPositivity := PLift (CC20FiniteVanishingWeilCriterion ...)
that field is FALSE (847/848): the universal `<= 0` statement is refuted on the
concrete orbit.  Hence NO `CC20PropositionC1InputData` consumer builds for that
input.  The constructive candidate is the other `WeilPositivityInput` producer,
`Route.FullWeilPositivity` (positive by construction, Exhaustion.lean) whose
positivity slot is `Sort 1` and not refuted per-type (848).

This file therefore records the honest assembly state:

  (1) it BUILDS the three per-f rows (finite set is the CC20 triple, disjoint
      from the nontrivial zeros, triple-vanishing matches) as axiom-clean
      `SourceFiniteSetAdmissibilityForBridge` data, `#print axioms` =
      [propext, Classical.choice, Quot.sound];
  (2) it assembles `CC20PropositionC1InputData` FROM any provided positivity
      witness `hpositive`, isolating that witness as the single unclosed field;
  (3) it does NOT claim RH.

The `fullWeilPositivity`-existence at a concrete `g` remains the honest B-lane
door (849 pointed exactly here), and it is the SAME positive-canonical sign
decision as 842/847b pin-hole.  No RH is claimed; zero `sorry`; only library
axioms.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20FiniteVanishingAssemble

-- per-f row: the concrete CC20 triple is an admissible finite set, axiom-clean.
noncomputable def cc20TripleAdmissible :
    SourceFiniteSetAdmissibility cc20TripleFiniteVanishingSet :=
  cc20_triple_finite_set_admissibility

-- per-f row: the CC20 triple is disjoint from the standard source nontrivial
-- zeros (849; tail = zeta(1/2) != 0 via the Dirichlet-eta identity).
noncomputable def cc20TripleDisjoint :
  SourceFiniteSetDisjointFromNontrivialZeros
    RHDefinitionBridge.standard cc20TripleFiniteVanishingSet :=
  cc20_triple_disjoint_from_standard_source_nontrivial_zeros

-- the two per-f rows in one bridge-admissibility record.
noncomputable def cc20TripleAdmissibleForBridge :
  SourceFiniteSetAdmissibilityForBridge
    RHDefinitionBridge.standard cc20TripleFiniteVanishingSet :=
  { finiteSetAdmissible := cc20TripleAdmissible
    finiteSetDisjointFromNontrivialZeros := cc20TripleDisjoint }

-- assemble the full CC20 input record from a triple-match and the positivity
-- witness. Everything except `hpositive` is sourced from the closed per-F rows,
-- so this def is exactly "only `hpositive` is open".
noncomputable def c1InputData_of_positivity_witness
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    CC20PropositionC1InputData
      RHDefinitionBridge.standard cc20TripleFiniteVanishingSet input :=
  { finiteSetIsTriple := cc20_triple_finite_set_admissibility.finiteSetIsTriple
    finiteSetDisjointFromNontrivialZeros := cc20TripleDisjoint
    tripleVanishingMatchesMellin := htriple
    fullWeilPositivity := hpositive }

-- the positivity slot is the only open field: supplying ANY witness for the
-- already-closed rows yields the full Proposition-C1 input data.
theorem c1InputData_exists_iff_positivity
    {input : WeilPositivityInput}
    (htriple : input.tripleVanishing) :
    Nonempty input.fullWeilPositivity ↔
      Nonempty (CC20PropositionC1InputData
        RHDefinitionBridge.standard cc20TripleFiniteVanishingSet input) := by
  constructor
  · rintro ⟨hp⟩
    exact ⟨c1InputData_of_positivity_witness input htriple hp⟩
  · rintro ⟨hdata⟩
    exact ⟨hdata.fullWeilPositivity⟩

-- axiom audit of the closed rows and the assembly (expect only
-- [propext, Classical.choice, Quot.sound]).
#print axioms cc20TripleAdmissible
#print axioms cc20TripleDisjoint
#print axioms c1InputData_exists_iff_positivity

end CC20FiniteVanishingAssemble
end Source
end ConnesWeilRH