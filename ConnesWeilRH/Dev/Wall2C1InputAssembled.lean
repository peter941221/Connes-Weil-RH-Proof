import ConnesWeilRH.Dev.Wall1StrictWeilInput
import ConnesWeilRH.Dev.CC24DoorBCarrierAssemblyProbe912

/-!
# Wall2C1InputAssembled — the healthy strict-diagonal witness closes the
last construction slot of `CC20PropositionC1InputData` (axiom-clean)

`CC24DoorBCarrierAssemblyProbe912` isolates `fullWeilPositivity` as the ONLY
open field of `CC20PropositionC1InputData` (the other three row-facts are
already axiom-clean on the CC20 triple), and `c1InputData_of_positivity_witness`
builds the full record from ANY `input.fullWeilPositivity`.  `Wall1StrictWeilInput`
provides the healthy candidate `healthyWeilInput` whose `fullWeilPositivity :
Sort 1` is the genuine strict Hilbert diagonal on the crossing space and is
inhabited (`healthyFullWeil_positivity_nonempty`, axiom-clean).

This module feeds the healthy strict-diagonal witness into the 912 assembly and
constructs a complete, data-bearing `CC20PropositionC1InputData` on the healthy
carrier, so the "B-lane door" positivity slot (912, 946 (a)) is now provided by
verified data instead of left open.  RH is NOT discharged: this is input-data
construction only; the RH-equivalent criterion (and RH itself) stays untouched.

Axioms: [propext, Classical.choice, Quot.sound], 0 sorry / 0 project axiom.
RH NOT claimed.
-/
namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall2C1InputAssembled

open CC20FiniteVanishingAssemble
open Wall1StrictWeilInput

/-- The healthy CC20 datum: `healthyWeilInput` carries strict positivity and
   trivial triple-vanishing, so `c1InputData_of_positivity_witness` closes the
   last open slot of `CC20PropositionC1InputData`. -/
noncomputable def healthyCC20C1InputData :
    CC20PropositionC1InputData
      RHDefinitionBridge.standard cc20TripleFiniteVanishingSet healthyWeilInput :=
  let hpos : healthyWeilInput.fullWeilPositivity :=
    Classical.choice healthyFullWeil_positivity_nonempty
  c1InputData_of_positivity_witness healthyWeilInput trivial hpos

/-- The assembled healthy input data is nonempty; the last B-lane construction
   slot is closed on the healthy strict-diagonal carrier. -/
theorem healthyCC20C1InputData_nonempty :
    Nonempty (CC20PropositionC1InputData
      RHDefinitionBridge.standard cc20TripleFiniteVanishingSet healthyWeilInput) :=
  ⟨healthyCC20C1InputData⟩

end Wall2C1InputAssembled
end Dev
end Source
end ConnesWeilRH