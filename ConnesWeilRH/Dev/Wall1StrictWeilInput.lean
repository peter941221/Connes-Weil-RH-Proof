import ConnesWeilRH.Dev.Wall1HealthyPositive
import ConnesWeilRH.Basic

/-!
# Wall1StrictWeilInput — the task-2 re-type seam: healthy strict diagonal into `fullWeilPositivity`

`docs/proofs/912` isolates the ONLY open field of `CC20PropositionC1InputData` as
`fullWeilPositivity`.  `docs/proofs/936` names the re-type seam: the healthy
CompactLog/HS strict positive diagonal must become a `Sort 1` inhabitant of a
`WeilPositivityInput.fullWeilPositivity`.

`Dev/Wall1GlobalConvNonzero` proves the strict diagonal for any nonzero kernel
(h->nonzero operator; `cc20GlobalConvolutionPositive_strict_diagonal`); instantiated
at the concrete nonzero test it is `Wall1HealthyPositive.healthy_strict_positive_diagonal`
(axiom-clean). This module realises the seam by packaging that genuine Strict
Hilbert diagonal as a concrete `WeilPositivityInput` whose `fullWeilPositivity :
Sort 1` is inhabited.  Feeding it to `c1InputData_of_positivity_witness`
(CC24DoorBCarrierAssemblyProbe912) then closes the only-runtime open field of
`CC20PropositionC1InputData`.

This is an assembly/re-type brick, NOT an RH claim.  The RH-equivalent C1
criterion (and hence RH itself) is not discharged here.
-/
namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall1StrictWeilInput

open MeasureTheory
open scoped InnerProduct InnerProductSpace
open CC20Concrete
open A3NonzeroCompactLogGateProbe
open CCM25Concrete.CompactLogConvolution

/-- The healthy source strong positivity witness: there is a Hilbert vector on
   the global crossing space along which the convolution-square operator at the
   concrete nonzero test has strictly positive real diagonal.  This is the
   `Sort 1` content that shall occupy `WeilPositivityInput.fullWeilPositivity`. -/
def healthyFullWeilPositivity : Sort 1 :=
  { u : CC20Concrete.cc20GlobalLogCrossingL2 //
    0 < (⟪u, CC20Concrete.cc20GlobalConvolutionPositive nonzeroTest.test u⟫_ℂ).re }

/-- `healthyFullWeilPositivity` carries data (a `Sort 1`): the strict diagonal
   single piece. -/
theorem healthyFullWeil_positivity_nonempty :
    Nonempty healthyFullWeilPositivity := by
  rcases Wall1HealthyPositive.healthy_strict_positive_diagonal with ⟨u, hu⟩
  exact ⟨⟨u, hu⟩⟩

/-- The concrete `WeilPositivityInput` on the healthy carrier whose
   `fullWeilPositivity` is the genuine strict positive diagonal. -/
noncomputable def healthyWeilInput : WeilPositivityInput where
  tripleVanishing := True
  fullWeilPositivity := healthyFullWeilPositivity

/-- The witness claim: the healthy input's `fullWeilPositivity` (a `Sort 1`)
   is inhabited, i.e. the re-type seam that closes the last open field of
   `CC20PropositionC1InputData` is provided by the healthy strict diagonal. -/
theorem healthyWeilInput_full_pos_nonempty :
    Nonempty healthyWeilInput.fullWeilPositivity :=
  healthyFullWeil_positivity_nonempty

end Wall1StrictWeilInput
end Dev
end Source
end ConnesWeilRH