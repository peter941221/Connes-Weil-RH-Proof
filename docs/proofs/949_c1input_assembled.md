# 949 — task-2 B-lane door: healthy strict-diagonal witness closes the last construction slot of `CC20PropositionC1InputData` (axiom-clean)

Date: 2026-08-10. Status: verification note. RH NOT claimed.
Mirror: `cwr-lanb-archlift` (isolated ext4, warm seed, Windows sources). Build:
`ConnesWeilRH.Dev.Wall2C1InputAssembled` 3595 jobs green, axioms
`[propext, Classical.choice, Quot.sound]`, 0 sorry / 0 project axiom.

## What closed

`CC24DoorBCarrierAssemblyProbe912` (docs/912) showed `CC20PropositionC1InputData`
has four fields, three of which are already axiom-clean on the CC20 triple
(`finiteSetIsTriple`, `finiteSetDisjointFromNontrivialZeros`,
`tripleVanishingMatchesMellin`), leaving `fullWeilPositivity` as the ONLY open
slot; `c1InputData_of_positivity_witness` builds the record from ANY witness.
`Wall1StrictWeilInput` (946) supplies the candidate `healthyWeilInput` whose
`fullWeilPositivity : Sort 1` is the genuine strict Hilbert diagonal on the
crossing space, inhabited by `healthyFullWeil_positivity_nonempty`.

New `Dev/Wall2C1InputAssembled.lean` feeds that healthy witness into the 912
assembly:

  * `healthyCC20C1InputData : CC20PropositionC1InputData
      RHDefinitionBridge.standard cc20TripleFiniteVanishingSet healthyWeilInput`
  * `healthyCC20C1InputData_nonempty : Nonempty ...`   (axiom-clean)

so the B-lane door's last construction slot is now closed by verified data on
the healthy carrier, not left open.

## Honest scope

This closes the DATA/CONSTRUCTION level of the re-type seam (946 (a)); it does
NOT close the RH-equivalent discharge.  The mathematical "semantic" bridge --
the genuine Hilbert-space quadratic form `0 < Re <u, G*t G u>` (healthy,
crossing-space) to the localized Weil-quadratic-functional meaning on the
finite vanishing set -- is discursive/analytic, not forced by the `Sort 1`
typed slot, and the C1-RH discharge itself is a real RH proof. RH NOT claimed.
## Consolidated session soundness (single-import audit)

Importing `CompactArchTotal`, `CompactLogArchimedeanLift`, `CompactSCealBalance`,
`Wall2C1InputAssembled`, and `WellFormHealthyRepoint` together, `#print axioms`
for `totalArchimedean`, `compactLogArchimedeanTerm`, `weilValue_re_split`,
`healthyCC20C1InputData_nonempty`, and `healthySymbols_archimedeanTerm_eq` all =
`[propext, Classical.choice, Quot.sound]`, 0 sorry, 0 project axiom. The
top-level residual remains exactly the 5 listed `RhOutputAxiomLedger` axioms
(no new project axiom introduced).