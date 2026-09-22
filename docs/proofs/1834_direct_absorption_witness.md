# 1834 — Direct absorption witness to Mathlib RH

Date: 2026-09-22

## Result

`C1P2DirectAbsorptionWitness.lean` formalizes the direct witness package
`OrbitG8AbsorptionWitness` for the healthy `CompactLog` Option A route,
and proves that the existence of such a witness for every hypothetical
right-hand zero directly yields Mathlib's canonical `_root_.RiemannHypothesis`.

It establishes:
1. `OrbitG8AbsorptionWitness rho`: structure packaging a detector `g`,
   its `OrbitG8Geometry rho g`, and the absorption inequality
   `finitePrimeSum g.convolutionSquare <= - archimedeanTerm g.convolutionSquare`.
2. `weilGeometricEnergy`: defined as `archimedeanTerm + finitePrimeSum`,
   with `absorption_iff_weilGeometricEnergy_nonpos` proving definitional equivalence.
3. `orbitWindowSemiLocalGate_of_absorptionWitness`: an absorption witness directly
   satisfies the orbit-window semi-local gate.
4. `sourceRH_of_absorptionWitnesses`: existence of absorption witnesses implies `SourceRH`.
5. `riemannHypothesis_of_absorptionWitnesses`: master exit to Mathlib `_root_.RiemannHypothesis`.
6. Construction theorems from:
   - margin transfer: `absorptionWitness_of_margin` and `riemannHypothesis_of_marginWitnesses`
   - norm absorption: `absorptionWitness_of_norm_absorption`
   - range majorants: `absorptionWitness_of_range_majorant` and `riemannHypothesis_of_rangeMajorantWitnesses`
   - signed credit/deficit budget: `absorptionWitness_of_signedBudget`
   - componentwise nonpositivity: `absorptionWitness_of_componentwise_nonpos`

The module and its paired audit `C1P2DirectAbsorptionWitnessAudit.lean` build clean,
zero error, zero sorryAx, standard axioms only `[propext, Classical.choice, Quot.sound]`.

## Boundary

This completes the top-level witness architecture for Option A. The remaining
mathematical obligation is to exhibit the witness geometry by aligning the
quantitative prime profile bound with the negative Archimedean margin.
