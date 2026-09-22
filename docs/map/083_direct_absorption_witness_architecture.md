# 083 — Direct absorption witness architecture

Date: 2026-09-22.

Status: formal witness contract landed; connects absorption witnesses directly to Mathlib RH.
Subordinate to binding B5 route ruling in [003](003_b1_b5_minimal_exit_route_selection.md).

Consumer: the healthy `CompactLog`, detector-specific B5 statement `0 <= qw g`,
through `SourceRH` and Mathlib RH.

## Result

`C1P2DirectAbsorptionWitness.lean` establishes the packaged witness contract
`OrbitG8AbsorptionWitness` for Option A (Bone 4 direct assault).

It proves:
```text
OrbitG8AbsorptionWitness
  ==> orbitWindowSemiLocalGate(g)
  ==> 0 <= qw(g)
  ==> SourceRH
  ==> _root_.RiemannHypothesis
```

Key theorems:
- `riemannHypothesis_of_absorptionWitnesses`: existence of `OrbitG8AbsorptionWitness`
  for every right-hand zero directly implies Mathlib's canonical `RiemannHypothesis`.
- `riemannHypothesis_of_marginWitnesses`: existence of scalar margin witnesses
  implies Mathlib `RiemannHypothesis`.
- `riemannHypothesis_of_rangeMajorantWitnesses`: existence of finite-range profile majorant
  witnesses implies Mathlib `RiemannHypothesis`.

## Boundary and Open Obligation

This formalizes the witness packaging for Option A. The remaining open mathematical
obligation is to instantiate `OrbitG8AbsorptionWitness` for hypothetical off-line zeros
by certifying that the actual finite prime sum does not exceed the negative Archimedean margin.

Evidence: `ConnesWeilRH/Dev/C1P2DirectAbsorptionWitness.lean` and
`C1P2DirectAbsorptionWitnessAudit.lean`; build log `build-logs/1834_direct_absorption_witness.log`
(clean, standard axioms, zero sorryAx).
