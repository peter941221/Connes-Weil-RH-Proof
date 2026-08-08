# 868 — Unit-scale h_factor is CLOSED (axiom-clean)

Date: 2026-08-07. Status: verdict change on the infinite-carrier Gate trace bottom.

## What was thought blocked

The 867 handoff recorded that closing Gate 3U's infinite-carrier trace readout
needed `hfactor`, i.e. the Hilbert--Schmidt summability of the prolate square
root `sourceProlateHilbertSchmidtFactor lambda` along the global basis, plus
`sourceProlateRemainder` being trace-class. That was listed as a genuine
analytical blocker "not present in mathlib", and the only closed edge was the
Route-A finite-band gate (861).

## What is actually true

The unit-scale (`lambda = unitSoninScale`) version of that premise **was already
proven unconditionally** in `ConnesWeilRH/Source/CCM25Concrete/CCM24UnitScaleStrictAngle.lean`
(lines 1483-1522). The four declarations:

- `norm_unitProlateFactor_lt_one` : `-norm unitProlateFactor- < 1`
- `sourceProlateRemainder_unit_isTraceClassAlong`
- `sourceProlateHilbertSchmidtFactor_unit_summable`
- `sourceThreeBranchCommutator_unit_isTraceClassAlong`

each depend on axioms only `[propext, Classical.choice, Quot.sound]` (WSL
`#print axioms` verified), with no `sorry`, no project axiom. The strict unitary
angle `< 1`, the compact physical/Fourier support uniqueness, and the additive
even Plancherel transport are all in-library for `lambda = unitSoninScale`.

## Wiring into the Gate

New leaf: `ConnesWeilRH/Source/CCM25Concrete/CCM24UnitScaleCanonicalGateHandoff.lean`.
It discharges the adjoint Gate's `hfactor` premise at `lambda = unitSoninScale`
via `sourceProlateHilbertSchmidtFactor_unit_summable globalBasis` and proves

`canonicalRealGate3UAt_unit_of_rightEnergy owner a c hac hsupp ... basis hright`

whose conclusion is `canonicalRealGate3UAt owner unitSoninScale sourceBasis bound`.
Build green + `#print axioms` clean on WSL.

## What remains

Only the premise `hright` (the source-physical coframe completed-kernel right
energy bound) stays open - it is the disclosed analytic producer (reduced to
the physical leakage radius norm, Proof 717), not a hidden field. The unit-scale
`h_factor` obstacle has been removed; the last analytic bottom for the
infinite-carrier Gate at the unit scale is exactly that right-energy bound.
the *general* (arbitrary `lambda`) h_factor is still open; only the
unit-scale instance is closed here.