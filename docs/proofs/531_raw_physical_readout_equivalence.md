# Proof 531: raw physical readout equivalence

## Result

The missing family-uniform physical Douglas producer can now be stated at the
level of the recombined raw four-term intertwinement. The unconditional polar
readout supplies the other summand, so the two formulations are equivalent at
the level of existence of a finite uniform bound:

```text
raw readout family
        <==>  mismatch readout family
        <==>  physical Douglas domination family
```

For a fixed numerical bound, converting between the first two formulations
adds the fixed detector cost:

```text
raw bound C      -> mismatch bound ||detector|| + C
mismatch bound C -> raw bound ||detector|| + C
```

The raw row is the exact four-term operator in
`suffixActualBandRawQuadraticIntertwiningDefect_adjoint_eq_fourTerm`; no
primewise estimate or `rho_S` inverse is introduced.

## What this changes

The source-specific bottom can be pursued directly on the four physical terms

```text
endpoint(S) * commutator * transition(p,S)^dagger
forward(S) * commutator * transition(p,S)^dagger
transition(p,S)^dagger * endpoint(p::S)^dagger * commutator
transition(p,S)^dagger * forward(p::S)
```

Any proof that factors this complete signed row through the summed
ambient-plus-boundary analysis column immediately gives the required mismatch
producer by subtracting the already available polar readout. Conversely, the
existing `rawCorrectionReadout` shows that every mismatch producer already
contains such a raw factorization.

## Boundary

Proof 531 is an interface reduction only. It does not construct the raw
readout, prove the uniform domination, close Gate 3U, prove the finite-S sign,
prove Burnol's identity, or prove `_root_.RiemannHypothesis`.

The focused audit must remain axiom-clean with exactly
`[propext, Classical.choice, Quot.sound]`.
