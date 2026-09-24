# Proof Record 1963: explicit smooth seed for Route A

## Result

Added `ConnesWeilRH/Dev/C1ExplicitSmoothSeed.lean` with a concrete seed
built from `Real.smoothTransition`:

```text
smoothSeedRaw(x) = smoothTransition(x + 2) * smoothTransition(2 - x)
```

The focused Lean source proves:

- smoothness to order infinity;
- support contained in `[-2, 2]`;
- nonnegativity and an exact unit plateau on `[-1, 1]`;
- compact-log packaging as a `CompactLogTest`;
- `laplaceAt smoothSeed 0 != 0`.

A paired audit in `C1ExplicitSmoothSeedAudit.lean` reports only
`[propext, Classical.choice, Quot.sound]`.

## Why this matters

This replaces the former noncomputable `ContDiffBump` seed at the construction
boundary. Unlike the old seed, the new function has an explicit analytic
formula from Mathlib's smooth transition. It is therefore suitable for the
next derivative and L1 estimates required by `cardinalRaw`.

## Remaining open obligation

The derivative-shift L1 recurrence was attempted but is not yet compiled as a
valid theorem. The remaining work is to certify explicit derivative/L1
constants for this concrete seed and then iterate the recurrence over the
actual node list. No determinant sign, producer witness, or RH conclusion is
claimed here.