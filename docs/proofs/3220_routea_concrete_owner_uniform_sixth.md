# 3220: Route A concrete-owner uniform sixth bound

Status: verified analytic bound; this does not close `producer_go` by itself.

## What was proved

`C1RouteAConcreteOwnerUniformSixth3220.lean` proves a uniform sixth-derivative
bound for the actual selected owner
`record2680CorrectionCoefficient` with the exact captured modulations
`capturedModulations2584`.

The proof keeps the complex 30-family sum intact until the final norm bound:

```text
30 weighted family derivatives
            |
            v
weightedPhysical2539 sixth derivative
            |
            v
real-part projection for weightedExternal3201
            |
            v
uniform sixthBound for every Taylor cell and coordinate
```

For each family, the existing `weightedFamilyCellUpper2538` envelope is used
with the conservative geometry `near = 0`, `far = 1`, and the full family
support interval `[-radius, radius]`. Inside support, the cell envelope applies;
outside support, the exact zero theorem applies. No external JSONL row is
imported.

## Exported declarations

- `record2680_uniform_sixth_real_bound3220`
- `record2680_uniform_sixth_upper_nonneg3220`
- `record2680UniformSixthBound3220`
- `record2680_uniform_sixth_bound_nonneg3220`
- `record2680_uniform_sixth_array_bound3220`

The last theorem has the shape needed by the 3213 aggregate interface:

```text
forall index < 40960, forall coordinate,
  norm (sixth derivative coordinate)
    <= record2680UniformSixthBound3220 index
```

## Verification

The focused module was built in WSL2 ext4 with:

```text
lean-toolchain: leanprover/lean4:v4.30.0
Lean: 4.30.0
LEAN_NUM_THREADS=1 lake build ConnesWeilRH.Dev.C1RouteAConcreteOwnerUniformSixth3220
```

The audit reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

for the real bound, its nonnegativity theorem, and the array wrapper.

## Remaining producer work

This closes only the sixth-derivative array. The midpoint value array, second-
derivative array, fourth-derivative array, signed finite aggregate, and
full-line tail remain open.
