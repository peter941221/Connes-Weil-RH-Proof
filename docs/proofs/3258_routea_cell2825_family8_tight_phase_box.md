# Route A record 3258: cell 2825 family-8 staged phase box

## Result

The result is positive but deliberately narrow: the selected Route A owner at
cell 2825 now has a mechanically checked family-8 phase enclosure through all
nine repeated-squaring layers. This is not yet a signed 22-family aggregate,
not a B5 certificate, and not `producer_go`.

```text
exact owner phase at cell 2825
        |
        v
Taylor base rectangle, outward rounded
        |
        v
four-corner interval multiplication, stages 1..9
        |
        v
family-8 phase rectangle at power 512
```

## Why this record exists

The first 2825 trial propagated an error estimate from the phase center. That
was too optimistic for `RealInterval2429.mul`: real-part subtraction and
imaginary-part addition combine independent corner extrema. The accepted file
therefore computes each next rectangle from the previous rectangle's exact
four-corner products and then adds an explicit outward margin.

## Verification

The focused Lean check was run in the native WSL2 ext4 workspace with:

```text
cat lean-toolchain
lean --version
LEAN_NUM_THREADS=1 lake env lean ConnesWeilRH/Dev/C1RouteAConcreteOwnerPhaseCell2825Family8TightStaged3258.lean
```

The toolchain was `leanprover/lean4:v4.30.0` and Lean reported version
`4.30.0`. The focused command returned status 0. The log contains only local
dependency-change warnings and no `error`, `sorry`, or axiom violation.

The audit entry is kept in
`C1RouteAConcreteOwnerPhaseCell2825Family8TightStaged3258Audit.lean`; it audits
the scale premise, Taylor base membership, every staged step, and the final
phase-box theorem. The expected audited axiom set is exactly
`[propext, Classical.choice, Quot.sound]`.

## Boundary

This record proves only family 8. The remaining families 9 through 29 still
need the same owner-specific boxes before a coefficient-phase aggregate can be
checked. Even that aggregate would still leave the signed physical-kernel
budget, full-line tail, exact B5 readback, `producer_go`, `SourceRH`, and RH
open.
