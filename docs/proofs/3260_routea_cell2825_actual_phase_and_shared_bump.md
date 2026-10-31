# Record 3260: Cell-2825 Actual Phase Sign and Shared-Bump Identity

## Result

The formal phase rectangle at cell `2825` contains the exact 22-family owner
phase sum. Since the rectangle's real upper endpoint is negative, Lean proves
that the actual phase sum has negative real part:

```text
(sum slot : Fin 22, coefficient(slot) * phase(slot)).re < 0
```

The same module also proves the exact owner-preserving rewrite:

```text
sum familyTerm(family)
  = common_bump * sum coefficient(family) * phase(family)
```

for families `8..29` at cell `2825`. The equality uses the stored-width
identity; it does not use a numerical approximation or discard signed
cancellation.

## Files

```text
ConnesWeilRH/Dev/C1RouteAConcreteOwnerPhaseCell2825CoeffPhaseAggregateSplit3258.lean
ConnesWeilRH/Dev/C1RouteAConcreteOwnerSharedBumpCell2825Split3259.lean
ConnesWeilRH/Dev/C1RouteAConcreteOwnerSharedBumpCell2825Split3259Audit.lean
```

## Verification

The focused WSL2 ext4 build used:

```text
lean-toolchain: leanprover/lean4:v4.30.0
Lean: 4.30.0
```

The audit reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

for the actual phase sign, the shared-width theorem, and the exact shared-bump
target equality.

## Boundary

The common bump is represented exactly, but its strict positivity at cell
`2825` is not yet proved. Therefore this record does not establish a negative
physical block, the signed physical-kernel/C3' budget, the full-line tail,
B5-shaped semi-local positivity, `producer_go`, `SourceRH`, or RH.
