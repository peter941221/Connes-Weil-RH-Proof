# Record 3272: Bump-Aware Correlated Phase Blocks at Cell 16923

## Result

This record closes the local enclosure correction identified after record
3271. At cell 16923, the physical family term is not merely

```text
coefficient * phase
```

but

```text
coefficient * bump(radius, center) * phase.
```

Record 3272 encloses the coefficient-times-bump factor for each family before
combining families with the same modulation and multiplying by the shared
phase rectangle. The resulting full physical block rectangles prove strict
negative real upper endpoints for blocks 5..9, 10..14, 20..24, and 25..29.

The proof is local to one selected cell and one owner. It does not prove the
40960-cell finite aggregate, the full-line tail, the signed physical-kernel
or C3' budget, the B5 readback, `producer_go`, `SourceRH`, or RH.

## Dependency correction

The earlier 3271 enclosure correlated coefficients and phases but left the
family-specific bump outside that correlation. Because the stored widths can
differ by family, a sign for a coefficient-phase rectangle cannot be reused
for the weighted physical sum. 3272 fixes the dependency order:

```text
family coefficient
        +
family bump interval
        |
        v
coefficient-bump rectangle
        |
        +-- same modulation families are added
        v
group rectangle
        |
        +-- multiply by the shared phase rectangle
        v
physical block rectangle
        |
        v
prove reHi < 0 where the margin survives
```

Here a rectangle is a certified complex enclosure: its real and imaginary
intervals contain the corresponding component of the exact complex value.
The phrase “same modulation” means families with the same frequency
coordinate, so they share the same phase at the chosen center. This shared
factor is what preserves cancellation instead of replacing it by independent
absolute-value bounds.

## Lean artifacts

The construction and membership theorems are in
`ConnesWeilRH/Dev/C1RouteAConcreteOwnerBumpCorrelatedPhaseBlocks3272.lean`.
The four strict sign theorems are in
`ConnesWeilRH/Dev/C1RouteAConcreteOwnerBumpCorrelatedPhaseBlocks3272SignProbe.lean`.
The exact-value sign bridge is in
`ConnesWeilRH/Dev/C1RouteAConcreteOwnerBumpCorrelatedPhaseBlocks3272PhysicalSign.lean`.
The independent axiom entrypoint is
`ConnesWeilRH/Dev/C1RouteAConcreteOwnerBumpCorrelatedPhaseBlocks3272Audit.lean`.

The six block membership theorems cover all contiguous five-family blocks:

```text
0..4, 5..9, 10..14, 15..19, 20..24, 25..29
```

The strict negative upper-endpoint results are currently available for:

```text
5..9, 10..14, 20..24, 25..29
```

For those four blocks, the exact physical value now also has strictly
negative real part. This follows directly from rectangle membership, which
contains `exactValue.re <= rectangle.reHi`, together with the strict endpoint
theorem. The bridge is explicit so later aggregate code can consume an
object-level inequality rather than reinterpreting a rectangle endpoint.

Blocks 0..4 and 15..19 remain enclosed but are not claimed negative by this
record.

## Verification

The focused Lean build was run in the WSL2 native ext4 workspace after
checking the repository toolchain:

```text
lean-toolchain: leanprover/lean4:v4.30.0
Lean: 4.30.0
```

The sign probe log contains only existing linter warnings about redundant
`norm_num` calls and no `error:`, `sorry`, or `sorryAx` output. The audit
target is intended to be run separately so the exact axiom list is visible.

## Boundary

This is a value-level local certificate. It proves that the exact physical
block value lies inside the certified rectangle, and that the rectangle's
real upper endpoint is negative for the four listed blocks. It does not by
itself establish a global integral inequality. In particular, no tail,
finite-window summation, derivative remainder, or owner readback step is
silently inferred from this result.
