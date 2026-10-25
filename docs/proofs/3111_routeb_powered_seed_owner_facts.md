# Route-B powered-seed owner facts (record 3111)

Status: completed owner-identity brick. This record does not prove the three
cardinal pins, the fixed-24 gate, the spectral prefix bound, SourceRH, or RH.

The previous 3110 carrier repaired the seed-object mismatch: the wired carrier
must use Lean's `poweredSeed`, whose zero-frequency transform is `3^10`. Record
3111 now connects the explicit powered-seed correction to the rho-dependent
owner obligations. The owner is

```text
poweredSeedExplicitOwner3111 rho N routeNodes
  = selectedOwner (explicitPoweredHealthyBase rho)
      (explicitPoweredHealthyCorrection rho N routeNodes) 3
      |>.sourceTest
```

The module proves five transport facts:

```text
target interpolation      selected owner reads healthyUnscaledTargetValue
square-zero transport     closed-ball non-target nodes give zero square values
minimal interpolation     0, 1/2, 1 vanish and rho is detected off-line
centered orbit sum        the same owner has orbit sum -2
support                   the selected test is supported in (-55, 55)
```

The square-zero theorem uses the existing powered-owner kill theorem and then
the selected-owner centered transform. The orbit theorem uses the same raw
target map at every functional-equation orbit node, so the `rho` and companion
values are not supplied by a second owner.

Source module:

```text
ConnesWeilRH/Dev/C1RouteBPoweredSeedOwnerFacts3111.lean
```

Audit module:

```text
ConnesWeilRH/Dev/C1RouteBPoweredSeedOwnerFacts3111Audit.lean
```

Linux ext4 verification:

```text
RH_VERIFY_ROOT=/path/to/linux-ext4-mirror
LEAN_NUM_THREADS=1 lake build \
  ConnesWeilRH.Dev.C1RouteBPoweredSeedOwnerFacts3111 \
  ConnesWeilRH.Dev.C1RouteBPoweredSeedOwnerFacts3111Audit
```

Result: build completed successfully; five audited theorems had no `sorryAx`
and exactly `[propext, Classical.choice, Quot.sound]`.

The remaining dependency chain is:

```text
owner facts (3111)
        |
        v
three cardinal pins from a full D-ladder / envelope certificate
        |
        v
hgate24 and the same-owner spectral prefix bound
        |
        v
same-span contradiction -> SourceRH -> Mathlib RH
```

The existing 3104 adapter proves an unconditional powered-seed envelope with
D4/D7. It intentionally does not prove the pins. Record 2727's controlled
comparison found that the stored pin lane clears at rung set `{1,2,3,4}` while
`{1,2,3}` fails the quadratic and contraction pins; this makes low-order rung
certificates the next mathematical target. No numerical screen is promoted to
a Lean theorem by this record.
