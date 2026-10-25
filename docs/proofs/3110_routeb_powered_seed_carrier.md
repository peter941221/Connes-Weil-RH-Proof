# Route-B powered-seed carrier (3110)

Date: 2026-10-25.

Record 2724 proved that the old `explicitSeed` object is not the object on
which the wired cardinal pins were certified.  The mismatch was enormous, so
the old identification cannot be repaired by a tighter bound.  This record
rebuilds the same finite carrier with Lean's actual `poweredSeed`.

The new owner is

```text
poweredSeedCarrierSourceTest3110 targets nodes y
  = selectedOwner
      (cardinalOwner targets poweredSeed (fun _ => 1))
      (cardinalOwner nodes poweredSeed y) 3
```

The Lean proofs establish:

```text
poweredSeedCarrier_target3110
  finite interpolation target on the same powered owner

poweredSeedCarrier_cc20Vanishes3110
  the shifted CC20 triple vanishes by interpolation

poweredSeedCarrier_sourceTest_support3110
  support is contained in (-55, 55)

fourPointContradictionRowBPoweredSeed3110
  wired contradiction interface with poweredSeed cardinal pins

fourPointContradictionRowBPoweredSeedStored3110
  stored row-B node sets and target values, re-seeded at poweredSeed
```

The three cardinal pins, fixed-24 gate, and spectral prefix remain explicit
premises.  This record removes only the seed-object mismatch and proves the
owner transport around the corrected object.

Verification in the Linux ext4 mirror:

```text
lake build ConnesWeilRH.Dev.C1RouteBPoweredSeedCarrier3110Audit
```

The audit must report no errors or `sorryAx`, with every declaration using only
`[propext, Classical.choice, Quot.sound]`.
