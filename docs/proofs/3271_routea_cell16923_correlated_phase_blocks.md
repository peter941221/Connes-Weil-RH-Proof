# 3271: Route A cell-16923 correlated phase blocks

Status
------

Lean-verified local enclosure improvement at cell 16923. Families with the
same captured modulation are grouped before interval multiplication, so the
shared phase rectangle is multiplied by the summed owner coefficient. The
zero-frequency families 5, 6, and 7 use the exact phase point 1.

The four diagnostic blocks that were useful in the 3267 screen now have
strictly negative real upper bounds:

```text
5..9       reHi < 0
10..14     reHi < 0
20..24     reHi < 0
25..29     reHi < 0
```

This is a cell-local result only. It does not yet prove the 40960-cell finite
aggregate, the full-line tail bridge, B5 readback, `producer_go`, `SourceRH`,
or RH. The remaining blocks 0..4 and 15..19 are intentionally not claimed by
this record because their local signs are not the required producer-facing
target.

Construction
------------

```text
same modulation families
          |
          v
sum owner coefficients
          |
          v
multiply one shared phase rectangle
          |
          v
add correlated group rectangles
          |
          v
block reHi sign
```

Source:

    ConnesWeilRH/Dev/C1RouteAConcreteOwnerCorrelatedPhaseBlocks3271.lean

Sign probes:

    ConnesWeilRH/Dev/C1RouteAConcreteOwnerCorrelatedPhaseBlocks3271SignProbe.lean
    ConnesWeilRH/Dev/C1RouteAConcreteOwnerCorrelatedPhaseBlocks3271SignProbeAll.lean

Audit:

    ConnesWeilRH/Dev/C1RouteAConcreteOwnerCorrelatedPhaseBlocks3271SignAudit.lean

Verification
------------

The focused WSL2 ext4 build used the repository `lean-toolchain` and Lean
4.30.0. The membership and sign audit reports only
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` was observed.
