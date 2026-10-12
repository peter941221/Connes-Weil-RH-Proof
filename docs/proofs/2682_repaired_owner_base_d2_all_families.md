# Record 2682: repaired-owner base-D2 family bridges

Status: Lean bridge GREEN for all 29 nonzero family indices in cell 4096 and
the repaired-owner base-D2 cell consumer. This is not an RH proof.

The generator `scripts/generate_routea_repaired_owner_base_d2_2682.py` reads
the passing record-2676 aggregate screen and recomputes the D2 factor
rectangle for each family from the stored repaired-owner inputs. It preserves
the record-2676 staged rounding contract: each factor endpoint is rounded
outward to the denominator-2^160 dyadic grid before the complex product
rectangle is formed. The Lean proof handles the three modulation signs
explicitly: negative, positive, and zero imaginary modulation.

The generated modules are
`C1RouteARepairedOwnerBaseD22682Family1.lean` through
`C1RouteARepairedOwnerBaseD22682Family29.lean`, with one audit module for each
family. `C1RouteARepairedOwnerBaseD22682Consumer.lean` imports all 29 modules
and proves `record2682RepairedOwnerBaseD2CellContained` by applying the
existing finite rectangle-sum consumer to every family bridge.

Evidence:

- `results/2676_cell4096_containment_screen.json` has status
  `CELL4096_CONTAINMENT_SCREEN_PASS`; its `base_D2` aggregate is inside the
  exported rectangle.
- Linux-native Lean 4.30 compiled the consumer with exit 0.
- Linux-native Lean 4.30 compiled all 29 family audits and the consumer audit
  with exit 0. Every audited declaration reports exactly
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx` appears.

Scope remains local. This closes the 29 remaining base-D2 family premises for
cell 4096 under the repaired-owner enclosure. The correction-D2 cell, the
other 8191 cells, the global finite-sum owner transfer, `chargeRest`, the
signed infinite-xi tail, Producer GO, `SourceRH`, and RH remain open.
