# Record 3264: Cell-17168 Phase Boxes for Families 11-14

Status: verified phase enclosures; no sign claim.

The module extends the corrected staged repeated-squaring enclosure used by
3256 to families 11 through 14 at the same owner cell 17168. Each family has a
base rectangle, eight intermediate square transitions, and a final phase
rectangle. The WSL2 Lean 4.30.0 build and independent axiom audit pass with
exactly `[propext, Classical.choice, Quot.sound]`.

This record does not claim that the coefficient-phase block is negative. The
sign is handled separately by record 3265 after correcting the earlier
second-derivative diagnostic mismatch.
