Record 3257: family-8 and family-9 tight staged phase boxes

Status: verified family-8 and family-9 phase enclosures; verified a strict
negative upper for family 8 alone; no full shared-block sign claim.

The staged boxes use the exact owner center at cell 17168 and the same
four-corner multiplication as `ComplexRect2427.mul`. The first generated
attempt used `17169 / 2` instead of `17168 + 1 / 2` for the grid midpoint and
was discarded. The verified boxes use the corrected center and are checked by
Lean from the Taylor rectangle through nine repeated-squaring stages.

The exact coefficient-point multiplication is then enclosed by
`ComplexRect2427`. Lean verifies membership for family 8, family 9, and their
pair sum. The family-8 coefficient-phase rectangle has strict real upper
`reHi < 0`. The pair 8+9 upper is not claimed to be negative: family 9 is a
positive contribution at this cell, so a pair sign would be false.

The focused WSL2 Lean 4.30.0 build and audit pass with no `error` or `sorry`;
the audited declarations use exactly `[propext, Classical.choice, Quot.sound]`.
This is a signed local block result, not `producer_go`, `SourceRH`, or RH.