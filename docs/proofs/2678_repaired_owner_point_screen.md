# Record 2678: repaired-owner aggregate screen

Status: exact-rational design screen GREEN; no Lean certificate is claimed.

The first 2678 check established that the repaired binary64 midpoint owner is
outside the narrow 2338 analytic coefficient boxes. Reusing the exact-center
2677 family rectangles would therefore be unsound. The second check rebuilds
all 30 base-M0 family rectangles from the actual binary64 point owner, rounds
each rectangle outward to a dyadic denominator 2^160, and sums those boxes
before comparing with the record-2675 base-M0 rectangle.

The exact aggregate is inside the exported rectangle. The four positive
coordinate margins are stored in
`results/2678_repaired_owner_point_screen.json`; the screen reports
`aggregate_inside_exported: true` and `family_count: 30`.

This is the shortest viable bridge discovered in this round, but it still has
two named obligations: prove the repaired-owner factor evaluator in Lean and
consume the resulting rectangles over the continuum cell. The signed tail,
other three channels, `chargeRest`, Producer GO, SourceRH, and RH remain open.

Reproduction uses the active Linux/WSL numerical environment:

```text
python3 scripts/routea_repaired_owner_point_screen_2678.py
```

The script uses exact rational decoding of stored binary64 values and the
existing directed interval machinery; it does not promote a floating-point
sample or a midpoint identity into a theorem.
