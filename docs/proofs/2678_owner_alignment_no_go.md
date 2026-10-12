# Record 2678: repaired-owner alignment no-go

Status: exact rational obstruction recorded; no Lean theorem is claimed.

The 2338 repair artifact says that the analytic coefficient solution was not
cast to binary64 as part of its certificate. The numerical repaired-owner
replay nevertheless uses the binary64 cast of each 2338 interval midpoint.
Record 2677's exact-center family rectangles consume the Lean midpoint
`baseCoefficientCenter2540`, so they cannot be treated as repaired-owner
rectangles without a transfer theorem.

The first exact test is decisive. For family 0, base M0, cell 4096, the
midpoint-cast bit patterns are `0x42eedc401ee43eb1` (real) and
`0xc2ca5a877020782a` (imag). Decoding those patterns as exact binary64
rationals and comparing them with the 2338 rectangle gives a nonzero
outward gap in both coordinates. The complete rational replay is stored in
`results/2678_owner_alignment_no_go.json`.

This is a scoped no-go for consuming the exact-center 2677 rectangles. It is
not a no-go for the Route-A producer. The shortest valid continuation is to
regenerate all 30 family rectangles from the repaired binary64 point owner,
prove the aggregate rectangle and its norm budget against record 2675, then
connect the result to the cell integral theorem. The signed tail and the
remaining three channels stay separate obligations.

Validation: `python scripts/record2678_owner_alignment_no_go.py` exits 0 and
reports exact rational gaps; no external arithmetic or Lean axiom is promoted.
