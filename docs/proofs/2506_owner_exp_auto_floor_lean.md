# Record 2506 — automatic owner exponent split

`C1RouteAOwnerExpAuto2506.lean` removes the need to store an integer split
index as an unverified input.  For every nonnegative exponent `x`, Lean takes
`n = ⌊x⌋₊` and proves `n ≤ x ≤ n+1`, then applies the formal negative-
exponential envelope from record 2498.

This closes only the integer-selection interface.  It does not prove the
cellwise lower-ratio bound, the 2501 numerical table, hcell, or the producer
margin.
