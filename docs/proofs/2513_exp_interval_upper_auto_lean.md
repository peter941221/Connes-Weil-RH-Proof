# Record 2513 — automatic interval-factor positivity

The 2513 wrapper removes the two manually supplied nonnegativity premises from
the 2512 interval exponential adapter.  From `0 ≤ t`, `t < 1`, and
`0 < radius`, Lean proves positivity of `1 - t^2`, then closes both derivative
factor bounds by `positivity`.  The exponential/table comparison remains an
explicit certified premise; this does not close the owner cell inequality.

Evidence: `ConnesWeilRH/Dev/C1RouteAExpIntervalUpper2512.lean` and its audit
file.  The same file now also provides the 30-family panel sum adapter, with
the per-family certified exponential upper as its only replacement input.
The audit must report only the standard three Mathlib axioms.
