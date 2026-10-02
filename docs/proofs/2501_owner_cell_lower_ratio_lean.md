# Record 2501 — Lean lower-ratio geometry

`C1RouteAOwnerCellLowerRatio2501.lean` defines the ratio needed by the
negative exponential envelope: zero on cells crossing zero, and the nearer
endpoint ratio on same-sign cells.  It proves that this ratio is bounded by
`|coordinate / ownerRad|` throughout the cell, plus nonnegativity.

This is a geometry interface only.  It does not import the 2501 JSON, prove
the exponential split for the owner constants, or close the hcell/table
premise.
