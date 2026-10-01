# 2394 — directed span partition audit

Date: 2026-10-02.

The 2385 replay's ordered spans are reconstructed from its recorded
`nodes=776611` and `span=20001`, with the 2359 source hash checked first. The
39 slices are contiguous, have no overlap or gap, and cover every node from
zero through `nodes - 1`.

This closes only the index-partition/readback obligation for the 2393
interface. It does not prove pointwise directed term dominance and does not
import a numeric value into Lean.
