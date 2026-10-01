# 2387 — composite node monotonicity interface

Date: 2026-10-02.

The Lean layer now exposes the exact per-cell form of the composite upper and
proves monotonicity under pointwise node-upper replacement for nonnegative
step.  This is the formal shape needed by the numerical import: once a
directed node upper dominates the owner value at every node, the composite
bound follows without an implicit sum-reordering argument.
