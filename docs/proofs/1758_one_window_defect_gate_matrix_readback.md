# 1758 — One-window defect gate matrix readback

Date: 2026-09-21

The theorem
`oneWindowICdefect_gate_iff_twoSpan_qform_nonpos` gives the exact same-owner
readback for a one-window Stage-B defect. Under common support for `g` and
`W`, the defect gate is equivalent to the nonpositive quadratic form of the
two-by-two `gateMatrix` on coefficients `[1, -lam]`.

This makes the unresolved defect route explicit: the diagonal reference gate,
the head gate, and the cross terms must satisfy the signed budget. The theorem
does not assume that budget and proves no sign or RH statement.

Verification: `shortest_route_20260921_defect_matrix_v11.log`, 3784 jobs,
zero `error:` lines, zero `sorryAx`, and standard three-axiom Audit output.
