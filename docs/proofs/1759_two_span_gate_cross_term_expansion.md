# 1759 — Two-span gate cross-term expansion

Date: 2026-09-21

The theorem `twoSpan_gate_qform_expand` expands the exact two-dimensional
gate quadratic form for basis tests `A` and `B` and coefficient vector
`[1, -lam]`. It identifies the diagonal terms with the two genuine
convolution-square gates and retains both directed cross gates separately.

This is the algebraic normal form needed by the active Stage-B defect attack.
It makes no symmetry, sign, or numerical assumption about the cross gates and
proves no RH statement.

Verification: `shortest_route_20260921_cross_expand_v13.log`, 3784 jobs,
zero `error:` lines, zero `sorryAx`, and standard three-axiom Audit output.
