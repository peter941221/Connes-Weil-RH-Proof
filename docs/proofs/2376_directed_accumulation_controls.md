# 2376 — directed accumulation dominance control

Date: 2026-10-02.

The nodal evaluator now records two explicit dominance controls: every
worker-span MPFR round-up dominates the exact sum of the binary64 terms in
that span, and the final MPFR round-up dominates the exact binary64 integral.
Both controls are true for all four channels on the 1001-node sequential
control.

This is a regression/control artifact only.  The 776611-node run did not
finish within the 180-second bounded replay and produced no artifact, so this
record does not upgrade the full-grid status.  The directed accumulation
theorem, nodewise import into Lean, and trapezoid certificate remain open.
