# 2845 Route B phase-box gate failure

The first direct phase soundness gate was attempted on cell 4096 for orders
0 through 7. The gate fails at order 2: the Python exported phase box is not
proved to contain the exact Lean `phaseJetInterval2734` box.

This is a scoped gate failure, not a conclusion that either recurrence is
wrong. It means the current Python phase endpoint artifact cannot yet be used
as a Lean soundness input. The next action is to compute the endpoint delta and
either correct the Python stage convention or add a proved outward inflation.
No transition charge or global claim may consume the current phase boxes until
this gate passes.
