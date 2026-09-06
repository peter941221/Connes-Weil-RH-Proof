# 1210 - Plain-window positive-trace no-go

Date: 2026-09-06.

Status: formal no-go for the plain-window detector family. RH is not claimed.

The canonical cutoff operator `windowedBoundaryDetector` has an exact trace
formula proportional to the growing window length times the fixed
`L2`-mass of `g.test`.  For every nonzero compact-log root these traces are
unbounded.  Any `CutoffLimitContracts` package would instead force the same
traces to converge to the finite same-owner `qw(g)`, because its remainder
tends to zero.  Therefore that contract type is empty for every nonzero test.

This closes only the plain-window detector.  It does not close the
projection-window owner `C_n† K C_n`, whose trace and readback obligations are
different and remain live.

Evidence: `not_nonempty_cutoffLimitContracts_of_test_ne_zero` in
`C1PositiveTraceCutoffVerdict`, audited by the probe module. Focused build:
`p2-plain-window-trace-nogo.log`, footer `Build completed successfully (3705
jobs)`, zero `error:` lines, standard three axioms, and no `sorryAx`.
