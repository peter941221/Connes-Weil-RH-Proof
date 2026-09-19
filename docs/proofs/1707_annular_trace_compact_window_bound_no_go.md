# 1707 — finite-window compact-kernel energy cannot supply the S3 uniform annular bound

Date: 2026-09-20.

This record fixes the next analytic boundary after the projected-root normal
form of record 1706.  The finite-window root operator is Hilbert--Schmidt for
each fixed window, but its compact-kernel trace estimate grows with the window
length.  Consequently that estimate cannot prove the uniform annular trace
bound required by S3.

## Committed evidence

`C1G8R3SourceRootFiniteWindowCriterion.lean` proves, for every fixed `n`,
square-summability of the finite-window root columns and of the annular
columns.  It then proves that S3 follows from a uniform bound on the annular
trace.  The same source defines the annular output as the difference of two
finite output projections.

Independently, `C1PositiveTraceCutoffGrowth.lean` proves the exact compact
boundary-kernel formula

```text
trace(window) = window_length * root_L2_mass
```

and proves divergence when the root mass is positive.  This is the same
finite-window mechanism used by the fixed-`n` root energy consumer.  A norm
one projection estimate therefore gives only a bound proportional to the
expanding window length; it cannot yield an `n`-independent annular bound.

## Route consequence

The missing S3 producer must use the detector-specific source carrier, in
particular the interaction between its radial half-line condition and its
Fourier-support condition.  The following shortcuts are ruled out by the
committed definitions:

1. bounding the annular columns by the unwindowed root columns;
2. applying the fixed-window compact-kernel HS estimate uniformly in `n`;
3. replacing the source-compressed response by an ambient compact-kernel
   trace.

The live target remains the exact uniform annular trace bound from record
1706.  No S3 estimate, RH conclusion, or numerical inference is claimed.

Classification: formal source audit, based on committed theorems; no new
axiom and no unresolved numerical observation.
