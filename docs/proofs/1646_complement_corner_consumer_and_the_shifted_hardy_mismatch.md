# 1646 — Complement-corner consumer and the shifted-Hardy mismatch

## Result

The actual finite-S leakage leg is already known to have the exact form

```text
U_b C [R_b (I - Q_0) R_b] U_{-b},   b = log(lambda).
```

This brick formalizes the only valid transport direction: if the source-basis
square sum of the complement corner `R_b (I-Q_0) R_b` is supplied, bounded
root convolution and the two logarithmic translations give the actual leakage
square sum.  The Lean declaration is
`sourceRootCompletedRightCommutatorLeftLeg_sourceBasis_normSq_summable_of_complementCorner`.

## What the failed first attempt established

The existing shifted-Hardy theorem supplies square summability for the
different crossing block `(I-R_b) Q_0 R_b`.  Lean rejects substituting it for
`R_b (I-Q_0) R_b`, as it should.  Thus the S3 obligation is not closed by the
already-controlled interior compression; the live analytic target is exactly
the complement corner after the selected root.

The build of the corrected consumer and Audit completed with 3285 jobs, zero
`error:` lines, zero `sorryAx`, and the standard three axioms.

No RH conclusion is claimed.
