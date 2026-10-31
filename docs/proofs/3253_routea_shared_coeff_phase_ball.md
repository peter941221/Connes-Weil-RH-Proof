Record 3253: shared coefficient-phase taxi ball

Status: verified enclosure bridge; numerical sign still open.

The axis-aligned staged boxes from record 3252 grow exponentially under
repeated squaring and are therefore unsuitable for a signed real-part bound.
This record switches the phase block to a center-plus-radius `ComplexTaxiBall`.
The center is the rational Taylor evaluator propagated through the exact
squaring recurrence; the radius tracks only the Taylor remainder and its
product propagation.

Families 8 through 29 are summed before the real-part upper is taken. This
preserves coefficient-phase cancellation and leaves one explicit target:

```text
shared coefficient-phase ball
        |
        v
center.re + radius < 0
```

The record currently proves membership and exports the real upper interface;
it does not claim the strict inequality, the shared bump product sign, the
finite aggregate, `producer_go`, `SourceRH`, or the Riemann Hypothesis.
