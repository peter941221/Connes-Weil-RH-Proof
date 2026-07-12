# Proof 181: window exponential/logarithm homeomorphism prerequisites

## Result

The finite-window coordinate maps in `GlobalLogKernel.lean` now have the
complete pointwise and continuity layer:

```text
cc20LogWindowExpPoint : log window -> Haar window
cc20WindowLogPoint   : Haar window -> log window

exp(log rho) = rho
log(exp t) = t
```

Both maps are proved continuous.  These statements are the exact prerequisites
for constructing a measure-preserving equivalence and transporting complete
`Lp`/Hilbert-space operators.  The earlier integral change-of-variables facts
remain unchanged.

## Verification

Using the retained WSL2 Lake cache:

```text
lake build ConnesWeilRH.Source.CC20Concrete
lake env lean ConnesWeilRH/Dev/GlobalLogHaarAudit.lean
```

Both pass (`3497/3497`). The focused declarations use only:

```text
propext
Classical.choice
Quot.sound
```

No measure-preserving assertion, `sorry`, `admit`, or `axiom` was introduced.

## Boundary

The measure equality `Measure.map exp = d rho/rho`, the induced Lp isometry,
and positive-trace transport are still open.  Therefore the same-test CC20
trace read-off and unconditional RH consumer remain unreached.
