# Proof 183: Haar/log finite-window L2 isometry

## Result

`GlobalLogKernel.lean` now defines

```text
cc20WindowHaarLogL2IsometryEquiv
```

between

```text
Lp Complex 2 (cc20WindowHaarMeasure lambda hlambda)
```

and

```text
Lp Complex 2 (cc20LogWindowBaseMeasure lambda)
```

The forward map is Mathlib's `Lp.compMeasurePreservingₗᵢ` along
`rho = exp t`; the inverse uses `rho -> log rho`. The two inverse laws are
reduced to the already proved subtype identities `exp(log rho)=rho` and
`log(exp t)=t`.

For every continuous logarithmic input, the same module also proves that the
norm of the Haar regular-kernel output after this isometry equals the norm of
the existing global-log finite-window action. This is a same-test numerical
compatibility theorem, not merely equality of ambient carrier dimensions.

## Verification

Using the retained WSL2 Lake cache:

```text
lake build ConnesWeilRH.Source.CC20Concrete.GlobalLogKernel
lake env lean ConnesWeilRH/Dev/GlobalLogHaarAudit.lean
```

Both passed. The focused declaration uses only:

```text
propext
Classical.choice
Quot.sound
```

## Boundary

The isometry transports finite-window `L2` vectors, but the regular-kernel
operator has not yet been proved equal, as an operator, to the restricted
global-log operator. Positive-trace transport, common-window exhaustion, the
diagonal distributional identity, the same-test trace read-off, and
unconditional RH remain open.
