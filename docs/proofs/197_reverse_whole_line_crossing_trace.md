# Proof 197: Reverse compact trace has the adjoint whole-line owner

Status: accepted crossing-layer milestone. Both orientations of the compact
finite-prime trace now have distinct, correct whole-line operator owners. RH
remains unproved.

## Operator direction

For compact analysis operators `L` and `R`, the two kernel owners are

```text
forward trace product = L† R,
reverse trace product = R† L = (L† R)†.
```

Therefore the reverse trace cannot be connected to the same whole-line
operator as the forward trace. The correct pair is

```text
forward = C_h C_(h*) J_b,
reverse = (C_h C_(h*) J_b)†
        = J_b† C_h C_(h*).
```

This uses only the adjoint of the proved forward identity. It does not commute
`J_b` through convolution.

## Lean chain

`PositiveTrace.ordinaryTraceAlong_adjoint` proves in any fixed Hilbert basis

```text
Tr(T†) = star(Tr(T)).
```

`reversePairData_traceProduct_eq_pairData_adjoint` proves the compact operator
identity. Combining it with proof 196 gives
`reversePairData_trace_eq_globalConvolutionCrossing_adjoint`:

```text
Tr_compact(reversePairData.traceProduct)
  = Tr_global((cc20GlobalConvolutionCrossing h b)†).
```

Together with the compact coefficient theorem, this whole-line adjoint trace
is `b F(-b)`, while the forward trace is `b F(b)`. Their weighted sum is the
existing selected finite-prime atom.

## Verification

The source bridge builds with 2978 jobs and the focused import-facing audit
builds with 2979 jobs. The three new declarations report only:

```text
propext
Classical.choice
Quot.sound
```

The next route obligation is to identify the forward/adjoint pair with the
single-crossing main term of the semilocal Euler-log metric variation on the
same selected convolution square.
