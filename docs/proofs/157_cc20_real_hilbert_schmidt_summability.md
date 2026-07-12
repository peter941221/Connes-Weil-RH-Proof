# CC20 Real Hilbert--Schmidt Summability

Date: 2026-07-12

## Result

The compact real `L²` operator now has a proved kernel-coefficient
representation on every input:

```text
cc20CompactL2Operator u = toLp (x |-> inner u K_x).
```

For every real Hilbert basis, the squared output norms are summable:

```text
Summable (fun i => ||cc20CompactL2Operator (basis i)||^2).
```

## Proof shape

The kernel sections form a continuous map into the same `L²` space. Their
inner products with an arbitrary input define a bounded continuous coefficient
operator. Agreement with the original integral operator on continuous inputs,
followed by density, identifies this coefficient operator with the existing
`cc20CompactL2Operator`.

For a finite basis subset, the squared operator norms become integrals of
squared kernel coefficients. Bessel's inequality bounds their pointwise sum by
the squared `L²` norm of the same kernel section. Integration gives one uniform
finite-sum bound, and `summable_of_sum_le` gives basis summability.

## Boundary

This is a genuine real Hilbert--Schmidt summability theorem. It does not yet
construct the project's complex `PositiveTrace.BasisHilbertSchmidtData`, prove
the exact Parseval equality with the product kernel integral, identify the
operator with the source CC20 `K_I`, provide a trace read-off, or prove RH.
