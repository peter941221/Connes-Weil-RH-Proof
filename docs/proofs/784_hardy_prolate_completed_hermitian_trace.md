# Proof 784: Hermitian completed Hardy--prolate trace endpoint

## Result

Proof 783 identifies each Hermitian target diagonal with the real part of one
completed physical boundary pairing. Proof 784 lifts that pointwise identity
to the actual named-basis trace and then to the canonical real Gate contract.

For every named source Hilbert basis `(e_i)`, Lean proves

```text
Tr(Hermitian(Target_S))
  = sum_i Re(-<A_S e_i, Q_S K_complete J e_i>).
```

For the route-selected canonical finite family, it proves the exact
equivalence

```text
canonicalRealGate3UAt(owner, bound)

iff

norm(sum_i Re(-<A_S e_i, Q_S K_complete J e_i>)) <= bound.
```

The existing fixed-family trace-legality witness is explicit in the second
theorem. No source-to-ambient trace cycle is inserted.

## Why It Matters

The remaining analytic theorem now has a single literal target:

```text
compact root
    |
    v
K_complete: outer + reflected second support + prolate
    |
    v
one completed Hardy--prolate pairing
    |
    v
one real trace series
    |
    v
canonical real Gate 3U
```

This removes the need for a future estimator to pass through an oblique
full-kernel coordinate. It does not localize the chosen source basis; compact
root locality still has to be proved directly for the completed series.

## Scope

Proof 784 is a trace readout and equivalence theorem. It does not establish a
support-polynomial bound, exchange a basis sum with a renewal expansion, or
separate the outer, reflected-second-support, and prolate branches.

Proof 784 does not prove Gate 3U, the finite-S sign, Burnol's identity, or
`_root_.RiemannHypothesis`.
