# 3173: Route-A owner node interval certificate

Status: Lean-verified on 2026-10-29 with the project Lean 4.30.0 toolchain.

This record defines the concrete data that a numerical producer must supply for
one fixed `OrbitG8Geometry`:

```text
lower[n] <= actual signed node[n] <= upper[n]

archimedeanTerm + sum(upper[n]) <= 0
```

The module converts those lower/upper intervals into the 3172 representation:

```text
center[n] = (lower[n] + upper[n]) / 2
error[n]  = (upper[n] - lower[n]) / 2
```

It proves the resulting absolute enclosure and feeds the existing same-owner
physical-kernel gate. It supplies no numerical intervals and does not claim a
producer theorem, SourceRH, or RH.

The current numerical evidence does not instantiate this contract. Record 2038
marks the one-copy G8-H interval attempt as `A-DEAD-CURRENT-CERTIFICATE` with
source-transform, signed-kernel, coefficient, quadrature, and full-line-tail
components still open. That is a stop condition for the old numerical payload,
not a failure of this reusable contract.

The WSL2 audit reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```
