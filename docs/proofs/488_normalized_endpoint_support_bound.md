# Proof 488: normalized endpoint support bound

## Result

The normalized-endpoint result is good. Proof 488 proves a family-uniform
support bound on the exact source Sonin carrier. Gate 3U still asks for the
raw endpoint.

Write

```text
P        = (c-a)^2 * seminorm_0,0(owner.sourceTest)^2,
H_lambda = sum_i norm(sourceProlateHilbertSchmidtFactor(lambda)(e_i))^2.
```

For every finite prime-power family, Lean proves the exact carrier identity

```text
Tr_source(normalized endpoint)
  = -Tr_ambient(
      complete three-branch commutator
      * normalized metric coframe
      * source inclusion^dagger)
```

and the estimate

```text
norm(Tr_source(normalized endpoint)) <= (6 + 2 H_lambda) * P.
```

The right side is independent of the visible finite set.

## Proof mechanism

The proof retains the physical operator as one complete trace-class owner:

```text
outer boundary
  + reflected outer boundary
  + second-support boundary
  - prolate commutator.
```

Two explicit Hilbert--Schmidt trace cycles transport the source trace through
the common physical pair carrier. On the ambient side, the right sandwich is

```text
normalizedFiniteEulerMetricCoframe * sourceInclusion^dagger.
```

Both factors are contractions, so the complete physical support estimate
applies without exposing an unbounded raw Euler inverse. The proof assembles
all four trace-class branches before taking an absolute value. The three
boundary branches cost `2 P` each. The prolate branch costs

```text
2 * norm(detectorOperator) * H_lambda,
```

and Proofs 484--485 reduce this to `2 P H_lambda` using the genuine selected
convolution root.

## Verification

The final acceptance batch ran in the Ubuntu 24.04 ext4 verification
environment using the existing Lake cache.

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| Proof 488/489 focused axiom audits                   |  3298 | PASS   |
| CCM25Concrete aggregate                              |  3763 | PASS   |
| full repository                                      |  3844 | PASS   |
+------------------------------------------------------+-------+--------+
```

All four audited Proof 488 theorems depend exactly on
`[propext, Classical.choice, Quot.sound]`. The source and audit add no
`sorry`, `admit`, or new axiom declaration. The only non-repository notice
was the existing WSL localhost-proxy warning; replayed repository warnings
are unchanged, and the new source emits no linter warning.

## Boundary

The scaling identity controls the boundary:

```text
normalized endpoint = lowerFactor(S)^2 * raw endpoint.
```

Therefore Proof 488 does not bound the raw canonical response. Dividing its
estimate by `lowerFactor(S)^2` introduces a family-dependent inverse square.
Gate 3U still requires cancellation inside the complete signed raw response
before any family-uniform absolute-value estimate is taken. The finite-S
sign, negative-owner integration, Burnol identity, and
`_root_.RiemannHypothesis` remain open.
