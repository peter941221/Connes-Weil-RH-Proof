# Proof 489: raw endpoint lower-factor bound

## Result

The fixed-family result is good. Proof 489 converts Proof 488 back to the raw
source endpoint and exposes a coefficient that depends on the finite family.

Let

```text
L_S      = finiteEulerLowerFactor(family.visiblePrimes),
P        = (c-a)^2 * seminorm_0,0(owner.sourceTest)^2,
H_lambda = sum_i norm(sourceProlateHilbertSchmidtFactor(lambda)(e_i))^2.
```

Lean proves

```text
Tr(raw endpoint) = L_S^(-2) * Tr(normalized endpoint)
```

and hence

```text
norm(Tr(raw endpoint))
  <= L_S^(-2) * (6 + 2 H_lambda) * P.
```

Combining this with Proof 487's actual source first-jet estimate gives

```text
norm(Tr(actual quadratic remainder))
  <= ((12 + 4 H_lambda)
      + L_S^(-2) * (6 + 2 H_lambda)) * P.
```

Proof 489 also specializes the bound to the exact selected canonical family
and the `canonicalActualBandCompletedRelativeResponse` consumed by the route.

## Proof mechanism

The endpoint conversion uses the defining scaling identity

```text
normalizedSourceBandGramResponse = L_S^2 * sourceBandGramResponse.
```

The positivity theorem `finiteEulerLowerFactor_pos` makes `L_S^2` invertible,
and linearity of the ordinary trace gives the exact inverse-square formula.
No estimate is used in this step.

The proof keeps the nonlinear source ledger on one carrier:

```text
actual quadratic remainder
  = actual paired first jet
  - raw Gram endpoint.
```

The triangle inequality separates only these two complete trace-class
responses. Proof 487 supplies `(12 + 4 H_lambda) P` for the first jet, and
Proof 488 plus the exact scaling supplies the displayed raw-endpoint term.
The existing same-object identification between the canonical completed
response and the canonical source remainder yields the canonical theorem.

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

All four audited Proof 489 theorems depend exactly on
`[propext, Classical.choice, Quot.sound]`. The source and audit add no
`sorry`, `admit`, or new axiom declaration. The only non-repository notice
was the existing WSL localhost-proxy warning; replayed repository warnings
are unchanged, and the new source emits no linter warning.

## Boundary

Proof 489 closes the fixed-`S` bound, not Gate 3U:

```text
normalized endpoint uniform bound       CLOSED
raw endpoint fixed-S bound               CLOSED
raw endpoint family-uniform bound        OPEN
Gate 3U                                  OPEN
```

The repository has no family-independent bound for `L_S^(-2)`. The active
analytic bottom is a signed raw-response cancellation theorem that keeps the
outer, reflected, second-support, and prolate branches together and removes
the inverse lower-factor-square loss before taking an absolute value.
The finite-S sign, negative-owner integration, Burnol identity, and
`_root_.RiemannHypothesis` remain open.
