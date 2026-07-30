# Proof 656: two-step coboundary factorization

## Result

Proof 656 isolates the paired-prefix channel left after Proof 655. If the
scaled complete adjoint coboundary factors as

```text
s_p^(-1) (I-U_(-a)) C_(p,S)^*
  = (I-U_(-2a)) R_(p,S),
a = log p,
```

then the prime-square-step sum telescopes to two endpoints and has norm at
most `2 ||R_(p,S)||`.

A route-uniform Proof 655 size bound together with route-uniform factors
`R_(p,S)` is sufficient for Proof 649 and therefore for the raw and renewed
Bone 1 consumers.

Proof 669 later proves that the two inputs are not independent on the actual
whole-line carrier: the two-step factor alone implies the horizon-one size
bound, and is same-bound equivalent to Proof 648's ambient-loss quotient.
Proof 670 then shows that a restricted raw Bone 1 bound `B` plus an actual
route-uniform frame-loss stability bound `K` is sufficient to construct that
quotient and this factor with constant `B*K`. Both inputs remain open
producers.

## Boundary

The factorization is a named producer contract. No source theorem constructs
the factors or proves a route-uniform factor norm. It must not be inferred
from the horizon-one bound alone. The valid converse direction supplied by
Proof 669 is `two-step factor -> horizon-one bound`.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorTwoStepCoboundaryFactorization.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorTwoStepCoboundaryFactorizationAudit.lean
```

The combined Proof 650--659 audit passed with `3454` jobs. Audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.
