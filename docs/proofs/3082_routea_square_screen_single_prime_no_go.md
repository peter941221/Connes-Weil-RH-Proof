# 3082 - Route A Gate 1 single-prime square-kernel screen

Date: 2026-10-24

Status: SINGLE-PRIME NONNEGATIVE-KERNEL PROPOSAL REJECTED.

The Lean module
`ConnesWeilRH/Dev/C1RouteAJointSymbolSquareScreen3082.lean` proves, for every
prime p, that the owner-specific Poisson contribution changes sign:

```text
routeAPrimePoissonSymbol p 0 > 0
routeAPrimePoissonSymbol p (pi / log p) < 0
```

The second point uses `log p * (pi / log p) = pi`, so the cosine is -1. The
first point uses cosine 1. Therefore no single-prime contribution can itself
be a pointwise nonnegative kernel. The audited theorem
`no_single_prime_nonnegative_kernel_factor` records this as a formal no-go.

This is a scoped result. It does not exclude a genuinely joint factorization
whose kernel combines the archimedean term and all prime-power contributions
before taking a square. Such a joint mechanism is the only remaining Gate 1
candidate worth testing.

Verification: Linux ext4 `lake build` completed 3797 jobs. The audit reports
only `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

Correction to the Gate 1 investigation: the Poisson multiplier at zero
frequency is not zero. With r = 1/sqrt(p), it equals
`(1-r^2)/(1-r)^2 - 1 = 2r/(1-r) > 0`. The attempted stronger joint zero-frequency
no-go was therefore withdrawn and is not part of the compiled module. The
validated 3082 result remains only the single-prime sign-change theorem.

## Zero-frequency transform result

Record 3082 now formally proves that the actual off-line orbit geometry has
`routeAOrbitTransform geometry 0 = 0`. This follows from the exact half-node
interpolation pin and the centered selected-owner Laplace identity. Hence the
negative joint symbol at xi = 0 seen in record 3083 is masked by a zero square
factor. A joint-kernel no-go must use a nonzero frequency or a derivative jet.
