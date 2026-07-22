# Proof 487: source-Sonin first-jet support bound

## Result

The result is good: Proof 486's family-uniform support estimate now lives on
the exact source Sonin carrier used by the nonlinear Gram ledger.

Let

```text
J = sourceInclusion(lambda),
R = sourceSoninProjection(lambda),
T_S = actual paired finite-Euler first jet.
```

Lean proves the two-sided support identities

```text
R T_S = T_S = T_S R
```

and the legal carrier trace equality

```text
Tr_source(J^dagger T_S J) = Tr_ambient(T_S).
```

Consequently, with

```text
P        = (c-a)^2 * seminorm_0,0(owner.sourceTest)^2,
H_lambda = sum_i norm(sourceProlateHilbertSchmidtFactor(lambda)(e_i))^2,
```

the genuine source response satisfies

```text
norm(Tr_source(sourceActualBandFiniteEulerSoninResponse_S))
  <= (12 + 4 H_lambda) * P.
```

The constant is unchanged and independent of the finite prime-power family.

## Proof mechanism

The carrier map is the actual closed-subspace inclusion.  The pre-existing
Gram-response theorem supplies

```text
J J^dagger = R.
```

The paired response has `R` as the first and last factor in both causal
orientations, so its left and right absorption follow from `R^2=R` without
assuming that the causal inverse is self-adjoint.

The trace transport does not invoke an informal basis-independence principle.
Let the ambient Hilbert--Schmidt pair be `T_S=L^dagger M`.  The source pullback
pair has legs `LJ` and `MJ`.  Its trace is cycled to the common physical pair
carrier:

```text
Tr_source((LJ)^dagger(MJ))
  = Tr_pair(M J J^dagger L^dagger)
  = Tr_pair(M R L^dagger).
```

A second Hilbert--Schmidt cycle returns to the ambient carrier:

```text
Tr_pair(M R L^dagger)
  = Tr_ambient(L^dagger M R)
  = Tr_ambient(T_S R)
  = Tr_ambient(T_S).
```

Every exchange is backed by explicit square-summability.  In particular,
precomposition of `M` by the bounded projection `R` is proved
Hilbert--Schmidt before the second cycle is used.

## Verification

The acceptance commands ran in the Ubuntu 24.04 ext4 verification environment
using the existing Lake cache.

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| Proof 487 source plus axiom audit                    |  3286 | PASS   |
| CCM25Concrete aggregate                              |  3761 | PASS   |
| full repository                                      |  3842 | PASS   |
+------------------------------------------------------+-------+--------+
```

All four audited Proof 487 theorems depend exactly on
`[propext, Classical.choice, Quot.sound]`.  The source and audit contain no
`sorry`, `admit`, or new axiom declaration.  The only non-repository notice
was the existing WSL localhost-proxy warning; replayed repository warnings
are unchanged, and the new Proof 487 source emits no linter warning.

## Boundary

This closes the source-carrier homogeneous first-jet bound, not Gate 3U.  The
remaining same-object path is

```text
source first jet
  + quadratic Gram remainder
  = canonical finite-S endpoint response
  -> Gate 3U.
```

The next producer must control the quadratic remainder on this same source
carrier with a family-uniform support/Sobolev polynomial.  The finite-S sign,
negative-owner integration, Burnol identity, and `_root_.RiemannHypothesis`
remain open.
