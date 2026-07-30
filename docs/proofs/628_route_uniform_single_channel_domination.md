# Proof 628: route-uniform single-channel domination

## Result

Proof 628 names the exact analytic statement left by Proof 627.  There must
exist one finite constant `C` such that, for every route-valid adjacent step
`(p,S)` and every source vector `x`,

```text
||signedCompressedInteriorOwner_(p,S) x||^2
  <= C^2
     ||L_p^dagger N_p^dagger newFrame_(p,S) x||^2.
```

Here

```text
L_p = primeEulerAmbientLossFactor(p),
N_p = normalizedPrimeEulerInverse(p).
```

The quantifier order is part of the theorem:

```text
exists C >= 0,
  forall route-valid (p,S),
    forall source x,
      relative-energy inequality.
```

It is not enough to choose a different bound after seeing `(p,S)`.

## Exact equivalences

For a fixed `C`, Lean proves

```text
route-uniform renewed-channel factor of bound C
  <->
route-uniform renewed-channel domination by C.
```

The reverse direction is the repository's Douglas factorization theorem
applied at each route-valid step.  It introduces no closed-range hypothesis
and does not change `C`.

Combining this fixed-bound equivalence with Proof 627 gives

```text
exists a finite route-uniform Proof 625 physical bound
  <->
exists a finite route-uniform renewed-channel domination bound.
```

The existential formulation is necessary.  The two coordinate conversions
have the asymmetric norm ledger

```text
Physical(C)      -> SingleChannel(C),
SingleChannel(C) -> Physical(17*C).
```

Proof 628 also specializes the route-uniform inequality to every genuine
suffix `p :: S` of `FinitePrimePowerFamily.visiblePrimes` using the existing
deduplication theorem.

The numerator has one further exact same-object normal form.  With

```text
K_(p,S)
  = reverseTransition_(p,S)^dagger * band_S
    - band_(p::S) * reverseTransition_(p,S)^dagger,
```

Lean proves

```text
A_(p,S) = transition_(p,S)^dagger * K_(p,S),

||A_(p,S) x|| <= ||K_(p,S) x||
               <= 8 ||A_(p,S) x||.
```

The first bound uses contractivity of the actual transition.  The second
uses the paired reverse transition and the source bound
`primeSchurMarkovScalar(p) >= 1/8`.  Consequently a route-uniform quotient
for `K` implies the renewed domination with the same bound, while renewed
domination implies the quotient for `K` with bound `8*C`.  After existentially
quantifying the finite constant, the two statements are equivalent.

This reduction keeps both signed adjacent boundary responses inside `K`.
It does not assert that either response vanishes or that their difference
cancels.

## Why this is the correct Bone 1 bottom

The denominator is the complete same-object channel

```text
L_p^dagger * N_p^dagger * newFrame_(p,S).
```

It must remain whole.  The target does not ask for a family-uniform lower
bound on `L_p`, `N_p`, or `newFrame` separately.  Such a lower bound would be
strictly stronger and repeats the rejected closed-range/spectral-gap route.

The next theorem must be source-specific and quantitative.  It must exploit
the actual Sonin/Fourier compact-support geometry or an exact covariance
identity relating `signedCompressedInteriorOwner` to this same denominator.
Proof 629 later closes exact kernel compatibility, but injectivity alone gives
no uniform lower bound.  Independent operator-norm estimates do not prove
relative-energy domination.

```text
 +---------------------------+
 | signed interior owner A   |
 +-------------+-------------+
               |
               | must vanish/control on the same fibers
               v
 +---------------------------+
 | B = L^dagger N^dagger J   |
 +-------------+-------------+
               |
               v  Douglas
 +---------------------------+
 | bounded readout R, A=R B  |
 +---------------------------+
```

## Boundary

Proof 628 is an exact quantifier and interface reduction.  It does not prove
the displayed inequality or construct `C`.  Bone 1, Gate 3U, the finite-S
sign, Burnol's identity, and RH remain open.

## Verification

The Ubuntu-24.04 WSL2 ext4 verification copy passed:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| route-domination source              |  3399 | PASS   |
| focused axiom audit                  |     - | PASS   |
| CCM25Concrete aggregate              |  3901 | PASS   |
| full repository                      |  3982 | PASS   |
+--------------------------------------+-------+--------+
```

All ten audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorSingleChannelRouteDomination.lean

ConnesWeilRH/Dev/
  ...AntiresonantInteriorSingleChannelRouteDominationAudit.lean
```
