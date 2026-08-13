# 01 - PSP / Paley-Wiener project

Status: open, corrected 2026-08-12. This project tests the current
infinite-carrier Gate-3U route. It does not prove RH.

## Target

The required witness is stronger than a nonzero Sonin vector:

```text
find u : sourceSoninCarrier(lambda) such that
  soninWindowRestriction(lambda, u) != 0
in L2(volume.restrict (log lambda, log lambda + log 2)).
```

This formulation is invariant under the almost-everywhere quotient in `L2`.
It replaces the invalid point-value test.

## Progress

| Step | Claim | Status |
|---|---|---|
| A | Ambient radial indicator has nonzero restricted norm | Closed |
| B | HT isometry and radial/HT-radial membership decomposition | Closed |
| C | Nonzero scattering Toeplitz kernel / Sonin witness | Open |
| D | Witness has nonzero log-2-window restriction | Open |
| E | Coframe bridge proves `twoOuterNonzeroObligation` | Open |

The exact `+-1` eigenvector approach remains unsuitable as a generic L2
construction. The closed reflection identity `R P+ R = P-` supports the
Fourier-side reduction but does not create a kernel vector.

## Fourier-side form

The valid Fourier target is

```text
find psi in H+ intersect L2(R), psi != 0,
with m * psi in H- intersect L2(R),

m(xi) = Gamma_R(1/2 - i * 2*pi*xi) /
        Gamma_R(1/2 + i * 2*pi*xi).
```

In repository terms this is
`archimedeanScatteringToeplitzKernel_nontrivial`. A Wiener--Hopf
factorization does not prove this predicate: a unimodular boundary factor has
constant modulus and is not in `L2(R)`.

## Construction candidate

The prolate/Sonin route is the current candidate. Connes--Moscovici state that
a negative eigenfunction of their self-adjoint prolate operator belongs to the
Sonin space:

```text
https://pmc.ncbi.nlm.nih.gov/articles/PMC9295779/
```

The formal work must establish the operator domain, a negative eigenfunction,
transport to this repository's `sourceSoninCarrier`, and nonzero restriction
to the required window.

## Consequence boundary

If steps C through E close, the result proves nonzero outer leakage for the
family `{2}` and rejects the current infinite-carrier Gate-3U cancellation
route. It supplies route diagnosis, not an RH proof.
