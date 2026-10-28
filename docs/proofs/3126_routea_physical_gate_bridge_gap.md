# 3126 - Route-A versus physical-gate symbol bridge gap

Date: 2026-10-27.

Status: owner and coverage audit. The Route-A joint symbol and the 3122
physical gate use compatible frequency coordinates only after an explicit
`2*pi` rescaling, but their prime terms are not identified by the current
API. Therefore the 3122 deficit theorem cannot be reused as a Route-A core
margin or no-go result.

## The two symbols

Route A defines, for an angular frequency `xi_A`,

```text
m_A(xi_A) = -c3Sigma(xi_A)
              - sum_(p in routeAVisiblePrimes geometry)
                  log(p) * P_p(xi_A)

P_p(xi_A) = (1-r^2)/(1-2*r*cos(log(p)*xi_A)+r^2) - 1
r = p^(-1/2).
```

The 3120/3122 physical gate uses cycle frequency `xi_B`:

```text
m_B(xi_B) = c3Sigma(2*pi*xi_B)
              + sum_(q in globalPrimeIndexSet square)
                  2*Lambda(q)/sqrt(q) * cos(2*pi*xi_B*log(q)).
```

The archimedean coordinates align under `xi_A = 2*pi*xi_B`, with the
overall sign handled by the respective density definitions. The prime terms
require a separate owner-preserving proof.

## Why the prime terms are not equal yet

For one prime `p`, the formal Poisson expansion is

```text
P_p(xi_A) = 2 * sum_(k >= 1) p^(-k/2) * cos(k*log(p)*xi_A).
```

After `q = p^k`, this matches the 3120 coefficient
`2*Lambda(q)/sqrt(q)` only when the finite physical index set contains exactly
the required prime powers. The current definitions do not establish that:

```text
routeAVisiblePrimes geometry
  = (orbitVisiblePrimeRange geometry).filter Nat.Prime

globalPrimeIndexSet square
  = {q | IsPrimePow q and finitePrimeTerm square q != 0}.
```

The first set is every prime below a support-derived upper range. Its Poisson
multiplier contains all powers of each selected prime, including powers above
the finite range. The second set is the exact owner-dependent finite set of
nonzero prime-power terms. A support upper bound proves only that members of
the second set are below a cutoff; it does not prove set equality, vanishing
of omitted powers, or the sign of the omitted aggregate.

This is the same class of coverage issue documented in record 3118, now seen
at the attempted Route-A/Route-B symbol bridge. It is not repaired by
changing the frequency grid or by comparing sampled values.

## Consequence for 3125

The strict positive deficit in
`C1ActualWeilUnavoidableDeficit3122.lean` belongs to `gateSymbol3122` and its
actual `globalPrimeIndexSet`. Until the prime-power bridge is proved, that
theorem cannot be transported to `routeAJointSymbol` or used to sign
`Qcore(T)` for Route A. Reusing it would silently change both the symbol and
the owner.

The finite-core target therefore remains:

```text
Qcore_A(T) >= E_ann + E_tail
```

with the Route-A symbol and the exact moving owner. The candidate shortcut
`reuse the 3122 deficit/credit split` is closed under the current hypotheses.

## Admissible bridge options

1. Prove an exact same-owner identity between the Poisson expansion of
   `routeAJointSymbol` and the complete `globalPrimeIndexSet` prime-power sum,
   including `xi_A = 2*pi*xi_B` and all integrability conditions.

2. Keep the finite Route-A symbol and prove a signed, owner-specific bound for
   the omitted prime-power residual. An absolute support envelope is not
   enough because later powers can cancel earlier terms.

3. Change the Route-A symbol definition to consume the exact finite
   prime-power owner, then re-audit every downstream theorem that currently
   relies on its prime-base Poisson form. This is an API/owner change and must
   be treated as a separate design decision.

Evidence:

- `ConnesWeilRH/Dev/C1RouteAJointSymbolData3080.lean`
- `ConnesWeilRH/Dev/C1RouteBPrimeFourierReadback3120.lean`
- `ConnesWeilRH/Dev/C1ActualWeilUnavoidableDeficit3122.lean`
- `ConnesWeilRH/Source/CCM25Concrete/SelectedWeilSquare.lean`
- `ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean`
- `docs/proofs/3118_routeb_gate_coverage_direction_review.md`
- `docs/proofs/3125_owner_core_margin_gate.md`
