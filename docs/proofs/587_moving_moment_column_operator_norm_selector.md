# Proof 587: moving moment-column operator-norm selector

Proof 586 required an explicitly supplied bounded sequence in the actual
source Sonin carrier.  This batch supplies the exact functional-analytic
selector for that sequence.

The arithmetic sequence is fixed explicitly as

```text
p_n = Nat.nth Nat.Prime n.
```

Mathlib proves `n + 2 <= p_n`, so the actual Euler coefficient satisfies

```text
ccm24PrimeEulerCoefficient(p_n) = p_n^(-1/2) -> 0.
```

For

```text
C_p = M_p oldFrame_p^dagger newFrame_0
```

acting on `sourceSoninCarrier lambda`, assume the strict operator-norm lower
bound on this actual arithmetic-prime sequence

```text
epsilon < ||C_(p_n)||   eventually.
```

Mathlib's continuous-linear-map norm selector then gives source vectors
`x_n` with

```text
||x_n|| < 1,
epsilon < ||C_(p_n) x_n||
```

on the same eventual set.  The direct theorem feeds these vectors into Proof
586, so together with `ccm24PrimeEulerCoefficient (p_n) -> 0` it rules out
every finite uniform old-carrier domination package.

```text
operator-norm lower bound for C_p
              |
              v
unit-ball x_n in the actual source Sonin carrier
              |
              v
moment lower bound on C_(p_n) x_n
              |
              v
no uniform old-carrier quotient
```

The selector is deliberately stated on the concrete source subtype.  It does
not use an ambient translated detector, does not assume that the source Sonin
intersection is translation invariant, and does not prove the missing
operator-norm lower bound itself.  The remaining source-specific Bone 1
producer is therefore reduced to one statement for the actual signed column
on the actual arithmetic primes:

```text
epsilon < ||C_(Nat.nth Nat.Prime n)|| eventually.
```

The direct entry point is
`noExistsUniformOldCarrierDomination_of_eventually_arithmeticPrime_column_norm_gt`.

Lean owners:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMovingMomentColumnSelector.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMovingMomentColumnSelectorAudit.lean
```

The audited declarations are expected to use exactly:

```text
[propext, Classical.choice, Quot.sound]
```

This remains a Bone 1 conditional obstruction.  It is not a Gate 3U estimate,
finite-S sign, Burnol identity, or RH proof.
