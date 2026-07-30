# Proof 626: route-valid physical factorization

## Result

The previous Bone 1 package quantified over every visible prime and every
finite list, including lists with repeated primes.  The actual arithmetic
owner does not have that domain:

```text
FinitePrimePowerFamily.visiblePrimes is deduplicated,
and every Schur step uses a suffix p :: S of that list.
```

Proof 626 therefore defines the route-valid step predicate

```text
SuffixRouteValidStep p S := (p :: S).Nodup
```

and packages the family-uniform physical factor only on this domain.  The new
physical-factor contract and the synchronized joint-gap readout contract are
equivalent with exactly the same bound.  The earlier all-list contract implies
the route-valid contract, but no converse is claimed.

For an actual `FinitePrimePowerFamily`, Lean uses
`family.visiblePrimes_nodup` together with `List.IsSuffix.nodup` to prove that
every suffix step is route-valid.  A route-valid producer therefore supplies
the Proof 625 physical factor, with one shared bound, at every genuine step of
that finite family.

```text
 +----------------------------------+
 | all-list contract                |
 | forall p S                       |
 +----------------+-----------------+
                  |
                  v  restriction, no norm cost
 +----------------------------------+
 | route-valid contract             |
 | forall p S, (p :: S).Nodup       |
 +----------------+-----------------+
                  |
                  v  every actual suffix
 +----------------------------------+
 | family.visiblePrimes             |
 | deduplicated by construction     |
 +----------------------------------+
```

## Why this matters

Repeating an Euler factor changes the transport and is explicitly not harmless
in the finite-family source definition.  Requiring a Bone 1 estimate on
arbitrary repeated-prime lists was therefore a genuine strengthening, not a
notational convenience.  Proof 626 removes that unnecessary obligation from
the active search domain.

## Boundary

No route-valid factor is constructed.  The remaining producer must still give
one bound independent of every route-valid `p` and `S`.  Proof 626 does not
close Bone 1, Gate 3U, the finite-S sign, Burnol's identity, or RH.  It also
does not assert that the existing all-list downstream packages follow from
the weaker route-valid package; future consumers should specialize directly
to the deduplicated finite family.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorizationAudit.lean
```
