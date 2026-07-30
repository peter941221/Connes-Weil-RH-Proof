# Proof 624: physical Bone 1 factor contract

## Result

Proof 624 replaces the bookkeeping response contract by a contract on the
actual reverse-intertwining owner.

The named physical cofactor is

```text
P_(p,S) = oldFrame * Transition * K_(p,S)^dagger * Transition.
```

The local response cofactor is

```text
J_(p,S) = oldFrame * localRawDefect * Transition.
```

Proof 623 gives the exact identity

```text
P_(p,S) = -J_(p,S).
```

The new producer data requires one factor satisfying

```text
P_(p,S)
  = rho_p * oldCarrierAnalysis_(p,S)^dagger * factor_(p,S),

norm(factor_(p,S)) <= bound.
```

Lean proves, pointwise and uniformly over all visible primes and suffixes,

```text
physical factor data
  <=> old response factor data
  <=> synchronized-gap readout data.
```

The numerical bound is unchanged in both directions.

## Build boundary

Expanding the physical cofactor inside the producer structure caused Lean to
retain 7--11 GB during deterministic definitional equality.  The successful
implementation puts the expanded owner identity in a separate `.olean`
module and lets the producer module consume only that theorem.  This changes
no public mathematical condition.

## Remaining theorem

Construct a single family-uniform `factor_(p,S)` for the physical owner above.
The contract itself is not the producer, so Bone 1 remains open.
