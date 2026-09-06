# Record 1159 — P2 aggregate bilateral-profile socket

Date: 2026-09-06

## Result

`C1P2BilateralProfile.lean` proves the exact finite-prime readback

```text
finitePrimeSum(F)
  = Σ Λ(n)/√n · Re(bilateralProfile(F, log n)).
```

It then proves that

```text
archimedeanTerm(g²) + weightedProfileSum(g²) ≤ 0
```

implies `qw(g) ≥ 0` for a triple-vanishing healthy owner.  The exit module
packages this as `P2BilateralProfileAggregateWitness` and wires its exact
right-oriented-zero quantifier directly to `SourceRH`.

This weakens the earlier pointwise profile-sign contract: the producer may
control the finite visible prime powers only in aggregate.  No positivity is
stored in the witness.

The owning and audit modules build successfully in 3660/3661 jobs.  Audited
declarations use only `[propext, Classical.choice, Quot.sound]`; there are no
`error:` lines and no `sorryAx`.

## Route meaning

This is FORMAL target reduction, not a detector sign proof.  The aggregate
inequality for the formal orbit detector is still the live P2 obligation; P2
and RH remain OPEN.
