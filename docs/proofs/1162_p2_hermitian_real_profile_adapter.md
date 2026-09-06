# Record 1162 — P2 Hermitian real-profile adapter

Date: 2026-09-06

## Result

The P2 profile module now records the exact Hermitian identity

```text
bilateralProfile(g², y) = 2 · Re(g²(y)).
```

Consequently the finite-prime sum is also read back as

```text
Σ Λ(n)/√n · 2 · Re(g²(log n)).
```

`P2BilateralProfileAggregateWitness.of_twoRealWeightedSum` converts this
real-valued estimate into the existing aggregate witness socket.

The focused owner/audit build completed successfully in 3661 jobs.  Audited
declarations use only `[propext, Classical.choice, Quot.sound]`; there are no
`error:` lines and no `sorryAx`.

## Route meaning

This makes the producer interface match the real-valued semi-local trace
observable.  It does not prove the estimate for the pinned orbit detector;
the detector-specific P2 inequality and hence RH remain OPEN.
