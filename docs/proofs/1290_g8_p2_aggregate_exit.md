# G8 to P2 aggregate exit (2026-09-11)

The import-facing leaf `C1G8P2AggregateExit` proves the exact same-owner
consumer from a supplied `G8SameOwnerReadbackData` and healthy detector data:

```text
0 ≤ qw(g)
  ⇒ archimedeanTerm(g□)
     + Σ Λ(n)/√n · Re(bilateralProfile(g□, log n)) ≤ 0.
```

The proof is the existing triple-vanishing Weil identity plus the exact P2
aggregate iff; it supplies no readback witness and therefore no new analytic
sign or RH conclusion.

Acceptance: `/home/peter/rh/build-logs/1325_g8_p2_aggregate_exit.log`,
3958 jobs, zero `error:`/`sorryAx`, standard audit axioms only.
