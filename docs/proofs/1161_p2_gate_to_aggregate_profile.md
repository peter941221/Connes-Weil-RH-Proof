# Record 1161 — P2 gate-to-aggregate profile adapter

Date: 2026-09-06

## Result

`P2BilateralProfileAggregateWitness.of_orbitWindowSemiLocalGate` now converts
the existing same-owner `orbitWindowSemiLocalGate g` into the aggregate
bilateral-profile witness for `g`.  The proof unfolds the gate and rewrites
`finitePrimeSum` using the exact weighted profile identity from record 1159.

The focused owner/audit build completed successfully in 3661 jobs.  The audit
prints only `[propext, Classical.choice, Quot.sound]` for the new declaration,
with no `error:` lines and no `sorryAx`.

## Route meaning

This removes an interface duplication between the Stage-B/local-configuration
route and the P2 aggregate socket.  It does not construct a Stage-B
contraction, prove the orbit-window gate for the selected detector, or close
the P2/RH obligation; those remain OPEN.
