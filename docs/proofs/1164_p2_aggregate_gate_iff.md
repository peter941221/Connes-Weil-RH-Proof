# Record 1164 — P2 aggregate/gate exact equivalence

Date: 2026-09-06

## Result

`p2AggregateWitness_iff_orbitWindowSemiLocalGate` proves that the aggregate
bilateral-profile witness and the existing orbit-window gate are logically
equivalent.  The forward direction rewrites the finite-prime sum through the
exact profile readback; the reverse direction uses the gate adapter.

The focused owner/audit build completed successfully in 3721 jobs.  The audit
uses only `[propext, Classical.choice, Quot.sound]`, with no `error:` lines and
no `sorryAx`.

## Route meaning

All current P2 producer routes now target one proposition on one owner.  This
does not prove that proposition for the pinned orbit detector; P2 and RH remain
OPEN.
