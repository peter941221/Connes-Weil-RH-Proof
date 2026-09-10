# G8 P1 aggregate boundary trace ledger (2026-09-11)

The import-facing leaf `C1G8P1BoundaryTraceLedger` lifts the exact
survivor--aggregate-boundary operator identity to the ordinary trace on the
same source basis.  For every finite cutoff it proves

```text
Tr(SB_n)
  = upperFactor(S) * Σ_{boundary map in the ordered visible list} Tr(channel_n(boundary map)).
```

The proof supplies trace-class witnesses for every list summand and uses only
finite trace linearity.  It does not identify a boundary map with a radial
prime-power crossing, assert a sign, or take a cutoff limit.

Acceptance: `/home/peter/rh/build-logs/1321_g8_p1_boundary_trace_ledger.log`,
3927 jobs, zero `error:`/`sorryAx`, standard audit axioms only.
