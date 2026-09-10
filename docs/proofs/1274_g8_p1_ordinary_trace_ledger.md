# G8 P1 — ordinary-trace P0 ledger

Date: 2026-09-10

Consumer: the healthy-`CompactLog`, selected-detector, same-owner B5/P2
readback `G8SameOwnerReadbackData`.

The P0 source-level operator identity now has an exact ordinary-trace form on
the same named source basis.  Define `complement_n` to be exactly the three
forced literal-cutoff channels from the source split.  Lean proves it trace
class and proves

```text
Tr(P_n) = Tr(T_n) + (Tr(C_n† K_forward C_n) - Tr(complement_n)).
```

Here `T_n` is the existing G8 cutoff trace product, `P_n` is the positive
physical endpoint trace product, and the correction remains the internal
kernel sandwich `C_n† K_forward C_n`.  The formula is an identity, not an
inequality or an asymptotic assertion.

This closes the P0-to-scalar bookkeeping step.  It gives neither a finite
visible-prime identification, a vanishing estimate for `complement_n`, nor a
limit/readback to `qw`.

Evidence: `ConnesWeilRH.Dev.C1G8P1TraceLedger` and paired Audit completed in
`build-logs/1274_g8_p1_trace_ledger_retry3.log` (3923 jobs; zero `error:` and
`sorryAx`; audit prints only `[propext, Classical.choice, Quot.sound]`).

Next: compare the literal cutoff metric/Euler trace with the finite visible
prime boundary expression, retaining owner, cutoff, scale, and family.
