# 1295 — G8 P1 metric-history energy and basis summability

Date: 2026-09-11.

The leaf `ConnesWeilRH/Dev/C1G8P1BoundaryColumnEnergy.lean` now lifts the
boundary-column estimate to the completed metric coframe history.  For every
finite visible-prime list and source vector `x`, Lean proves

```text
‖finiteEulerMetricCoframeHistoryColumn λ S x‖² ≤ ‖x‖².
```

The proof uses the `WithLp` product norm identity, the Julia defect-energy
telescope, and the previously established metric boundary-column estimate.
It also proves summability and the corresponding basis-level `tsum` bound for
every Hilbert–Schmidt input with summable source-basis energy.  This is a
consumer-side estimate on the literal metric owner and supplies quantitative
control for a future cutoff trace argument.

It does not identify metric history outputs with whole-line radial crossings,
does not prove the finite visible-prime/prime-power trace comparison, and does
not provide the remainder limit or the P2 producer.  The typed same-owner
transport obligation recorded in proof 1292 therefore remains open.

Evidence: owning build `1357_g8_p1_history_generalized.log` (3464 jobs) and audit
build `1358_g8_p1_history_generalized_audit.log` (3465 jobs), both with zero
`error:`/`sorryAx`; the audit prints only
`[propext, Classical.choice, Quot.sound]`.

Status: **formal, consumer-side P1 energy extension; P2/P3 producer open**.
