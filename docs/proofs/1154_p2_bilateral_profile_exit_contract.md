# Record 1154 — P2 bilateral-profile exit contract

Date: 2026-09-06

## Result

`C1P2BilateralProfileExit.lean` packages the direct profile consumer into a
same-owner data structure:

```text
P2BilateralProfileSignWitness g :=
  { archimedeanTerm(g□) ≤ 0,
    Re(g□(log n) + g□(-log n)) ≤ 0 for every visible n }.
```

The theorem `qw_nonneg_of_p2BilateralProfileSignWitness` combines this data
with the detector's existing triple vanishing and proves `qw(g) ≥ 0`.  The
theorem `sourceRH_of_healthyDetector_p2BilateralProfileSignWitness` then has
the exact B5 quantifier: for every right-oriented hypothetical off-line zero,
one healthy detector carrying this witness suffices for `SourceRH`.

The owning and audit modules build successfully in 3661 jobs.  The audited
declarations use only `[propext, Classical.choice, Quot.sound]`; there are no
`error:` lines and no `sorryAx`.

## Route meaning

This is a FORMAL exit contract, not a producer.  The pinned orbit detector is
not yet proved to have either the archimedean nonpositive sign or the visible
bilateral-profile nonpositive sign.  The route remains healthy `CompactLog`
B5-shaped; P2/C3 is OPEN and RH is not claimed.
