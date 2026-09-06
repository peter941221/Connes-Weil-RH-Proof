# Record 1157 — P2 fixed-window scalar-budget no-go

Date: 2026-09-06

## Result

The theorem
`not_p2NarrowReferenceCanonicalWitness_of_healthyDetectorData` proves:

```text
HealthyYoshidaDetectorData rho g
  ∧ P2NarrowReferenceCanonicalWitness g
  -> False.
```

The proof derives `qw(g) < 0` from the healthy detector's local-Weil field,
converts the canonical same-owner budget into the required defect-gate bound,
and applies `no_stageB_budget_of_qw_negative` with the certified negative
`narrowArchRoot` window and its margin.  No numerical premise or stored sign is
used.

## Route meaning

This is a FORMAL no-go for the fixed-window triangle-budget producer, not for
P2 itself.  It confirms that an actual detector defect cannot be made small by
the current absolute-value budget while retaining a negative reference gate.
The viable P2 work must instead prove a signed bilateral-profile inequality or
a new same-owner semi-local trace comparison.  P2 and RH remain OPEN.

The owning and audit modules build successfully in 3674 jobs.  The audited
declaration uses only `[propext, Classical.choice, Quot.sound]`; there are no
`error:` lines and no `sorryAx`.
