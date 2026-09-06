# Record 1160 — P2 aggregate profile exactness

Date: 2026-09-06

## Result

The bilateral-profile module now proves that, for any triple-vanishing
`CompactLogTest`, the desired sign `qw(g) ≥ 0` is equivalent to the single
same-owner inequality

```text
archimedeanTerm(g²)
  + Σ Λ(n)/√n · Re(bilateralProfile(g², log n)) ≤ 0.
```

The prior pointwise profile-sign witness is formally converted into this
aggregate witness.  The aggregate B5 witness and its `SourceRH` exit remain
unchanged and axiom-clean.

The owning and audit modules build successfully in 3662 jobs.  Audited
declarations use only `[propext, Classical.choice, Quot.sound]`; there are no
`error:` lines and no `sorryAx`.

## Route meaning

This is a FORMAL exactness/weakening result, not a detector sign proof.  The
aggregate inequality for the formal orbit detector remains the live P2
obligation; P2 and RH remain OPEN.
