# Proof 1248 — positivity of the G8 metric-history Gram

Status: FORMAL-ALGEBRA (Lean), 2026-09-10.

The history factorization from record 1247 is positive on the source carrier:

```text
C† R† W_g R C ≥ 0,
```

where `C` is the finite-visible-prime history column followed by the fixed
Gram inverse square root and `R` is the history readout.  Lean obtains this
by rewriting back to the already identified metric-coframe Gram and applying
the detector positivity through `adjoint_conj`.

This closes the source-side positivity certificate for the finite-visible
history owner.  It is not yet a trace-class statement, a `qw` limit, or the
required finite-prime sign inequality on the healthy `CompactLog` carrier.

Audit evidence: `/home/peter/rh/build-logs/1248_g8_metric_history_positive_retry1.log`.
The owning module and audit build completed successfully (3922 jobs), with
standard axioms only and no `error:` or `sorryAx`.

RH is not claimed.
