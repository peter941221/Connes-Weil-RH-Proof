# Proof 1250 — positivity of the source-side G8 cutoff trace

Status: FORMAL-SOURCE-POSITIVITY (Lean), 2026-09-10.

The source-precomposed G8 cutoff pair from record 1249 has a positive trace
product on the actual `sourceSoninCarrier` owner:

```text
T_source = J† T_ambient J ≥ 0.
```

The proof uses the established ambient finite-window positivity and
`ContinuousLinearMap.IsPositive.adjoint_conj`.  Its named source-basis
ordinary trace is therefore formally nonnegative by expanding the diagonal
series, applying the trace-class witness carried by the source pair, and
using positivity on every basis vector.

This is still only finite-window source positivity.  It supplies neither the
healthy `CompactLog` projection-limit contract nor a `qw` readback or the
finite-visible-prime sign inequality.

Audit evidence: `/home/peter/rh/build-logs/1250_g8_source_trace_positive_retry3.log`.
The owning module and audit build completed successfully (3922 jobs), with
standard axioms only and no `error:` or `sorryAx`.

RH is not claimed.
