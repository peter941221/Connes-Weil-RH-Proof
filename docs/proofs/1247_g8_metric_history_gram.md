# Proof 1247 — G8 metric-history Gram bridge

Status: FORMAL-ALGEBRA (Lean), 2026-09-10.

The metric-coframe identity from record 1246 now factors through the existing
finite-visible-prime history owner.  Let

```text
C = finiteEulerMetricCoframeHistoryColumn ·
    parameterizedSoninGramInvSqrt,
R = finiteEulerMetricCoframeHistoryReadout.
```

The existing exact readback `R C = finiteEulerMetricCoframe` therefore gives

```text
J† G8 J = C† R† W_g R C.
```

This is the same-owner finite-visible channel form: the detector is now
between the history readout and its adjoint, while the source-side factor is
the history column with the fixed Gram square-root normalization.  It is an
exact operator identity, not yet the `qw` limit or the finite-prime sign
inequality.  The remaining work is to connect this history Gram to the
healthy `CompactLog` readback without silently replacing the owner by a ROOT
window.

Audit evidence: `/home/peter/rh/build-logs/1247_g8_metric_history_retry6.log`.
The owning module and audit build completed successfully (3922 jobs), with
standard axioms only and no `error:` or `sorryAx`.

RH is not claimed.
