# Proof 1254 — channel trace-class carriers and the traced G8 ledger

Status: FORMAL-TRACE-LEDGER (Lean), 2026-09-10.

The four finite-window G8 channel operators now have separate trace-class
carriers on the same healthy source owner.  A channel pair keeps the existing
source Hilbert--Schmidt cutoff leg and postcomposes it by the corresponding
bounded finite-S channel.  The four choices are

```text
W,       N W,       W N†,       N W N†,
```

where `W` is the positive detector and `N` is the pulled oblique shear.  The
Hilbert--Schmidt ideal gives `IsTraceClassAlong` for each resulting operator;
no trace-class fact is stored as data.

Using these four witnesses and the exact operator ledger from record 1251,
Lean proves the ordinary source trace is the sum of the four channel traces.
This is the first legally traced G8 four-channel decomposition, not merely an
operator identity.  The diagonal positivity and cross-adjoint results remain
available, but no sign is inferred for the cross pair.

The result still stops before the required detector-specific `qw` readback:
there is no theorem here identifying any channel trace with the finite visible
prime sum or with the healthy-limit `qw`.  L4 and A4 remain open analytic
obligations.

Audit evidence: `/home/peter/rh/build-logs/1256_g8_trace_ledger_retry2.log`.
The owning module and audit build completed successfully (3922 jobs), with
standard axioms only and no `error:` or `sorryAx`.

RH is not claimed.
