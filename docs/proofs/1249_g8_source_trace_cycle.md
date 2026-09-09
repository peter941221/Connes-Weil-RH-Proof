# Proof 1249 — source/ambient trace transport for the G8 cutoff

Status: FORMAL-TRACE-TRANSPORT (Lean), 2026-09-10.

For the existing finite-window G8 Hilbert--Schmidt pair, precomposing both
Hilbert--Schmidt legs with the healthy source inclusion `J` is legal: the
source-basis square-summability obligations follow from the established
`summable_normSq_precomp` transport.  Lean then proves the exact source trace
product identity

```text
T_source = J† T_ambient J.
```

The bounded-sandwich construction with `J J†` supplies the matching ambient
pair, and its cyclic trace identity transports the source trace to

```text
Tr_source(J† T_ambient J)
  = Tr_ambient(T_ambient J J†).
```

This is a same-owner trace-class/trace-cycle transport theorem.  It does not
identify the trace with `qw`, does not prove the finite-visible-prime sign,
and does not assert the projection-limit contracts.  In particular, no
external subtraction or owner change is hidden in the result.

Audit evidence: `/home/peter/rh/build-logs/1249_g8_source_trace_cycle_retry10.log`.
The owning module and audit build completed successfully (3922 jobs), with
standard axioms only and no `error:` or `sorryAx`.

RH is not claimed.
