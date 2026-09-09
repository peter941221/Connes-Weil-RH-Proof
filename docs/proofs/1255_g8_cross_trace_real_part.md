# Proof 1255 — the traced G8 cross pair is twice a real part

Status: FORMAL-CROSS-TRACE-REAL (Lean), 2026-09-10.

On the same source basis and finite cutoff, the two cross channels satisfy the
exact scalar identity

```text
Tr(T_cross + T_adjointCross)
  = 2 · Re(Tr(T_cross)).
```

The proof combines the independent trace-class witnesses from record 1254,
the operator-level adjoint relation from record 1253, and the ordinary-trace
adjoint/conjugation law.  It therefore controls only the algebraic form of the
cross contribution; it does not make that real number nonnegative.

No finite-visible-prime or healthy-limit `qw` readback is supplied here.  The
L4 projection-limit and A4 aggregate sign obligations remain open.

Audit evidence: `/home/peter/rh/build-logs/1255_g8_cross_trace_real_retry1.log`.
The owning module and audit build completed successfully (3922 jobs), with
standard axioms only and no `error:` or `sorryAx`.

RH is not claimed.
