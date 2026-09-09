# Proof 1253 — G8 cross channels are adjoints

Status: FORMAL-CROSS-ADJOINT (Lean), 2026-09-10.

For every selected owner, Sonin scale, finite prime-power family, and cutoff,
the source finite-window operators satisfy

```text
T_adjointCross = T_cross†.
```

The identity is obtained by expanding the continuous-linear-map adjoint of
the cross composition, using self-adjointness of the detector, and normalizing
composition associativity.  Consequently the cross contribution plus its
adjoint is self-adjoint (and its trace, once separately justified, can be
treated as twice a real part).

This is only a structural relation.  It gives no sign for either cross term
or their sum, and it does not identify a finite-window trace with `qw`; the
healthy `CompactLog` readback, L4 limit contract, and A4 finite-visible-prime
inequality remain open.

Audit evidence: `/home/peter/rh/build-logs/1253_g8_cross_adjoint_retry1.log`.
The owning module and audit build completed successfully (3922 jobs), with
standard axioms only and no `error:` or `sorryAx`.

RH is not claimed.
