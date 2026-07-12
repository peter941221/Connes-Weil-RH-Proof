# 123 Semilocal Negative-Projection Trace Screen

Date: 2026-07-12

## Result

The source-shaped one-sided negative-prolate trace remains a mathematical
candidate, but the current finite Jacobi sections do not provide convergence
evidence strong enough for a route owner.  No Lean declaration is authorized.

The probe is `123_semilocal_negative_projection_probe.py`.  It evaluates the
finite-section quantity

```text
Tr(exp(-tau D^2) P_- exp(-tau D^2)),
```

where `P_-` is the negative spectral projection of the finite semilocal
prolate matrix.  The same quantity is evaluated for the archimedean model.

## Screened Values

The following rows use `lambda=1` and `tau=0.10`:

```text
+------+------------------+------------------+------------------+
| size | infinity trace   | p=2 trace        | p=2 - infinity   |
+------+------------------+------------------+------------------+
| 128  | 2.8967e-06       | 1.1728e-04       | 1.1438e-04       |
| 192  | 2.4274e-06       | 1.2156e-04       | 1.1913e-04       |
| 256  | 8.6992e-07       | 1.0426e-04       | 1.0339e-04       |
| 384  | 7.5633e-06       | 1.5064e-04       | 1.4308e-04       |
| 512  | 2.0332e-06       | 1.2447e-04       | 1.2243e-04       |
+------+------------------+------------------+------------------+
```

Every negative eigenvector in these finite sections has tail mass near `1` in
the final quarter of the Jacobi basis.  Thus the sections do not isolate a
stable finite-support negative spectral subspace.  The observed difference is
therefore compatible with boundary pollution and is not evidence for a
semilocal Weil limit.

## Route Judgment

```text
negative spectral projection: source-backed candidate
finite-section convergence: not established
same-object Weil read-off: absent
common self-adjoint domain: absent
Lean owner: forbidden
RH: unproved
```

The only admissible reopening theorem remains:

```text
one self-adjoint semilocal negative projection on a common form domain
  -> exact same-test positive trace
  -> p^m coefficient p^(-m/2)/m before crossing length
  -> post-Q remainder -2 Id + compact
  -> restricted strict bound below 2.
```

Finite Jacobi sections, cross-energy plots, or a formal projection formula do
not prove any item in this contract.

