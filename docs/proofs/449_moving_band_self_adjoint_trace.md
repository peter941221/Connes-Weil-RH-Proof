# Proof 449: Moving-band self-adjoint trace readback

The endpoint response is

```text
C (B_S - B_0) C†
```

where `C` is the selected convolution root and both `B_S` and `B_0` are
orthogonal support projections.  The new Lean bridge proves that the
projection difference is self-adjoint and that the root sandwich is therefore
self-adjoint on the actual finite-S common-log carrier.

For any Hilbert basis, `ordinaryTraceAlong_adjoint` identifies the trace of an
adjoint with the complex conjugate of the original diagonal trace.  Combining
this identity with self-adjointness proves that the endpoint trace has zero
imaginary part and equals the complex embedding of its real part.

This does not prove the missing same-carrier `IsTraceClassAlong` witness.  It
only strengthens the scalar conclusion once that witness is supplied, and it
keeps the endpoint operator on the same carrier used by Proof 448.

The canonical consumer now upgrades Proof 448 from

```text
abs Re ordinaryTraceAlong <= support-radius polynomial
```

to the full complex norm statement

```text
norm ordinaryTraceAlong <= support-radius polynomial.
```

It uses exactly the same two open premises: endpoint trace legality and the
uniform finite signed diagonal integral bound.

The acceptance batch passed:

```text
+-------------------------------------------+------+--------+
| target                                    | jobs | result |
+-------------------------------------------+------+--------+
| moving-band self-adjoint source           | 3282 | PASS   |
| CCM25Concrete aggregate                   | 3724 | PASS   |
| full repository                           | 3805 | PASS   |
+-------------------------------------------+------+--------+
```

The focused audit uses only:

```text
[propext, Classical.choice, Quot.sound]
```
