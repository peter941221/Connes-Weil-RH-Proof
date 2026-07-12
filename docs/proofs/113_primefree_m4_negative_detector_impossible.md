# 113 Prime-Free M4 Negative Detector Is Impossible

Date: 2026-07-12

## Source Identity

For a test whose convolution square sees no finite prime and whose pole
evaluations vanish, the corrected CC20 identity is

```text
PositiveTrace(g) = QW(g,g) + D_infinity(F_g).
```

The left side is `Tr(A* A)` and is nonnegative.  For a `Q`-root `xi` in the
M4 control-space complement, the archimedean remainder is

```text
D_infinity(Q(xi*xi*))
  = <xi,(-2 Id+K_I)xi>
  <= -||xi||^2.
```

Consequently

```text
QW(g,g)
  = PositiveTrace(g)-D_infinity(F_g)
  >= ||xi||^2.
```

It is strictly positive for a nonzero root.

## Rejection

Proof 083 proposed imposing finitely many M4 bad-space rows on a negative Xi
detector while retaining the negative zero sum.  The exact inequality above
shows that the desired endpoint of that orthogonalization does not exist in a
prime-free window.  Linear independence of the orbit rows and bad-space rows
only preserves finitely many Mellin values; it does not preserve the full
spectral quadratic sum over all other zeros.

Thus the missing step was not a conditioning estimate below the route.  It was
the contradiction itself.

## Verdict

```text
prime-free fixed-window M4 complement: QW-positive unconditionally
strict negative same-test detector there: impossible
Plan 025/083 prime-free rescue: rejected
Plan 028 prime-free branch: rejected
finite-S branch: still open
RH: unproved
```

Evidence:

```text
docs/proofs/016_corrected_trace_identity.md
docs/proofs/083_xi_quotient_compact_badspace_rescue.md
docs/proofs/099_fixed_detector_needs_inequality_not_read_off_equality.md
```

