# 035 Prime-Free M4 Detector Rejection

Date: 2026-07-12

Status: rejected by the corrected CC20 trace identity.

## Candidate

Keep the Xi detector in a support window smaller than `log 2`, impose the M4
bad-space orthogonality rows, and retain a strict negative same-test Weil value.

## Exact Death

In the prime-free window and with the pole nodes zero, the corrected source
identity is

```text
PositiveTrace = QW + D_infinity.
```

On the M4 bad-space complement at threshold `1`,

```text
D_infinity <= -||xi||^2.
```

Since `PositiveTrace >= 0`, every nonzero test in that complement satisfies

```text
QW = PositiveTrace - D_infinity >= ||xi||^2 > 0.
```

Therefore no strict negative detector exists in the required prime-free M4
complement.  Finite functional independence of orbit and bad-space rows cannot
preserve the negative zero sum; it only preserves selected point values.

## Verdict

```text
prime-free M4 sign: source-backed and positive
negative detector in the same complement: impossible
finite-row orthogonalization rescue: rejected
Plan 028 prime-free branch: dead
remaining Plan 028 branch: genuinely semilocal finite-S remainder theorem
```

See proof 113.

