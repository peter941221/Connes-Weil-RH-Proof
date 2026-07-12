# 099 Fixed Detector Needs an Inequality, Not the Old Read-Off Equality

Date: 2026-07-12

## Rejection

Plan 028 must not try to prove the existing
`NormalizedRouteBackedYoshidaLocalSumReadOff` as a universal exact equality.
The source-backed CC20 formula contains the nonzero remainder

```text
D_infinity(Q(xi * xi*)) = <xi, (-2 Id + K_I) xi>.
```

The compact `K_I` term is not killed by the three route vanishings. This is the
same obstruction recorded in the Plan 012 verdict and the M3A audits.

## Correct consumer shape

For one fixed detector, choose the M4 control space at threshold `1` and impose
orthogonality to it. Then

```text
<xi, (K_I - Id) xi> <= 0
```

and hence

```text
<xi, (-2 Id + K_I) xi> <= -norm(xi)^2.
```

The needed route theorem is therefore a one-test inequality transporting this
strict sign to the full QW value, with finite-prime and pole terms on the same
square. It is not an equality obtained by deleting the remainder.

## Remaining obstruction

CC20's displayed M4 identity is archimedean. The full QW also contains pole and
finite-prime terms. Plan 028 must prove a fixed-test semilocal inequality that
assigns those terms correctly; archimedean compactness alone does not control
the full QW sign.

## Verdict

```text
old exact LocalSumReadOff target: rejected
M4 strict inequality on bad-space complement: survives
transport to full QW including primes: open and decisive
```

