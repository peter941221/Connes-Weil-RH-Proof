# 1025 - Lane R prefix/tail absolute-budget screen

Date: 2026-08-18.

Probe: `docs/proofs/1025_lane_r_prefix_tail_budget_scan.py`.

## Verdict

The first all-negative prefix (`N=4`) is too short for the absolute profile
tail to serve as a matching budget in the tested nullspaces.  Extending the
prefix to `N=21` leaves a usable numerical margin in the same finite screens.
This selects `N=21` as the next constrained-prefix proof target; it does not
prove that target.

## Method

The probe reuses the exact sine-basis and three-moment nullspace owner from
1022.  For each normalized coefficient vector `c`, it computes

```text
P_N(c) = c^T (constant + prefix_N) c
A_N(c) = sum_(N <= n < 801) |c^T profile_n c|
ratio   = A_N(c) / (-P_N(c)).
```

The first candidate vector is the least-negative eigenvector of the finite
prefix.  The remaining vectors are deterministic random unit vectors.  The
tail is finite and therefore cannot certify the infinite theorem; ratios over
one are nevertheless a direct rejection of that finite absolute budget for
the sampled vector.

## Recorded run

WSL2 command:

```text
python docs/proofs/1025_lane_r_prefix_tail_budget_scan.py \
  --radii 0.20 0.30 0.34 --basis-sizes 16 24 \
  --quadrature-size 1200 --prefix-lengths 4 21 \
  --tail-end 801 --samples 3000 --seed 20260818
```

Representative basis-size-16 output:

```text
+--------+----+----+-------------+-------------------+------------------+------------------+
| radius | K  | N  | prefix_max | least-margin ratio| sample min ratio | sample max ratio |
+--------+----+----+-------------+-------------------+------------------+------------------+
|  0.200 | 16 |  4 |   -0.195055 |            6.349 |            7.085 |           10.752 |
|  0.200 | 16 | 21 |   -1.235558 |            0.146 |            0.220 |            0.561 |
|  0.300 | 16 |  4 |   -0.141532 |            6.238 |            6.427 |            9.199 |
|  0.300 | 16 | 21 |   -0.920517 |            0.094 |            0.132 |            0.396 |
|  0.340 | 16 |  4 |   -0.116645 |            6.697 |            6.148 |            8.808 |
|  0.340 | 16 | 21 |   -0.813739 |            0.083 |            0.134 |            0.352 |
+--------+----+----+-------------+-------------------+------------------+------------------+
```

The finite tail in this table is only `N <= n < 801`.  The 1023 theorem gives
an infinite magnitude rate, but its existential profile constant is not yet
related to the square mass strongly enough to replace this screen.

## Route decision

Do not spend the next proof round on an `N=4` absolute-tail coupling.  The
next producer should target the finite constrained-kernel inequality at
`N=21`, together with a mass-relative infinite tail bound.  The existing 1024
consumer is the correct final assembly once those two producers share one
owner.  This screen is numerical evidence only; prime-inclusive Lane R,
universal spectral nonnegativity, and RH remain open.
