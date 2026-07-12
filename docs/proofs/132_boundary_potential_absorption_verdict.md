# Boundary-Potential Absorption Verdict

Date: 2026-07-12

Status: partial pass at one prime, rejected as a cofinal finite-prime owner.
This is the first candidate in the current batch that passes the single-prime
absorption gate. RH remains unproved.

## Candidate

For a crossing coefficient `a^m/m` and shift `b=log(p)`, the Schur diagonal
cost is a boundary interval potential

```text
V_p(x) = sum_(m >= ceil(x/b)) a^m/m,
a=p^(-1/2), x>=0.
```

Instead of demanding that this defect vanish, seek a same-object inequality

```text
integral V_S(x)|h(x)|^2 dx
  <= c_S * integral (|h'(x)|^2 + |h(x)|^2/4) dx.       (B.1)
```

on the pole-vanishing test space. If `c_S<1`, the archimedean graph norm
could absorb the positive Schur cost.

## Numerical single-prime gate

The finite-difference generalized eigenvalue probe
`132_boundary_potential_absorption_probe.py` estimates the sharp ratio in
(B.1) on `[0,20]` with Dirichlet data at zero:

```text
+------------------+----------------------+
| visible primes   | largest ratio        |
+------------------+----------------------+
| 2                | 0.4381356667         |
| 2,3              | 0.8887161164         |
| 2,3,5            | 1.3180959825         |
| 2,3,5,7,11       | 2.1106308771         |
+------------------+----------------------+
```

The one-prime value is below one and is stable under grid refinement (200,
400, 800 points gave approximately `0.426`, `0.438`, `0.444`). This is a
genuine partial pass: local Schur defect need not be fatal at `p=2`.

## Cofinal obstruction

Fix `delta<log(2)` and choose a nonzero smooth `h` supported in `(0,delta)`
with `h(0)=0`. For every prime with `log(p)>delta`, the `m=1` term contributes
throughout this support:

```text
V_S(x) >= sum_(p in S, log p>delta) p^(-1/2).
```

Therefore

```text
integral V_S |h|^2
  >= (sum_(p in S, log p>delta) p^(-1/2)) * ||h||_2^2.  (B.2)
```

The graph norm of this fixed `h` is independent of `S`, while the prime sum
diverges along cofinal finite-prime sets. Thus no constant `c_S<1`, or even a
uniform finite bound, can absorb the Schur defect on a common test domain.

Moving each prime to a disjoint spatial window does not remove the obstruction:
positivity charges each nonzero off-diagonal channel its own Schur square cost.
Disjoint windows remove cross terms, not the sum of the diagonal costs.

## Verdict

```text
single p=2 local absorption: passes numerically
finite S={2,3}: near the threshold
cofinal S: rejected by the fixed-test lower bound (B.2)
sparse boundary windows: no escape from additive PSD cost
Lean owner: not authorized
```

This candidate narrows the remaining possibility: a successful nontranslation
positive owner would need a cancellation mechanism that is not a sum of
independent Schur channels and does not change the archimedean form.
