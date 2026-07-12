# Visible-Boundary Absorption Screen

Date: 2026-07-12

Status: support-aware refinement of proof 132 is numerically rejected as a
uniform graph-norm producer, but the rejection is not yet an analytic theorem.
No Lean owner is authorized. RH remains unproved.

## Refinement

The cofinal divergence in proof 132 counted prime channels outside the test
support. The corrected candidate keeps only visible prime powers

```text
m log(p) <= lambda,
```

for a support window of width `lambda`. Its boundary potential is

```text
V_lambda(x)
 = sum_(p,m: x <= m log(p) <= lambda)
     p^(-m/2)/m.
```

The proposed producer is the same inequality as (B.1), with the graph norm on
the exact compact-support test window.

## Numerical scan

`135_visible_boundary_absorption_probe.py` computes the largest generalized
eigenvalue of `V_lambda` against `|h'|^2+|h|^2/4` with Dirichlet data at zero:

```text
+--------+----------------+----------------------+
| lambda | visible primes | absorption constant  |
+--------+----------------+----------------------+
|  0.70  |              1 | 0.0346756374         |
|  1.40  |              2 | 0.2227513770         |
|  2.00  |              4 | 0.5810962178         |
|  3.00  |              8 | 1.7056518468         |
|  4.00  |             16 | 3.7340428216         |
|  5.00  |             34 | 7.0861640361         |
|  7.00  |            183 | 22.0303746096        |
+--------+----------------+----------------------+
```

The visible cutoff removes the artificial fixed-test divergence, but the
simple local graph norm still loses its margin once the window reaches about
three logarithmic units.

## Current interpretation

This is a screen, not a theorem: the true same-square mixed Gram may reduce
the defect below the diagonal-potential estimate. However, no route owner may
use the support-aware inequality until either

```text
an analytic uniform bound below one is proved, or
the mixed Gram is included and independently bounded.
```

The next mathematically meaningful test is therefore an adversarial broad
window with explicitly controlled autocorrelation, not a larger generic
finite-difference scan.
