# 2126 — Route-A n=6 high-order sampling remainder screen

Date: 2026-09-28.

Status: HIGH-ORDER-REMAINDER-CANDIDATE. The derivative readings are finite-
difference diagnostics, not a certified interval bound.

The second- and fourth-order absolute Euler-Maclaurin screens were too loose
for the `D` channel. A pilot using the eighth-order remainder scale

```text
delta_sampling(f) ~= h^8 / 40320 * integral |f^(8)(xi)| dxi
```

at `h = 0.02`, multiplied by the full absolute prime-weight sum, reads:

```text
channel       estimated sampling error
C              5.15e4
b              2.99e8
D              1.80e12
```

These readings are comparable to, but do not replace, the Route-A spline-only
budget from record 2125:

```text
channel       spline budget       sampling pilot
C              2.79e4              5.15e4
b              1.53e8              2.99e8
D              8.92e11             1.80e12
```

Using the sum of the two budgets and the same determinant perturbation formula
still leaves a numerical determinant margin below `|det| = 5.1064e19`. This
identifies the remaining technical task precisely:

```text
replace finite-difference f^(8) readings with an interval/analytic
derivative chain for W, P*W, and P^2*W
    -> add the spline and sampling budgets
    -> certify C > 0, b > 0, det < 0
```

The screen does not charge forward rounding, endpoint/window tails, or the
formal-owner gap. It is therefore a route-selection result, not a Go theorem.
