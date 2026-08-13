# 990 - complete-QW width scan (SUPERSEDED boundary removed)

Date: 2026-08-12. Status: floating-point scan. RH NOT claimed.
Companion: `docs/proofs/990_m2_sign_boundary_scan.py`.

## Result first

The historical sign boundary `w ~= 2.8175` does not exist in the corrected
scan. It was produced by the wrong pole coordinate, wrong prime coordinates,
and a prime-2 truncation. With the complete `C1SameOwnerWeil` functional, no
sampled negative value occurs for widths `1.6 <= w <= 5.0`.

```text
+------------------------+------------------+
| scan item              | result           |
+------------------------+------------------+
| width range            | 1.6 to 5.0       |
| width step             | 0.2              |
| grid samples           | 20001            |
| negative samples       | 0                |
| minimum sampled QW     | +0.00000766      |
| minimum width          | 4.8              |
+------------------------+------------------+
```

The near-minimum point was checked separately across resolutions:

```text
+--------+-------------------+
| N      | QW at width 4.8   |
+--------+-------------------+
| 10001  | +6.457236897e-6   |
| 20001  | +7.663332403e-6   |
| 40001  | +7.821468453e-6   |
| 80001  | +7.868798247e-6   |
| 160001 | +7.873102381e-6   |
+--------+-------------------+
```

This is convergent numerical evidence, not a certified lower bound.

## Width sweep

```text
1.6:+0.02063  1.8:+0.05373  2.0:+0.01889  2.2:+0.00078
2.4:+0.00644  2.6:+0.00090  2.8:+0.00202  3.0:+0.00311
3.2:+0.00032  3.4:+0.00048  3.6:+0.00048  3.8:+0.00002
4.0:+0.00023  4.2:+0.00007  4.4:+0.00004  4.6:+0.00009
4.8:+0.00001  5.0:+0.00002
```

At fixed support width, translated windows agree to the printed precision in
this sampled family. This observation is not promoted to a Lean translation
invariance theorem.

## Scope

The script evaluates an L2-normalized polynomial-times-bump residual whose
moments at `0`, `1/2`, and `1` vanish numerically. `M2HealthyPsiPort.lean` and
`M2WidthPlateau.lean` contain plain plateau tests, not these residuals. A shared
width does not make them the same mathematical owner.

The corrected conclusion is only:

```text
No sampled counterexample was found in this finite parametric family.
```

It is not `forall g, QW(g) >= 0`, and it is not RH. The old negative family,
monotonicity claim, and bisection root are retracted.
