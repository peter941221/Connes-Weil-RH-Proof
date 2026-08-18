# 1032 - One-sided Lane R penalty fails the translation test

Date: 2026-08-19.

Probe: `docs/proofs/1032_lane_r_prefix_penalty_sine_screen.py`.

## Verdict

The original rank-three candidate

```text
P_21(g) <= |L(g,0)|^2 + |L(g,1/2)|^2 + |L(g,1)|^2
```

is not a viable certificate on the un-gauged Lane R owner.  The failure is
structural, not a quadrature artifact: the finite Gamma_R prefix depends only
on the convolution square and is unchanged by translating the root, whereas
the bilateral Laplace law is

```text
L(translate(g,a), s) = exp(s*a) * L(g,s).
```

Consequently, the three positive-node penalty terms scale by different factors
`exp(2*s*a)`.  A certificate with fixed coefficients cannot be translation
invariant unless it has an additional gauge or uses paired nodes.

## Reproduction

```text
python docs/proofs/1032_lane_r_prefix_penalty_sine_screen.py \
  --length 21 --quadrature 600 \
  --radii 0.3464 --centers -1.0 0.0 \
  --basis-sizes 24 48
```

The same output is obtained at quadrature sizes `600`, `900`, `1200`, and
`1800` to the displayed digits.

## Representative boundary output

```text
+------+--------+----+-----------------+-----------------+------------+
| c    | radius | K  | constrained_max | certificate_max | lambda_star|
+------+--------+----+-----------------+-----------------+------------+
| -1.0 | 0.3464 | 24 |       -0.79162493|       +0.29219886|  1.3575025 |
| -1.0 | 0.3464 | 48 |       -0.78522943|       +0.29377972|  1.3612792 |
| +0.0 | 0.3464 | 24 |       -0.79162493|       -0.05340511|  0.7584294 |
| +0.0 | 0.3464 | 48 |       -0.78522943|       -0.04672313|  0.7701067 |
+------+--------+----+-----------------+-----------------+------------+
```

The constrained prefix itself remains negative in both rows.  Only the
stronger full-space certificate fails after translation.

## Lean consequence

The source law is already available at
`Source/CC20YoshidaCriticalContraction.lean`:

```lean
theorem laplaceAt_translate (f : CompactLogTest) (a : ℝ) (s : ℂ) :
  laplaceAt (translate f a) s =
    Complex.exp (s * (a : ℂ)) * laplaceAt f s
```

The corrected owner therefore keeps the one-sided penalty as a historical
candidate only.  It must not be promoted to a universal Lean proposition.
