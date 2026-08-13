# 988 - one finite-vanishing numeric test (SUPERSEDED result corrected)

Date: 2026-08-12. Status: floating-point diagnostic. RH NOT claimed.
Companion: `docs/proofs/988_vanishing_probe.py`.

The earlier `A ~= 0`, `Psi ~= 0.0036`, and "one-sided support makes the square
degenerate" verdict is false. A star-convolution square is an autocorrelation,
so its zero lag is `||g||_2^2` regardless of whether the support is one-sided.

## Construction

On `[0.4,2.2]`, the sampled test is

```text
g(t) = bump(t) * (c0 + c1*t + c2*t^2 + c3*t^3).
```

A numerical null vector of the three-by-four moment matrix makes the sampled
Mellin/Laplace moments at `0`, `1/2`, and `1` nearly zero, and the test is L2
normalized. This is a numerical object; its coefficients and vanishings have
not been certified as an exact Lean `CompactLogTest`.

## Result

```text
+------------------------+----------------+
| quantity               | value          |
+------------------------+----------------+
| M(0)                   | +5.457e-14     |
| M(1/2)                 | +1.901e-13     |
| M(1)                   | +3.874e-13     |
| A = ||g||_2^2          | +1.00000000    |
| arch                   | -0.10610525    |
| pole                   | approximately 0|
| all visible primes     | +0.05237029    |
| QW = Psi(g^* * g)      | +0.05373496    |
+------------------------+----------------+
```

The invariant errors are `abs(A-L2)=1.104e-13`, pole-product error
`6.306e-17`, and maximum vanishing residual `3.874e-13`.

The complete source sign convention is:

```text
source QW(g) = Psi(g^* * g)
CC20 local sum on g^* * g = -QW(g)
```

Thus this sampled positive value is in the criterion-compatible direction. It
does not prove the universal inequality, and the approximate test is not a
formal Lean witness. RH NOT claimed.
