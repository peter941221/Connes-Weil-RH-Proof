# 支路 3 decision: the arch sign normalization is NOT universal - band test is oscillatory

Date: 2026-08-07. Status: **decision recorded; arch-sign slot must be a specific test-family,
not a universal inequality.**

## 1. The lane

The Hilbert-carrier arch sign (route-1) reduces (axiom-clean Lean, `MellinSignAssembly` +
`MellinBandGamma`) to the single real slot

```
  arch-sign   Re[(M g (i/2))^4] >= 0,    band test f_a(t) = t^a e^(-t),  a > 0,
  and         M(f_a)(i/2) = Gamma(a + i/2)         (mellin_band_eq_Gamma)
```

so the convention is exactly `Re[(Gamma(a + i/2))^4] >= 0`.

## 2. Decisive numeric evidence (exact Gamma, 45-digit mpmath; no grid / operator proxy)

A global "for all a" statement is FALSE.  Using the exact complex Gamma function:

```
  a      Re[Gamma(a+i/2)^4]
  0.20   +2.270    positive
  0.30   -1.104    negative
  0.40   -1.985    negative (min zone)
  0.70   -0.363    negative
  0.80   -0.034    negative
  ~0.815  ~0.000   <-- first sign crossing
  0.90   +0.156    positive
  1.00   +0.261
  1.50   +0.388
  2.00   +0.465
  2.60   +0.169
  2.70   -0.178   <-- second sign crossing
  3.00   -3.728    negative, then explodes negative (a=4 -> -9.1e2, a=5 -> -2.9e5)
```

So the sign is negative on `(0.30, 0.815)` and on `(2.7, oo)`, positive on `(0.815, 2.7)`
plus a small patch near `0.2`. It is not monotone.

## 4. Why it oscillates (Stirling phase)

For real `a >> 1`, `ln Gamma(a+it) = (a+it-1/2) ln(a+it) - (a+it) + O(1)`, and
`ln(a+it) = ln a + i t / a + ...` gives `arg Gamma(a+it) ~ t (ln a - 1)`.  At `t = 1/2`,
`4 arg ~ 2 (ln a - 1) (mod 2 pi)`, so the sign of `Re[Gamma^4] = |Gamma|^4 cos(4 arg)` is
oscillatory in `ln a`: `cos(2 (ln a - 1))`. That is why no universal `Re[Gamma^4] >= 0` holds.

## 5. The decision (拍板)

- The arch-sign convention on the Hilbert band carrier **cannot** be stated as
  `forall a > 0, Re[(M f_a (i/2))^4] >= 0`; that proposition is false.
- A legitimate convention must pin a **specific sign-family** and prove a concrete lower
  bound on a chosen `a`-band (e.g. inside `(0.815, 2.6)`), which is a real analytic
  obligation (AGENTS §6: do not fabricate a `True`).
- Numerically a positive band exists for future work, but closing it in Lean needs a
  controlled Stirling/arg bound (the same open Gamma-phase gate as Task 1 / mathlib
  Stirling gap).

Status: OPEN (analytic). The arch-sign slot must be a specifically chosen and proven sign
test, not a universal slope. This is consistent with doc 859 and the existing guards.
