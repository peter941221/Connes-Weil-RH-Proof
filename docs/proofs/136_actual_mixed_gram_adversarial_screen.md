# Actual Mixed-Gram Adversarial Screen

Date: 2026-07-12

Status: the support-aware shared-Gram route fails a numerical adversarial test
with real compactly supported oscillatory factors. This is a screen, not yet a
formal no-go, because pole-vanishing constraints must be imposed explicitly.
No Lean owner is authorized. RH remains unproved.

## Test

For a compact real factor

```text
h_k(x) = bump_lambda(x) cos(kx),
```

construct the exact same-square crossing Gram

```text
G_ij(h_k)
  = min(log p_i,log p_j) F_(h_k)(log p_j-log p_i).
```

The first-channel weight vector remains `w_i=p_i^(-1/2)`. The probe computes
`w^T G(h_k)^(-1) w` for visible primes `log p<=lambda`.

## Results

```text
+--------+-----------+-----------+----------------+
| lambda | frequency | primes    | mixed cost     |
+--------+-----------+-----------+----------------+
|  1.4   |       0   | {2,3}     | 0.7409687582   |
|  1.4   |       5   | {2,3}     | 1.2528504366   |
|  1.4   |      10   | {2,3}     | 1.4525186182   |
|  2.0   |       0   | 4 primes  | 0.7768979417   |
|  2.0   |      10   | 4 primes  | 2.8436555528   |
|  3.0   |       0   | 8 primes  | 0.7520392750   |
|  3.0   |       5   | 8 primes  | 4.9072389208   |
+--------+-----------+-----------+----------------+
```

The cost increase is caused by oscillatory autocorrelation suppressing the
off-diagonal mixed-prime Gram entries. This is the opposite of the ideal
Brownian model: the shared discount disappears when the test decorrelates the
prime shifts.

## Analytic direction for a formal gate

For two distinct visible primes, let `d=log(3/2)`. The overlap autocorrelation
of `bump_lambda(x)cos(kx)` is a continuous oscillatory function of `k`; for
large `k` its leading term is proportional to `cos(kd)`. Hence frequencies near
`(pi/2+pi n)/d` can make the `{2,3}` mixed entry arbitrarily small while the
diagonal norms remain nonzero. A finite linear combination of such frequencies
can additionally satisfy the finite pole-node constraints.

That construction must still be written as a rigorous compact-support test
lemma before it can reject the route formally. The numerical evidence already
blocks using mixed autocorrelation as an unconditional uniform discount.

## Verdict

```text
ideal Brownian shared discount: invalid for the actual square
unmodulated bump: below one
real oscillatory factor: above one
support-aware mixed-Gram producer: not accepted
next gate: explicit pole-vanishing oscillatory witness or a domain theorem
```
