# Shared Brownian-Gram Schur Candidate

Date: 2026-07-12

Status: idealized candidate only. Its Brownian cost passes, but the actual
same-object crossing Gram contains autocorrelation factors and is rejected by
proof 134. No Lean owner is authorized. RH remains unproved.

## Construction

Let `b_p=log(p)` and let `e_b` be the indicator of `[0,b]` in the common
half-line boundary channel. Then

```text
<e_b, e_c> = min(b,c).
```

For a finite ordered prime set `S={p_1,...,p_N}`, define

```text
C_ij = min(b_i,b_j),
w_i = p_i^(-1/2) = exp(-b_i/2).
```

The finite-prime Weil coefficient is `w_i * b_i` after the crossing trace
supplies the interval length `b_i`. The shared-channel Schur cost is the
Riesz norm

```text
kappa_S = w^T C^(-1) w.
```

This is different from independent prime channels, whose cost is the divergent
sum of diagonal weights.

## Exact cost formula

For `0<b_1<...<b_N`, the inverse of the Brownian covariance matrix gives

```text
kappa_S
  = w_1^2/b_1
    + sum_(i<N) (w_(i+1)-w_i)^2/(b_(i+1)-b_i).          (G.1)
```

With `w_i=f(b_i)` and `f(x)=exp(-x/2)`, Cauchy-Schwarz bounds each secant term:

```text
(f(b_(i+1))-f(b_i))^2/(b_(i+1)-b_i)
  <= integral_[b_i,b_(i+1)] |f'(x)|^2 dx.
```

Therefore every finite prime set satisfies the uniform bound

```text
kappa_S
  <= 1/(2 log 2) + integral_[log 2,infinity] exp(-x)/4 dx
  = 1/(2 log 2) + 1/8
  = 0.846347... < 1.                                   (G.2)
```

The numerical probe `133_shared_brownian_gram_probe.py` agrees:

```text
+-------+------------------+
| count | kappa_S          |
+-------+------------------+
|     1 | 0.7213475204     |
|     5 | 0.8232094939     |
|    20 | 0.8424006605     |
|    80 | 0.8450683257     |
|   120 | 0.845184...      |
+-------+------------------+
```

## Why this could help

For boundary data `z_i=F_h(b_i)`, the shared Riesz representation gives

```text
|sum_i w_i z_i|^2
  <= kappa_S * z^T C z.                                (G.3)
```

Unlike the independent-channel estimate, the coefficient `kappa_S` stays
below one along cofinal finite-prime sets. If the same convolution square
proves

```text
z^T C z <= archimedean_graph_norm(h),
```

then (G.3) is a genuine lower-producer inequality rather than a restatement of
Weil positivity.

## Remaining gates

1. Construct one positive same-object operator whose boundary channel is the
   Brownian span `{e_b}` and whose cross trace reads `F_h(b_i)`.
2. Prove the boundary Gram estimate `z^T C z <= graph_norm(h)` on the exact
   pole-vanishing test domain.
3. Transport the finite-prime linear functional, pole term, and archimedean
   term through the same owner without introducing mixed-prime values.
4. Formalize (G.1)--(G.3) in Lean and audit the resulting theorem for hidden
   RH or Weil-positivity premises.

The candidate is therefore accepted as a research direction, not as a route
owner. Its idealized quantitative advantage is real, but it does not survive
the same-object Gram gate; see `134_shared_gram_mixed_prime_death.md`.
