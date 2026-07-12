# Shared-Gram Mixed-Prime Death

Date: 2026-07-12

Status: the shared Brownian-Gram candidate of proof 133 is rejected by its
actual same-square crossing Gram matrix. The ideal `min(log p,log q)` model
passes, but the common convolution square inserts autocorrelation factors and
fails the positivity margin already for `{2,3,5}`. RH remains unproved.

## Actual crossing Gram

Let `J_b=Q U_b P` be the half-line crossing of length `b`, and let `C_h` be
convolution by a compactly supported smooth `h`. Direct kernel calculation
gives

```text
Tr((J_b C_h)^* (J_c C_h))
  = min(b,c) * F_h(c-b),                             (M.1)
```

where `F_h` is the autocorrelation of the same test. The Brownian matrix of
proof 133 is therefore replaced by the test-dependent matrix

```text
G_ij(h) = min(log p_i,log p_j) * F_h(log p_j-log p_i).
```

This is the required same-object matrix; dropping `F_h` changes the owner.

## Narrow-support witness

Choose a nonzero `C-infinity` test supported in an interval of width strictly
less than `log(3/2)`. The finite-codimension pole-vanishing conditions can be
imposed inside this infinite-dimensional compact-support space without making
it zero. Its autocorrelation then satisfies

```text
F_h(log p_j-log p_i)=0   for every distinct p_i,p_j in {2,3,5},
F_h(0)=||h||_2^2.
```

Thus the actual crossing Gram is diagonal:

```text
G_pp = log(p) ||h||_2^2.
```

For the first-channel weights `w_p=p^(-1/2)`, the minimal positive Schur cost
is exactly

```text
w^T G^(-1) w
  = (1/||h||_2^2) * sum_(p in S) 1/(p log p).          (M.2)
```

After normalizing `||h||_2=1`, the first three primes already give

```text
1/(2 log 2) + 1/(3 log 3) + 1/(5 log 5)
  = 1.149027... > 1.
```

Therefore the shared positive Schur defect cannot be absorbed by one copy of
the archimedean graph norm uniformly even on the finite set `{2,3,5}`.

## Consequence

The bounded ideal Brownian cost

```text
1/(2 log 2)+1/8 < 1
```

is not a valid same-object estimate: it assumes boundary vectors with Gram
`min(b,c)` but ignores the test-dependent autocorrelation in (M.1). The exact
same-square requirement forces the mixed-prime factors back in, and a narrow
test can eliminate all off-diagonal help.

## Verdict

```text
ideal shared Brownian Gram: passes cofinal cost
actual same-square Gram:    includes F_h(log p-log q)
narrow-support test:        diagonalizes the Gram
S={2,3,5}:                  cost 1.149... > 1
shared positive owner:      rejected
Lean owner:                 forbidden
```

The remaining possible mechanism must create cross-prime cancellation without
discarding the autocorrelation factors and without allowing narrow tests to
diagonalize the positive Gram.
