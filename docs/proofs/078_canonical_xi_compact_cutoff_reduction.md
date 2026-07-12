# 078 Canonical Xi Compact-Cutoff Reduction

Date: 2026-07-12

Result: assuming the quotient inverse has uniform weighted derivative tails,
compact cutoff errors are summable over all source zeros without a nearby-
radius/later-threshold fixed point. Triple vanishing can be imposed exactly
after cutoff by a constant-coefficient differential operator.

## Tail Estimate

Let `q` be the centered inverse transform of the orbit quotient and let
`chi_A` be smooth, equal to one on `[-A,A]`, and compactly supported. Put

```text
e_A = (1-chi_A) q,
E_A(u) = integral exp(u*x) e_A(x) dx.
```

For `u=a+it`, `a in [-1/2,1/2]`, integration by parts `N` times gives

```text
|E_A(u)|
  <= |u|^(-N) integral exp(a*x) |e_A^(N)(x)| dx.
```

Uniform weighted derivative tails of `q` therefore imply

```text
|E_A(a+it)| <= C_(A,N) (1+|t|)^(-N),
C_(A,N) -> 0 as A -> infinity.
```

The finitely many bounded ordinates can be absorbed into the constant.

## Zero Sum

Before cutoff, the quotient transform vanishes at every source zero outside
the removed orbit. At such a zero `v`, both factors of the convolution square
are cutoff errors:

```text
H_A(v) = -E_A(v),
conjugate(H_A(-conjugate(v))) = cutoff error at the orbit companion.
```

Hence the square contribution is bounded by

```text
C_(A,N)^2 (1+|Im v|)^(-2N).
```

The existing source-zero shell-count/summability consumers handle this bound
for fixed sufficiently large `N`. The full non-target zero contribution tends
to zero as `A -> infinity`, while the finite target-orbit contribution tends
to the strict negative value from proof record 077. One sufficiently large
finite cutoff therefore preserves a strict negative total.

## Exact Triple Vanishing

Multiplying by a cutoff does not preserve transform zeros exactly. Do not add
three ad hoc correction witnesses. Instead define the final compact root by
applying the constant-coefficient operator whose centered multiplier is

```text
p_route(u)=u*(u^2-1/4).
```

This preserves compact support and gives exact zeros at `u=0,+1/2,-1/2`.
At nontrivial target-orbit points the multiplier is nonzero, so orbit values
can be normalized before applying the operator. Polynomial growth costs only
three powers in the tail estimate; choose `N` larger by three.

## Remaining Gates

```text
prove the weighted derivative tails for the iterated orbit quotient
instantiate the existing zero-count consumer with the centered cutoff bound
prove the final compact root lies in the common source/QW form domain
add the M4 bad-space rows without destroying the strict sign
```

This reduction removes the Plan 023 radius/count shape but does not yet supply
the lower sign consumer required by Plan 025 Gate X5.
