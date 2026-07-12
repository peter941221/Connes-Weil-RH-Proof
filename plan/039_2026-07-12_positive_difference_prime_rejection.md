# 039 Positive Difference Prime Rejection

Date: 2026-07-12

Status: rejected at `S={infinity,2}` by an exact scalar compensation.

## Candidate

The positive log factor has the exact termwise decomposition

```text
N_p = sum_(m>=1) p^(-m/2)/m
  (I-U_p^m)^*(I-U_p^m).
```

This makes every prime-power channel positive before the half-line crossing.

## Exact Death

Let `b=m log(p)` and `F_h=h^**h`. Then

```text
||(I-U_b)h||^2
  = 2||h||^2-F_h(b)-F_h(-b).
```

After the crossing length cancels the factor `1/m`, the weighted positive
energy is

```text
p^(-m/2) log(p) ||(I-U_b)h||^2
  = -W_(p,m)(F_h)
    +2 p^(-m/2) log(p)||h||^2.
```

Summing over `m` produces the noncompact scalar compensation

```text
C_p=2 log(p) p^(-1/2)/(1-p^(-1/2)).
```

For `p=2`, `C_2` is about `3.346`, already larger than the fixed archimedean
essential coefficient `2`.  Hence the post-Q remainder has positive essential
scalar `C_2-2`; it is not `-2 Id+compact` and no finite bad-space conditioning
can remove it.

## Verdict

```text
termwise positive difference factorization: exact
prime-power coefficient: exact
scalar compensation: noncompact and unavoidable
one-prime p=2 gate: fails
Plan 039: rejected before numerics or Lean
```

See proof 117.

