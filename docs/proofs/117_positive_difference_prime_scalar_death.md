# 117 Positive Difference Prime Scalar Death

Date: 2026-07-12

## Identity

For a translation `U_b` and convolution root `h`,

```text
||(I-U_b)h||^2
  =2||h||^2-2 Re<h,U_b h>
  =2||h||^2-F_h(b)-F_h(-b).
```

With `b=m log(p)` and `a=p^(-1/2)`, multiplication by `a^m log(p)` gives

```text
a^m log(p)||(I-U_b)h||^2
  =-a^m log(p)[F_h(b)+F_h(-b)]
   +2a^m log(p)||h||^2.
```

The first term is exactly the negative finite-prime Weil atom.  The second is
a scalar identity contribution.  Summing over all powers of one prime gives

```text
C_p||h||^2,
C_p=2 log(p) a/(1-a).
```

At `p=2`,

```text
C_2=2 log(2)/(sqrt(2)-1) approximately 3.346 > 2.
```

Thus even the smallest finite-S extension changes the essential scalar from
`-2` to a positive value.  This cannot be a compact perturbation and cannot be
removed by finitely many orthogonality rows.

## Scope

The calculation rejects the termwise positive-difference realization of the
prime atoms.  It does not reject a boundary identity that cancels the scalar
before forming the positive object.

```text
Plan 039 positive differences: rejected
empirical stage: unnecessary
Lean owner: forbidden
RH: unproved
```

