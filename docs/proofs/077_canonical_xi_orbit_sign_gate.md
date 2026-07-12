# 077 Canonical Xi Orbit Sign Gate

Date: 2026-07-12

Result: Hermitian symmetry does not force a nonnegative contribution on a
hypothetical off-line zero orbit. The finite orbit admits an explicit negative
square-value pattern, and the triple-vanishing polynomial does not kill it.

## Centered Orbit

For `u=rho-1/2`, the functional-equation/conjugation orbit is

```text
{u,-u,conjugate(u),-conjugate(u)}.
```

An off-line source nontrivial zero has `u.re != 0`. Nontrivial-zero and pole
exclusion also remove `u=0,+1/2,-1/2`. In the nonreal off-line case the four
orbit points are distinct.

## Square Form

For centered transform values `H`, the convolution-square value at `v` is

```text
conjugate(H(-conjugate(v))) * H(v).
```

The pair `u,-conjugate(u)` contributes

```text
2 Re(conjugate(H(-conjugate(u))) * H(u)).
```

Assign

```text
H(u)=1,
H(-conjugate(u))=-1,
H(conjugate(u))=H(-u)=0.
```

The orbit sum is then `-2` (times the common positive multiplicity). Finite
polynomial interpolation realizes these four values after the orbit factors
have been removed from Xi.

## Triple Vanishing

The source points `s=0,1/2,1` become centered points
`u=-1/2,0,1/2`. Multiplication by

```text
u*(u^2-1/4)
```

adds all three zeros. It is nonzero at every nontrivial off-line orbit point,
so the negative value pattern can be pre-divided by this polynomial and is
preserved.

## Decision

```text
finite orbit Hermitian sign: negative direction exists
triple vanishing versus target value: compatible
Plan 025 Gate X4 finite algebra: passes
analytic quotient/cutoff and lower consumer: still open
```
