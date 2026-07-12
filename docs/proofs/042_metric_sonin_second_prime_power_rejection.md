# Metric Sonin Second Prime-Power Rejection

Date: 2026-07-12

Status: the endpoint metric Sonin projection is rejected as a fixed-`S` Weil
trace owner. Its first Euler coefficient agrees with the `p` atom, but its
single-crossing `p^2` coefficient is twice the Weil coefficient. The excess is
an infinite-rank partial translation and cannot enter a compact remainder. RH
remains unproved.

## 1. Result First

```text
metric projection first p-channel: matches
metric projection second p^2-channel: factor 2 too large
excess channel: one cutoff crossing, infinite rank before smoothing
compact fixed-S remainder: impossible for this endpoint projection
Plan 024 metric projection: rejected mathematically, not only ill-typed
```

The earlier common-domain rejection showed that the proposed de Branges
Rayleigh problem was not defined. The calculation below goes further: even on
the correct Hilbert space, the endpoint metric projection has the wrong Euler
generating series.

## 2. Exact Same-Object Trace Identity

Let `T_S` be CCM24's bounded Sonin isomorphism, put

```text
H_S=T_S* T_S,
A_S=R H_S R | Ran(R),
R_S=T_S R A_S^(-1) R T_S*,
```

and let `C_f` be the archimedean scaling convolution. The intertwining relation
is

```text
C_S(f) T_S = T_S C_f.
```

Whenever the CC20 smoothed products are trace class, bounded/trace-class
cyclicity gives

```text
L_S(f)
 := Tr(C_S(f) R_S)
  = Tr(C_f R A_S^(-1) R H_S)
  = Tr(C_f H_S R A_S^(-1) R).
```

Write `Q=I-R`. Since

```text
H_S R = R H_S R + Q H_S R = A_S + Q H_S R,
```

one obtains the exact decomposition

```text
L_S(f)
 = Tr(C_f R)
   + Tr(R C_f Q H_S R A_S^(-1)).                       (A.1)
```

This is the correct common-domain replacement for the former de Branges
quadratic form. The first term is the archimedean Sonin trace. All finite-place
information is in the second term, with one explicit Sonin boundary crossing.

Source inputs:

```text
CCM24 theta_S isomorphism and multiplier:
  arXiv:2310.18423v2, mainc2m24fine.tex:946-1029

CC20 Sonin trace and smoothing legality:
  arXiv:2006.13771, weil-compo.tex:1178-1199, 2105-2120
```

## 3. One-Prime Expansion

For `S={infinity,p}`, set

```text
a=p^(-1/2),
U=translation by log(p),
V=U+U*,
H_a=(I-aU)^* (I-aU)=I-aV+a^2 I.
```

On `Ran(R)`,

```text
A_a=(1+a^2)R-a R V R.                                  (A.2)
```

Because `Q R=0`, equation (A.1) becomes

```text
L_a(f)-L_infinity(f)
 = -a Tr(R C_f Q V R A_a^(-1)).                         (A.3)
```

The inverse has the norm-convergent expansion near `a=0`

```text
A_a^(-1)
 = R+a R V R+a^2((R V R)^2-R)+O(a^3).                  (A.4)
```

Substitution gives

```text
Delta L_a(f)
 = -a   Tr(R C_f Q V R)
   -a^2 Tr(R C_f Q V R V R)
   +O(a^3).                                             (A.5)
```

## 4. Single-Crossing Quotient

The arithmetic main channel is the quotient in which words with at least two
boundary crossings are assigned to the trace-class residual ideal. In the
second term of (A.5), replace the internal `R` by `I-Q`:

```text
Q V R V R
 = Q V^2 R - Q V Q V R.                                (A.6)
```

The second word has two crossings and is trace class after CC20 smoothing. The
first word is the noncompact single-crossing channel. Since

```text
V^2=U^2+2I+U*^2
```

and `Q I R=0`, its second-order principal part is

```text
-a^2 Q(U^2+U*^2)R.                                     (A.7)
```

There is no factor `1/2`.

## 5. Weil Coefficient Mismatch

A translation `U^m` crosses a half-line over an interval of length
`m log(p)`. For the same convolution square `F_h=h**h`, the exact local trace
is

```text
Tr(C_h* C_h (J_(m log p)+J_(m log p)*))
 = m log(p) (F_h(m log p)+F_h(-m log p)).                (A.8)
```

At `m=2`, (A.7)--(A.8) therefore contribute magnitude

```text
2 a^2 log(p) (F_h(2 log p)+F_h(-2 log p)).               (A.9)
```

The finite-prime Weil atom is

```text
a^2 log(p) (F_h(2 log p)+F_h(-2 log p)).                 (A.10)
```

Equations (A.9) and (A.10) differ by a factor of `2`. The first-order channel
does match because `m=1`; that accidental agreement does not extend to prime
powers.

The missing `1/m` belongs to

```text
-log(I-aU)=sum_(m>=1) a^m U^m/m,
```

not to the endpoint orthogonal projection resolvent. Differentiating the moving
projection and integrating only the explicit logarithmic generator misses the
additional direct channel created by differentiating the moving `R_a` factors.
At order `a^2` the two derivative contributions integrate to coefficient `1`,
not `1/2`.

## 6. Why The Error Is Fatal

The excess term is another copy of the `m=2` single-crossing partial
translation. Before test smoothing it has infinite rank. It is therefore not a
multi-crossing or prolate compact correction and cannot be absorbed into
`K_(S,I)` while retaining

```text
remainder = -2 Id + compact.
```

Changing the compact bad-space conditions cannot remove a wrong noncompact
principal coefficient. The read-off owner itself must change.

## 7. Route Judgment

```text
theta_S bounded Sonin isomorphism: retained
metric orthogonal projection formula: retained as operator geometry
metric projection as Weil positive-trace owner: rejected
036 logarithmic-flow coefficient claim: rejected after moving-projector terms
038 exact all-prime-power read-off claim: rejected beyond m=1
Plan 016 M3B through Plan 024: inactive
Lean owner: forbidden
RH: unproved
```

Reopening requires a different positive pre-cutoff object whose endpoint
expansion contains the Euler logarithm coefficient `a^m/m` before the crossing
length supplies `m log(p)`. The endpoint metric orthogonal projection does not.

Primary sources:

```text
https://arxiv.org/abs/2006.13771
https://arxiv.org/abs/2310.18423
```
