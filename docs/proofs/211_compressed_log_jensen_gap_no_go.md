# Proof 211: compressed Euler-log Jensen-gap no-go

Date: 2026-07-13

Status: the compression Jensen gap for the finite Euler metric is genuinely
positive and the uncompressed logarithm has the exact `a^m/m` coefficients.
These two facts occur in different summands.  The positive gap cancels every
first-order boundary channel and starts with a two-crossing loop.  The direct
logarithm retains the desired single crossings but is sign-indefinite; making
it positive adds a noncompact scalar bulk.  This candidate is not the missing
common-domain positive owner.  RH remains unproved.

## 1. Candidate and exact logarithm

On the one-prime whole-line model let

```text
0<a=p^(-1/2)<1,
U = translation by log(p),
H_a = (I-aU)^*(I-aU).
```

Since `U` is unitary,

```text
(1-a)^2 I <= H_a <= (1+a)^2 I.                         (J.1)
```

The norm-convergent functional-calculus series is

```text
ell_a := -log(H_a)
       = sum_(m>=1) a^m(U^m+U*^m)/m.                   (J.2)
```

Formula (J.2) has exactly the coefficient required before a crossing of
length `m log(p)` supplies the factor `m log(p)`:

```text
(a^m/m) * m log(p) = a^m log(p).                       (J.3)
```

Thus the direct off-diagonal block

```text
Q ell_a R
```

is coefficient-correct for the existing whole-line crossing trace owner.
This is the attraction already isolated in proofs 038, 128, and 207.

## 2. The genuine positive Jensen gap

Let `R` be the archimedean Sonin projection and `Q=I-R`.  On `Ran(R)` put

```text
A_a = R H_a R | Ran(R).
```

By (J.1), `A_a` is positive and boundedly invertible.  Since `-log` is
operator convex, compression Jensen gives

```text
-log(A_a) <= R(-log H_a)R.
```

Therefore

```text
J_a := R(-log H_a)R + log(A_a) >= 0.                   (J.4)
```

The source theorem is Hansen--Pedersen, Jensen's Operator Inequality,
Theorem 2.1(iii): for operator-convex `f` and an isometry `V`,

```text
f(V* X V) <= V* f(X) V.
```

Primary source: `jensen.tex:180-217`,
https://arxiv.org/abs/math/0204049.

This positivity is unconditional and does not assume any Weil sign.

## 3. Why positivity removes the desired channel

Write

```text
V = U+U*.
```

Then

```text
H_a = I-aV+a^2 I,
A_a = R-a RVR+a^2 R.
```

Expanding both logarithms on `Ran(R)` gives

```text
R(-log H_a)R
  = a RVR+(a^2/2)R(U^2+U*^2)R+O(a^3),                 (J.5)

-log A_a
  = a RVR-a^2 R+(a^2/2)(RVR)^2+O(a^3).                (J.6)
```

Subtracting (J.6) from (J.5),

```text
J_a
  = (a^2/2)[R V^2 R-(RVR)^2]+O(a^3)
  = (a^2/2)R V Q V R+O(a^3).                           (J.7)
```

The coefficient-correct first-order block `a QVR` has canceled completely.
The first surviving term in the positive object crosses the Sonin boundary,
returns across it, and only then contributes on `Ran(R)`.

This is not an accident of the Taylor expansion.  The integral representation

```text
-log X = integral_(0,infinity)
           [(X+tI)^(-1)-(1+t)^(-1)I] dt
```

gives

```text
J_a = integral_(0,infinity)
        [R(H_a+tI)^(-1)R-(A_a+tR)^(-1)] dt.            (J.8)
```

In the block decomposition `Ran(R) direct-sum Ran(Q)`, put

```text
B_a = R H_a Q,
D_(a,t) = Q(H_a+tI)Q.
```

The compressed resolvent in (J.8) is the Schur complement

```text
R(H_a+tI)^(-1)R
 = [A_a+tR-B_a D_(a,t)^(-1) B_a*]^(-1).                (J.9)
```

Every term in the difference with `(A_a+tR)^(-1)` therefore contains both
`B_a` and `B_a*`.  Hence every Jensen-gap word has at least two boundary
crossings.  It belongs to the smoothed multi-crossing remainder class, not to
the noncompact single-crossing class that carries the finite-prime atom.

## 4. Why the direct logarithm is not positive

On the bilateral-shift spectral circle, (J.2) has symbol

```text
ell_a(theta)
 = -log(1-2a cos(theta)+a^2).
```

At the two endpoints,

```text
ell_a(0)  = -2log(1-a) > 0,
ell_a(pi) = -2log(1+a) < 0.                             (J.10)
```

Thus `ell_a` is sign-indefinite.  Wave packets supported far inside the
half-line transfer the negative spectral values in (J.10) to the compression
`R ell_a R`, so compression does not repair positivity.

The smallest translation-invariant scalar shift making the direct logarithm
positive is

```text
ell_a+2log(1+a)I >= 0.                                  (J.11)
```

The extra term in (J.11) is a noncompact same-range bulk.  After
`Q_+=-partial^2+1/4`, its trace contribution contains

```text
2log(1+a)[-F''(0)+(1/4)F(0)],                           (J.12)
```

which grows quadratically on the narrow modulated roots used in proofs 026
and 210.  This is scalar compensation, not central-atom cancellation.

## 5. The sign directions cannot be recombined

Equations (J.4) and (J.2) say

```text
R ell_a R = -log(A_a)+J_a.                              (J.13)
```

The positive term `J_a` contains no single-crossing principal channel.  The
other term `-log(A_a)` is not positive in general.  Adding `J_a` to an
existing positive trace only adds multi-crossing energy.  Subtracting `J_a`
to expose a signed single-crossing term loses positivity and requires a new
domination theorem on the same post-Q domain.  Jensen's inequality supplies
no such reverse bound.

In particular, (J.13) does not evade:

```text
proof 119: the raw Fredholm determinant is undefined for U;
proof 122: a signed linear channel inside a positive square has diagonal cost;
proof 128: an orthogonal graph projection pollutes p^3;
proof 207: no translation multiplier has the exact Euler-log regression graph.
```

The Jensen construction is bounded for fixed `a`; it is not yet the surviving
unbounded relative-form lane merely because a logarithm appears in its name.

## 6. Route judgment

```text
exact Euler logarithm:                  accepted
a^m/m single-crossing coefficients:    accepted
direct-log positivity:                 false
positive scalar repair:                rejected by noncompact central bulk
compression Jensen positivity:         accepted
Jensen first variation:                zero
Jensen principal class:                 at least two boundary crossings
existing finite-prime crossing read-off: not carried by the positive gap
Lean owner:                             forbidden for this candidate
RH:                                     unproved
```

A remaining common-domain relative form must couple the archimedean unbounded
owner to the finite Euler logarithm before taking the positive completion, so
that a genuine first-order cross term survives without adding a central
second-order bulk.  A finite-place compression Jensen gap does not do this.

Primary sources:

```text
https://arxiv.org/abs/math/0204049
https://arxiv.org/abs/2006.13771
https://arxiv.org/abs/2310.18423
```
