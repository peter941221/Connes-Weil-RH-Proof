# Proof 220: correct-Q-root PNT Green identity

Date: 2026-07-13

Status: exact mathematical reduction and reproducible numerical check.  On the
genuine source root `g=(d/dx+1/2)xi`, the continuous PNT main kernel is exactly
`-Id` on the pre-root.  This was not present in Proof 215, which treated a raw
root.  The result isolates the arithmetic obstruction as the signed difference
between the von Mangoldt measure and its continuous main measure.  It does not
prove the sign of that defect, a finite-S positive trace, or RH.

## 1. Setup

Use the additive logarithmic coordinate and put

```text
L = d/dx+1/2,
g = L xi,
T_b f(x)=f(x-b).
```

Let `xi` be smooth and compactly supported in an interval of diameter strictly
less than `T=log(c)`.  The continuous PNT replacement of the finite-prime
translation operator is

```text
K_0
 = integral_(0<T) exp(b/2)(T_b+T_(-b)) db.              (G.1)
```

On the support of `g`, changing variables in the two translation integrals
gives the kernel

```text
k_0(x,y)=exp(|x-y|/2).                                  (G.2)
```

This is the same continuous main operator introduced in Proof 215, equations
`(P.2)--(P.3)`.  The difference is that it is now evaluated on the genuine
CC20 Q-root from Proofs 217--218.

## 2. Exact Green identity

For `r=x-y`, the first derivative of `exp(|r|/2)` has jump one at the origin.
Consequently, as a distribution,

```text
(-d_r^2+1/4) exp(|r|/2) = -Dirac_0.                     (G.3)
```

Integrate by parts once in each variable.  Compact support removes every
endpoint term.  The two formal adjoints acting on the kernel are

```text
L_x^* = -d_x+1/2 = -d_r+1/2,
L_y^* = -d_y+1/2 =  d_r+1/2.
```

Their product is exactly the operator in `(G.3)`:

```text
L_x^* L_y^*
 = (-d_r+1/2)(d_r+1/2)
 = -d_r^2+1/4.                                         (G.4)
```

Therefore

```text
<L xi,K_0 L xi>
 = double_integral conjugate(xi(x))
     (-d_r^2+1/4)exp(|r|/2) xi(y) dx dy
 = -||xi||_2^2.                                        (G.5)
```

Equation `(G.5)` is valid for complex `xi`.  By density it extends from smooth
compact support to the corresponding `H_0^1` form domain.

There is an equivalent bounded-Green interpretation.  The kernels
`exp(|r|/2)` and `-exp(-|r|/2)` differ by `2cosh(r/2)`, a rank-two homogeneous
solution of `(-d^2+1/4)h=0`.  One of its two Mellin factors vanishes
automatically on `Range(L)`, so both kernels induce the same quadratic form
there.  Thus `(G.5)` is the form-level identity

```text
L^* K_0 L = -Id                                       (G.6)
```

on compactly supported pre-roots, not merely the inequality `K_0<=0` on a
pole-neutral raw-root subspace.

## 3. Exact transport of the route rows

For the bilateral Laplace row

```text
M_s(f)=integral exp(sx)f(x) dx,
```

one integration by parts gives

```text
M_s(L xi)=(1/2-s)M_s(xi).                              (G.7)
```

The three source-root rows therefore become

```text
M_(1/2)(g)=0                         automatically,
M_0(g)=0          iff M_0(xi)=0,
M_(-1/2)(g)=0     iff M_(-1/2)(xi)=0.                  (G.8)
```

This is useful ownership information: the Q-root range condition is built into
`g=L xi`, and the remaining three route rows impose only two independent rows
on the pre-root.  It does not remove any finite-prime translation channel.

## 4. The exact von Mangoldt defect

The same-object finite-prime operator is

```text
K_c
 = sum_(q=p^m<c) Lambda(q)/sqrt(q)
     (T_(log q)+T_(-log q)).                            (G.9)
```

This is the operator proved to read the selected finite-prime quadratic form
in `SelectedPrimeTranslationQuadratic.lean`.  Since

```text
x^(-1/2) dx = exp(b/2) db,  b=log x,
```

`K_0` is exactly the result of replacing the von Mangoldt Stieltjes measure
`d psi(x)` by `dx`.  Define the signed PNT defect

```text
E_c=K_c-K_0
    =integral_(1<x<c) x^(-1/2)
       (T_(log x)+T_(-log x)) d(psi(x)-x).              (G.10)
```

For pole-neutral source roots, Proof 218 gives

```text
QW_c(g,g)=<g,2 theta'(D)g>-<g,K_c g>.                  (G.11)
```

Combining `(G.5)`, `(G.10)`, and `(G.11)` yields the new correct-root
decomposition

```text
QW_c(L xi,L xi)
 = <L xi,2 theta'(D)L xi>
     +||xi||_2^2
     -<L xi,E_c L xi>.                                 (G.12)
```

Every term in `(G.12)` belongs to the same pre-root/source-root pair.  No CC20
positive multiplier, ordinary remainder, or finite-prime term has been placed
on a different convolution square.

There is also a scalar cumulative form of the defect.  Define the symmetric
autocorrelation and weighted Chebyshev discrepancy

```text
C_g(b)=<g,T_b g>+<g,T_(-b)g>,
M(B)=sum_(q=p^m<exp(B)) Lambda(q)/sqrt(q)
       -2(exp(B/2)-1).                                  (G.13)
```

Then `(G.10)` is the Stieltjes pairing

```text
<g,E_c g>=integral_(0<T) C_g(b) dM(b).                  (G.14)
```

Here `M(0)=0`; compact support of diameter strictly below `T` gives `C_g(T)=0`.
Stieltjes integration by parts therefore yields

```text
<g,E_c g>=-integral_0^T M(b) C_g'(b) db.                (G.15)
```

The Q-root identity also gives

```text
C_(L xi)(b)=(-d_b^2+1/4)C_xi(b).                        (G.16)
```

Equations `(G.15)--(G.16)` name the exact remaining arithmetic object.  A
future detector theorem must retain the signed cumulative discrepancy `M`; an
absolute bound destroys precisely the cancellation that made `(G.5)` exact.

## 5. Scalar-only defect domination is impossible

Equation `(G.12)` must not be read as saying that `||xi||^2` alone controls the
PNT defect.  This fails on the correct root, even after the transported route
rows are imposed.

Fix `c>2`, put `ell=log(2)`, and choose a small interval `J` such that distinct
translates of `J` by the finitely many visible values `log(q)` do not overlap,
except for the intended displacement `ell`.  For `h` supported in `J`, define

```text
xi=h+T_ell h,
g=L xi=Lh+T_ell Lh.                                    (G.17)
```

Only the `q=2` channel connects the two cells.  Hence

```text
<g,K_c g>
 =2 log(2)/sqrt(2) ||Lh||^2,                            (G.18)

<g,E_c g>
 =2 log(2)/sqrt(2) ||Lh||^2+||xi||^2.                  (G.19)
```

The two nonautomatic rows in `(G.8)` reduce to two continuous linear
conditions on `h`:

```text
M_0(h)=0,
M_(-1/2)(h)=0.                                         (G.20)
```

Their common kernel in `H_0^1(J)` is infinite-dimensional.  It contains a
unit-norm sequence `h_n` with `||Lh_n||` tending to infinity: take high
Dirichlet modes and remove their projection onto a fixed two-dimensional
representer space for `(G.20)`.  Equations `(G.18)--(G.19)` then imply

```text
sup <L xi,E_c L xi>/||xi||^2 = infinity                (G.21)
```

on the transported route-row domain.  Thus no estimate of the form

```text
<L xi,E_c L xi> <= C ||xi||^2                           (G.22)
```

can close the route for a fixed scalar `C`.  Any viable theorem must retain the
noncompact archimedean graph form `<Lxi,2theta'(D)Lxi>` or use a genuinely
detector-specific signed cancellation.

## 6. What this changes

Proof 215 established only that `K_0` is nonpositive after imposing a `cosh`
row on an arbitrary raw vector.  Equation `(G.5)` is sharper and correctly
owned:

```text
raw root:       <f,K_0 f> <= 0 on one constrained subspace,
correct Q-root: <L xi,K_0 L xi> = -||xi||^2 exactly.    (G.23)
```

The all-prime difficulty is now localized to one named signed operator `E_c`.
The next independent theorem must exploit Paley--Wiener coupling and prove a
detector-specific or constrained form bound for

```text
<L xi,E_c L xi>.                                       (G.24)
```

An absolute-value PNT estimate is not enough: the discrete translations retain
second-order growth after pulling through `L`, while the cancellation in
`(G.5)` uses the full continuous measure.  Conversely, simply proving that the
right side of `(G.12)` is nonnegative for every route test would already be the
restricted Weil sign and is not a lower producer.

The useful next target is narrower: specialize `(G.15)` to the canonical
off-line detector, retain its target-zero signed contribution, and test whether
the two independent pre-root rows in `(G.8)` remove the non-decaying boundary
terms.  Equation `(G.21)` rules out replacing that work by a scalar norm bound.

## 7. Reproduction

The companion script uses analytic derivatives of a smooth compact bump and
checks `(G.5)` under several modulations and grid refinements.  It also checks
`(G.7)` and reports the split `K_c=K_0+E_c`.

```text
python3 -B docs/proofs/220_qroot_pnt_green_identity.py
```

The exact proof is `(G.3)--(G.5)`; numerical convergence is only a guard against
sign, adjoint, translation, and half-density mistakes.

## 8. Route judgment

```text
correct Q-root ownership:                 exact
continuous PNT Green form:                -||xi||^2 exactly
three source-root rows on the pre-root:   two independent rows
finite-prime versus continuous main:      exact signed defect E_c
scalar L2 domination of E_c:              impossible on route rows
sign of E_c on the detector family:       open
finite-S positive owner:                  not constructed
Lean owner or route rewire:               none
RH:                                       unproved
```
