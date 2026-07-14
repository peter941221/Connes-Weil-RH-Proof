# Proof 207: Exact Euler-log regression invariance no-go

Date: 2026-07-13

## Result

The natural repair after proof 206 also fails. There is no bounded
translation-invariant metric `H` on the one-prime half-line model whose exact
compressed regression map is the one-sided Euler logarithm:

```text
Q H R(R H R)^(-1)
  = Q sum_(m>=1) a^m U^(-m)/m R.                       (W.1)
```

This is not the compact Wiener--Hopf no-go of proof 118. Equation (W.1) asks
for a new noncompact principal symbol. It fails because the requested graph is
not invariant under the translation that every multiplier metric commutes
with.

## Proposed repair

Proof 206 rejects deriving the Euler-log channel from
`H=((1+b)I-ell)^(-1)`. A stronger proposal is to solve the inverse problem:

```text
find H>0, translation invariant, such that
X_H=Q H R(R H R)^(-1)=D_a
```

with

```text
D_a=Q sum_(m>=1) a^m U^(-m)/m R,
0<a<1.
```

If it existed, `H` would commute with the test convolution, and the metric
trace cycle would expose `D_a` without the normalization ambiguity of proof
205.

## Translation-fiber reduction

For a shift length `L`, use

```text
L2(R)=L2([0,L)) tensor ell2(Z).
```

It is enough to work on one `ell2(Z)` fiber. Let

```text
U e_n=e_(n+1),
R=projection onto span{e_n : n>=0},
Q=I-R.
```

The desired graph map is

```text
D_a e_j
  = sum_(r>=0) d_(r+j) e_(-r-1),

d_n=a^(n+1)/(n+1)>0.                                  (W.2)
```

These are the moments `d_(r+j)=integral_0^a t^(r+j) dt`; `D_a` is the scaled
Hilbert Hankel operator.

## Invariant-graph obstruction

Assume (W.1). Since `R H R` is invertible, the image `H Ran(R)` is exactly the
graph of `D_a`:

```text
H Ran(R)=Graph(D_a).
```

The unilateral direction of `U` preserves `Ran(R)`, and a translation
multiplier `H` commutes with `U`. Therefore

```text
U Graph(D_a)
  = U H Ran(R)
  = H U Ran(R)
  subset Graph(D_a).                                   (W.3)
```

Now take

```text
y=e_0+D_a e_0 in Graph(D_a).
```

Equation (W.2) gives

```text
R U y=e_1+d_0 e_0,

Q U y=sum_(s>=0) d_(s+1)e_(-s-1).                     (W.4)
```

If (W.3) held, the negative component in (W.4) would have to equal

```text
D_a(e_1+d_0e_0)
  =sum_(s>=0)(d_(s+1)+d_0 d_s)e_(-s-1).                (W.5)
```

But `d_0 d_s>0` for every `s`. Equations (W.4)--(W.5) contradict each other.
Thus `Graph(D_a)` is not `U`-invariant, and no translation-invariant `H` can
satisfy (W.1).

## Scope

The proof closes the exact one-half-line regression repair. It does not claim
that every two-cutoff Sonin construction is translation invariant relative to
one half-line. A successor using the full support/Fourier-support geometry
must state its two-cutoff operator and prove the global trace identity; it
cannot inherit the local regression identity (W.1).

```text
compact boundary repair:                  already rejected by proof 118
inverse-log multiplier metric:            rejected by proof 206
exact multiplier regression repair:       rejected here
two-cutoff non-multiplier Sonin identity:  not covered
unbounded relative form:                   not covered
Lean owner:                               forbidden
RH:                                       unproved
```
