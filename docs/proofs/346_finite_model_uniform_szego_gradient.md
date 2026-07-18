# Proof 346: finite-model uniform Szego gradient

Date: 2026-07-18

Status: uniform condition-number-free bound for the normalized determinant
gradient in every finite Blaschke model space.  Positivity of Böttcher's
Hankel product bounds the complete Fredholm quotient between `1` and the
scalar strong-Szego constant.  Convexity then bounds its gradient by the
product of two `H^(1/2)` norms, independently of the model inner function.

This closes the full finite-dimensional model-space analogue of the Gate 3U
near estimate.  The route's continuous prime-log shifts have infinite
half-line multiplicity, so their unsmoothed logarithm is not in the disk
`H^(1/2)` class after Cayley transport.  A root-relative continuous
localization of the inequality remains open.  Gate 3U and RH remain unproved.

## 1. Result

Let `u` be any finite Blaschke product.  For real symbols `f,w` in the scalar
Wiener--Krein class define

```text
Phi_u(f)
 :=log det T_u(exp(f))
   -sum_(alpha in sigma(u)) log G(exp(f) o mu_(-alpha)).       (UG.1)
```

Then

```text
0<=Phi_u(f)<=norm(f)_(H^(1/2))^2,                    (UG.2)

abs D Phi_u(f)[w]
 <=4 norm(f)_(H^(1/2)) norm(w)_(H^(1/2)).             (UG.3)
```

The norm convention is

```text
norm(f)_(H^(1/2))^2
 :=sum_(k>=1) k |f_k|^2                               (UG.4)
```

for real `f`, so `f_(-k)=conj(f_k)`.

The constant in `(UG.2)--(UG.3)` is independent of:

```text
degree(u),
zeros of u,
the smallest compressed-metric eigenvalue,
the condition number of T_u(exp(f)).                  (UG.5)
```

## 2. Positive BOGC kernel

For `a=exp(f)>0`, choose its scalar canonical Wiener--Hopf factors so that

```text
a=a_- a_+,
a_-=conj(a_+) on the boundary.                        (UG.6)
```

In Proof 345 notation,

```text
b=a_- a_+^(-1),
c=a_-^(-1)a_+=conj(b).                                (UG.7)
```

With Böttcher's Hankel convention,

```text
mathcalK_f
 :=H(b)H(tilde(c))
  =H(b)H(b)*.                                         (UG.8)
```

Consequently,

```text
0<=mathcalK_f<I,
mathcalK_f in S_1.                                    (UG.9)
```

Strict inequality follows from invertibility of the canonical Toeplitz
factors in the source theorem.

## 3. Fredholm determinant sandwich

Proof 345 `(FB.5)` gives

```text
exp(Phi_u(f))
 =det(I-Q_u mathcalK_f Q_u)
   /det(I-mathcalK_f).                                (UG.10)
```

For a positive trace-class contraction `K` and an orthogonal projection `Q`,
the eigenvalues of the compression `QKQ|Ran(Q)` are termwise no larger than
those of `K`, by the min--max principle.  Therefore

```text
det(I-K)
 <=det(I-QKQ)
 <=1.                                                 (UG.11)
```

Apply `(UG.11)` to `(UG.10)`:

```text
1<=exp(Phi_u(f))<=1/det(I-mathcalK_f).                 (UG.12)
```

Böttcher records in the scalar case that

```text
1/det(I-mathcalK_f)
 =exp(sum_(k>=1)k f_k f_(-k))
 =exp(norm(f)_(H^(1/2))^2).                           (UG.13)
```

Taking logarithms in `(UG.12)--(UG.13)` proves `(UG.2)`.

No inverse Fredholm norm occurs.  In particular, `(UG.2)` remains valid when
`norm(mathcalK_f)` is arbitrarily close to one.

## 4. Convexity

Choose an orthonormal basis `e_1,...,e_N` of `K_u`.  Andreief's Gram
determinant formula gives

```text
det T_u(exp(f))

 =1/N! integral_(T^N)
   exp(sum_(j=1)^N f(z_j))
   |det(e_i(z_j))_(i,j)|^2 dz_1...dz_N.               (UG.14)
```

The logarithm of `(UG.14)` is a log-Laplace transform and is therefore convex
in the real symbol `f`.  The geometric term subtracted in `(UG.1)` is linear
in `f`.  Hence

```text
Phi_u is convex,
Phi_u(0)=0.                                           (UG.15)
```

The quadratic upper bound `(UG.2)` applied to `t w` also implies

```text
D Phi_u(0)[w]=0.                                      (UG.16)
```

## 5. Gradient bound

Let

```text
x=norm(f)_(H^(1/2)),
y=norm(w)_(H^(1/2)).                                  (UG.17)
```

For `t>0`, convexity and nonnegativity give

```text
D Phi_u(f)[w]
 <=[Phi_u(f+t w)-Phi_u(f)]/t
 <=(x+t y)^2/t.                                       (UG.18)
```

Apply the same argument to `-w`:

```text
-D Phi_u(f)[w]
 <=(x+t y)^2/t.                                       (UG.19)
```

If `x,y>0`, choose `t=x/y`.  Equations `(UG.18)--(UG.19)` give

```text
abs D Phi_u(f)[w]<=4xy.                               (UG.20)
```

The cases `x=0` or `y=0` follow by continuity.  This proves `(UG.3)`.

## 6. Exact relation to the transported response

Let

```text
f=log(|tau|^2).                                       (UG.21)
```

Proof 345 `(FB.12)--(FB.17)` and the geometric cancellation show

```text
Tr[M_w(P_(tau K_u)-P_u)]
 =D Phi_u(f)[w].                                      (UG.22)
```

Thus `(UG.3)` is an estimate of the complete Gram-corrected projection
response.  It does not estimate separate phase, amplitude, canonical, or
boundary terms.

Combining `(UG.3)` with Proof 344's Euler energy `(SQ.6)` gives the desired
`p^(-m)` square ledger for every finite multiplicity-one model.

## 7. Continuous multiplicity obstruction

The route is on the real Mellin line.  A prime-log exponential

```text
exp(i ell s)                                           (UG.23)
```

acts in the physical logarithmic coordinate as a translation by `ell`.  Its
commutator with a sharp continuous half-line projection contains an identity
operator on an interval of length `ell`; that operator has infinite rank and
is not Hilbert--Schmidt.  After a Cayley transform, `(UG.23)` becomes a
singular-inner boundary factor, not a disk Wiener--Krein symbol with finite
norm `(UG.4)`.

This is exactly why the raw continuous Euler commutator is forbidden in
Proofs 253, 260, and 261.  Compact-root completion makes the final derivative
trace class, but it does not make the unsmoothed determinant in `(UG.1)`
finite.

Consequently `(UG.3)` cannot be applied to Gate 3U by declaring Proof 344's
atomic energy to be the disk norm.  The missing theorem is a localized
continuous version:

```text
abs D Phi_(Theta,root)(f)[w]
 <=C sqrt(mathcalE_S(4B+4))
      P(B,root Sobolev norms),                        (UG.24)
```

where `Phi_(Theta,root)` is constructed directly in Proof 261's
root-sandwiched determinant line and differentiates to Proof 343's endpoint
response.

Proof 344 bounds the right side of `(UG.24)` polynomially.  Proof 336 supplies
the excluded far tail.  Constructing and proving `(UG.24)`, including the
Burnol singular-inner limit, is the remaining near Gate 3U theorem.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| finite model BOGC positivity                  | exact                     |
| finite model Fredholm inverse conditioning    | eliminated                |
| uniform normalized determinant bound          | exact `(UG.2)`            |
| uniform finite-model response gradient        | exact `(UG.3)`            |
| prime-power quadratic ledger                   | Proof 344 closed          |
| continuous root-relative localization         | open `(UG.24)`            |
| Gate 3U                                        | not yet closed            |
| finite-S sign / Burnol identity / RH           | open / open / unproved    |
+------------------------------------------------+---------------------------+
```
