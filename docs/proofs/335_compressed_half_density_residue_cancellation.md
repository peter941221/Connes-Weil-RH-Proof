# Proof 335: Compressed half-density residue cancellation

Date: 2026-07-17

Status: exact cancellation of the leading half-density residue in Proof 334's
complete Burnol Schur covariance.  The boundary moment has a rank-one weak
residue.  Burnol's Gram inverse sends its two boundary vectors to the literal
window endpoint evaluators, so the compressed Toeplitz residue is exactly an
`exp(-u/2)` character.  The root differential
`Q=-partial_u^2+1/4` annihilates it.

This closes the leading-residue part of the complete compressed product.  It
does not yet prove a uniform next-order remainder in the required trace
topology, the near stopped-path bound, Gate 3U, the finite-`S` sign, Burnol's
identity, or RH.

## 1. Result

```text
+----------------------------------------------------+-------------------------+
| layer                                              | judgment                |
+----------------------------------------------------+-------------------------+
| positive-displacement boundary moment residue     | explicit rank one       |
| Burnol Gram inverse on both residue vectors        | exact                   |
| static Q-paired half-density residue               | zero                    |
| compressed Toeplitz half-density residue           | zero                    |
| negative-displacement reflected residue            | zero by same Q          |
| next-order Schur trace remainder                    | open                    |
| near complete-product stopped path                  | open                    |
| Gate 3U and RH                                     | open / unproved         |
+----------------------------------------------------+-------------------------+
```

The mechanism is

```text
M(z) ~exp(-z/2)|a><b|
       |
       | G^(-1)a=(delta_0,0),
       | G^(-1)b=(0,delta_0/2)
       v
compressed residue
 =1/2 <delta_0,M_21(Q phi)delta_0>
 =integral (Q phi)(u)exp(-u/2)du
 =0.                                                     (BS.1)
```

No prolate mode is estimated separately, and no finite section is used in
the derivation.

## 2. Boundary functionals

Work on the even half-line window

```text
H_0=L2([0,1]).                                        (BS.2)
```

On a smooth even core define

```text
epsilon(f)=f(0),
ell(f)=integral_0^1 f(x)dx.                           (BS.3)
```

`epsilon` is a boundary distribution rather than an `L2` vector.  Every
identity below is first an identity of continuous bilinear forms on a Sobolev
core where endpoint evaluation is legal.  The missing remainder theorem must
then place the root-sandwiched difference in the ordinary trace domain.

Use Proof 334's boundary map and Gram

```text
A(f,g)=f+Fourier(g),
G=A*A=[[I,F_0],[F_0,I]],
F_0=P Fourier P.                                     (BS.4)
```

The even cosine transform is

```text
(Fourier f)(x)=2 integral_0^infinity
  cos(2 pi x y)f(y)dy.                               (BS.5)
```

## 3. Explicit rank-one residue

Let `rho=exp(z)` and use the CC20 dilation convention

```text
(U_z f)(x)=sqrt(rho) f(rho x).                       (BS.6)
```

Proof 334 gives

```text
M(z)=A*U_zA

 =[[P U_z P,         P U_z Fourier P],
   [P Fourier U_z P, P U_(-z)P]].                    (BS.7)
```

For smooth window vectors, the four positive-displacement limits are

```text
rho^(1/2) P U_z P
  ->|epsilon><ell|,

rho^(1/2) P U_z Fourier P
  ->(1/2)|epsilon><epsilon|,

rho^(1/2) P Fourier U_z P
  ->2|ell><ell|,

rho^(1/2) P U_(-z)P
  ->|ell><epsilon|.                                  (BS.8)
```

The first and fourth limits follow by `y=rho x`.  The third follows directly
from

```text
2 rho^(-1/2)cos(2 pi x y/rho)
 ->2 rho^(-1/2).                                     (BS.9)
```

For the second, Fourier inversion at the even endpoint gives

```text
integral_0^infinity (Fourier g)(X)dX=g(0)/2.          (BS.10)
```

After `X=rho x`, `(BS.10)` gives its factor `1/2`.

Put

```text
a=(epsilon,2 ell)^T,
b=(ell,epsilon/2)^T.                                 (BS.11)
```

Equations `(BS.8)` recombine as the single rank-one residue

```text
M_+=|a><b|,
M(z)=exp(-z/2)M_+ + lower boundary order.             (BS.12)
```

The phrase `lower boundary order` in `(BS.12)` is deliberate.  The weak
leading limit is proved by `(BS.8)`.  An `O(exp(-3z/2))` estimate uniform in
the root Sobolev/support ledger is still required.

## 4. Burnol Gram inverse collapses the residue

At the window endpoint, the truncated cosine transform satisfies the
distributional identity

```text
F_0 epsilon=2 ell.                                    (BS.13)
```

Therefore

```text
G(epsilon,0)^T
 =(epsilon,F_0 epsilon)^T
 =(epsilon,2 ell)^T=a,

G(0,epsilon/2)^T
 =(F_0 epsilon/2,epsilon/2)^T
 =(ell,epsilon/2)^T=b.                               (BS.14)
```

Since `G` is invertible,

```text
G^(-1)a=(epsilon,0)^T,
G^(-1)b=(0,epsilon/2)^T.                             (BS.15)
```

This is the decisive correction to treating the compressed product as
arbitrary data.  The large inverse `(I-F_0^2)^(-1)` disappears completely on
the residue vectors.  No `1/(1-lambda_0)` estimate enters `(BS.15)`.

## 5. The compressed residue is Q-harmonic

For `phi in C_c^2(R)`, define

```text
M_(Q,phi)(0)=integral (Q phi)(u)M(u)du,
Q=-partial_u^2+1/4.                                  (BS.16)
```

Proof 334 showed that the only possible compressed half-density coefficient
is

```text
c_(Q,phi)
 =<b,G^(-1)M_(Q,phi)(0)G^(-1)a>.                    (BS.17)
```

Substitute `(BS.15)`.  Only the `21` block of `M(u)` remains:

```text
c_(Q,phi)
 =1/2 integral (Q phi)(u)
   <epsilon,(P Fourier U_u P)epsilon>du.             (BS.18)
```

The `21` block has the explicit kernel

```text
2 exp(-u/2)
 cos(2 pi x y exp(-u)).                              (BS.19)
```

Endpoint evaluation at `x=y=0` gives

```text
<epsilon,(P Fourier U_u P)epsilon>
 =2 exp(-u/2).                                       (BS.20)
```

Consequently

```text
c_(Q,phi)
 =integral (Q phi)(u)exp(-u/2)du
 =integral phi(u)Q(exp(-u/2))du
 =0.                                                 (BS.21)
```

Compact support removes both integration-by-parts boundary terms.  The
reflected negative-displacement residue uses `exp(u/2)` and is killed by the
same operator `Q`.

Equation `(BS.21)` proves Proof 334 `(BR.15)` for the actual Burnol boundary
moment.  It is not a stored orthogonality premise.

## 6. Relation to the static CC20 residue

Proof 333 proved that the static CC20 coefficient has the form

```text
d(z)=c exp(-z/2)+O(exp(-3z/2)).                      (BS.22)
```

Its leading term is killed by

```text
integral (Q phi)(u)exp(-u/2)du=0.                    (BS.23)
```

Proof 335 shows that the compressed Toeplitz product has exactly the same
half-density character at its leading boundary residue.  Thus the full Schur
difference has no surviving `exp(-z/2)` coefficient after the root
differential.

This statement is stronger than the static calculation and narrower than a
global two-variable kernel bound:

```text
static residue                    killed;
compressed Schur residue         killed;
next root-sandwiched Schur order still to estimate.  (BS.24)
```

## 7. Non-periodic certificate

The Proof 334 probe uses shifted Legendre polynomials on `[0,1]`.  In that
basis the truncated endpoint evaluation vector is explicit:

```text
epsilon_n=sqrt(2n+1)(-1)^n.                         (BS.25)
```

It checks both identities in `(BS.15)` and the scalar `(BS.21)`.  With
`B=0.8` and an 80-point compact-correlation quadrature, the convergence is

```text
+------+------------------+------------------+------------------+
| size | column error     | row error        | Q residue scalar |
+------+------------------+------------------+------------------+
|    6 | 6.408e+0         | 6.408e+0         | -3.176821e-2     |
|    8 | 1.972e-1         | 1.972e-1         | -8.263707e-4     |
|   10 | 3.791e-3         | 3.791e-3         | -1.149087e-4     |
|   12 | 5.170e-5         | 5.170e-5         | -1.409392e-6     |
|   16 | 4.28e-9          | 4.28e-9          | -9.99e-11        |
|   20 | <4.5e-12         | <4.5e-12         | +9.47e-12        |
+------+------------------+------------------+------------------+
```

The last values are quadrature and floating-point noise.  This certificate
tests the explicit window identities; the proof is `(BS.13)--(BS.21)`.

Run without a Lean build:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/334_burnol_schur_tail_probe.py \
  --sizes 6,8,10,12,16,20 --integration-order 220 \
  --quadrature-order 80 --displacements 3
```

## 8. Remaining theorem

The far-tail theorem is now reduced to a remainder estimate, not a residue
identity.  In Proof 334 notation it must show

```text
abs Tr G^(-1)[
  M_(Q,phi)(z)-M(z)G^(-1)M_(Q,phi)(0)
]

 <=C exp(-3z/2)
   P(B_root,norms of eta and xi),                    (BS.26)
```

for `z` beyond the compact window, with a polynomial `P` and in a trace
topology strong enough for Proof 289's complete-prime telescope.

The source attack should estimate the four fixed-window blocks in `(BS.7)`
after subtracting the rank-one residue `(BS.12)`.  The strict-angle inverse is
fixed source data, and `(BS.15)` prevents it from multiplying the leading
mode.  The outer, reflected, and prolate branches remain recombined through
the Schur difference.

After `(BS.26)`, the remaining Gate 3U bottom is the near-displacement
complete-product stopped path from Proofs 289--296.  Gate 3U, the finite-`S`
sign, Burnol's identity, and RH remain open.

## 9. Sources

```text
Burnol, On the "Sonine Spaces" associated by de Branges to the Fourier
Transform, projection theorem and boundary distributions:
https://arxiv.org/abs/math/0208121

Connes--Consani, Weil positivity and Trace formula, the archimedean place,
prolate and Q formulas:
https://arxiv.org/abs/2006.13771
```
