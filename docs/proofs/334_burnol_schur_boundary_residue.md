# Proof 334: Burnol Schur boundary residue

Date: 2026-07-17

Status: exact fixed-window reduction of the complete Sonin Toeplitz
covariance.  The static CC20 term and the compressed Toeplitz product are the
two terms of one operator-valued Schur difference.  After the root
differential `Q=-partial_u^2+1/4` is transferred to the compact correlation,
the entire possible `exp(-z/2)` obstruction is one boundary-row scalar.

This is a genuine narrowing of Proof 333's missing two-variable theorem.  It
does not prove that the boundary-row scalar vanishes, the uniform near-path
bound, Gate 3U, the finite-`S` sign, Burnol's identity, or RH.

## 1. Result

```text
+--------------------------------------------------+---------------------------+
| layer                                            | judgment                  |
+--------------------------------------------------+---------------------------+
| Burnol complementary projection                 | source theorem            |
| complete Toeplitz covariance on boundary space  | exact Schur difference    |
| static / compressed terms kept together         | exact                     |
| Q transfer before absolute value                 | exact                     |
| static half-density residue                      | annihilated by Q           |
| compressed half-density residue                  | one boundary-row scalar   |
| boundary row = Mellin +/-1/2 row                 | open source identification|
| non-periodic Galerkin probe                      | inconclusive guard        |
| Gate 3U and RH                                   | open / unproved           |
+--------------------------------------------------+---------------------------+
```

The ownership reduction is

```text
Tr(T_(w h_z)^R-T_w^R T_(h_z)^R)
  -> fixed-window Schur difference
  -> compact Q-correlation
  -> static residue dies automatically
  -> one compressed boundary-row residue remains
  -> identify that row with the two pre-root Mellin rows
  -> complete far tail.                                      (BR.1)
```

Proof 277 left an apparently two-variable compressed product.  Equation
`(BR.11)` below shows that its leading far-tail obstruction is only one
scalar matrix coefficient.

## 2. Burnol boundary coordinate

Let `P` be the even source-window projection on `[0,1]`, let `Fourier` be the
even cosine transform, and put

```text
H_0=P H,
F_0=P Fourier P|_(H_0),

A:H_0 direct-sum H_0 -> H,
A(f,g)=f+Fourier(g),

G=A* A=[[I,F_0],[F_0,I]].                            (BR.2)
```

Burnol proves `norm(F_0)<1`, so `G` is positive and invertible.  If `R` is
the orthogonal Sonin projection and `C=I-R`, his projection formula is

```text
C=A G^(-1) A*.                                       (BR.3)
```

Primary source:

```text
Jean-Francois Burnol,
On the "Sonine Spaces" associated by de Branges to the Fourier Transform,
Theorem 4, arXiv:math/0208121.
https://arxiv.org/abs/math/0208121
```

Let `U_t` be logarithmic dilation and define the operator-valued boundary
moment

```text
M(t)=A* U_t A.                                       (BR.4)
```

The group law gives `U_z U_u=U_(z+u)`, but `M` is not a representation:
the missing part is exactly the Sonin compression.

## 3. Exact complete covariance

For a compact correlation `F`, write the detector as

```text
W_F=integral F(u) U_u du.                            (BR.5)
```

Under Proof 261's fixed-`S` root-sandwiched trace legality, Burnol's centered
formula `(AO.8)` gives

```text
S_R(F,z)
 :=Tr(R W_F(I-R)U_z R)

 =integral F(u) Tr_(H_0 direct-sum H_0)
    G^(-1)[
      M(z+u)-M(z)G^(-1)M(u)
    ]du.                                             (BR.6)
```

The derivation is direct:

```text
A* U_z W_F A
 =integral F(u) A*U_(z+u)A du
 =integral F(u)M(z+u)du,

A* U_z A G^(-1) A*W_F A
 =integral F(u)M(z)G^(-1)M(u)du.                    (BR.7)
```

Thus the compressed Toeplitz product is not independent arbitrary data after
passing to Burnol's boundary carrier.  It is the second term of the same
Schur complement as the static coefficient.  It must still not be deleted or
estimated separately.

The operator identity behind `(BR.6)` is

```text
M(z+u)-M(z)G^(-1)M(u)
 =A*U_z R U_u A.                                    (BR.8)
```

Indeed insert `R=I-A G^(-1)A*` between `U_z` and `U_u`.  Equation `(BR.8)`
is the exact fixed-window form of the complete Sonin covariance.

## 4. Q-centered Schur moment

Let `F=Q phi`, where

```text
Q=-partial_u^2+1/4,
phi in C_c^2(R).                                     (BR.9)
```

Define

```text
M_(Q,phi)(t)=integral (Q phi)(u)M(t+u)du.            (BR.10)
```

No support is enlarged.  Substituting `(BR.10)` into `(BR.6)` gives the
exact centered form

```text
S_R(Q phi,z)
 =Tr G^(-1)[
    M_(Q,phi)(z)
    -M(z)G^(-1)M_(Q,phi)(0)
  ].                                                 (BR.11)
```

This formula locates the gap in Proof 333.  Suppose the source boundary
moment has a root-sandwiched expansion

```text
M(z)=exp(-z/2)M_+ +O(exp(-3z/2)).                    (BR.12)
```

The first term in `(BR.11)` has no half-density residue, because

```text
integral exp(-u/2)(Q phi)(u)du=0.                   (BR.13)
```

The compressed product leaves precisely

```text
-exp(-z/2)
 Tr(G^(-1)M_+G^(-1)M_(Q,phi)(0)).                   (BR.14)
```

Therefore the complete far-tail gain is equivalent to the single scalar
boundary-row orthogonality

```text
Tr(G^(-1)M_+G^(-1)M_(Q,phi)(0))=0.                  (BR.15)
```

Equation `(BR.15)`, plus an `O(exp(-3z/2))` remainder in the legal
root-sandwiched trace topology, is sufficient for the complete covariance.
There is no need to estimate an arbitrary two-variable kernel after this
reduction.

## 5. Exact source theorem now needed

If the residue has finite rank

```text
M_+=sum_(j=1)^r |a_j><b_j|,                          (BR.16)
```

then `(BR.15)` reduces to finitely many boundary matrix coefficients

```text
<b_j,G^(-1)M_(Q,phi)(0)G^(-1)a_j>.                  (BR.17)
```

The desired source identification is that these boundary rows are the two
half-density Mellin characters

```text
u -> exp(u/2),
u -> exp(-u/2),                                      (BR.18)
```

or finite linear combinations of them.  Since `Q` annihilates both
characters, `(BR.17)` then vanishes exactly.

Burnol constructs the boundary distributions `A_lambda,B_lambda`, proves
that they have the Sonin property, and identifies their completed Mellin
transforms with the de Branges structure functions.  CC20 independently
shows that the explicit archimedean and prolate static coefficients have
their first boundary mode at half-density.  These source facts make
`(BR.18)` the correct next calculation, but neither paper states `(BR.15)`
for the centered Schur moment.

Relevant primary sources:

```text
Burnol, arXiv:math/0208121:
https://arxiv.org/abs/math/0208121

Connes--Consani, arXiv:2006.13771,
source labels spectral, sonine0, sonineQbis, rapid-decay:
https://arxiv.org/abs/2006.13771
```

The next proof must calculate `(BR.17)` from those actual boundary
distributions.  It must not store `(BR.15)` as a premise.

## 6. Non-periodic diagnostic and its limit

The companion probe discretizes the genuine even cosine transform on
`[0,1]` in an orthonormal shifted-Legendre basis.  It computes all four blocks

```text
M(t)=
 [[P U_t P,         P U_t Fourier P],
  [P Fourier U_t P, P U_(-t) P]]                    (BR.19)
```

and evaluates the Schur difference before taking its trace.  The top
finite-window Fourier eigenvalue converges to the CC20 value

```text
lambda_0=0.999971376267...,
1/(1-lambda_0)=34936.04... .                         (BR.20)
```

That strict-angle conditioning is real, not a numerical bug.  It amplifies
any truncation that separates the two terms in `(BR.6)`.  The static
`Q`-paired trace converges rapidly across polynomial sizes, while the small
Schur residual changes sign and has not stabilized at a rate that can certify
either `exp(-z/2)` or `exp(-3z/2)`.

Representative `integration_order=320` values are:

```text
+------+-----+----------------+----------------+----------------+
| size | z   | Q static       | Q product      | Q covariance   |
+------+-----+----------------+----------------+----------------+
|   32 | 3.0 | -4.193541e-2   | -4.003659e-2   | -1.898824e-3   |
|   40 | 3.0 | -4.193541e-2   | -4.290807e-2   | +9.726605e-4   |
|   48 | 3.0 | -4.193541e-2   | -4.150275e-2   | -4.326665e-4   |
+------+-----+----------------+----------------+----------------+
```

The strong static/product cancellation is visible.  The residual is not
converged, so it is not evidence for `(BR.15)`.  This is also a new guard:
a periodic model or a low-order Galerkin tail fit cannot decide the boundary
row.

Run without a Lean build:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/334_burnol_schur_tail_probe.py \
  --sizes 32,40,48 --integration-order 320 \
  --quadrature-order 48 --displacements 2.5,3,3.5,4
```

## 7. Consequence for Gate 3U

The corrected far/near split is

```text
far displacement:
  prove the boundary expansion (BR.12);
  identify its boundary rows by (BR.18);
  discharge the one scalar residue (BR.15);
  obtain the next half-density tail for the complete covariance;

near displacement:
  retain Proof 289's complete-prime telescope and Proof 290's finite path;
  do not replace the stopped product by the boundary Gram truncation. (BR.21)
```

Proof 334 replaces the vague instruction "control the compressed product" by
one exact source calculation.  It does not close the near stopped-product
estimate, Gate 3U, the finite-`S` sign, Burnol's identity, or RH.

## 8. Successor correction: Proof 335

Proof 335 proves the formerly open boundary-row identity `(BR.15)`.  The weak
boundary moment residue is rank one with

```text
a=(epsilon,2 ell),
b=(ell,epsilon/2),

G^(-1)a=(epsilon,0),
G^(-1)b=(0,epsilon/2).
```

The compressed residue therefore reads only the `21` boundary kernel
`2 exp(-u/2)`, and its pairing with `Q phi` is exactly zero.  The active far
bottom is now the uniform next-order Schur remainder `(BS.26)`, not the
leading compressed residue.  See
`docs/proofs/335_compressed_half_density_residue_cancellation.md`.
