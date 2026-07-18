# Proof 343: polar-normalized quotient owner

Date: 2026-07-18

Status: exact polar normalization of Proof 342's remaining quotient-crossing
frame.  The fixed Burnol angle `I-F_0^2` is a coordinate artifact in the
relative endpoint trace and cancels completely.  The only inverse left is the
compressed Euler metric on one fixed, orthonormally represented quotient
subspace.

This is a stronger owner reduction, not a uniform estimate.  It does not
identify the quotient subspace with an explicit standard model space, prove
Gate 3U, prove the finite-S sign, prove Burnol's identity, or prove RH.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| Proof 342 quotient frame                       | exact                     |
| fixed Burnol Gram polar factor                 | cancels exactly           |
| fixed quotient subspace                        | orthonormal owner         |
| remaining inverse                             | compressed Euler metric   |
| explicit inner/model-space identification      | open                      |
| uniform compact-root signed bound              | open, Gate 3U             |
| RH                                             | unproved                  |
+------------------------------------------------+---------------------------+
```

The reduction is

```text
L_S=A_S L_0
  -> polar-decompose L_0
  -> cancel its fixed positive coordinate factor
  -> compress A_S* A_S to one fixed quotient subspace.          (PN.1)
```

The cancellation in `(PN.1)` happens inside the complete relative trace.  It
does not estimate either endpoint separately.

## 2. Factor the moving crossing through the source crossing

Keep Proof 342's notation.  On `Ran(I-P)`, put

```text
V_C=(I-P)V(I-P),
H_0=(I-P)mathcalF J.                                  (PN.2)
```

Proof 342 gives

```text
L_S=mathcalF V_C H_0,
L_0=mathcalF H_0.                                     (PN.3)
```

Define the quotient Euler transport on `Ran(I-Q)` by

```text
A_S=mathcalF V_C mathcalF.                            (PN.4)
```

Then

```text
L_S=A_S L_0.                                          (PN.5)
```

No extension of `A_S` outside `Ran(I-Q)` is used in the formulas below.

## 3. Polar-normalize the fixed Burnol crossing

The source Gram is

```text
Sigma_0=L_0*L_0=I-F_0^2>0.                            (PN.6)
```

Set

```text
U_0=L_0 Sigma_0^(-1/2),
K=Ran(U_0)=Ran(L_0).                                  (PN.7)
```

Then `U_0:H_0 -> K` is unitary onto its closed range.  In particular,

```text
L_0=U_0 Sigma_0^(1/2),
L_S=A_S U_0 Sigma_0^(1/2).                            (PN.8)
```

The fixed subspace has the intrinsic description

```text
K=Ran(I-Q) minus-orthogonal Ran(R),                    (PN.9)
```

because Proof 342 gives the orthogonal decomposition

```text
I-R=Q+projection_K.                                   (PN.10)
```

Equation `(PN.9)` is enough for ownership.  Calling `K` a standard Hardy
model space would additionally require an explicit invariant-subspace/inner-
function identification, which is not currently proved in the route.

## 4. Fixed Gram cancellation

Define operators on `H_0` by

```text
H_S=U_0* A_S* A_S U_0,
N_S(W)=U_0* A_S* W A_S U_0.                           (PN.11)
```

Equations `(PN.8)--(PN.11)` give

```text
Sigma_S=L_S*L_S
 =Sigma_0^(1/2) H_S Sigma_0^(1/2),                    (PN.12)

L_S*W L_S
 =Sigma_0^(1/2) N_S(W) Sigma_0^(1/2).                 (PN.13)
```

Substitute these two identities into Proof 342 `(FC.17)`.  The fixed
`Sigma_0` factors form a bounded similarity.  Proof 261's completed relative
trace is invariant under that similarity, so

```text
Q_S(eta,xi)
 =Tr_(H_0)[
    H_S^(-1)N_S(C_xi* C_eta)
   -U_0* C_xi* C_eta U_0].                            (PN.14)
```

Thus neither `Sigma_0^(-1)` nor the large coefficient associated with
Burnol's lowest prolate angle is part of the analytic Gate constant.  The
fixed angle was only a nonorthonormal frame coordinate.

The inverse in `(PN.14)` is still essential:

```text
H_S^(-1)
 =(U_0* A_S* A_S U_0)^(-1).                           (PN.15)
```

It is the compressed Euler metric after the complete product.  Proof 254's
guard forbids replacing `(PN.15)` by an ambient inverse or a probability
average of pointwise inverses.

## 5. Projection readback

Let `P_K=U_0U_0*`.  The orthogonal projection onto `A_S K` is

```text
P_(A_SK)
 =A_S U_0 H_S^(-1)U_0* A_S*.                         (PN.16)
```

Rectangular cycling in the already legal root-sandwiched difference gives

```text
Q_S(eta,xi)
 =Tr_H[C_xi* C_eta(P_(A_SK)-P_K)].                    (PN.17)
```

Equation `(PN.17)` is the same complete endpoint as Proof 341 `(BY.10)` and
Proof 342 `(FC.17)`.  Its value is not changed by the polar normalization.

## 6. Research audit

The fixed compression in `(PN.14)` resembles a truncated Toeplitz operator
when `K` is represented as a Hardy model space.  The following survey gives
the standard definition and operator theory of such compressions:

```text
Garcia--Ross, Recent Progress on Truncated Toeplitz Operators,
arXiv:1108.1858
https://arxiv.org/abs/1108.1858
```

The searched literature does not provide the theorem required here.  Two
contracts are missing:

```text
1. an exact identification of the route's K and A_S with the paper's
   explicit model space and symbol;

2. an S-uniform relative determinant derivative bound for the finite
   almost-periodic Euler product with polynomial compact-support cost.       (PN.18)
```

The general Wiener--Hopf/Toeplitz determinant formulas in
Ehrhardt--Virtanen `arXiv:2407.21222` assume a specified factorization and
trace-class Hankel remainder.  They do not prove `(PN.18)` for the route.

## 7. Exact remaining theorem

For compact roots supported in `[-B_root,B_root]`, the Gate 3U bottom is now

```text
sup_(finite S)
 abs Tr_(H_0)[
   (U_0*A_S*A_SU_0)^(-1)
     U_0*A_S*C_xi*C_eta A_SU_0
   -U_0*C_xi*C_eta U_0]

 <=C(1+B_root)^d
   norm(eta)_(H^r) norm(xi)_(H^r).                   (PN.19)
```

All fixed Burnol conditioning has disappeared from `(PN.19)`.  A successful
proof must now use the actual half-line quotient action of `A_S` and compact
root support before the first absolute value.  A bound on
`||(U_0*A_S*A_SU_0)^(-1)||`, a generic model-space theorem, or separate
trace norms of the two terms does not close `(PN.19)`.

Proof 336 remains available for the fixed-source far-displacement part after
the complete near/far split is made inside `(PN.19)`.

## 8. Finite certificate

Proof 342's companion probe now also inserts an ill-conditioned source-frame
coordinate, polar-normalizes it, and compares `(PN.14)` with the direct
ambient projection response.  The coordinate condition number is deliberately
large while the response error remains at floating-point scale.

This verifies cancellation of a fixed frame Gram only.  It is not evidence
for an `S`-uniform lower bound on `(PN.15)`.

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| Proof 341/342 same-object endpoint             | retained                  |
| fixed Burnol angle inverse                     | eliminated exactly        |
| compressed complete Euler inverse              | remains                   |
| standard model-space identification            | not yet proved            |
| off-the-shelf determinant closure              | no matching theorem       |
| uniform signed estimate `(PN.19)`              | open, Gate 3U             |
| finite-S sign / Burnol identity / RH           | open / open / unproved    |
+------------------------------------------------+---------------------------+
```
