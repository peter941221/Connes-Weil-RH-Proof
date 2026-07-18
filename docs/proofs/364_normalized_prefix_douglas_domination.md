# Proof 364: normalized-prefix Douglas domination

Date: 2026-07-18

Successor audit: Proof 365 invalidates the route instantiation of the
commuting-prefix premise used in `(NP.6)`.  The generic Douglas and
condition-number statements remain correct, but `(NP.8)` is not the complete
quotient covariance.  Proof 369 supplies the corrected covariance with the
mandatory compression-commutator term.

Status: exact consolidation of Proofs 360--363 into the one remaining
source-side positive operator inequality.  The fixed outer, reflected
second-support, and prolate branches have a common Hilbert--Schmidt owner,
but the complete owner is still dressed by the inverse Euler prefix and its
compressed Gram inverse.

An isometric normalized prefix does not by itself control that dressing.  A
commuting two-dimensional guard makes the required Douglas constant approach
the full prefix condition number.  The actual causal half-line and shorted-
metric geometry must therefore remove the bad Gram directions in the complete
signed bracket.  That source theorem is open.  Gate 3U, the finite-`S` sign,
Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| fixed outer/reflected/prolate HS owner         | Proofs 361--363          |
| normalized-prefix crossing identity            | Proof 358               |
| HC.10 Douglas reformulation                    | exact                    |
| compressed Gram inverse                        | retained inside owner   |
| isometric-frame-only uniform estimate          | false, 2D guard         |
| causal source covariance domination            | open, sole near bottom  |
| finite certificate                             | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
## 2. Literal normalized prefix

Let `U_0:H_0->H` be Proof 343's fixed quotient isometry and put

```text
P_K=U_0 U_0*.                                       (NP.1)
```

For the complete inverse Euler prefix `A_<j`, define

```text
H_<j=U_0* A_<j* A_<j U_0,
V_<j=A_<j U_0 H_<j^(-1/2),
P_<j=V_<j V_<j*.                                    (NP.2)
```

Then

```text
V_<j* V_<j=I.                                       (NP.3)
```

This identity controls `A_<j U_0 H_<j^(-1/2)` on the fixed quotient
subspace.  It says nothing by itself about `A_<j` on a vector first sent into
`Ran(I-P_K)` by a boundary crossing.

## 3. Insert the fixed common owner

Proofs 361--363 construct one fixed direct-sum Hilbert--Schmidt owner after
the complete source signs are retained:

```text
mathcalB_W=B_fixed A_fixed.                         (NP.4)
```

Here `B_fixed` contains the literal outer-minus-Sonin-plus-prolate signs and
bounded support/scattering dressings.  The common right factor satisfies a
square budget of the form

```text
norm(A_fixed)_2^2
 <=C_boundary B_root norm(g)_2^2
   +Tr(K_prol)(1+norm(W_g)^2).                      (NP.5)
```

The moving old-projection crossing from Proof 358 is

```text
D_<j
 :=(I-P_<j) A_<j (I-P_K)
    mathcalB_W U_0 H_<j^(-1/2)

  =(I-P_<j) A_<j (I-P_K)
    B_fixed A_fixed U_0 H_<j^(-1/2).                (NP.6)
```

Equation `(NP.5)` does not bound `(NP.6)`: the varying
`H_<j^(-1/2)` occurs on the right of the fixed owner, while `A_<j` acts on
the crossed output on the left.

## 4. The complete covariance inequality

Let `A_L` denote Proof 357's common near-window envelope, read on the same
fixed `H_0` source coordinate as `(NP.6)`.  Proof 360 applies without any
further trace manipulation.  The factorization required by Proof 359,

```text
D_<j=C_<j A_L,
sup_(log(p_j)<=L) norm(C_<j)
 <=C(1+L+B_root)^d,                                (NP.7)
```

is equivalent to the following family of positive operator inequalities on
`H_0`:

```text
H_<j^(-1/2) U_0* A_fixed* B_fixed*
  (I-P_K) A_<j* (I-P_<j) A_<j (I-P_K)
  B_fixed A_fixed U_0 H_<j^(-1/2)

 <=C^2(1+L+B_root)^(2d) A_L* A_L.                  (NP.8)
```

Equivalently, for every `x in H_0`,

```text
norm(
  (I-P_<j) A_<j (I-P_K)
  B_fixed A_fixed U_0 H_<j^(-1/2) x
)

 <=C(1+L+B_root)^d norm(A_L x).                    (NP.9)
```

This is the normalized-prefix Douglas domination.  It is the full expanded
form of `(HC.10)`, not an additional hypothesis.  In particular it includes
the mandatory kernel condition

```text
ker(A_L) subset ker(D_<j).                          (NP.10)
```

The signs in `B_fixed`, both boundary orientations, the prolate correction,
the prefix Gram normalization, the half-density residue cancellation, and
the boundary trace anomaly must remain inside `(NP.8)` before an absolute
value or branch norm is taken.

## 5. Why prefix isometry is insufficient

The equality `(NP.3)` only gives

```text
norm(A_<j U_0 H_<j^(-1/2)x)=norm(x).                (NP.11)
```

The vector entering the left prefix in `(NP.6)` is instead

```text
(I-P_K) mathcalB_W U_0 H_<j^(-1/2)x.               (NP.12)
```

It lies in the crossed complement, where `(NP.11)` supplies no comparison.
The separate estimate

```text
norm(A_<j>) norm(H_<j^(-1/2))                       (NP.13)
```

is a prefix condition number.  Multiplying such bounds over primes recreates
the forbidden half-power growth from Proof 356.

## 6. Commuting two-dimensional guard

The obstruction already occurs with a detector which commutes with the
prefix.  Let

```text
H=C^2,
A_kappa=diag(kappa^(-1),1),  kappa>1,
W=diag(0,1),
u_theta=(cos(theta),sin(theta)),
U_theta z=z u_theta.                                (NP.14)
```

Put `P_theta=U_theta U_theta*` and

```text
h_theta=U_theta* A_kappa* A_kappa U_theta
       =kappa^(-2)cos(theta)^2+sin(theta)^2,

V_theta=A_kappa U_theta h_theta^(-1/2),
P_theta^A=V_theta V_theta*.                         (NP.15)
```

Thus `V_theta*V_theta=1`, and `[W,A_kappa]=0`.  The fixed and normalized
crossings are

```text
F_theta=(I-P_theta) W U_theta,

D_theta=(I-P_theta^A) A_kappa (I-P_theta)
        F_theta h_theta^(-1/2)
       =(I-P_theta^A)W V_theta.                     (NP.16)
```

Writing `t=tan(theta)`, direct calculation gives

```text
norm(D_theta)/norm(F_theta)
 =kappa(1+t^2)/(1+kappa^2 t^2)
 ->kappa as theta->0.                               (NP.17)
```

Therefore the least constant in

```text
D_theta*D_theta<=C^2 F_theta*F_theta                (NP.18)
```

approaches the full condition number `kappa`, although the normalized frame
is exactly isometric and the detector commutes with the prefix.  This guard
rules out deriving `(NP.8)` from `(NP.3)`, commutation, and the fixed
Hilbert--Schmidt budget alone.

## 7. Exact remaining source theorem

The only remaining near producer is `(NP.8)`.  A successful proof must use
the actual one-sided causal half-line action and the shorted CC20 metric to
show that the complete signed physical bracket does not feed the bad Gram
directions exposed by `(NP.14)--(NP.18)`.

The permitted proof order is

```text
retain the complete physical bracket B_fixed
  -> apply the causal prefix and compressed Gram normalization together
  -> prove the source covariance `(NP.8)`
  -> invoke Douglas once
  -> take the common-envelope HS norm and harmonic prime weights.           (NP.19)
```

Neither `norm(H_<j^(-1/2))`, a branchwise Douglas constant, nor the bare
isometry `(NP.3)` can replace the source covariance theorem.

Once `(NP.8)` is proved, Proof 360 gives `(NP.7)`, Proof 359 closes the near
row, and Proof 336 supplies the far lane.  At present `(NP.8)` is open, so
Gate 3U is not closed.

## 8. Reproducible certificate

The companion finite probe checks

```text
the normalized-frame isometry `(NP.3)`;
the transported crossing `(NP.6)` for commuting prefix/detector data;
the fully expanded covariance on the left of `(NP.8)`;
the exact two-dimensional ratio `(NP.17)`;
condition-number amplification despite exact isometry. (NP.20)
```

Run only in the unified verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/364_normalized_prefix_douglas_domination_probe.py
```

The finite guard proves that no carrier-independent contraction follows from
the preceding abstract facts.  It does not prove or disprove the
source-specific inequality `(NP.8)`.

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| fixed physical HS bundle                      | closed, Proofs 361--363  |
| complete prefix/Gram covariance owner          | exact `(NP.8)`           |
| abstract isometry-based uniformity             | false `(NP.17)`          |
| causal/shorted-metric domination `(NP.8)`       | open, sole near bottom  |
| Proof 359 near consumer                        | ready after `(NP.8)`    |
| Proof 336 far lane                             | closed                   |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
