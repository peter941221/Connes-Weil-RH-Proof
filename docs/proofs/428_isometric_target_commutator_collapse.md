# Proof 428: Isometric target-commutator collapse

Date: 2026-07-20

Status: exact source-coordinate strengthening of Proof 427.  After absorbing
Burnol's base weight into its isometric frame, the moving weighted complement
becomes the pullback of the actual target Gram projection.  The completed
boundary difference then reduces to one inverse-transport-sandwiched target
detector commutator.

This proof does not establish the uniform canonical-family estimate, close
Gate 3U, prove the finite-`S` sign, prove Burnol's identity, or prove RH.

## 1. Result

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| absorb `h_0` into Burnol's isometric frame            | exact source input   |
| moving oblique complement = pulled-back target band   | exact                |
| explicit endpoint Gram inverse disappears             | exact                |
| completed response = one target commutator             | exact                |
| inverse transport may use Markov normalization         | exact scalar gauge   |
| remaining right transported frame is uniformly tame   | not proved           |
| Proof 416 `(EN.7)` / Gate 3U / RH                     | open / open / open   |
+------------------------------------------------------+----------------------+
```

The ownership chain is now

```text
two weighted Burnol semicommutators
  -> Proof 427 moving weighted complement
  -> pull back the actual target projection
  -> cancel the transported-frame adjoint branch
  -> one target detector commutator.                    (IT.1)
```

## 2. Absorb the base Burnol weight

Proof 407 has

```text
M_0=g_0 K_Theta,
U_g f=g_0 f,
A_Theta(|g_0|^2)=I.                                   (IT.2)
```

Thus `U=U_g` is an isometry from the fixed model carrier into the physical
Burnol carrier:

```text
U*U=I,
P_0=UU*.                                              (IT.3)
```

Let `T=T_S` be the complete causal Euler transport, `A=T^-1`, and set

```text
G=U*T*T U,
P_1=T U G^-1 U*T*.                                    (IT.4)
```

Here `P_1` is the canonical orthogonal Gram projection onto `T M_0`.  In the
formal Lean algebra, orthogonality is not postulated; the two Gram inverse
identities prove exactly the range and corange relations used below:

```text
P_1 T U=T U,
U*T*(I-P_1)=0.                                        (IT.5)
```

## 3. Pull back the moving complement

The new weighted retraction and its ambient oblique projection are

```text
R_1=G^-1 U*T*T,
O_1=U R_1.                                            (IT.6)
```

Because `AT=I`, direct multiplication gives

```text
A(I-P_1)T
 =I-U G^-1 U*T*T
 =I-O_1.                                              (IT.7)
```

Proof 427's moving-complement identity, with old weight `I`, is

```text
R_1-U*
 =U*(T*T-I)(I-O_1).                                   (IT.8)
```

Insert `(IT.7)`.  Since `TA=I`,

```text
(T*T-I)A=T*-A.                                        (IT.9)
```

The `T*` branch dies against `(IT.5)`, leaving the exact inverse-transport
crossing

```text
R_1-U*
 =-U*A(I-P_1)T.                                      (IT.10)
```

No determinant, trace cycle, norm estimate, or limiting argument occurs in
`(IT.7)--(IT.10)`.

## 4. One target detector commutator

Let `W` be the compact-root detector.  Euler convolution commutes with it:

```text
TW=WT.                                                (IT.11)
```

Since `P_1TU=TU` and `P_1^2=P_1`,

```text
(I-P_1)W T U
 =(I-P_1)[W,P_1]T U,                                 (IT.12)

[W,P_1]=W P_1-P_1 W.
```

Multiplying `(IT.10)` by `WU` and using `(IT.11)--(IT.12)` proves

```text
(R_1-U*)WU
 =-U*A(I-P_1)[W,P_1]T U.                            (IT.13)
```

Equation `(IT.13)` is the complete normalized boundary-form difference from
Proof 415 after the base Burnol weight has been absorbed into `U_g`.  It has
three useful properties:

```text
the target projection is the actual Gram projection;
the detector appears only through one target commutator;
the explicit compressed Gram inverse is absent.        (IT.14)
```

For the route's scalar normalization, replace `T` by `cT` and `A` by
`c^-1 A`.  The two scalar factors in `(IT.13)` cancel, so `A` may be chosen as
Proof 253's Markov contraction without changing the owner.

## 5. What the collapse does not bound

Proof 376 controls the compact-root commutator of every nearly invariant
target range.  Equation `(IT.13)` therefore aligns the detector factor with an
existing source theorem.  It does not authorize

```text
norm(U*A) norm([W,P_1]) norm(TU)                     (IT.15)
```

as the Gate estimate.  The right frame `TU` still contains the complete Euler
history, and separating `(IT.13)` into factor norms loses the same signed
Gram cancellation rejected by Proofs 255, 260, 416, and 417.

The Proof 417 rank-one family makes this visible.  With

```text
epsilon=exp(-M),
U=(sqrt(1-epsilon),sqrt(epsilon)),
T=diag(1,epsilon^-1/2),
A=diag(1,epsilon^1/2),
W=diag(0,1),                                          (IT.16)
```

the old detector crossing is small, while `P_1` rotates to an order-one
angle and `(IT.13)` remains

```text
1/(2-epsilon)-epsilon ->1/2.                         (IT.17)
```

Thus target-commutator ownership does not create the missing `p^-1/2` to
`p^-1` gain prime by prime.  The complete canonical-family signed pairing must
still be estimated before one absolute value.

## 6. Lean ownership

The module

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSIsometricTargetCrossing.lean
```

formalizes `(IT.5)--(IT.13)` over an arbitrary noncommutative ring.  Its audit
module is

```text
ConnesWeilRH/Dev/CCM24FiniteSIsometricTargetCrossingAudit.lean.
```

The formal theorem records only the ordered algebra.  The continuous route
must still instantiate `U` with Burnol's isometry, `P_1` with the genuine
transported projection, and the final product with Proof 261's already
completed trace-class pairing.

## 7. Literature pressure test

Liang--Partington's current compressed-shift analysis gives the exact source
coordinate theorem used here:

```text
Y. Liang and J. R. Partington,
Spectra and invariant subspaces of compressed shifts on nearly invariant
subspaces,
Theorem 1.2 and Proposition 2.3,
https://arxiv.org/abs/2506.18646
```

Their Theorem 1.2 proves that compression to `h K_Theta` is unitarily
equivalent to the `|h|^2`-weighted truncated Toeplitz operator on `K_Theta`.
This supports `(IT.2)--(IT.3)`.  Proposition 2.3 proves that the compressed
single shift is a rank-one perturbation of the model compressed shift.

That result does not estimate `(IT.13)`.  The route detector is a general
compact-root multiplier, `(IT.13)` contains the ambient target projection and
the complete Euler frame, and only the completed relative product is known to
be trace class.  The paper proves no Schatten completion, relative projection
trace, canonical Euler-family estimate, or polynomial root-support constant.
The rank-one compressed-shift statement therefore cannot replace Proof 416
`(EN.7)`.

## 8. Route verdict

```text
What is closed:
  base-weight absorption into an isometric source frame;
  moving-oblique to actual-target complement pullback;
  cancellation of the explicit Gram-inverse branch;
  one target detector-commutator owner.

What remains open:
  continuous instantiation inside the legal completed trace;
  a canonical-family signed estimate for `(IT.13)`;
  Proof 416 `(EN.7)`, Gate 3U, and the finite-S sign;
  same-object arithmetic identity and negative-owner integration;
  Burnol's all-zero identity and unconditional RH.
```

The active analytic object is now the whole product on the right of
`(IT.13)`.  Neither the Markov inverse, the target commutator, nor the
transported frame may be estimated separately.

## 9. Verification

The Windows source was copied one way into the isolated Ubuntu 24.04 ext4
verification directory.  The batched Lean acceptance is

```text
+----------------------------------------------+------+
| target                                       | jobs |
+----------------------------------------------+------+
| focused Proof 428 axiom audit                | 1409 |
| `ConnesWeilRH.Source.CCM25Concrete` aggregate | 3703 |
| full repository                              | 3784 |
+----------------------------------------------+------+
```

All nine audited public theorems depend exactly on `[propext]`.  No `sorryAx`,
new project axiom, placeholder proof, or new warning was introduced.  The
warnings replayed by the aggregate and full build belong to existing modules.
