# Proof 390: Schur-frame polar cocycle

Date: 2026-07-18

Status: exact one-step identification of the source-owned Schur frame behind
the moving Gram normalization.  The raw inverse Euler frame is the canonical
graph isometry followed by the inverse Schur frame.  Its polar phase is
therefore explicit.  After harmless scalar normalization, the Schur frame is
a contraction with an exact positive defect formula.

This replaces the incorrect attempt to use the Julia transfer `Phi` itself as
the physical state transition.  It does not yet bound the complete detector
response or close Gate 3U.  The finite-`S` sign, Burnol's identity, and RH
remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| one inverse Euler range                       | canonical graph           |
| physical source-coordinate frame              | Schur frame `Z`          |
| raw inverse frame                             | `V Z^(-1)`               |
| Gram polar cocycle                            | polar phase of `Z^(-1)`  |
| normalized Schur frame                        | contraction              |
| normalized input defect                       | exact positive formula   |
| complete cascade / Gate 3U                    | open                    |
+------------------------------------------------+---------------------------+
```

## 2. Unitary colligation and graph

Let `P` be an orthogonal projection, `Q=I-P`, and let `U` be unitary.  In the
decomposition `Ran(P) direct-sum Ran(Q)`, write

```text
U=[[U_00,U_01],
   [U_10,U_11]].                                  (SF.1)
```

For `0<a<1`, put

```text
T=I-aU,
X=a(I-aU_11)^(-1)U_10,                            (SF.2)

Phi=U_00+U_01X.                                   (SF.3)
```

Proof 350 gives

```text
X*X=a^2/(1-a^2)(I-Phi*Phi).                       (SF.4)
```

Define the graph cosine, sine, and canonical isometry by

```text
C=(I+X*X)^(-1/2),
S=XC,
V=[C;S].                                          (SF.5)
```

Then `V*V=I` and `Ran(V)=T^(-1)Ran(P)`.

## 3. The exact Schur frame

The graph equation is

```text
X-a(U_10+U_11X)=0.                                (SF.6)
```

Apply `T` to `(SF.5)`.  The lower block vanishes by `(SF.6)`, while the upper
block is

```text
C-a(U_00C+U_01S)
 =(I-aPhi)C.                                      (SF.7)
```

Define the Schur frame

```text
Z=(I-aPhi)C.                                      (SF.8)
```

Equations `(SF.6)--(SF.8)` give the exact intertwining

```text
T V=iota_P Z.                                     (SF.9)
```

Both factors in `(SF.8)` are invertible: `C>0` and
`norm(aPhi)<1`.  Hence

```text
T^(-1)iota_P=V Z^(-1).                            (SF.10)
```

This is the physical inverse-Euler frame.  The Julia transfer `Phi` alone is
not its source coordinate.

## 4. Gram metric and polar phase

Let

```text
B=T^(-1)iota_P.                                   (SF.11)
```

Since `V` is isometric, `(SF.10)` gives

```text
B*B=Z^(-*)Z^(-1).                                 (SF.12)
```

The direct Gram-normalized frame is

```text
N=B(B*B)^(-1/2)=V Omega,                          (SF.13)

Omega
 =Z^(-1)(Z^(-*)Z^(-1))^(-1/2).                   (SF.14)
```

Thus `Omega` is exactly the unitary polar factor of `Z^(-1)`.  Proof 388's
unitary cocycle is no longer an unnamed coordinate discrepancy.

## 5. A source-owned contraction

Scalar multiplication does not change a transported range or its Gram polar
frame.  Define

```text
G=Z/(1+a).                                        (SF.15)
```

By `(SF.9)`,

```text
G*G=V*T*T V/(1+a)^2<=I,                           (SF.16)
```

because `norm(I-aU)<=1+a`.  Therefore `G` is a contraction on the literal
old source coordinate.

More precisely, unitarity gives

```text
(1+a)^2 I-T*T
 =a(2I+U+U*)
 =a(I+U*) (I+U).                                  (SF.17)
```

Combining `(SF.9)` and `(SF.17)`,

```text
I-G*G
 =a/(1+a)^2 V*(I+U*) (I+U)V.                     (SF.18)
```

Equation `(SF.18)` is an exact defect formula, not an operator-norm estimate.
It is positive and retains the complete one-step Euler denominator.

## 6. Why this is different from Proof 351

Proof 351 uses the contraction product of the Julia transfers `Phi_j`.  The
physical frame instead uses

```text
Z_j=(I-a_jPhi_j)C_j,
G_j=Z_j/(1+a_j).                                  (SF.19)
```

Both missing factors in `(SF.19)` matter:

```text
I-a_jPhi_j:
  the Schur complement of the Euler denominator;

C_j:
  the positive graph-coordinate normalization.   (SF.20)
```

Replacing `G_j` by `Phi_j` changes the Gram metric and recreates Proof 388's
kernel mismatch.

## 7. Reproducible certificate

The companion probe uses nonreducing random subspaces and unitary
colligations for `p=2,3,5`.  It checks

```text
the graph identity `(SF.4)` and isometry `(SF.5)`;
the Schur intertwining `(SF.9)`;
the raw inverse identity `(SF.10)`;
the Gram and polar formulas `(SF.12)--(SF.14)`;
contractivity and the exact defect `(SF.16)--(SF.18)`. (SF.21)
```

Run only after Proofs 390--394 are complete:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/390_schur_frame_polar_cocycle_probe.py
```

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| physical one-step source frame                | closed `(SF.8)`          |
| Gram polar cocycle                            | closed `(SF.14)`         |
| source contraction and defect                 | closed `(SF.18)`         |
| complete Schur cascade                        | next proof               |
| compact-root detector bound / Gate 3U          | open                    |
| finite-S sign / Burnol / RH                    | open / open / open       |
+------------------------------------------------+---------------------------+
```
