# Proof 380: midpoint self-adjoint root dilation

Date: 2026-07-18

Status: exact root-level reformulation of the positive midpoint detector
response.  A non-self-adjoint convolution root is embedded in its canonical
self-adjoint two-copy dilation.  The response is then one Hilbert--Schmidt
pairing between the root commutator corner and an explicit range-root
anticommutator corner.

This identifies the exact same-object factor still missing after Proof 378.
It does not prove that the range-root corner factors through Proof 357's one
common boundary input.  Gate 3U, the finite-`S` sign, Burnol's identity, and
RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| positive detector root split                  | exact                    |
| non-self-adjoint root                         | self-adjoint dilation   |
| detector `S_2` factor                         | `[C,M]` corners         |
| range factor                                  | explicit anticommutator |
| trace cycles                                  | legal after two `S_2` legs|
| common boundary-root factor                   | open                    |
| finite certificate                            | supplied                |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

The new exact contract is

```text
positive root response
  -> self-adjoint two-copy dilation
  -> midpoint off-diagonal decomposition
  -> one root commutator corner
  -> one range-root anticommutator corner
  -> common boundary localization only afterward.              (RD.1)
```

## 2. Self-adjoint root theorem

Let `P` be an orthogonal projection, put `Q=I-P`, and let

```text
A=A*,
P A P=0,
Q A Q=0.                                           (RD.2)
```

Thus

```text
R=Q A P,
A=R+R*.                                            (RD.3)
```

Let `G=G*` be bounded and define

```text
B=Q G P,
Y=Q(G A+A G)P.                                    (RD.4)
```

Whenever `B,Y` are Hilbert--Schmidt, all products below are trace class and

```text
Tr(G^2 A)=2 Re <B,Y>_(S_2).                        (RD.5)
```

To prove `(RD.5)`, write

```text
G=[[g_00,B*],
   [B,g_11]],

A=[[0,R*],
   [R,0]].                                         (RD.6)
```

Then

```text
Y=g_11 R+R g_00,                                   (RD.7)
```

and direct block multiplication gives

```text
Tr(G^2 A)
 =2 Re Tr[(g_00 B*+B* g_11)R]

 =2 Re Tr[B*(g_11R+R g_00)]
 =2 Re <B,Y>_(S_2).                                (RD.8)
```

The only cycle in `(RD.8)` moves `g_00` across a product of the two displayed
Hilbert--Schmidt factors.  It is therefore an ordinary trace-class cycle, not
a finite-section trace assumption.

The detector factor is exactly one half of the self-adjoint commutator:

```text
norm([G,P])_2^2=2 norm(B)_2^2.                     (RD.9)
```

## 3. Canonical dilation of a positive detector

Let `C` be an arbitrary bounded root and put

```text
W=C* C.                                            (RD.10)
```

On `H direct-sum H`, define

```text
G=[[0,C*],
   [C,0]],

G=G*,
G^2=[[C*C,0],
     [0,C C*]].                                    (RD.11)
```

Lift the midpoint and projection difference by

```text
P_tilde=P direct-sum P,
A_tilde=A direct-sum 0.                            (RD.12)
```

Then `(RD.2)` remains true and

```text
Tr(G^2 A_tilde)=Tr(W A).                           (RD.13)
```

Write the root blocks relative to `P direct-sum Q` as

```text
C_00=P C P,
C_01=P C Q,
C_10=Q C P,
C_11=Q C Q.                                       (RD.14)
```

The two components of the dilated detector corner are

```text
B_root=(C_10,C_01*),                               (RD.15)
```

while the two components of the range-root corner are

```text
Y_root=(C_11 R,R C_00*).                           (RD.16)
```

Consequently `(RD.5)` becomes

```text
Tr(C* C A)
 =2 Re[
    <C_10,C_11 R>_(S_2)
   +<C_01*,R C_00*>_(S_2)
  ].                                               (RD.17)
```

Moreover,

```text
norm(B_root)_2^2
 =norm(C_10)_2^2+norm(C_01)_2^2
 =norm([C,P])_2^2.                                 (RD.18)
```

Thus Proofs 375--378 control exactly the detector factor in `(RD.17)`.

## 4. Apply the canonical midpoint

For consecutive quotient projections `P_(j-1),P_j`, let `M_j` be Proof 354's
canonical midpoint and put

```text
A_j=P_j-P_(j-1),
R_j=(I-M_j)A_j M_j.                                (RD.19)
```

Proof 354 gives the hypotheses `(RD.2)--(RD.3)` with `P=M_j`.  For the compact
root `C_g`, define its four midpoint blocks by `(RD.14)`.  The literal step
response is therefore `(RD.17)`.

Proof 378 supplies

```text
sum_(log(p_j)<=L)
 norm(B_(root,j))_2^2/(p_j-1)

 <=C(1+L)(1+B_root)^d norm(g)_(H^3)^2.             (RD.20)
```

The still-open source theorem has two parts.  First insert one common root
without changing `(RD.17)`:

```text
Tr(C_g* C_g A_j)
 =2 Re <Bhat_(root,j),
          Ytilde_(root,j) A_root>_(S_2).           (RD.21)
```

Then align the inserted range root with the actual Julia column:

```text
Ytilde_(root,j) A_root
 =one bounded readout of
   S_j J_(j-1) Psi_(j-1) A_root.                  (RD.22)
```

where the same source-owned Hilbert--Schmidt `A_root` must be used for every
near prime.  Neither `(RD.21)` nor `(RD.22)` follows from unitary coordinate
changes alone.  Together they are the correct interface to Proof 351.

## 5. Why the dilation matters

Applying the midpoint identity directly to `W=C* C` hides the two root
orientations inside

```text
(I-M)W M.                                          (RD.22)
```

The dilation separates them without choosing a square root of the positive
Fourier multiplier:

```text
first copy:   C_10 paired with C_11 R;
second copy:  C_01* paired with R C_00*.            (RD.23)
```

Therefore the route keeps the original compact root and its reflected adjoint.
It does not replace them by the generally noncompact positive square root
`W^(1/2)`.

The same construction also prevents a false conclusion from `(RD.18)`.  A
Hilbert--Schmidt detector factor does not make either component of `(RD.16)`
Hilbert--Schmidt.  That property must come from the physical boundary owner.

## 6. Reproducible certificate

The companion probe constructs two strict-angle graph projections, their
canonical midpoint, and a nonnormal complex root.  It checks

```text
the midpoint off-diagonal decomposition;
the self-adjoint dilation identities `(RD.11)--(RD.13)`;
the two-copy root blocks `(RD.15)--(RD.16)`;
the exact pairing `(RD.17)`;
the commutator norm identity `(RD.18)`.              (RD.24)
```

Run only after Proofs 380--384 are complete:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/380_midpoint_selfadjoint_root_dilation_probe.py
```

The finite certificate verifies the block algebra.  It does not establish
the infinite-dimensional insertion/alignment `(RD.21)--(RD.22)`.

## 7. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| positive detector root split                  | exact `(RD.17)`          |
| detector root row                             | Proof 378 controls       |
| exact range-root target                       | `(RD.16)`                |
| common-root insertion/alignment                | open `(RD.21)--(RD.22)` |
| finite-S sign / Burnol / RH                    | open / open / open       |
+------------------------------------------------+---------------------------+
```
