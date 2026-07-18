# Proof 371: positive-detector root commutator

Date: 2026-07-18

Status: exact factorization of the moving variance for a positive detector
`W=C* C` through the two off-diagonal blocks of the single root `C`.  The
detector-row Hilbert--Schmidt energy is bounded by the root commutator with the
moving projection, without treating the raw whole-line root as
Hilbert--Schmidt.

This reduces Proof 370's weighted variance theorem to a root-commutator row.
It does not prove that row uniformly in the Euler prefix.  Gate 3U, the
finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| positive detector                             | `W=C* C`                 |
| detector crossing                             | two root off-diagonals   |
| raw `CP` as Hilbert--Schmidt                   | not used                 |
| detector S2 cost                              | root commutator bound    |
| explicit Gram inverse                         | absent                   |
| uniform moving root commutator                | open                    |
| finite certificate                            | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Root blocks

Let `P` be an orthogonal projection and write `P_perp=I-P`.  For a bounded
root operator `C`, define

```text
X=P_perp C P,
Y=P C P_perp.                                      (RC.1)
```

The commutator has only these two off-diagonal blocks:

```text
[C,P]=X-Y.                                         (RC.2)
```

If `[C,P]` is Hilbert--Schmidt, orthogonality of its two corners gives

```text
norm([C,P])_2^2=norm(X)_2^2+norm(Y)_2^2.           (RC.3)
```

## 3. Positive detector crossing

Put

```text
W=C* C,
D_W=P_perp W P.                                    (RC.4)
```

Insert `P+P_perp` between the two roots:

```text
D_W
 =(P C P_perp)* (P C P)
  +(P_perp C P_perp)* (P_perp C P).                (RC.5)
```

Every term in `(RC.5)` contains one genuine root crossing.  Neither diagonal
root block is asserted to be Hilbert--Schmidt.

## 4. Hilbert--Schmidt estimate

The ideal property and `(RC.3)` imply

```text
norm(D_W)_2
 <=norm(C)(norm(Y)_2+norm(X)_2)
 <=sqrt(2) norm(C) norm([C,P])_2.                   (RC.6)
```

Therefore

```text
norm(D_W)_2^2
 <=2 norm(C)^2 norm([C,P])_2^2.                    (RC.7)
```

If `V:X->H` is an isometry onto `Ran(P)`, then

```text
norm((I-P)W V)_2=norm(D_W)_2.                       (RC.8)
```

Equations `(RC.7)--(RC.8)` apply directly to Proof 370's moving frame.

## 5. Compatibility with compact support

For the selected compact root `C=C_g`, the kernel of `[C_g,E]` is supported
only where the two variables lie on opposite sides of a physical boundary
and differ by at most `B_root`.  Thus the root commutator, unlike `C_gE`, has
finite Hilbert--Schmidt mass.

Proof 259's obstruction remains respected:

```text
norm(C_g E)_2=infinity
```

for a nonzero whole-line root.  The proof of `(RC.7)` never invokes that
forbidden norm.

## 6. New detector-row target

For the canonical midpoint projections `M_j`, Proof 371 reduces the detector
row to

```text
sum_(log(p_j)<=L) 1/(p_j-1) *
 norm([C_g,M_j])_2^2

 <=C(1+L+B_root)^d norm(g)_(H^r)^2.                (RC.9)
```

The factor `2 norm(C_g)^2` from `(RC.7)` is polynomially controlled by the
root Sobolev norm.  No Gram inverse or positive-detector square remains in
`(RC.9)`.

## 7. Reproducible certificate

The companion probe checks

```text
the two-block commutator identity `(RC.2)--(RC.3)`;
the detector factorization `(RC.5)`;
the Hilbert--Schmidt estimate `(RC.7)`;
the moving-isometry equality `(RC.8)`.              (RC.10)
```

Run only in the unified five-batch verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/371_positive_detector_root_commutator_probe.py
```

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| detector variance -> root commutator           | closed `(RC.7)`          |
| raw root infinite-mass guard                  | preserved                |
| moving midpoint root row `(RC.9)`              | open                    |
| target two-support factorization               | next batch              |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
