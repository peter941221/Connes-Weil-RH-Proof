# Proof 372: two-support prolate renewal

Date: 2026-07-18

Status: exact two-projection renewal identity for a root crossing between the
Sonin intersection and its quotient complement.  The explicit prolate
commutator is eliminated before estimation; the remaining prolate operator is
the Gram defect of the genuine second-support boundary frame.

This identifies the precise target-angle obstruction in Proof 371's moving
root row.  It does not prove a uniform inverse bound for that boundary Gram.
Gate 3U, the finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| two support projections                       | exact geometry           |
| Sonin/quotient root crossing                  | signed renewal           |
| explicit `[C,K_prol]`                         | eliminated               |
| remaining prolate factor                      | boundary Gram defect     |
| outer/second boundary ownership               | explicit                |
| uniform moving angle bound                    | open                    |
| finite certificate                            | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Two-support geometry

Let `E,Q` be orthogonal projections.  Let `R` be the projection onto their
closed intersection and put

```text
R<=E,
R<=Q,
P=E-R.                                            (PR.1)
```

The prolate operator on the quotient carrier is

```text
K=P Q P.                                          (PR.2)
```

The standard two-projection identity is

```text
E Q E=R+K.                                        (PR.3)
```

No trace or compactness assumption is needed for the algebra below.

## 3. Root-crossing renewal

Let `C` be any bounded root operator and define

```text
D=R C P,
[C,Q]=C Q-Q C.                                    (PR.4)
```

Since `RQ=R`,

```text
D=R Q C P=R C Q P-R[C,Q]P.                        (PR.5)
```

Decompose the intermediate vector by `E+(I-E)`.  Equation `(PR.3)` gives

```text
E Q P=K.                                          (PR.6)
```

Consequently

```text
D
 =R C(I-E)Q P+D K-R[C,Q]P,                       (PR.7)

D(I-K)
 =R C(I-E)Q P-R[C,Q]P.                            (PR.8)
```

Equation `(PR.8)` is the prolate renewal.  Its right side contains only a
completed outer boundary crossing and a completed second-support
commutator.  No separate `[C,K]` occurs.

## 4. Boundary Gram meaning

The second-support boundary map

```text
L=(I-Q)P : Ran(P)->Ran(I-Q)                        (PR.9)
```

has Gram operator

```text
L*L=P(I-Q)P=I_P-K.                                (PR.10)
```

When the two supports have strict angle, `I_P-K>0`, and the polar normalized
boundary frame is

```text
U_L=(I-Q)P(I_P-K)^(-1/2),
U_L*U_L=I_P.                                       (PR.11)
```

Thus solving `(PR.8)` by `(I-K)^(-1)` is exactly a boundary-frame Gram
problem.  It is not an unrelated prolate remainder estimate.

## 5. Moving CCM24 specialization

For every literal Euler prefix, take

```text
E   = fixed radial support,
Q_j = actual moving Fourier-support projection,
R_j = actual moving Sonin projection,
P_j = E-R_j,
K_j = P_j Q_j P_j.                                 (PR.12)
```

The existing Lean theorem
`parameterizedProlateRemainder_eq_factor` owns `(PR.2)--(PR.3)` on the
common-log carrier.  Applying `(PR.8)` to the compact root gives

```text
R_j C_g P_j(I-K_j)
 =R_j C_g(I-E)Q_jP_j-R_j[C_g,Q_j]P_j.             (PR.13)
```

The reverse root crossing follows by taking adjoints and replacing `g` by
the route's reflected/conjugated root.

## 6. What has improved

Proof 363 factors `[W,K_prol]` through `K_prol^(1/2)`, whose moving trace cost
is not known uniformly.  Equation `(PR.13)` avoids that target trace
altogether.  The remaining problem is sharper:

```text
control the two boundary terms after polar normalization by
(I-K_j)^(-1/2), uniformly in the prefix.             (PR.14)
```

The inverse in `(PR.14)` must stay paired with the signed outer-minus-second
boundary numerator.  Bounding it separately recreates the rejected angle
condition number.

## 7. Reproducible certificate

The companion probe constructs two projections with a prescribed nontrivial
intersection and principal angles.  It checks

```text
the compression identity `(PR.3)`;
the renewal `(PR.8)`;
the boundary Gram `(PR.10)`;
the polar isometry `(PR.11)`.                       (PR.15)
```

Run only in the unified five-batch verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/372_two_support_prolate_renewal_probe.py
```

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| moving prolate commutator                     | removed by renewal       |
| signed outer-minus-second numerator            | exact `(PR.13)`          |
| prolate inverse meaning                       | boundary Gram            |
| uniform polar-normalized boundary row          | open                    |
| midpoint detector consumer                    | next batch              |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
