# Proof 358: fixed-quotient commutator recombination

Date: 2026-07-18

Successor audit: Proof 365 shows that `(QR.9)` does not follow for Proof
343's actual quotient transport `A_S=mathcalF V_C mathcalF`.  Ambient
commutation `[W,V]=0` is not inherited by the compressed quotient operator.
Consequently `(QR.10)--(QR.13)` are superseded by the boundary-corrected
transport in Proofs 366--369.  The fixed projection and physical bracket
identities `(QR.2)--(QR.7)` remain valid.

Status: exact same-object identification of the surviving Proof 355 detector
crossing with the complete fixed Burnol-quotient physical commutator.  Proof
356 then transports that single recombined commutator to every sequential
moving quotient projection.  Proof 357's common finite-window owner may be
inserted only after this recombination.

This closes the owner-identification step.  It does not prove that the
prefix/Gram dressings form a uniformly bounded observation row.  Gate 3U, the
finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| fixed quotient projection                     | Proof 343 literal owner   |
| quotient detector crossing                    | one complete commutator   |
| outer/second/prolate recombination             | exact before any norm    |
| moving-prefix crossing readback                | exact via Proof 356      |
| common near-window insertion                   | legal after recombination|
| prefix/Gram observation-row bound              | open                     |
| finite certificate                            | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Fixed quotient owner

Use distinct names for the two support roles.  Let

```text
E       =physical source support projection,
Q_f     =Fourier/scattering support projection,
Q_b     =fixed Burnol boundary projection,
K_prol  =positive prolate correction,
R       =source Sonin projection.                  (QR.1)
```

The CC20 identities used by Proofs 257, 342, and 343 are

```text
R=E Q_f E-K_prol,
I-R=Q_b+P_K,                                        (QR.2)
```

where the second sum is orthogonal and `P_K` is the projection onto Proof
343's polar-normalized fixed quotient subspace `K`.  Thus

```text
P_K=I-R-Q_b.                                        (QR.3)
```

## 3. Quotient crossing is one commutator

For every bounded detector `W`,

```text
(I-P_K)W P_K=[W,P_K]P_K.                            (QR.4)
```

Substitute `(QR.2)--(QR.3)` before expanding:

```text
[W,P_K]
 =-[W,Q_b]-[W,R]

 =-[W,Q_b]
   -[W,E]Q_f E
   -E[W,Q_f]E
   -E Q_f[W,E]
   +[W,K_prol].                                     (QR.5)
```

Equation `(QR.5)` is the complete fixed physical bracket.  It contains both
orientations of the outer boundary, the compressed second boundary, the
prolate correction, and the fixed-boundary term.  The residue and trace
anomaly are retained because `(QR.5)` is an operator identity before trace
cycling.

The route crossing is therefore

```text
(I-P_K)W P_K
 =mathcalB_W P_K,                                   (QR.6)

mathcalB_W
 :=-[W,Q_b]
   -[W,E]Q_f E
   -E[W,Q_f]E
   -E Q_f[W,E]
   +[W,K_prol].                                     (QR.7)
```

No branch in `(QR.7)` has an independent Gate estimate.

## 4. Transport to every prefix

Let `U_0:H_0->K` be Proof 343's fixed isometry and let `A_<j` be the complete
inverse Euler prefix before the `j`-th prime.  Put

```text
H_<j=U_0* A_<j* A_<j U_0,
V_<j=A_<j U_0 H_<j^(-1/2),
P_<j=V_<j V_<j*.                                    (QR.8)
```

The compact convolution detector commutes with every Euler prefix:

```text
[W,A_<j]=0.                                         (QR.9)
```

Proof 356 `(CT.7)` and `(QR.6)` give the exact moving crossing

```text
(I-P_<j)W V_<j

 =(I-P_<j)A_<j(I-P_K)
   mathcalB_W U_0 H_<j^(-1/2).                      (QR.10)
```

This is the literal old-projection crossing required by Proof 355 at the
`j`-th Julia step.  It is not an abstract replacement.

## 5. Legal window insertion

For roots supported in `[-B_root,B_root]`, the commutators `[W,E]` and
`[W,Q_f]` in `(QR.7)` are completed real-line boundary crossings.  After the
five terms have been recombined, Proof 357 supplies a common near envelope
for every translation displacement at most `L`, with Hilbert--Schmidt square
at most

```text
(L+2B_root) norm(g)_2^2.                            (QR.11)
```

The legal order is

```text
form mathcalB_W
  -> multiply by the fixed quotient frame U_0
  -> use the exact prefix/Gram expression `(QR.10)`
  -> split near/far inside that same expression
  -> apply the common near envelope.                (QR.12)
```

In particular, `(QR.11)` may not be applied independently to the five terms
of `(QR.7)`.

## 6. The exact remaining row theorem

Combining Proofs 351, 355, 357, and `(QR.10)` leaves one source theorem.  For
the near prefix family, prove

```text
sum_(log(p_j)<=L) 1/(p_j-1) *
 norm(
   (I-P_<j)A_<j(I-P_K)
   mathcalB_W U_0 H_<j^(-1/2)
 )_2^2

 <=C (1+L+B_root)^d norm(g)_(H^r)^4.                (QR.13)
```

The powers of the root norm depend on whether the diagonal or polarized
response is used; the structural content is the single recombined row in
`(QR.13)`.

No raw Euler condition number is allowed.  The left side must be factored as
one observability/Bessel row before a norm is taken.

## 7. Reproducible certificate

The companion finite probe constructs orthogonal `R,Q_b`, the quotient
projection `P_K=I-R-Q_b`, arbitrary support operators `E,Q_f`, and defines
`K_prol=E Q_f E-R`.  It checks

```text
the two commutator equalities `(QR.4)--(QR.7)`;
the direct Gram-normalized prefix projection;
the transported crossing identity `(QR.10)`;
scalar invariance of the prefix frame.              (QR.14)
```

Run only in the unified verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/358_fixed_quotient_commutator_recombination_probe.py
```

The unified WSL2 run reports maximum exact error
`5.746080426180e-15` across the fixed commutator, moving-prefix crossing, and
scale-invariant frame checks.

The probe verifies finite algebra.  It does not prove `(QR.13)`.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| Proof 355 crossing -> fixed physical bracket  | exact `(QR.6)`            |
| fixed bracket -> moving prefix crossing        | exact `(QR.10)`           |
| physical common near HS owner                  | Proof 357 available      |
| branchwise norm estimate                       | forbidden                |
| complete observation row `(QR.13)`             | open, active bottom      |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
