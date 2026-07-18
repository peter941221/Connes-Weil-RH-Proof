# Proof 391: complete Schur-cascade Gram owner

Date: 2026-07-18

Status: exact finite-cascade assembly of Proof 390's Schur frames on the
literal fixed quotient source.  Their ordered product reconstructs the raw
complete inverse Euler frame, its compressed Gram metric, and Proof 343's
ordered relative response.  The normalized Schur factors also supply forward
and reverse constant-one defect telescopes.

This closes the same-object ownership gap left by Proof 388: the correct
source cascade is now explicit.  It does not yet give a uniform bound for the
ordered similarity anomaly, so Gate 3U, the finite-`S` sign, Burnol's
identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| sequential physical range frames              | exact                    |
| complete source coordinate                    | ordered Schur product    |
| Proof 343 compressed Gram metric              | exact readback           |
| Gram-corrected target projection              | sequential frame range  |
| normalized forward/reverse defect rows        | constant one             |
| complete relative response                    | ordered similarity       |
| uniform trace-anomaly bound / Gate 3U          | open                    |
+------------------------------------------------+---------------------------+
```

## 2. Sequential setup

Let `K_0` be Proof 343's fixed polar-normalized quotient source with isometry

```text
J_0=U_0:K_0->H.                                   (SC.1)
```

Choose one order of the visible Euler factors and write

```text
T_j=I-a_jU_j,
a_j=p_j^(-1/2).                                   (SC.2)
```

The ambient translations commute, but the source-coordinate products below
retain this chosen order.  Let `J_j:K_0->H` be the canonical graph isometry
onto

```text
K_j=T_j^(-1)K_(j-1).                              (SC.3)
```

Apply Proof 390 at step `j`, relative to `K_(j-1)`.  Pull its Schur frame back
through `J_(j-1)` and denote the resulting endomorphism of `K_0` by `Z_j`.
Then

```text
T_j J_j=J_(j-1)Z_j.                               (SC.4)
```

## 3. Complete Schur product

Define chronological products

```text
mathcalT_n=T_1...T_n,
mathcalZ_n=Z_1...Z_n.                             (SC.5)
```

Repeated substitution of `(SC.4)` gives

```text
mathcalT_n J_n=U_0 mathcalZ_n.                    (SC.6)
```

The ambient factors commute, so `mathcalT_n` is the complete finite Euler
denominator independent of the bookkeeping order.  The source product
`mathcalZ_n` records the chosen sequence of canonical graph coordinates.

Since every factor is invertible,

```text
mathcalT_n^(-1)U_0
 =J_n mathcalZ_n^(-1).                            (SC.7)
```

Equation `(SC.7)` is the complete version of Proof 390 `(SF.10)`.

## 4. Proof 343 Gram readback

Let `A_S` be the literal complete inverse Euler transport on the fixed
quotient carrier.  On `K_0`, `(SC.7)` reads

```text
A_SU_0=J_n mathcalZ_n^(-1).                       (SC.8)
```

Therefore Proof 343's compressed metric is

```text
H_S
 =U_0*A_S*A_SU_0
 =mathcalZ_n^(-*)mathcalZ_n^(-1).                 (SC.9)
```

Its Gram-corrected range projection is exactly

```text
A_SU_0H_S^(-1)U_0*A_S*
 =J_nJ_n*.                                        (SC.10)
```

Thus the sequential canonical frame and Proof 343's direct Gram projection
are the same operator owner.  No `Psi` product occurs.

## 5. Harmless scalar normalization

For every step put

```text
G_j=Z_j/(1+a_j),
Gamma_n=G_1...G_n.                                (SC.11)
```

Proof 390 shows `norm(G_j)<=1`.  If

```text
c_n=product_(j=1)^n(1+a_j),                       (SC.12)
```

then

```text
mathcalZ_n=c_n Gamma_n.                           (SC.13)
```

The scalar `c_n` cancels from `(SC.9)--(SC.10)` and from every ordered
similarity below.  It may therefore be removed before a norm without changing
the physical endpoint.

## 6. Two constant-one defect telescopes

Let

```text
D_j=(I-G_j*G_j)^(1/2),
D_j^left=(I-G_jG_j*)^(1/2).                       (SC.14)
```

For the chronological product in `(SC.11)`, direct multiplication gives the
co-defect telescope

```text
I-Gamma_nGamma_n*
 =sum_(j=1)^n
   Gamma_(j-1) D_j^left^2 Gamma_(j-1)*.           (SC.15)
```

Here `Gamma_0=I`.  The input-defect telescope runs from the other end:

```text
I-Gamma_n*Gamma_n
 =sum_(j=1)^n
   (G_(j+1)...G_n)* D_j^2 (G_(j+1)...G_n).        (SC.16)
```

Consequently, the rows

```text
x |->(D_j^left Gamma_(j-1)*x)_j,
x |->(D_j G_(j+1)...G_n x)_j                     (SC.17)
```

are contractions.  Both constants are exactly one and independent of the
number, order, or spacing of visible primes.

## 7. Exact ordered response

For a bounded detector `W`, define the source compressions

```text
alpha_0=U_0*WU_0,
alpha_n=J_n*WJ_n.                                 (SC.18)
```

Using `(SC.8)`, Proof 343's numerator is

```text
N_S(W)
 =mathcalZ_n^(-*) alpha_n mathcalZ_n^(-1).        (SC.19)
```

Multiplying by `(SC.9)` in the required order gives

```text
H_S^(-1)N_S(W)
 =mathcalZ_n alpha_n mathcalZ_n^(-1)
 =Gamma_n alpha_n Gamma_n^(-1).                  (SC.20)
```

Hence the complete relative response is

```text
Q_S(W)
 =Tr[
    Gamma_n alpha_n Gamma_n^(-1)-alpha_0
   ].                                             (SC.21)
```

Equation `(SC.21)` is a same-object readback of Proof 343 `(PN.14)`.  In
infinite dimensions it may not be cycled to `Tr(alpha_n-alpha_0)`.  The
unilateral-shift guard from Proof 264 shows that such a positive similarity
can carry a nonzero trace anomaly.

## 8. What remains

Proof 391 supplies both defect Bessel rows needed for a two-sided Schur
cascade estimate.  The remaining theorem must express the completed compact-
root numerator in `(SC.21)` through those rows before `Gamma_n^(-1)` is
expanded or normed.

The forbidden estimate remains

```text
norm(Gamma_n^(-1))
 <=product_j norm(G_j^(-1)).                      (SC.22)
```

The correct successor is a detector intertwinement telescope that retains
the ordered similarity anomaly and inserts the two defects in `(SC.17)`.

## 9. Reproducible certificate

The companion probe uses a commuting translation group, four prime
coefficients, and a nonreducing fixed source.  It checks

```text
every local identity `(SC.4)`;
the complete product identities `(SC.6)--(SC.10)`;
the scalar-normalized product `(SC.13)`;
both defect telescopes `(SC.15)--(SC.17)`;
the ordered response `(SC.19)--(SC.21)`;
agreement with the finite ambient projection trace. (SC.23)
```

Run only after Proofs 390--394 are complete:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/391_complete_schur_cascade_gram_owner_probe.py
```

## 10. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| complete physical source cascade              | closed `(SC.6)`          |
| Proof 343 Gram metric and projection           | closed `(SC.9)--(SC.10)`|
| forward/reverse Schur Bessel rows              | closed `(SC.15)--(SC.17)`|
| ordered trace owner                            | closed `(SC.21)`         |
| inverse-free detector intertwinement           | next proof               |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
