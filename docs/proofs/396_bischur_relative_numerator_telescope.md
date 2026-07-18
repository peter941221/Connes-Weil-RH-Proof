# Proof 396: bi-Schur relative-numerator telescope

Date: 2026-07-18

Status: exact scale-separated numerator for Proof 391's ordered response.
The forward Schur and inverse Markov contractions surround the detector, while
their scalar product is subtracted before any norm.  The complete numerator
has a noncommutative local telescope and annihilates every coherent scalar
channel exactly.

This is the correct scale-invariant successor to the raw inverse-energy view
of Proof 393.  A uniform bound proportional to the scalar `rho_S` remains
open, so Gate 3U, the finite-`S` sign, Burnol's identity, and RH are unproved.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| forward Schur cascade                         | contraction `Gamma`      |
| inverse Markov cascade                        | contraction `Lambda`     |
| product                                       | scalar `rho I`           |
| ordered Gate response                         | relative numerator/rho   |
| local relative defects                        | exact telescope          |
| coherent scalar detector channel              | cancels exactly         |
| uniform relative-numerator bound / Gate 3U     | open                    |
+------------------------------------------------+---------------------------+
```

## 2. Paired transitions

For every Euler step retain Proof 395's contractions

```text
G_j=Z_j/(1+a_j),
R_j=(1-a_j)Z_j^(-1),                              (BN.1)

rho_j=(1-a_j)/(1+a_j).                            (BN.2)
```

They satisfy

```text
G_jR_j=R_jG_j=rho_jI.                             (BN.3)
```

Define complete products

```text
Gamma_n=G_1...G_n,
Lambda_n=R_n...R_1,
rho_n=product_(j=1)^n rho_j.                      (BN.4)
```

Then

```text
Gamma_nLambda_n=Lambda_nGamma_n=rho_nI.           (BN.5)
```

## 3. Scale-separated Gate owner

Let

```text
alpha_j=J_j*WJ_j                                 (BN.6)
```

be the detector compression on the actual sequential range.  Proof 391 gives

```text
Q_S(W)
 =Tr[Gamma_nalpha_nGamma_n^(-1)-alpha_0].         (BN.7)
```

Use `(BN.5)` to define the relative numerator

```text
mathcalN_n(W)
 :=Gamma_nalpha_nLambda_n-rho_nalpha_0.           (BN.8)
```

Then the ordered response is exactly

```text
Q_S(W)=rho_n^(-1)Tr[mathcalN_n(W)].               (BN.9)
```

Equivalently,

```text
rho_n^(-1)mathcalN_n(W)
 =Lambda_n^(-1)alpha_nLambda_n-alpha_0.           (BN.10)
```

No inverse norm has been taken in `(BN.8)--(BN.10)`.

## 4. One local relative defect

Define

```text
f_j
 :=G_jalpha_jR_j-rho_jalpha_(j-1).                (BN.11)
```

Proof 392's forward intertwinement defect is

```text
e_j=G_jalpha_j-alpha_(j-1)G_j.                    (BN.12)
```

Using `(BN.3)`,

```text
f_j=e_jR_j.                                       (BN.13)
```

Thus every local relative defect retains the physical Schur co-defect from
Proof 392 and gains a right Markov contraction.  No new analytic species is
introduced.

## 5. Complete telescope

Let

```text
Gamma_(j-1)=G_1...G_(j-1),
Lambda_(j-1)=R_(j-1)...R_1,                      (BN.14)

rho_>j=product_(k=j+1)^n rho_k.                  (BN.15)
```

The recursion

```text
mathcalN_j
 =Gamma_(j-1)f_jLambda_(j-1)
  +rho_jmathcalN_(j-1)                            (BN.16)
```

gives

```text
mathcalN_n
 =sum_(j=1)^n
   rho_>j Gamma_(j-1)f_jLambda_(j-1).             (BN.17)
```

Every operator surrounding `f_j` in `(BN.17)` is a contraction, and every
scalar weight is at most one.  The hard part is not operator conditioning;
it is proving that the completed signed sum is of order `rho_n`.

## 6. Exact scalar-channel cancellation

Suppose a detector channel is coherent on every source coordinate:

```text
alpha_j=lambda I for all j.                       (BN.18)
```

Then `(BN.3)` gives

```text
f_j=lambda(G_jR_j-rho_jI)=0,                     (BN.19)

mathcalN_n(lambda I)=0.                           (BN.20)
```

This is the source-coordinate version of Proof 253's cancellation of the
coherent scalar Euler bulk.  The huge inverse energy in Proof 393's scalar
guard carries no physical detector response.

## 7. Correct uniform target

For the compact-root completed response, the near Gate theorem is now

```text
abs Tr[mathcalN_n(W_root)]

 <=rho_n C(1+L+B_root)^d
   norm(g)_(H^r)^2.                               (BN.21)
```

Dividing `(BN.21)` by `rho_n` and using `(BN.9)` gives the desired bound.
Unlike a direct estimate of `Gamma_n^(-1)`, `(BN.21)` is invariant under the
paired scalar normalization and makes the exact scalar cancellation visible.

The numerator in `(BN.21)` must use Proof 387's complete corrected root
ledger.  A branchwise bound on the summands of `(BN.17)` cannot recover the
factor `rho_n`.

## 8. Reproducible certificate

The companion probe constructs the paired cascades on a nonreducing source
and a detector commuting with the ambient translation group.  It checks

```text
the scalar pair `(BN.5)`;
the ordered numerator readback `(BN.8)--(BN.10)`;
the local identity `(BN.13)`;
the recursion and full telescope `(BN.16)--(BN.17)`;
exact annihilation of a scalar detector `(BN.20)`;
agreement with the finite ambient projection response. (BN.22)
```

Run only after Proofs 395--399 are complete:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/396_bischur_relative_numerator_telescope_probe.py
```

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| scale-separated same-object numerator         | closed `(BN.8)`          |
| complete local telescope                      | closed `(BN.17)`         |
| coherent scalar cancellation                  | closed `(BN.20)`         |
| relative bound `(BN.21)`                       | open, active Gate bottom|
| raw stable-coframe target `(DC.19)`             | requires gauge audit     |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
