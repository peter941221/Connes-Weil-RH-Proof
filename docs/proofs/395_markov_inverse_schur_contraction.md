# Proof 395: Markov-inverse Schur contraction

Date: 2026-07-18

Status: exact source-coordinate readback of the probability-normalized inverse
Euler factor.  It is a contraction dual to Proof 390's forward Schur
contraction, with an explicit minus-channel defect.  The complete forward and
inverse cascades multiply to one scalar.

This separates genuine boundary instability from the scalar gauge used in
Proof 393.  It does not yet prove the scale-invariant relative numerator
bound, Gate 3U, the finite-`S` sign, Burnol's identity, or RH.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| probability-normalized ambient inverse        | Markov contraction       |
| source-coordinate inverse frame               | contraction `R`          |
| inverse defect                                | exact minus channel      |
| forward/inverse Schur pair                    | scalar inverse pair      |
| complete Markov source cascade                | contraction              |
| scalar gauge versus physical response          | separated               |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. One inverse Euler factor

Retain Proof 390's notation

```text
T=I-aU,
T V=iota_P Z,
0<a<1.                                            (MI.1)
```

The inverse range identity is

```text
T^(-1)iota_P=VZ^(-1).                             (MI.2)
```

Normalize the ambient inverse by its spectral lower bound:

```text
M=(1-a)T^(-1).                                    (MI.3)
```

The Neumann expansion is

```text
M=sum_(m>=0)(1-a)a^mU^m.                          (MI.4)
```

Thus `M` is a probability average of unitary translations and

```text
norm(M)<=1.                                       (MI.5)
```

## 3. Source Markov transition

Define

```text
R=(1-a)Z^(-1).                                    (MI.6)
```

Equation `(MI.2)` becomes

```text
M iota_P=V R.                                     (MI.7)
```

Since both source and target frames are isometric, `(MI.5)--(MI.7)` imply

```text
R*R=iota_P*M*M iota_P<=I.                         (MI.8)
```

Therefore `R` is the literal source-coordinate Markov contraction.  It is not
the inverse of a contraction estimated by a product of inverse norms.

## 4. Exact minus-channel defect

Use unitarity of `U`:

```text
T*T-(1-a)^2I

 =a(2I-U-U*)
 =a(I-U*) (I-U).                                  (MI.9)
```

Multiplying `(MI.9)` by `T^(-*)` and `T^(-1)` gives

```text
I-M*M
 =a T^(-*) (I-U*) (I-U) T^(-1).                  (MI.10)
```

Compress through `(MI.7)`:

```text
I-R*R
 =a iota_P*T^(-*) (I-U*) (I-U) T^(-1)iota_P.
                                                               (MI.11)
```

Proof 390's forward defect contains `(I+U)`.  Equation `(MI.11)` supplies the
dual causal difference `(I-U)` channel.

## 5. Pair with the forward Schur frame

Proof 390 defines

```text
G=Z/(1+a).                                        (MI.12)
```

Together with `(MI.6)`,

```text
R G=G R=rho I,
rho=(1-a)/(1+a).                                  (MI.13)
```

Both `G` and `R` are contractions.  They are scalar inverses of one another;
neither is discarded.

## 6. Complete paired cascades

For the ordered finite Euler family define

```text
Gamma_n=G_1...G_n,
Lambda_n=R_n...R_1,
rho_n=product_(j=1)^n rho_j.                      (MI.14)
```

Repeated adjacent cancellation in `(MI.13)` gives

```text
Gamma_nLambda_n=rho_nI,
Lambda_nGamma_n=rho_nI.                           (MI.15)
```

The complete ambient Markov product

```text
mathcalM_n=M_n...M_1                              (MI.16)
```

satisfies

```text
mathcalM_nU_0=J_nLambda_n.                        (MI.17)
```

Hence `Lambda_n` is a contraction with an ordinary defect telescope.  The
large `Gamma_n^(-1)` from Proof 393 is

```text
Gamma_n^(-1)=rho_n^(-1)Lambda_n.                  (MI.18)
```

Its exponential scalar can cancel from a relative response even though it
dominates the norm of an arbitrary source vector.

## 7. Route consequence

The physical ordered similarity has the equivalent forms

```text
Gamma_n alpha Gamma_n^(-1)
 =Lambda_n^(-1)alpha Lambda_n
 =rho_n^(-1)Gamma_n alpha Lambda_n.               (MI.19)
```

The last form separates a bi-contractive numerator from the scalar
`rho_n^(-1)`.  A Gate estimate must prove that the numerator carries the
matching factor `rho_n`; estimating `Gamma_n^(-1)` first cannot see that
cancellation.

## 8. Reproducible certificate

The companion probe checks, for a commuting translation cascade,

```text
the one-step Markov intertwining `(MI.7)`;
contractivity and the minus defect `(MI.8)--(MI.11)`;
the scalar inverse pair `(MI.13)`;
the complete identities `(MI.15)--(MI.17)`;
the Markov defect telescope.                       (MI.20)
```

Run only after Proofs 395--399 are complete:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/395_markov_inverse_schur_contraction_probe.py
```

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| inverse physical source transition            | closed `(MI.6)`          |
| Markov contraction and minus defect            | closed `(MI.11)`         |
| complete forward/inverse pairing              | closed `(MI.15)`         |
| scale-invariant relative numerator             | next proof               |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
