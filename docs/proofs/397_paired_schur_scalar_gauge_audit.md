# Proof 397: paired-Schur scalar-gauge audit

Date: 2026-07-18

Status: exact audit of the scalar normalization in Proofs 393--396.  A paired
rescaling changes the raw inverse-coframe energy but leaves the ordered
similarity, every local relative defect, and the complete relative numerator
unchanged.  A reducing scalar channel can therefore have arbitrarily large
raw inverse energy and exactly zero physical response.

This supersedes Proof 393 `(DC.19)` as the invariant statement of the active
Gate bottom.  The canonical-gauge estimate remains a possible sufficient
tool, but the theorem that must ultimately be proved is Proof 396 `(BN.21)`.
That theorem, Gate 3U, the finite-`S` sign, Burnol's identity, and RH remain
open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| paired scalar normalization                   | exact gauge action       |
| ordered similarity                            | gauge invariant          |
| local and complete relative numerators        | gauge invariant          |
| raw inverse-coframe energy                     | gauge dependent          |
| coherent scalar detector channel              | zero physical numerator |
| invariant uniform numerator bound             | open `(SG.18)`          |
| Gate 3U / finite-S sign / Burnol / RH          | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Paired scalar gauge

Retain Proof 396's one-step pair

```text
G_jR_j=R_jG_j=rho_jI.                             (SG.1)
```

For arbitrary nonzero scalars `c_j`, define a paired coordinate change

```text
G_j^[c]=c_jG_j,
R_j^[c]=c_j^(-1)R_j.                              (SG.2)
```

Then

```text
G_j^[c]R_j^[c]=R_j^[c]G_j^[c]=rho_jI.             (SG.3)
```

The canonical choice `c_j=1` is still the physical normalization for which
both factors are contractions.  Equation `(SG.2)` is an audit of coordinate
dependence; it is not a proposal to discard that useful normalization.

Put

```text
c_[1:n]=product_(j=1)^n c_j.                      (SG.4)
```

For the chronological products from Proof 396,

```text
Gamma_n^[c]=c_[1:n]Gamma_n,
Lambda_n^[c]=c_[1:n]^(-1)Lambda_n.                (SG.5)
```

Their scalar pair `rho_nI` is unchanged.

## 3. Physical invariants

The ordered response is unchanged:

```text
Gamma_n^[c] alpha_n (Gamma_n^[c])^(-1)-alpha_0

 =Gamma_n alpha_n Gamma_n^(-1)-alpha_0.           (SG.6)
```

Likewise the paired numerator is unchanged before any inverse is exposed:

```text
mathcalN_n^[c]
 :=Gamma_n^[c] alpha_n Lambda_n^[c]-rho_nalpha_0

 =Gamma_n alpha_n Lambda_n-rho_nalpha_0
 =mathcalN_n.                                     (SG.7)
```

At one step, the forward defect rescales but its Markov-completed version
does not:

```text
e_j^[c]=c_je_j,

f_j^[c]=e_j^[c]R_j^[c]=e_jR_j=f_j.               (SG.8)
```

In the complete telescope, the prefix gauges cancel pairwise:

```text
Gamma_(j-1)^[c] f_j^[c] Lambda_(j-1)^[c]
 =Gamma_(j-1) f_j Lambda_(j-1).                  (SG.9)
```

Thus Proof 396 `(BN.17)` is termwise gauge invariant, not merely invariant
after taking a trace.

## 4. Raw inverse energy is not invariant

For a fixed source column `A`, define the raw terminal inverse energy

```text
E_Gamma(A)
 :=norm(Gamma_n^(-1)A)_2^2-norm(A)_2^2.           (SG.10)
```

Under `(SG.5)`,

```text
E_(Gamma^[c])(A)

 =abs(c_[1:n])^(-2)norm(Gamma_n^(-1)A)_2^2
  -norm(A)_2^2.                                  (SG.11)
```

There is no gauge invariance in `(SG.11)`.  Consequently a bound written only
as a norm of `Gamma_n^(-1)A` is not itself a physical Gate statement unless
the coordinate law of `A` is also fixed and justified.

This does not make Proof 393's inverse-energy identity false.  It identifies
exactly what that identity measures: conditioning of a chosen frame gauge,
not the signed endpoint response by itself.

## 5. Exact reducing-channel guard

Take the reducing scalar Euler channel `U_j=I`.  Then

```text
Z_j=(1-a_j)I,
G_j=rho_jI,
R_j=I.                                           (SG.12)
```

For a coherent detector compression

```text
alpha_j=lambda I for every j,                    (SG.13)
```

one has

```text
Gamma_n=rho_nI,
Lambda_n=I,                                      (SG.14)

mathcalN_n(lambda I)=0.                          (SG.15)
```

For any nonzero fixed source column, however,

```text
E_Gamma(A)
 =(rho_n^(-2)-1)norm(A)_2^2.                     (SG.16)
```

The right side grows rapidly as visible primes are added while the physical
numerator remains exactly zero.  This is a direct counterexample to using raw
dual energy as the definition of the remaining Gate quantity.

## 6. Corrected active target

The scale-invariant same-object target is

```text
abs Tr[mathcalN_n(W_root)]

 <=rho_n C(1+L+B_root)^d
   norm(g)_(H^r)^2.                               (SG.17)
```

Equivalently, after dividing by the known positive scalar,

```text
abs Tr[rho_n^(-1)mathcalN_n(W_root)]

 <=C(1+L+B_root)^d norm(g)_(H^r)^2.               (SG.18)
```

Equations `(SG.17)--(SG.18)` preserve Proof 264's ordered trace anomaly and
Proof 387's complete root correction.  They do not ask an arbitrary source
column to survive the inverse Schur cascade.

## 7. Reproducible certificate

The companion probe uses the physical finite Schur cascade from Proof 396
and a deliberately nontrivial sequence of scalar gauges.  It checks

```text
the paired products `(SG.3)--(SG.5)`;
ordered-response and numerator invariance `(SG.6)--(SG.7)`;
local-defect and telescope invariance `(SG.8)--(SG.9)`;
the raw-energy transformation `(SG.11)`;
the exact reducing-channel guard `(SG.12)--(SG.16)`. (SG.19)
```

Run only in the unified Proofs 395--399 verification batch:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/397_paired_schur_scalar_gauge_audit_probe.py
```

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| scalar-gauge action                           | closed `(SG.2)--(SG.5)`  |
| physical numerator invariance                 | closed `(SG.6)--(SG.9)`  |
| raw inverse energy as invariant Gate target   | rejected `(SG.11)`      |
| coherent scalar guard                         | closed `(SG.15)--(SG.16)`|
| relative bound `(SG.17)`                      | open, active Gate bottom|
| Gate 3U / finite-S sign / Burnol / RH          | open / open / open / open|
+------------------------------------------------+---------------------------+
```
