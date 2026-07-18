# Proof 392: Schur detector co-defect insertion

Date: 2026-07-18

Status: exact source-specific insertion of the normalized Schur co-defect
into the moving detector intertwinement.  The local defect is the completed
moving detector crossing compressed by the same normalized Euler factor that
defines the Schur transition.  Its complete history factors through Proof
391's constant-one co-defect row.

This repairs the abstract Gram/Julia mismatch from Proof 388 on the correct
physical cascade.  The remaining compact-root boundary column and ordered
trace anomaly still require a uniform estimate.  Gate 3U, the finite-`S`
sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| local detector intertwinement                 | exact boundary crossing  |
| Schur left co-defect                           | exact positive owner     |
| boundary compression through co-defect        | Douglas contraction      |
| complete prefix history                       | constant-one row         |
| cumulative Euler condition number             | absent before anomaly   |
| compact-root suffix column                    | open estimate           |
| ordered trace anomaly / Gate 3U                | open                    |
+------------------------------------------------+---------------------------+
```

## 2. One normalized step

Retain Proof 391's consecutive isometries

```text
J_(j-1):K_0->K_(j-1),
J_j:K_0->K_j,                                     (CD.1)
```

and put

```text
A_j=T_j/(1+a_j),
G_j=Z_j/(1+a_j).                                  (CD.2)
```

Proof 391 `(SC.4)` becomes

```text
A_jJ_j=J_(j-1)G_j.                               (CD.3)
```

Both `A_j` and `G_j` are contractions.

Let `W` be a bounded detector commuting with the ambient Euler factor:

```text
W T_j=T_j W.                                      (CD.4)
```

Define its source compressions

```text
alpha_(j-1)=J_(j-1)*WJ_(j-1),
alpha_j=J_j*WJ_j.                                 (CD.5)
```

## 3. Exact local intertwinement defect

Let

```text
P_j=J_jJ_j*,
K_j=(I-P_j)WJ_j.                                  (CD.6)
```

Thus `K_j` is the actual moving detector crossing, including the quotient
compression correction when read through Proofs 365--370.

Use `(CD.3)--(CD.4)`:

```text
A_jWJ_j=WA_jJ_j=WJ_(j-1)G_j.                     (CD.7)
```

Decompose

```text
WJ_j=J_jalpha_j+K_j.                              (CD.8)
```

Project `(CD.7)` onto `Ran(J_(j-1))`.  The old off-range crossing is killed
by `J_(j-1)*`, giving

```text
e_j
 :=G_jalpha_j-alpha_(j-1)G_j

 =-J_(j-1)*A_jK_j.                               (CD.9)
```

Equation `(CD.9)` is an operator identity before a trace or Schatten norm.

## 4. Co-defect ownership

Define the rectangular boundary compression

```text
L_j=J_(j-1)*A_j(I-P_j).                           (CD.10)
```

Its row Gram is part of the Schur co-defect.  Indeed,

```text
I-G_jG_j*

 =J_(j-1)*(I-A_jA_j*)J_(j-1)+L_jL_j*.            (CD.11)
```

Both terms on the right are positive.  If

```text
D_j^left=(I-G_jG_j*)^(1/2),                       (CD.12)
```

then `(CD.11)` implies

```text
L_jL_j*<=D_j^left^2.                              (CD.13)
```

Douglas factorization therefore gives a contraction `Omega_j^left` with

```text
L_j=D_j^left Omega_j^left.                        (CD.14)
```

Substitute `(CD.10)--(CD.14)` into `(CD.9)`:

```text
e_j
 =-D_j^left B_j,                                  (CD.15)

B_j=Omega_j^left WJ_j.                            (CD.16)
```

The old invalid route tried to put a Julia survivor `Psi_(j-1)` on the right.
Equation `(CD.15)` inserts the co-defect on the left, where the physical
Schur cascade actually supplies it.

## 5. Complete intertwinement telescope

Let

```text
Gamma_j=G_1...G_j,
Gamma_0=I.                                        (CD.17)
```

The complete ordered intertwinement defect is

```text
mathcalE_n
 :=Gamma_n alpha_n-alpha_0Gamma_n.                (CD.18)
```

The usual noncommutative product expansion gives

```text
mathcalE_n
 =sum_(j=1)^n
   Gamma_(j-1)e_jG_(j+1)...G_n.                  (CD.19)
```

Using `(CD.15)`, define

```text
C_j=Gamma_(j-1)D_j^left,
R_j=B_jG_(j+1)...G_n.                             (CD.20)
```

Then

```text
mathcalE_n=-sum_(j=1)^n C_jR_j.                  (CD.21)
```

Proof 391 `(SC.15)` gives

```text
sum_j C_jC_j*
 =I-Gamma_nGamma_n*<=I.                           (CD.22)
```

Thus the row `C=(C_1,...,C_n)` is a contraction.  All cumulative prefix
conditioning has disappeared before the remaining physical column is
estimated.

## 6. Interface with the corrected root bundle

The operator `K_j` in `(CD.6)` is exactly Proof 370's moving detector defect.
Proofs 380--387 give a two-root trace-compatible realization of the complete
corrected bracket that produces it.  Therefore `(CD.16)` is not an ambient
raw-root norm: `Omega_j^left` acts only after the completed boundary crossing
has been formed.

The remaining near theorem can now be stated without `Psi` or a Gram inverse:

```text
sum_(j=1)^n
 norm(
   Omega_j^left K_j^(root)
   G_(j+1)...G_n
 )_2^2

 <=C(1+L+B_root)^d norm(g)_(H^r)^2.               (CD.23)
```

Here `K_j^(root)` denotes the fixed common-root insertion from Proof 387, not
the raw bounded operator `WJ_j`.  If `(CD.23)` holds, `(CD.21)--(CD.22)` give
one legal direct-sum estimate with constant one.

## 7. Ordered response and the remaining anomaly

Proof 391 gives

```text
Gamma_n alpha_n Gamma_n^(-1)-alpha_0
 =mathcalE_nGamma_n^(-1).                         (CD.24)
```

Algebraically, `(CD.19)` also yields

```text
mathcalE_nGamma_n^(-1)
 =sum_(j=1)^n
   Gamma_(j-1)e_jG_j^(-1)Gamma_(j-1)^(-1).        (CD.25)
```

For a genuinely trace-class local term, bounded-similarity invariance removes
the surrounding `Gamma_(j-1)` without a norm cost.  Proof 264 warns that this
cycle is illegal when only the total difference, rather than each local root-
completed term, is trace class.

Thus the next proof must audit local trace legality and the two-sided root
factor before using `(CD.25)`.  No norm of `Gamma_(j-1)^(-1)` is permitted.

## 8. Reproducible certificate

The companion probe uses a commuting translation group, a nonreducing source,
and a detector in the same ambient spectral algebra.  It checks

```text
the local defect identity `(CD.9)`;
the co-defect decomposition `(CD.11)`;
the Douglas reconstruction `(CD.14)--(CD.16)`;
the global telescope `(CD.19)--(CD.22)`;
the ordered local-similarity expansion `(CD.25)`.  (CD.26)
```

Run only after Proofs 390--394 are complete:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/392_schur_detector_codefect_insertion_probe.py
```

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| physical defect -> Schur co-defect            | closed `(CD.15)`         |
| complete prefix row                           | closed `(CD.22)`         |
| old `Psi` alignment requirement               | removed                  |
| compact-root suffix estimate `(CD.23)`         | open, active near bound |
| local trace-anomaly legality                  | next audit               |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
