# Proof 398: corrected-root bi-Schur ledger

Date: 2026-07-18

Status: exact same-object splice between Proof 387's eleven-term corrected
root ledger and Proof 396's bi-Schur relative numerator.  Every local relative
defect is the complete moving boundary crossing with a left Schur co-defect
compression and a right Markov transition.  The complete numerator is one
signed telescope of these root-completed terms.

This closes the algebraic and trace-legality ledger.  It does not prove the
uniform `rho_S` gain for that signed telescope.  Gate 3U, the finite-`S` sign,
Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| Proof 387 corrected crossing                  | retained, all 11 atoms   |
| local forward Schur defect                    | same moving crossing     |
| right inverse transition                      | Markov contraction       |
| local relative numerator                      | two-root boundary product|
| complete relative numerator                   | exact signed telescope   |
| fixed finite-S trace legality                 | closed                    |
| uniform rho gain / Gate 3U                    | open `(RL.19)`           |
+------------------------------------------------+---------------------------+
```

## 2. Local Schur boundary identity

Retain Proof 392's normalized local Euler factor and consecutive frames:

```text
A_j=T_j/(1+a_j),
A_jJ_j=J_(j-1)G_j,
P_j=J_jJ_j*.                                      (RL.1)
```

For the actual compressed detector `W`, define

```text
K_j=(I-P_j)WJ_j.                                  (RL.2)
```

This is the identity operator of the quotient carrier; in ambient notation
`I-P_j` is Proof 387's `E-P_j`.  Proof 392 gives

```text
e_j
 :=G_jalpha_j-alpha_(j-1)G_j

 =-J_(j-1)*A_jK_j.                               (RL.3)
```

Proof 396 completes this defect on the right with

```text
R_j=(1-a_j)Z_j^(-1),
f_j=e_jR_j.                                       (RL.4)
```

Therefore

```text
f_j=-J_(j-1)*A_j(I-P_j)WJ_jR_j.                  (RL.5)
```

No inverse Schur norm occurs in `(RL.5)`.

## 3. Causal Markov readback

Proof 395 defines

```text
M_j=(1-a_j)T_j^(-1)                               (RL.6)
```

and proves

```text
M_jJ_(j-1)=J_jR_j.                               (RL.7)
```

Substitution in `(RL.5)` gives the causal boundary sandwich

```text
f_j
 =-J_(j-1)*A_j(I-P_j)W M_jJ_(j-1).              (RL.8)
```

Although `A_jM_j=rho_jI`, those two factors cannot be canceled across the
moving boundary `I-P_j`.  Doing so would erase the detector response.

## 4. Insert the complete corrected root ledger

Proof 387 expands the boundary-corrected quotient bracket before any norm:

```text
Y_j^corr
 =sum_(r=1)^11 epsilon_r
   B_(j,r)L_rA_rC_(j,r)

 =mathcalL_jmathcalA_j.                           (RL.9)
```

The eleven entries are exactly Proof 387 `(CI.10)`:

```text
two orientations of the first outer boundary, repeated in four dressings;
two orientations of the second support boundary;
one prolate commutator;
both quotient-compression corrections.           (RL.10)
```

The actual moving crossing is

```text
K_j
 =(I-P_j)Y_j^corr U_0H_j^(-1/2)

 =[(I-P_j)mathcalL_j]
   [mathcalA_jU_0H_j^(-1/2)].                    (RL.11)
```

All signs in `(RL.10)` are inside `mathcalL_j`.  The two bracketed maps in
`(RL.11)` are Hilbert--Schmidt for each fixed finite prefix.

## 5. Local bi-Schur root factor

Substitute `(RL.11)` into `(RL.5)` and define

```text
X_j^left
 :=J_(j-1)*A_j(I-P_j)mathcalL_j,                 (RL.12)

X_j^right
 :=mathcalA_jU_0H_j^(-1/2)R_j.                  (RL.13)
```

Then

```text
f_j=-X_j^left X_j^right.                         (RL.14)
```

Both factors are Hilbert--Schmidt.  Thus every `f_j` is trace class through
the literal corrected root owner.  Equation `(RL.14)` is not a direct sum of
eleven trace norms: the signed left readout remains one operator.

## 6. Complete relative numerator

Let

```text
Gamma_(j-1)=G_1...G_(j-1),
Lambda_(j-1)=R_(j-1)...R_1,
rho_>j=product_(k=j+1)^n rho_k.                  (RL.15)
```

Proof 396's telescope and `(RL.14)` give

```text
mathcalN_n(W_root)

 =-sum_(j=1)^n rho_>j
   Gamma_(j-1)X_j^left X_j^rightLambda_(j-1).
                                                               (RL.16)
```

Every term in `(RL.16)` has a legal two-Hilbert--Schmidt trace for fixed
finite `S`.  The sum is finite, so

```text
Tr[mathcalN_n(W_root)]

 =-sum_(j=1)^n rho_>j
   Tr[Gamma_(j-1)X_j^left
      X_j^rightLambda_(j-1)].                    (RL.17)
```

Equation `(RL.17)` preserves the chronological ordering required by Proof
264.  It does not use an infinite-dimensional similarity cycle.

## 7. Scalar cancellation and the remaining bound

For `W=lambda I`, every boundary atom in `(RL.9)` is zero.  Equivalently,
`(I-P_j)WJ_j=0`.  Hence

```text
X_j^left X_j^right=0,
f_j=0,
mathcalN_n(lambda I)=0.                          (RL.18)
```

The active analytic theorem is now the single signed estimate

```text
abs Tr[
  sum_(j=1)^n rho_>j
    Gamma_(j-1)X_j^left X_j^rightLambda_(j-1)
]

 <=rho_n C(1+L+B_root)^d norm(g)_(H^r)^2.         (RL.19)
```

Taking absolute values before the sum, splitting the eleven branches, or
bounding `H_j^(-1/2)` and `R_j` separately cannot recover the factor `rho_n`.
Proof 261 supplies fixed-`S` legality only; it does not supply `(RL.19)`.

## 8. Reproducible certificate

The companion probe builds a genuine two-support quotient with a nonzero
compression correction and nontrivial Gram normalization.  It combines that
complete Proof 387 ledger with one nonreducing Schur/Markov transition and
checks

```text
all eleven corrected atoms and their signed readout `(RL.9)--(RL.11)`;
the local Schur boundary identity `(RL.3)`;
the Markov readback `(RL.7)--(RL.8)`;
the root-completed relative defect `(RL.12)--(RL.14)`;
exact scalar-channel cancellation `(RL.18)`.      (RL.20)
```

Proof 396's companion probe separately checks the complete multi-step
telescope.  Proof 399 owns their algebraic composition in Lean.

Run only in the unified Proofs 395--399 verification batch:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/398_corrected_root_bischur_ledger_probe.py
```

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| corrected local root owner                    | closed `(RL.9)--(RL.14)` |
| fixed-S ordinary trace                        | legal `(RL.17)`          |
| complete scalar-channel cancellation          | closed `(RL.18)`        |
| branchwise / total-variation estimate         | forbidden                |
| signed relative bound `(RL.19)`                | open, active Gate bottom|
| Gate 3U / finite-S sign / Burnol / RH          | open / open / open / open|
+------------------------------------------------+---------------------------+
```
