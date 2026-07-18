# Proof 387: corrected-bracket two-sided insertion

Date: 2026-07-18

Status: exact signed direct-sum factorization of Proof 368's complete
boundary-corrected quotient bracket.  Both orientations of every outer and
second-support commutator, the prolate commutator, and both quotient
compression corrections remain in one left readout.  The resulting moving
crossing has a legal two-Hilbert--Schmidt trace insertion.

The right insertion column still contains the moving causal prefix and Gram
normalization.  Therefore this proves the complete pre-Julia insertion, not
Proof 382 `(JR.9)` with one fixed `A_root`.  Gate 3U, the finite-`S` sign,
Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| corrected physical bracket                    | exact six-term owner     |
| oriented root atoms after expansion           | eleven, fixed count     |
| signs and quotient corrections                | one left readout        |
| complete moving crossing                      | two `S_2` factors       |
| rectangular trace insertion                   | legal                    |
| one fixed Julia source root                   | not yet obtained        |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Corrected quotient bracket

Retain Proof 368's notation on the fixed quotient carrier `E H`:

```text
W_E=E W E,
T_j=E V_j E,
[W,V_j]=0,
R=E Q_f E-K_prol.                                 (CI.1)
```

The letter `T_j` is used here for Proof 368's `A_j`, so that root-factor
columns can keep the letter `A`.  The complete bracket is

```text
Y_j=-T_j[W_E,R]+[W_E,T_j].                        (CI.2)
```

Proofs 365 and 368 give

```text
[W_E,R]
 =E[W,E]Q_f E
  +E[W,Q_f]E
  +E Q_f[W,E]E
  -E[W,K_prol]E,                                  (CI.3)

[W_E,T_j]
 =E[W,E]V_jE+EV_j[W,E]E.                         (CI.4)
```

Equations `(CI.2)--(CI.4)` are formed before any branch norm or trace cycle.

## 3. Oriented atoms

For a projection `P`, define

```text
D_P^+=(I-P)W P,
D_P^-=P W(I-P).                                   (CI.5)
```

Then

```text
[W,P]=D_P^+-D_P^-.                                (CI.6)
```

Proof 385 supplies two-Hilbert--Schmidt factorizations for `D_E^+` and
`D_E^-`.  Proof 386 supplies them for `D_Q^+`, `D_Q^-`, and

```text
D_K=[W,K_prol].                                   (CI.7)
```

Write every atom as

```text
D_r=L_r A_r,                                      (CI.8)
```

where both `L_r` and `A_r` are Hilbert--Schmidt.  The atom label `r` includes
its orientation; no adjoint is silently identified with the same operator.

## 4. Eleven-term signed ledger

Substitute `(CI.6)--(CI.8)` into `(CI.2)--(CI.4)`.  The result has the form

```text
Y_j=sum_(r=1)^11 epsilon_r B_(j,r)L_r A_r C_(j,r). (CI.9)
```

The exact dressings are:

```text
+----+---------+----------------+---------+----------+
| r  | atom    | B_(j,r)        | epsilon | C_(j,r)  |
+----+---------+----------------+---------+----------+
|  1 | D_E^+   | T_j E          |   -1    | Q_f E    |
|  2 | D_E^-   | T_j E          |   +1    | Q_f E    |
|  3 | D_Q^+   | T_j E          |   -1    | E        |
|  4 | D_Q^-   | T_j E          |   +1    | E        |
|  5 | D_E^+   | T_j E Q_f      |   -1    | E        |
|  6 | D_E^-   | T_j E Q_f      |   +1    | E        |
|  7 | D_K     | T_j E          |   +1    | E        |
|  8 | D_E^+   | E              |   +1    | V_j E    |
|  9 | D_E^-   | E              |   -1    | V_j E    |
| 10 | D_E^+   | E V_j          |   +1    | E        |
| 11 | D_E^-   | E V_j          |   -1    | E        |
+----+---------+----------------+---------+----------+ (CI.10)
```

Repeated appearances of an atom in `(CI.10)` are bookkeeping copies, not
new analytic species and not one copy per prime.  The count `11` is fixed.

## 5. One signed direct sum

Let `Z_r` be the intermediate Hilbert carrier of `(CI.8)` and define

```text
mathcalA_j x=(A_r C_(j,r)x)_(r=1)^11,             (CI.11)

mathcalL_j(z_r)_r
 =sum_(r=1)^11 epsilon_r B_(j,r)L_r z_r.          (CI.12)
```

The sum is finite.  Every component of `mathcalA_j` and `mathcalL_j` is
Hilbert--Schmidt because bounded composition preserves `S_2`.  Equations
`(CI.9)--(CI.12)` give

```text
Y_j=mathcalL_j mathcalA_j.                        (CI.13)
```

Equation `(CI.13)` is the required recombination: all physical signs and the
two quotient corrections live inside `mathcalL_j` before a norm is taken.
It is not the forbidden sum of eleven trace norms.

## 6. Moving crossing and trace insertion

Let the Gram-normalized moving frame be

```text
V_j^K=T_j U_0 H_j^(-1/2),
P_j=V_j^K(V_j^K)*.                                (CI.14)
```

Proofs 366 and 368 identify its detector crossing as

```text
D_j
 =(E-P_j)Y_jU_0H_j^(-1/2)

 =underbrace((E-P_j)mathcalL_j)_(Lhat_j)
  underbrace(mathcalA_jU_0H_j^(-1/2))_(Ahat_j).
                                                               (CI.15)
```

For each fixed finite prefix, `Lhat_j` and `Ahat_j` are Hilbert--Schmidt.
Hence, for every bounded rectangular range corner `R_j` of the matching
orientation,

```text
Tr(D_j*R_j)
 =<Lhat_j,R_j Ahat_j*>_(S_2).                     (CI.16)
```

This cycle exchanges a product of two rectangular Hilbert--Schmidt maps.  It
does not appeal to finite-dimensional trace cyclicity.

## 7. Exact boundary of the result

The right column in `(CI.15)` is

```text
Ahat_j=mathcalA_j U_0H_j^(-1/2).                  (CI.17)
```

It depends on `j` in two places:

```text
the quotient corrections contain A_r V_j E;
the common source is followed by H_j^(-1/2).       (CI.18)
```

Proof 357 can place each near translated compact-root output in one fixed
window, but window containment alone does not identify `(CI.17)` with

```text
J_(j-1)Psi_(j-1)A_root.                           (CI.19)
```

Equation `(CI.16)` is therefore the complete trace-preserving physical
insertion before the Julia coordinate.  Calling it Proof 382 `(JR.9)` would
skip the nontrivial alignment `(CI.17)--(CI.19)`.

## 8. Reproducible certificate

The companion finite probe constructs two support projections with a genuine
intersection, a positive prolate compression, commuting ambient `W,V`, the
compressed prefix `T=EVE`, and the normalized quotient frame.  It checks

```text
the physical expansions `(CI.3)--(CI.4)`;
all eleven entries of `(CI.10)`;
the direct-sum factorization `(CI.13)`;
the moving crossing factorization `(CI.15)`;
the rectangular insertion `(CI.16)`;
nonzero quotient correction and nontrivial Gram normalization. (CI.20)
```

Run only after Proofs 385--389 are complete:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/387_corrected_bracket_two_sided_insertion_probe.py
```

The continuous atom legality comes from Proofs 385--386.  The direct-sum
recombination is finite Hilbert-space ideal algebra.

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| complete corrected bracket                    | closed `(CI.13)`         |
| complete fixed-prefix trace insertion          | closed `(CI.16)`         |
| branchwise norm expansion                     | not used                 |
| fixed `A_root` / Julia coordinate              | open `(CI.17)--(CI.19)` |
| Proof 382 `(JR.9)`                             | still open               |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
