# Proof 400: relative-trace cocycle collapse

Date: 2026-07-18

Status: exact trace-level collapse of Proof 396's bi-Schur numerator.  Once
Proof 398 has made every local relative defect trace class, all complete
forward/reverse prefixes disappear by legal cyclicity.  The endpoint scalar
is the signed sum of one-step normalized trace anomalies.

This replaces the operator-valued estimate `(BN.21)` by a strictly weaker,
equivalent scalar target.  It does not bound that signed sum, prove Gate 3U,
the finite-`S` sign, Burnol's identity, or RH.

## 1. Result

```text
+-----------------------------------------------+---------------------------+
| layer                                         | judgment                  |
+-----------------------------------------------+---------------------------+
| local corrected relative defects              | trace class by Proof 398|
| complete prefix similarities                  | disappear inside trace  |
| endpoint response                             | local signed cocycle sum|
| operator estimate `(BN.21)`                   | sufficient, not needed  |
| scalar local-sum estimate                     | open, active Gate bottom|
| Gate 3U / finite-S sign / Burnol / RH          | open / open / open / open|
+-----------------------------------------------+---------------------------+
```

## 2. Paired cascade

Retain Proof 396's notation

```text
Gamma_(j-1)=G_1...G_(j-1),
Lambda_(j-1)=R_(j-1)...R_1,

Gamma_(j-1)Lambda_(j-1)=rho_<j I,               (TC.1)

f_j=G_j alpha_j R_j-rho_j alpha_(j-1).          (TC.2)
```

The complete numerator is

```text
mathcalN_n
 =sum_(j=1)^n rho_>j
    Gamma_(j-1) f_j Lambda_(j-1).                (TC.3)
```

For the literal corrected root owner, Proof 398 factors every `f_j` as a
product of two Hilbert--Schmidt operators.  Hence

```text
f_j in S_1.                                      (TC.4)
```

All other factors in `(TC.3)` are bounded for fixed finite `S`.

## 3. Legal prefix collapse

Because `Lambda_(j-1)` is invertible and `(TC.1)` holds,

```text
Gamma_(j-1)=rho_<j Lambda_(j-1)^(-1).            (TC.5)
```

Use `(TC.4)` before cycling:

```text
Tr[Gamma_(j-1) f_j Lambda_(j-1)]

 =rho_<j Tr[Lambda_(j-1)^(-1)
              f_j Lambda_(j-1)]
 =rho_<j Tr[f_j].                                (TC.6)
```

The second equality is the ordinary trace cyclicity theorem for a trace-class
operator multiplied by bounded operators.  It is not finite-dimensional
cyclicity applied to two undefined endpoint traces.

Since

```text
rho_n=rho_<j rho_j rho_>j,                        (TC.7)
```

equations `(TC.3)--(TC.7)` give the exact scalar identity

```text
rho_n^(-1) Tr[mathcalN_n]
 =sum_(j=1)^n rho_j^(-1) Tr[f_j].                 (TC.8)
```

Proof 396 `(BN.9)` therefore becomes

```text
Q_S(W_root)
 =sum_(j=1)^n rho_j^(-1) Tr[f_j].                (TC.9)
```

No complete-prefix inverse remains in `(TC.9)`.

## 4. Why this changes the active theorem

Proof 396 proposed the operator-level sufficient estimate

```text
abs Tr[mathcalN_n]<=rho_n C_root.                 (TC.10)
```

Equation `(TC.8)` shows that the actual scalar Gate only asks for

```text
abs sum_(j=1)^n rho_j^(-1)Tr[f_j]
 <=C_root,                                        (TC.11)
```

uniformly in the finite visible-prime set.  The two statements have the same
scalar content after taking the trace, but `(TC.11)` does not require an
operator norm or trace norm of `mathcalN_n` to carry the exponentially small
factor `rho_n`.

The sum in `(TC.11)` is signed.  Replacing it with

```text
sum_j rho_j^(-1) abs Tr[f_j]
```

would discard the outer-minus-Sonin-prolate cancellation and is not licensed.

## 5. Reproducible certificate

The companion probe extends the physical Schur cascade from Proof 396.  It
checks `(TC.3)`, every prefix pair, the termwise trace collapse `(TC.6)`, the
complete scalar identity `(TC.8)`, and the endpoint readback `(TC.9)`.

Run only in the unified Proofs 400--404 batch:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/400_relative_trace_cocycle_collapse_probe.py
```

Finite matrices verify the algebra.  Infinite-dimensional legality comes
from Proofs 261 and 398's local `S_1` factorization.

## 6. Route judgment

```text
+-----------------------------------------------+---------------------------+
| layer                                         | judgment                  |
+-----------------------------------------------+---------------------------+
| complete scalar-prefix collapse               | closed `(TC.8)`         |
| local corrected trace legality                | closed by Proof 398     |
| operator `rho_n` estimate as necessary target | rejected                |
| signed local cocycle bound `(TC.11)`           | open, active Gate bottom|
| Gate 3U / finite-S sign / Burnol / RH          | open / open / open / open|
+-----------------------------------------------+---------------------------+
```
