# Proof 368: boundary-corrected physical ledger

Date: 2026-07-18

Status: exact recombination of Proof 366's corrected quotient transport with
the CC20 outer/second-support/prolate identity.  The fixed quotient crossing
contributes `-[W_E,R]`; quotient compression contributes two additional outer
boundary terms.  Their signed sum is the literal moving detector crossing.

This repairs the same-object owner after Proof 365's audit.  It does not prove
the normalized covariance bound.  Gate 3U, the finite-`S` sign, Burnol's
identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| fixed quotient crossing                       | `-[W_E,R]`               |
| source Sonin physical expansion                | exact                    |
| quotient compression correction                | two outer crossings     |
| complete corrected moving bracket              | exact                    |
| independent fixed-Q boundary branch            | absent after quotient   |
| normalized covariance estimate                 | open                    |
| finite certificate                             | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Fixed quotient geometry

Let

```text
E=I-Q_b,
R<=E,
P_K=E-R,
P_K=U_0 U_0*.                                      (PL.1)
```

Here `Q_b` is the fixed Burnol boundary projection and `R` is the source
Sonin projection.  On the quotient carrier `E H`, use

```text
W_E=E W E.                                         (PL.2)
```

Since `R U_0=0`, the old quotient crossing is

```text
K_0=R W_E U_0=-[W_E,R]U_0.                         (PL.3)
```

Equation `(PL.3)` is the crossing relevant after the common fixed `Q_b`
column has canceled.  The larger operator `(I-P_K)WP_K` from Proof 358 also
contains output into `Q_b`; that output is not part of the quotient crossing.

## 3. Moving quotient

Let `V_j` be the normalized ambient inverse Euler prefix and define

```text
A_j=E V_j E |_EH,
H_j=U_0* A_j* A_j U_0,
V_j^K=A_j U_0 H_j^(-1/2),
P_j=V_j^K (V_j^K)*.                                 (PL.4)
```

Proof 366 gives

```text
K_j
 =(E-P_j)Y_j U_0 H_j^(-1/2),                       (PL.5)

Y_j=-A_j[W_E,R]+[W_E,A_j].                         (PL.6)
```

All terms in `(PL.6)` must be formed before a Schatten norm.

## 4. Fixed Sonin branch expansion

The actual source identity is

```text
R=E Q_f E-K_prol.                                  (PL.7)
```

Compressing the commutator to `E H` gives

```text
[W_E,R]
 =E[W,E]Q_f E
  +E[W,Q_f]E
  +E Q_f[W,E]E
  -E[W,K_prol]E.                                   (PL.8)
```

This is the familiar outer/second-support/prolate ledger, now on the exact
quotient carrier.  Proofs 361--363 provide fixed Hilbert--Schmidt owners for
its boundary and prolate pieces.

## 5. Compression correction

Ambient commutation `[W,V_j]=0` and Proof 365 give

```text
[W_E,A_j]
 =E[W,E]V_j E+E V_j[W,E]E.                         (PL.9)
```

Substituting `(PL.8)--(PL.9)` into `(PL.6)` yields the complete physical
bracket

```text
Y_j
 =-A_j(
    E[W,E]Q_f E
    +E[W,Q_f]E
    +E Q_f[W,E]E
    -E[W,K_prol]E)

   +E[W,E]V_j E
   +E V_j[W,E]E.                                   (PL.10)
```

The last two terms are not new analytic species: they are the same outer
boundary commutator dressed on opposite sides by the causal prefix.  Their
presence is forced by quotient compression.

## 6. Recombination guard

Neither line in `(PL.10)` has an independent Gate sign or normalized bound.
In particular, the legal order is

```text
form the four fixed Sonin branches
  -> multiply their signed sum by -A_j
  -> add both quotient-boundary corrections
  -> apply E-P_j and H_j^(-1/2)
  -> only then estimate the compact-root row.        (PL.11)
```

Replacing the last two terms by zero returns the invalid Proof 358 formula.
Estimating all six terms independently returns the total-variation bound
rejected by Proofs 260 and 348.

## 7. Reproducible certificate

The companion finite probe constructs nested projections `R<=E`, commuting
ambient `V_j,W`, and an arbitrary second-support projection `Q_f`.  It checks

```text
the old crossing identity `(PL.3)`;
the physical commutator expansion `(PL.8)`;
the quotient correction `(PL.9)`;
the complete moving crossing `(PL.5)--(PL.10)`.      (PL.12)
```

The finite `K_prol=E Q_f E-R` is used only to verify the ledger algebra; the
route's positivity/trace-class facts are supplied by CC20.

Run only in the unified five-batch verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/368_boundary_corrected_physical_ledger_probe.py
```

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| fixed quotient output carrier                 | corrected to `R`         |
| fixed physical four-branch ledger              | exact `(PL.8)`           |
| dynamic quotient-boundary correction           | exact `(PL.9)`           |
| complete same-object bracket                   | exact `(PL.10)`          |
| normalized Douglas covariance                 | next batch              |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
