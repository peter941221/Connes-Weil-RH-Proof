# Proof 366: boundary-corrected quotient transport

Date: 2026-07-18

Status: exact replacement for Proof 358's commuting-prefix crossing formula.
For a detector compressed to the fixed Burnol quotient carrier, the moving
crossing is the sum of the transported old crossing and the compression
commutator identified by Proof 365.  Both terms retain the same Gram
normalization.

This repairs the operator identity but does not estimate its Hilbert--Schmidt
row uniformly.  Gate 3U, the finite-`S` sign, Burnol's identity, and RH remain
open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| quotient Gram-normalized frame                 | exact                    |
| transported old crossing                       | retained                 |
| compression-commutator correction              | mandatory               |
| scalar normalization                           | cancels exactly          |
| old-only transport                             | false in general        |
| uniform corrected row                          | open                    |
| finite certificate                             | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Quotient frame setup

Work on the quotient Hilbert carrier `E H`, with identity denoted by `E`.
Let

```text
U_0:H_0->E H,
U_0*U_0=I,
P_0=U_0 U_0*.                                      (QC.1)
```

Let `A:E H->E H` be bounded and invertible.  Define

```text
H_A=U_0* A* A U_0,
V_A=A U_0 H_A^(-1/2),
P_A=V_A V_A*.                                      (QC.2)
```

Then `V_A*V_A=I`, and `P_A` is the orthogonal projection onto `A Ran(P_0)`.

For the compressed detector

```text
W_E=E W E |_EH,                                    (QC.3)
```

put

```text
K_0=(E-P_0)W_E U_0,
K_A=(E-P_A)W_E V_A.                                (QC.4)
```

## 3. Correct transport identity

Use

```text
W_E A=A W_E+[W_E,A].                               (QC.5)
```

Substitution into `(QC.4)` gives

```text
K_A
 =(E-P_A)A W_E U_0 H_A^(-1/2)
  +(E-P_A)[W_E,A]U_0 H_A^(-1/2).                   (QC.6)
```

Split `W_EU_0` with `P_0+(E-P_0)`.  The `P_0` term is mapped by `A` into
`Ran(P_A)` and is killed by `E-P_A`.  Therefore

```text
K_A
 =(E-P_A)A(E-P_0)K_0 H_A^(-1/2)
  +(E-P_A)[W_E,A]U_0 H_A^(-1/2).                   (QC.7)
```

Equation `(QC.7)` is the corrected quotient transport.  It is an operator
identity before any trace cycle or Schatten estimate.

## 4. Relation to the ambient Euler operator

For the route,

```text
A=E V E,
[W,V]=0.                                           (QC.8)
```

Proof 365 gives

```text
[W_E,A]
 =E[W,E]VE+EV[W,E]E.                               (QC.9)
```

Thus the second term in `(QC.7)` consists of two completed physical boundary
crossings.  It is not a generic noncommutative remainder and may not be
dropped merely because the ambient convolution operators commute.

## 5. Scale invariance

Replace `A` by `cA` with `c>0`.  Then

```text
H_(cA)^(-1/2)=c^(-1)H_A^(-1/2),
P_(cA)=P_A,
[W_E,cA]=c[W_E,A].                                  (QC.10)
```

Both terms on the right of `(QC.7)` are unchanged.  Hence the Markov lower
factor may be inserted before taking norms without changing the moving
projection or its corrected crossing.

## 6. Why the old formula is not a harmless approximation

The omitted operator is exactly

```text
C_A=(E-P_A)[W_E,A]U_0 H_A^(-1/2).                  (QC.11)
```

There is no small parameter in `(QC.11)`.  Its two boundary factors can carry
the same compact-root scale as the transported fixed crossing.  Treating it
as higher order would repeat the quadratic-term omission rejected by Proofs
353--354.

The correct next step must recombine `(QC.7)` with the fixed
outer/second-support/prolate ledger before a norm.

## 7. Reproducible certificate

The companion probe uses a compressed pair of commuting ambient normal
matrices and checks

```text
the normalized-frame identities `(QC.2)`;
the corrected transport `(QC.7)`;
nonzero failure of the old-only formula;
scale invariance of both corrected terms.           (QC.12)
```

Run only in the unified five-batch verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/366_boundary_corrected_quotient_transport_probe.py
```

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| Proof 358 old transported term                | retained                 |
| quotient boundary correction                  | exact `(QC.9)`           |
| complete corrected crossing                   | exact `(QC.7)`           |
| old-only route formula                        | rejected                 |
| physical branch recombination                 | next batches            |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
