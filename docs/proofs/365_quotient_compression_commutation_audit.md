# Proof 365: quotient-compression commutation audit

Date: 2026-07-18

Status: exact audit of the commutation step used by Proof 358.  The compact
detector commutes with the ambient Euler convolution, but Proof 343 transports
the fixed quotient by a compressed one-sided operator.  Compression does not
preserve commutation.  The missing commutator is an exact sum of two physical
boundary crossings.

This supersedes Proof 358 `(QR.9)--(QR.13)` and the route specialization of
Proof 364.  It does not invalidate Proof 358's fixed physical bracket, the
generic Douglas theorem, or the fixed factors from Proofs 361--363.  Gate 3U,
the finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| ambient detector/Euler commutation             | retained                 |
| quotient transport                             | compressed Euler block   |
| compression preserves commutation              | false in general        |
| missing quotient commutator                    | exact two-boundary sum   |
| Proof 358 prefix transport                     | requires correction      |
| finite certificate                             | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Actual quotient carrier

Use Proof 342's Burnol support projection `P` and put

```text
C=I-P.                                             (QA.1)
```

Let `V` be the ambient inverse Euler convolution.  Proof 342 uses causality
to define the quotient block

```text
V_C=C V C : Ran(C)->Ran(C).                        (QA.2)
```

After Hardy--Titchmarsh conjugation, Proof 343's operator is

```text
A_S=mathcalF V_C mathcalF                           (QA.3)
```

on `Ran(I-Q)`, where `Q=mathcalF P mathcalF`.  Thus `A_S` is not the ambient
operator `V` on the whole common-log carrier.

## 3. Compression does not preserve commutation

Write the same issue without the harmless unitary conjugation.  Let `E` be an
orthogonal projection, and let

```text
A=E V E |_Ran(E),
W_E=E W E |_Ran(E).                                (QA.4)
```

Even if

```text
[W,V]=0,                                           (QA.5)
```

one generally has

```text
[W_E,A]!=0.                                        (QA.6)
```

The inference from `(QA.5)` to `[W_E,A]=0` would additionally require `E` to
reduce `W` or `V`.  The Burnol quotient support is not known to satisfy such a
reducing-subspace theorem.

## 4. Exact missing boundary term

Expand the compressed commutator before estimating it:

```text
[W_E,A]
 =E[W,E] V E+E V [W,E]E.                           (QA.7)
```

Indeed,

```text
E[W,E]VE+EV[W,E]E
 =EWEVE-EWVE+EVWE-EVEWE
 =EWEVE-EVEWE,                                     (QA.8)
```

where the middle terms cancel by `(QA.5)`.  Equation `(QA.7)` is an operator
identity, not a trace cycle.

For a compact-root detector, `[W,E]` is exactly the completed outer
half-line crossing from Proofs 261 and 361.  Therefore the correction is
physical and boundary-local before the causal prefix is expanded.  It is not
an arbitrary quotient error term.

## 5. Consequence for Proof 358

Proof 358 applies the commuting transport formula of Proof 356 directly to
`A_<j`.  That is legal for an ambient Euler factor, but the fixed quotient in
Proof 343 is transported by `(QA.3)`.  Its correct crossing formula must
contain

```text
(I-P_<j)[W_E,A_<j]U_0 H_<j^(-1/2).                 (QA.9)
```

in addition to the transported fixed crossing.  Dropping `(QA.9)` removes
two actual Burnol-boundary channels and changes the operator being estimated.

The following statements are therefore superseded as route claims:

```text
Proof 358 `(QR.9)--(QR.13)`,
Proof 364 `(NP.6)--(NP.10)`.                        (QA.10)
```

Their generic matrix algebra remains correct under an explicit commutation
premise.  The premise is what fails on the actual quotient carrier.

## 6. Reproducible certificate

The companion finite probe constructs commuting positive normal matrices
`V,W`, compresses both to one nonreducing subspace, and checks

```text
[W,V]=0;
[W_E,A] is nonzero;
the exact boundary identity `(QA.7)`;
the quotient compression remains contractive.       (QA.11)
```

Run only in the unified five-batch verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/365_quotient_compression_commutation_audit_probe.py
```

The finite model refutes a carrier-independent inference.  The continuous
route correction is the algebraic identity `(QA.7)` itself.

## 7. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| fixed physical bracket from Proof 358          | retained                 |
| ambient commutation                            | retained                 |
| quotient commutation `(QR.9)`                  | rejected                 |
| exact correction `(QA.7)`                      | closed                   |
| corrected moving crossing                      | next batch              |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
