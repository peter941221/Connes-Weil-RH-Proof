# Proof 394: Schur-cascade Lean owner

Date: 2026-07-18

Status: generic noncommutative Lean ownership for the Schur-cascade algebra
closed in Proofs 390--393.  The module proves the local detector boundary
identity, the co-defect expansion, composition of intertwinement defects, the
raw-frame Gram readback, the ordered numerator, and the inverse-energy
increment.

The module deliberately stores no analytic adjoint semantics, positivity,
Douglas factorization, Schatten estimate, stable-coframe bound, or Gate 3U
premise.  Gate 3U, the finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| local detector intertwinement                 | Lean owner               |
| Schur co-defect boundary expansion            | Lean owner               |
| cascade defect composition                    | Lean owner               |
| raw inverse-frame Gram                        | Lean owner               |
| ordered Gram numerator                        | Lean owner               |
| dual inverse-energy increment                 | Lean owner               |
| stable-coframe estimate / Gate 3U              | deliberately absent     |
+------------------------------------------------+---------------------------+
```

## 2. Source module

The new source and audit modules are

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSSchurCascade.lean

ConnesWeilRH/Dev/
  CCM24FiniteSSchurCascadeAudit.lean.             (SL.1)
```

They work over an arbitrary noncommutative ring.  Formal daggers are supplied
as independent ring elements; the module does not claim they are analytic
Hilbert-space adjoints.

## 3. Local detector identity

For old and new frames `J_0,J_1`, formal coframes `J_0d,J_1d`, normalized
ambient transport `A`, and Schur transition `G`, assume

```text
J_0d J_0=I,
A J_1=J_0 G,
A W=W A.                                          (SL.2)
```

The theorem `detectorIntertwiningDefect_eq_boundary` proves

```text
G(J_1d WJ_1)-(J_0d WJ_0)G

 =-J_0d A(I-J_1J_1d)WJ_1.                        (SL.3)
```

This is Proof 392 `(CD.9)` as a theorem conclusion.

## 4. Co-defect expansion

Add the formal dagger relation

```text
J_1d A_d=G_d J_0d                              (SL.4)
```

and the new-frame isometry `J_1dJ_1=I`.  The theorem
`transitionCoDefect_eq_ambient_add_boundary` proves

```text
I-GG_d

 =J_0d(I-AA_d)J_0
  +[J_0dA(I-J_1J_1d)]
   [(I-J_1J_1d)A_dJ_0].                          (SL.5)
```

No positivity or Douglas premise is stored.  Those follow analytically only
after the formal daggers are instantiated by actual adjoints.

## 5. Cascade and Gram algebra

The theorem `intertwiningDefect_mul` proves the two-step induction kernel

```text
defect(A_0,G_1G_2,A_2)

 =G_1 defect(A_1,G_2,A_2)
  +defect(A_0,G_1,A_1)G_2.                        (SL.6)
```

Repeated use gives Proof 392 `(CD.19)` without commutativity.

The theorem `rawFrame_gram_eq_inverseGram` proves

```text
(Z^(-*)J*)(JZ^(-1))=Z^(-*)Z^(-1)                 (SL.7)
```

from `J*J=I`.  The theorem
`gramInverse_mul_numerator_eq_ordered` then proves the ordered multiplication

```text
(ZZ*)[Z^(-*) alpha Z^(-1)]
 =Z alpha Z^(-1).                                 (SL.8)
```

Equation `(SL.8)` retains the similarity order and does not cycle a trace.

## 6. Dual inverse energy

For formal inverses `G_i,G_di`, the theorem
`inverseDefect_eq_inverseGrowth` proves

```text
G_di(I-G_dG)G_i=G_diG_i-I.                        (SL.9)
```

The theorem `conjugated_inverseDefect_eq_delta_sub` wraps `(SL.9)` in the
previous inverse prefix and produces one increment of Proof 393 `(DC.7)`.
Summation and positivity remain outside the ring module.

## 7. Deliberate theorem boundary

The source contains no theorem resembling

```text
norm(Gamma_n^(-1)A_corr)_2^2-norm(A_corr)_2^2
 <=C(1+L+B_root)^d norm(g)_(H^r)^2.               (SL.10)
```

Equation `(SL.10)` is Proof 393's open stable-coframe theorem.  Adding it as a
field would hide the Gate instead of proving it.

## 8. Verification results

After all five proofs were complete, the unified WSL2 verification ran

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build \
    ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurCascade \
    ConnesWeilRH.Dev.CCM24FiniteSSchurCascadeAudit

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CCM25Concrete.    (SL.11)
```

The focused owner and audit pass with `575` jobs.  All seven audited theorems
use exactly

```text
[propext].                                         (SL.12)
```

The `CCM25Concrete` aggregate passes with `3665` jobs.  Replayed warnings are
from existing unrelated modules.

The first two focused attempts exposed only associativity visibility in
`rw`: Lean could not see `A J_1=J_0G` or the square of the complementary
projection under a longer product.  Adding named helper equalities and one
final `noncomm_ring` closed the original statements without weakening them.

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| Schur cascade ring identities                 | Lean-owned               |
| positivity / co-defect Douglas                | source mathematics      |
| physical root trace legality                  | Proofs 385--392          |
| stable coframe `(DC.19)`                       | open, active Gate bottom|
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
