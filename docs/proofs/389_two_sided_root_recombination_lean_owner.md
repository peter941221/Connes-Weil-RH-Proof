# Proof 389: two-sided root recombination Lean owner

Date: 2026-07-18

Status: generic noncommutative Lean ownership for the algebra closed by
Proofs 385--387.  The module splits projection commutators into both oriented
crossings, expands a commutator with a square into two square-root legs, and
proves the complete quotient-corrected physical ledger with both compression
boundary terms retained.

The module deliberately stores no trace, adjoint, Schatten, Gram/Julia
alignment, Douglas inequality, or causal analytic premise.  Proof 388 shows
that the missing Julia alignment is not a formal consequence of the owned
algebra.  Gate 3U, the finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| two oriented projection crossings             | Lean owner               |
| two-sided square-root commutator               | Lean owner               |
| compressed detector/prefix correction         | Lean owner               |
| fixed outer/second/prolate ledger              | Lean owner               |
| complete corrected quotient bracket           | Lean owner               |
| root-ledger recombination                      | Lean owner               |
| Gram/Julia or Schatten theorem                 | deliberately absent     |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Source module

The new source and audit modules are

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSTwoSidedRootRecombination.lean

ConnesWeilRH/Dev/
  CCM24FiniteSTwoSidedRootRecombinationAudit.lean. (LR.1)
```

The source works over an arbitrary noncommutative ring.

## 3. Oriented and square-root algebra

For the additive commutator

```text
[W,P]=W P-P W,                                     (LR.2)
```

Lean proves

```text
[W,P]
 =(I-P)W P-P W(I-P).                              (LR.3)
```

The theorem is
`commutator_eq_orientedCrossing_sub_reverse`.  It is purely additive and
does not require idempotence.

For a formal square `K=S S`, the theorem
`commutator_square_eq_twoSidedSquareRoot` proves

```text
[W,S S]=(W S)S-S(S W).                            (LR.4)
```

Equation `(LR.4)` is the ring-level owner of Proof 386 `(RP.13)`.  The fact
that both displayed legs are Hilbert--Schmidt is analytic and is not encoded
as a premise.

## 4. Quotient-compression correction

Let `E` be idempotent and assume `W V=V W` in the ambient ring.  Define

```text
W_E=E W E,
V_E=E V E.                                        (LR.5)
```

The theorem `compressed_commutator_eq_boundary` proves

```text
[W_E,V_E]
 =E[W,E]V E+E V[W,E]E.                            (LR.6)
```

Thus both corrections found by Proof 365 are theorem conclusions, not stored
fields.

## 5. Fixed and moving physical ledgers

For a formal second support `Q` and a prolate remainder `K` supported by `E`,
define

```text
R=E Q E-K.                                        (LR.7)
```

The theorem `compressed_source_commutator_eq_physical` proves

```text
[W_E,R]
 =E[W,E]Q E
  +E[W,Q]E
  +E Q[W,E]E
  -E[W,K]E.                                       (LR.8)
```

Combining `(LR.6)` and `(LR.8)`, the theorem
`correctedQuotientBracket_eq_physical` proves

```text
-V_E[W_E,R]+[W_E,V_E]

 =-V_E(
     E[W,E]Q E
    +E[W,Q]E
    +E Q[W,E]E
    -E[W,K]E)
   +E[W,E]V E
   +E V[W,E]E.                                    (LR.9)
```

Equation `(LR.9)` is Proof 368 `(PL.10)` with every sign and both quotient
corrections present.

Finally, `correctedPhysicalBracket_eq_twoSidedRootLedger` substitutes
`(LR.3)--(LR.4)` into `(LR.9)`.  It does not distribute the result into
branch norms or take a trace.

## 6. Deliberate theorem boundary

The Lean module stops at the exact operator ledger

```text
complete corrected bracket
  =one signed combination of oriented root products.            (LR.10)
```

It does not assert

```text
Tr(D_j*R_j)=<Lhat_j,R_jAhat_j*>_(S_2),

Ahat_j=Z_jS_jJ_(j-1)Psi_(j-1)A_root,

mathcalY_root*mathcalY_root
 <=C^2 mathcalS_A*mathcalS_A.                     (LR.11)
```

The first line is the continuous two-`S_2` contract proved mathematically in
Proofs 385--387.  The latter two are the source-specific alignment rejected
as an abstract inference by Proof 388 and remain open.

## 7. Verification results

After all five proofs were complete, the unified WSL2 verification ran

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build \
    ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTwoSidedRootRecombination \
    ConnesWeilRH.Dev.CCM24FiniteSTwoSidedRootRecombinationAudit

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CCM25Concrete.    (LR.12)
```

The focused owner and audit pass with `576` jobs.  All six audited theorems
use exactly

```text
[propext].                                         (LR.13)
```

The `CCM25Concrete` aggregate passes with `3664` jobs.  Replayed warnings are
from existing unrelated modules.

The first three focused attempts exposed implementation-only issues.  Lean
reserves `prefix` as syntax, two associative rewrites initially carried one
extra support factor, and the final successful rewrite made one trailing
`noncomm_ring` redundant.  Renaming the variable to `transport`, correcting
the two ring expansions, and removing the already-closed tactic fixed the
source without changing any theorem statement.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| corrected noncommutative ledger               | Lean-owned               |
| two-sided analytic insertion                  | Proofs 385--387          |
| automatic Gram/Julia alignment                | rejected, Proof 388     |
| source-specific causal Julia insertion        | open                    |
| Proof 382 `(JR.9)/(JR.19)`                    | still open               |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
