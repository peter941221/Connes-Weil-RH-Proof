# Source Object Replacement Consistency Audit

Status: consistency audit for the source-object replacement batch.

This audit checks the proof packages that replace symbolic route fields with
source-owned objects:

```text
docs/proofs/source-object-definition-spine-discharge.md
docs/proofs/ccm25-finite-prime-index-normalization-discharge.md
docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md
docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md
docs/proofs/cc20-trace-object-normalization-discharge.md
docs/proofs/cc20-analytic-trace-legality-spine-discharge.md
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md
docs/proofs/cc20-rh-exit-object-normalization-discharge.md
docs/proofs/final-sign-bridge-spine-discharge.md
docs/proofs/final-sign-bridge-theorem-contract.md
docs/proofs/rh-definition-bridge-spine-discharge.md
docs/proofs/ccm24-semilocal-object-normalization-discharge.md
```

It does not certify RH. It checks whether the batch gives one coherent target
for the next Lean or source-import phase.

## Result

Good result:

```text
The four new source-object packages fit the existing route dependency graph.
They refine symbolic fields without changing the mathematical target.
```

Bad result for final certification:

```text
The packages remain manuscript-level source-object replacement targets.
They are not formal Lean theorems and not accepted imported source theorems.
```

## Dependency Graph

The batch should be read in this order:

```text
source-definition spine
        |
        v
common source test and convolution square
        |
        v
CCM24 semilocal source window
        |
        v
CCM25 finite-prime and QW_lambda source objects
        |
        v
CC20 trace object and sign bridge
        |
        v
CC20 Proposition C.1 and Mathlib RH bridge
```

Reason:

| stage | object fixed | downstream dependency |
|---|---|---|
| common test | one `g` and `F_g=g^* * g` | every support, finite-prime, Mellin, and trace statement |
| CCM24 semilocal | fixed `S`, window `I`, `V_S=M_S U_S`, support transport | `QW_lambda`, finite-prime visibility, and Cdef exhaustion |
| CCM25 finite prime | prime-power indices, `1<n<=lambda^2`, `Lambda(n)`, `<g|T(n)g>` | restricted Weil form and final sign bridge |
| CC20 trace | trace test, trace-class gate, cyclicity witness ledger, positive trace, no-defect trace | positive-trace-to-Weil read-off |
| CC20 exit | `F={0,1/2,1}`, Proposition C.1, source RH, Mathlib RH | final theorem target |

## Package Interface Check

| package | primary symbolic record replaced | source-owned outputs | consistency judgment |
|---|---|---|---|
| `ccm24-semilocal-object-normalization-discharge.md` | `SemilocalModelSymbols` | source place set, support window, common test, canonical coordinate, support transport, bounded comparison, Sonin exhaustion | consistent with the fixed-window route and CCM25 restricted read-off |
| `ccm25-finite-prime-index-normalization-discharge.md`; `ccm25-finite-prime-normalization-spine-discharge.md`; `ccm25-finite-prime-normalization-theorem-contract.md` | finite-prime fields in `WeilFormSymbols` | source prime-power index, visibility in `F_g`, global support, restricted lambda cut, fixed-S visible-prime side condition, von Mangoldt weight, `T(n)` pairing, pointwise term normalization before summation, finite-prime sign ownership | consistent with global `Psi`, restricted `QW_lambda`, and fixed-S visible-prime side condition |
| `cc20-trace-object-normalization-discharge.md`; `cc20-analytic-trace-legality-spine-discharge.md`; `cc20-analytic-trace-legality-theorem-contract.md` | `ArchimedeanTraceSymbols` | source trace test, operator identity, Hilbert-Schmidt gate, trace-class positive square, per-move cyclicity witnesses, ordinary positive trace, support-square trace after legality, no-defect trace after support square, bounded-comparison trace-ideal transport, Mellin and sign bridges | consistent with Theorem 1 trace order and final sign bridge |
| `cc20-rh-exit-object-normalization-discharge.md`; `final-sign-bridge-spine-discharge.md`; `final-sign-bridge-theorem-contract.md`; `rh-definition-bridge-spine-discharge.md` | `FiniteVanishingCriterionPackage` | `F={0,1/2,1}`, source finite-set admissibility, Mellin vanishing, CC20 Weil inequality through common-test equality, source `Psi` expansion, named sign equality, inequality-direction theorem, Proposition C.1, Mathlib RH bridge through zeta, zero, exclusion, and line targets | consistent with source-RH-to-Mathlib-RH package |

## Cross-Package Invariants

### Invariant 1. One Test Object

Statement:

```text
The same source test g feeds CCM24 support, CCM25 F_g=g^* * g, CC20 trace,
and CC20 Mellin vanishing.
```

Evidence:

```text
docs/proofs/source-test-convolution-compatibility.md
docs/proofs/ccm24-semilocal-object-normalization-discharge.md
docs/proofs/cc20-trace-object-normalization-discharge.md
docs/proofs/cc20-rh-exit-object-normalization-discharge.md
```

Status:

```text
consistent.
```

Failure if broken:

```text
support, trace, finite-prime visibility, and Mellin vanishing can refer to
different functions.
```

### Invariant 2. One Lambda Window

Statement:

```text
The same CCM24 source window controls QW_lambda, finite-prime visibility, and
Cdef exhaustion.
```

Evidence:

```text
docs/proofs/ccm24-semilocal-object-normalization-discharge.md
docs/proofs/ccm25-restricted-qwlambda-window-discharge.md
docs/proofs/ccm25-finite-prime-index-normalization-discharge.md
docs/proofs/fixed-test-graph-cdef-exhaustion.md
```

Status:

```text
consistent.
```

Failure if broken:

```text
the positive trace can use one cutoff, the restricted Weil form another, and
the endpoint-strip exhaustion a third.
```

### Invariant 3. Finite-Prime Terms Are Pointwise Source Terms

Statement:

```text
finitePrimeTerm n F_g = Lambda(n)<g|T(n)g>
```

for each source prime-power index `n`.

Evidence:

```text
docs/proofs/ccm25-finite-prime-support-pairing-discharge.md
docs/proofs/ccm25-finite-prime-index-normalization-discharge.md
docs/proofs/ccm25-restricted-qwlambda-window-discharge.md
```

Status:

```text
consistent.
```

The batch now states the quantifier over `n` in the combined finite-prime
result. This prevents a sum-level equality from hiding a wrong atom.

Failure if broken:

```text
the restricted finite-prime sum can match after cancellation while individual
source terms use wrong weights or pairings.
```

### Invariant 4. Positivity Becomes CC20 Nonpositivity Only Through The Sign Bridge

Statement:

```text
QW(g,g) >= 0
  ->
sum_v W_v(g * bar(g)^sharp) <= 0
```

only after:

```text
QW(g,g) = - sum_v W_v(g * bar(g)^sharp).
```

Evidence:

```text
docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md
docs/proofs/cc20-trace-object-normalization-discharge.md
docs/proofs/cc20-rh-exit-object-normalization-discharge.md
```

Status:

```text
consistent.
```

Failure if broken:

```text
the final Proposition C.1 input can receive the wrong inequality direction.
```

### Invariant 5. Source RH Must Be Transported To Mathlib RH

Statement:

```text
CC20 source RH -> _root_.RiemannHypothesis.
```

Evidence:

```text
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md
docs/proofs/cc20-rh-exit-object-normalization-discharge.md
ConnesWeilRH/Route/RouteTheorem.lean:26-33
```

Status:

```text
consistent.
```

Failure if broken:

```text
the route proves a source-named RH while the final Lean theorem claims
Mathlib's predicate.
```

## Corrections Applied In This Audit

This audit pass tightened three package statements:

| file | correction |
|---|---|
| `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md` | the combined result now quantifies the source index `n` instead of listing unbound `n`-dependent outputs |
| `docs/proofs/cc20-trace-object-normalization-discharge.md` | the combined result now includes both `SourceSupportSquareTraceReadOff` and `SourceNoDefectTraceReadOff` |
| `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | the combined result now includes `SourceSupportAndFourierSupportTransport` before convolution-support transport |

These were presentation-level consistency fixes. They did not change the route
target.

## Lean Interface Consequence

The next Lean pass should not add finer names only to preserve the same opaque
shape. It should encode this dependency graph:

```text
SourceObjectPackage
  |
  +-- common source test and convolution square
  +-- CCM24 semilocal source window package
  +-- CCM25 finite-prime index and QW package
  +-- CC20 trace-object and sign package
  +-- CC20 RH-exit and Mathlib bridge package
```

The compact current records can still exist as derived views:

```text
SemilocalModelSymbols
WeilFormSymbols
ArchimedeanTraceSymbols
FiniteVanishingCriterionPackage
```

Certification should consume the expanded source-object package first, then
derive these compact records.

## Current Judgment

| question | answer |
|---|---|
| Do the four source-object packages cover the symbolic records named in the ledger? | yes |
| Do they preserve one test object through CCM24, CCM25, and CC20? | yes |
| Do they keep the finite-prime, trace, sign, and RH-exit bridges visible? | yes |
| Do they prove or import the source theorems? | no |
| Is this batch ready to become a signed source-object replacement milestone after hygiene checks? | yes |

The five remaining formal gates also have a spine-level consistency audit:

```text
docs/audits/formal-gate-spine-consistency-audit.md
```

That audit checks the ordered chain from source-definition spine through trace
legality, finite-prime normalization, final sign bridge, and the Mathlib RH
definition bridge.

The next step is either:

```text
sign and commit this source-object replacement batch
```

or:

```text
start a Lean interface pass that encodes the expanded package while keeping the
current compact records as derived views.
```
