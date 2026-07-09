# Source-Conditional RH Route Closure Proof Package

Status: route-evidence composition package for the current Connes-Weil route.

This package composes the already written proof packages into one
source-conditional route closure. It does not prove any source paper theorem,
does not create a Lean theorem, and does not claim Clay, journal, or community
acceptance.

## Result

Good result:

```text
The current route is closed at route-evidence composition level.
```

Boundary:

```text
Accepted source-import status remains open.
Lean proof status remains open.
External certification remains open.
The public proof should still be described as source-conditional.
```

## Target

Compose:

```text
NoHiddenPositiveDefectOutsideCdef
RestrictedToFullQWBridgeContract
FinalSignBridgeContract
CC20FiniteVanishingRhExitDischarge
RHDefinitionBridgeContract
```

into:

```text
_root_.RiemannHypothesis
```

at route-evidence level.

## Dependency Graph

```text
PositiveTrace >= 0
        |
        v
NoHiddenPositiveDefectOutsideCdef
        |
        v
QW_lambda(g,g) >= -C Cdef(lambda,g)
        |
        v
RestrictedToFullQWBridgeContract
        |
        v
QW(g,g) >= 0
        |
        v
FinalSignBridgeContract
        |
        v
sum_v W_v(F_g) <= 0
        |
        v
CC20 Proposition C.1 with F={0,1/2,1}
        |
        v
CC20SourceRH
        |
        v
RHDefinitionBridgeContract
        |
        v
_root_.RiemannHypothesis
```

## Evidence Boundary

| step | evidence |
|---|---|
| no hidden positive defect | `docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md` |
| endpoint-strip `Cdef` exhaustion | `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md`; `docs/proofs/battle-3-cdef-exhaustion-proof-package.md`; `docs/proofs/fixed-test-graph-cdef-exhaustion.md` |
| restricted-to-full equality | `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` |
| final CCM25-to-CC20 sign bridge | `docs/proofs/final-sign-bridge-proof-package.md` |
| CC20 finite-vanishing exit | `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md`; `docs/proofs/cc20-rh-exit-object-normalization-discharge.md` |
| RH definition bridge | `docs/proofs/rh-definition-bridge-proof-package.md`; `docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md` |

## Lemma 1. Positive Trace Gives A Restricted Lower Bound

Statement:

```text
RestrictedLowerBoundAfterLedgerKilling(g):
  QW_lambda(g,g)
    >=
  - C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Proof.

Row 7 gives the exact read-off:

```text
PositiveTrace
  =
QW_lambda
  +
Rank
  +
PoleJetExtra
  +
R,

|R| <= C Cdef.
```

Triple vanishing kills:

```text
Rank = 0,
PoleJetExtra = 0.
```

Since:

```text
PositiveTrace >= 0,
```

the restricted lower bound follows.

Evidence:

```text
docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md
```

## Lemma 2. Restricted Lower Bound Gives Full QW Positivity

Statement:

```text
FullQWNonnegativity(g):
  QW(g,g) >= 0.
```

Proof.

The restricted-to-full bridge gives a fixed-test threshold:

```text
forall lambda >= lambda0,
  QW_lambda(g,g) = QW(g,g).
```

The endpoint-strip package gives:

```text
Cdef_(S,I,lambda,J)(g) -> 0.
```

Taking `lambda -> infinity` in Lemma 1 gives:

```text
QW(g,g) >= 0.
```

Evidence:

```text
docs/proofs/restricted-to-full-qw-bridge-proof-package.md
docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md
```

This step uses fixed-test scalar equality. It does not use finite-operator
spectral convergence.

## Lemma 3. Full QW Positivity Gives The CC20 Inequality

Statement:

```text
CC20WeilInequality(g):
  sum_v W_v(F_g) <= 0.
```

Proof.

The final sign bridge proves:

```text
QW(g,g) = - sum_v W_v(F_g).
```

Together with Lemma 2:

```text
QW(g,g) >= 0,
```

it gives:

```text
sum_v W_v(F_g) <= 0.
```

Evidence:

```text
docs/proofs/final-sign-bridge-proof-package.md
```

This is the inequality direction required by CC20 Proposition C.1.

## Lemma 4. The CC20 Finite-Vanishing Criterion Applies

Statement:

```text
CC20SourceRHFromRoute(g):
  CC20SourceRH.
```

Proof.

The final-exit package proves the finite set:

```text
F = {0,1/2,1}
```

is finite, contains `{0,1}`, and is disjoint from the non-trivial zero set.
It also translates route triple vanishing to CC20 Mellin vanishing on this
same finite set.

Lemma 3 supplies:

```text
sum_v W_v(F_g) <= 0.
```

Then CC20 Proposition C.1 gives source RH.

Evidence:

```text
docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md
docs/proofs/cc20-rh-exit-object-normalization-discharge.md
```

This package cites Proposition C.1 as a source theorem. It does not reprove
the Connes--Consani criterion.

## Lemma 5. Source RH Gives Mathlib RH

Statement:

```text
MathlibRHFromSourceRH:
  _root_.RiemannHypothesis.
```

Proof.

The RH definition bridge proves:

```text
CC20SourceRH -> _root_.RiemannHypothesis.
```

It exposes:

```text
source zeta = Mathlib riemannZeta,
source zero = riemannZeta s = 0,
source non-trivial zero = zero plus negative-even and pole exclusions,
source critical line = s.re = 1/2.
```

Apply the bridge to Lemma 4.

Evidence:

```text
docs/proofs/rh-definition-bridge-proof-package.md
```

## Theorem. Source-Conditional Route Closure

Statement:

```text
SourceConditionalRHRouteClosure:
  _root_.RiemannHypothesis
```

at route-evidence level, conditional on the source theorem contracts and proof
packages being accepted or formalized.

Proof.

Combine Lemmas 1 through 5.

The proof uses:

```text
positive trace with exact read-off,
ledger killing,
endpoint-strip Cdef exhaustion,
restricted-to-full fixed-test equality,
final CCM25-to-CC20 sign bridge,
CC20 finite-vanishing criterion,
source-RH-to-Mathlib-RH bridge.
```

It does not use:

```text
direct positive-trace-to-QW positivity,
hidden prolate/Sonin defect,
CCM25 spectral convergence,
determinant convergence,
route-local RH predicate,
or Lean axioms outside explicit source interfaces.
```

## Current Status

```text
Route-evidence composition:             closed
Accepted source-import status:          open
Lean proof status:                      open
External certification status:          open
Public proof status:                    source-conditional
```

## Certification Tasks Still Open

| task | reason |
|---|---|
| source theorem audit | replace proof-package evidence with accepted source theorem statements or referee-checkable proofs |
| Lean interface pass | encode the named contracts without hidden route-local predicates |
| axiom audit | verify final theorem depends only on explicit source interfaces and Mathlib/kernel foundations |
| public claim audit | do not claim unconditional RH until source interfaces are discharged |
