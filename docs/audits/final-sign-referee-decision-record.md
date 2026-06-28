# Final Sign Referee Decision Record

Date opened: 2026-06-28

Status:

```text
decision record opened
verdict: pending external decision
accepted-source certification: open
Lean status: not touched
```

## Packet Under Review

```text
packet file:
  docs/audits/final-sign-accepted-source-packet.md

row group:
  CCM25-to-CC20 final sign bridge

theorem candidate:
  FinalCCM25CC20SignTheorem(g,F_g)

review type:
  pending external referee / independent proof check / Lean theorem
```

## Theorem To Decide

The reviewer must decide whether the sources and project bridge packages prove:

```text
QW(g,g) = - sum_v W_v(F_g)
```

for the same convolution square:

```text
F_g = g^* * g.
```

The reviewer must also decide the inequality direction:

```text
QW(g,g) >= 0
  ->
sum_v W_v(F_g) <= 0.
```

## Evidence Submitted For Review

| evidence | role |
|---|---|
| `docs/audits/final-sign-accepted-source-packet.md` | primary packet |
| `docs/proofs/final-sign-bridge-proof-package.md` | route-evidence sign package |
| `docs/proofs/final-sign-bridge-theorem-contract.md` | theorem-contract target |
| `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md` | sign-orientation bridge |
| `docs/audits/ccm25-source-interface-referee-decision-record.md` | CCM25 `QW`/`Psi` prerequisite |
| `docs/audits/cc20-trace-source-interface-referee-decision-record.md` | CC20 sign convention prerequisite |

## Required Checks

| check | current project evidence | reviewer answer |
|---|---|---|
| `QW(g,g)` and the CC20 local Weil sum use the same `F_g` | common-test and final-sign packages | pending |
| source `QW=Psi` is accepted for the same test | CCM25 decision record | pending |
| `Psi` expansion owns archimedean, finite-prime, and pole signs | final sign packet | pending |
| finite-prime signs come from the source formula pointwise | finite-prime theorem contract | pending |
| pole terms are neither omitted nor counted twice | final sign packet | pending |
| multiplying by `-1` gives the CC20 nonpositive inequality | final sign proof package | pending |

## Decision Block

External reviewer or formal proof must fill this block.

```text
verdict:
  pending

accepted theorem statement:
  pending

accepted hypotheses:
  pending

accepted object bridges:
  pending

accepted sign bridges:
  pending

accepted limit order:
  pending

non-importable shortcuts checked:
  pending

remaining caveats:
  pending
```

## Rejection Names

If the reviewer rejects the final sign row, use the most precise obstruction
name:

```text
FinalSignMismatch(g,F_g)
QWCC20TestMismatch(g,F_g)
PsiExpansionSignMismatch(F_g)
FinitePrimeSignMismatch(F_g)
PoleSignMismatch(F_g)
InequalityDirectionMismatch(g,F_g)
```

## Current Judgment

| question | answer |
|---|---|
| Has the final sign row been accepted-source? | no |
| Does this record collect the evidence for a decision? | yes |
| What remains? | external referee, independent proof, or Lean theorem decision |
| Did this pass touch Lean? | no |

This record opens the final sign accepted-source decision. It does not decide
it.
