# CC20 Exit Referee Decision Record

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
  docs/audits/cc20-exit-accepted-source-packet.md

row group:
  CC20 finite-vanishing RH exit

theorem candidate:
  CC20FiniteVanishingRHExitTheorem(F_g)

review type:
  pending external referee / independent proof check / Lean theorem
```

## Theorem To Decide

The reviewer must decide whether CC20 Proposition C.1 can be used with:

```text
F = {0, 1/2, 1}
```

and whether the route supplies the exact CC20 hypotheses:

```text
route triple vanishing -> CC20 Mellin vanishing on F,
QW(g,g) >= 0 -> sum_v W_v(F_g) <= 0,
CC20 Proposition C.1 -> CC20 source RH.
```

## Evidence Submitted For Review

| evidence | role |
|---|---|
| `docs/audits/cc20-exit-accepted-source-packet.md` | primary packet |
| `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md` | route-evidence exit package |
| `docs/proofs/cc20-rh-exit-object-normalization-discharge.md` | source RH-exit object package |
| `docs/proofs/cc20-trace-legality-mellin-discharge.md` | Mellin convention package |
| `docs/audits/final-sign-referee-decision-record.md` | final sign prerequisite |
| `docs/audits/cc20-trace-source-interface-referee-decision-record.md` | CC20 trace/sign prerequisite |

## Required Checks

| check | current project evidence | reviewer answer |
|---|---|---|
| `F={0,1/2,1}` satisfies CC20 finite-set side conditions | CC20 exit packet | pending |
| route triple vanishing becomes CC20 Mellin vanishing on the same half-density object | Mellin package | pending |
| the route feeds `sum_v W_v(F_g) <= 0`, not raw `QW(g,g) >= 0` | final sign decision record | pending |
| Proposition C.1 states the exact implication used by the route | CC20 exit package | pending |
| no hidden uniform-in-`g` hypothesis is required beyond the route's pointwise `forall g` proof | S-local/global quantifier audit | pending |
| the conclusion is the CC20 source RH predicate consumed by the definition bridge | RH-exit object package | pending |

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

If the reviewer rejects the CC20 exit row, use the most precise obstruction
name:

```text
CC20FiniteSetSideConditionFailure
MellinVanishingMismatch(F_g)
CC20SignInputMismatch(F_g)
UniformityRequirementMismatch
PropositionC1StatementMismatch
CC20SourceRHConclusionMismatch
```

## Current Judgment

| question | answer |
|---|---|
| Has the CC20 exit row been accepted-source? | no |
| Does this record collect the evidence for a decision? | yes |
| What remains? | external referee, independent proof, or Lean theorem decision |
| Did this pass touch Lean? | no |

This record opens the CC20 exit accepted-source decision. It does not decide it.
