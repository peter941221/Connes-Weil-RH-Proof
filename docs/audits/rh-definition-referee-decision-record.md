# RH Definition Referee Decision Record

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
  docs/audits/rh-definition-accepted-source-packet.md

row group:
  source RH to standard RH definition bridge

theorem candidate:
  SourceRHToStandardRHTheorem

review type:
  pending external referee / independent proof check / Lean theorem
```

## Theorem To Decide

The reviewer must decide whether the CC20 source RH conclusion implies the
standard Riemann Hypothesis predicate used by the route.

For later Lean certification, the target is:

```text
_root_.RiemannHypothesis
```

and its predicate shape is:

```text
forall s,
  riemannZeta s = 0
  -> not (exists n : Nat, s = -2 * (n + 1))
  -> s != 1
  -> s.re = 1 / 2.
```

## Evidence Submitted For Review

| evidence | role |
|---|---|
| `docs/audits/rh-definition-accepted-source-packet.md` | primary packet |
| `docs/proofs/rh-definition-bridge-proof-package.md` | route-evidence definition bridge |
| `docs/proofs/rh-definition-bridge-theorem-contract.md` | theorem-contract target |
| `docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md` | source-to-Mathlib bridge package |
| `docs/audits/cc20-exit-referee-decision-record.md` | CC20 source RH prerequisite |
| `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean` | local Mathlib predicate evidence |

## Required Checks

| check | current project evidence | reviewer answer |
|---|---|---|
| CC20's zeta object is the standard Riemann zeta function | RH definition packet and bridge package | pending |
| source non-trivial zeros match standard zeros after exclusions | RH definition proof package | pending |
| negative-even trivial zeros are excluded in the standard predicate | Mathlib local evidence | pending |
| the pole at `s=1` is excluded in the standard predicate | Mathlib local evidence | pending |
| the source critical line is exactly `s.re = 1/2` | RH definition spine and theorem contract | pending |
| the final route concludes the standard predicate, not a project-local substitute | route theorem target and definition bridge package | pending |

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
  not applicable

accepted limit order:
  not applicable

non-importable shortcuts checked:
  pending

remaining caveats:
  pending
```

## Rejection Names

If the reviewer rejects the RH definition row, use the most precise obstruction
name:

```text
SourceZetaStandardZetaMismatch
ZeroPredicateMismatch
NegativeEvenExclusionMismatch
PoleExclusionMismatch
CriticalLineMismatch
ProjectLocalRHTargetLeak
```

## Current Judgment

| question | answer |
|---|---|
| Has the RH definition row been accepted-source? | no |
| Does this record collect the evidence for a decision? | yes |
| What remains? | external referee, independent proof, or Lean theorem decision |
| Did this pass touch Lean? | no |

This record opens the RH definition accepted-source decision. It does not
decide it.
