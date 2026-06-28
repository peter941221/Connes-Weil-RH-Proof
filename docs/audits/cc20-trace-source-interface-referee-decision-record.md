# CC20 Trace Source-Interface Referee Decision Record

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
  docs/audits/cc20-trace-source-interface-accepted-source-packet.md

row group:
  CC20 trace source interface

theorem candidates:
  CC20ArchimedeanTraceSquareTheorem(g)
  CC20TraceClassForPositiveSquare(g)
  CC20CyclicMoveWitnessLedger(g)
  CC20SupportSquareAfterLegality(g)
  CC20MellinHalfDensityTheorem(F_g)
  CC20LocalSignConventionTheorem(F_g)

review type:
  pending external referee / independent proof check / Lean theorem
```

## Theorem Bundle To Decide

The reviewer must decide whether CC20 supplies the exact trace source interface
used before S2-B1:

```text
Hilbert-Schmidt witness before trace-class square,
trace-class witness before positive trace,
cyclicity witnesses for every trace move,
support-square trace for the same transported source test,
Mellin half-density convention for the same F_g,
local signs compatible with the final CCM25-to-CC20 sign bridge.
```

This row does not decide trace-scale compatibility. It decides whether the
source trace front end is legal enough for S2-B1 review.

## Evidence Submitted For Review

| evidence | role |
|---|---|
| `docs/audits/cc20-trace-source-interface-accepted-source-packet.md` | primary packet |
| `docs/proofs/cc20-trace-legality-mellin-discharge.md` | trace legality and Mellin project package |
| `docs/proofs/cc20-trace-object-normalization-discharge.md` | trace-object normalization package |
| `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md` | trace-legality theorem targets |
| `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md` | final sign orientation package |
| `docs/audits/source-reread-v0.2.md` | source-line map |

## Required Checks

| check | current project evidence | reviewer answer |
|---|---|---|
| positive trace is used only after Hilbert-Schmidt and trace-class witnesses | trace-legality package | pending |
| every cyclic trace move has a trace-ideal witness | analytic trace-legality spine | pending |
| support-square scalar is the same finite-lambda scalar as the positive trace | trace-object package and Battle 2 package | pending |
| Mellin half-density convention uses the same `F_g` | trace-legality Mellin package | pending |
| local signs agree with the final CCM25-to-CC20 sign bridge | final sign bridge package | pending |
| this front-end row does not silently prove S2-B1 | S2-B1 decision record | pending |

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

If the reviewer rejects the CC20 trace source-interface row, use the most
precise obstruction name:

```text
TraceLegalityBeforePositivityFailure(g)
CyclicTraceMoveWithoutIdealWitness(g)
SupportSquareScalarMismatch(g)
MellinHalfDensityMismatch(F_g)
CC20LocalSignMismatch(F_g)
TraceFrontEndClaimsS2B1TooEarly
```

## Current Judgment

| question | answer |
|---|---|
| Has the CC20 trace source-interface row been accepted-source? | no |
| Does this record collect the evidence for a decision? | yes |
| What remains? | external referee, independent proof, or Lean theorem decision |
| Did this pass touch Lean? | no |

This record opens the CC20 trace source-interface decision. It does not decide
it.
