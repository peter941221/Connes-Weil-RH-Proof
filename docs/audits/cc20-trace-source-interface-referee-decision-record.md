# CC20 Trace Source-Interface Referee Decision Record

Date opened: 2026-06-28

Status:

```text
decision record opened
verdict: pending external decision
accepted-source certification: open
Lean status: theorem-base trace fields discharged
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
| `ConnesWeilRH/Source/CC20TheoremBase.lean` | Lean theorem-base record and compact-interface constructor |
| `ConnesWeilRH/Source/CC20TraceModel.lean` | trace source-model laws for the discharged theorem-base fields |

## Lean Theorem-Base Record

Goal 1 added the data-bearing target:

```text
ConnesWeilRH.Source.CC20TheoremBase
```

It carries:

```text
archimedeanSymbols
archimedeanTraceSquare
traceClassTemplate
mellinHalfDensityConvention
signsAndNormalizations
rhDefinitionBridge
cc20RHExitObjectPackage
```

The constructor
`ConnesWeilRH.Source.CC20TheoremBase.toInterface` builds `CC20Interface`
without using `SourceObligation.Holds`.

Axiom audit:

```text
'ConnesWeilRH.Source.CC20TheoremBase.toInterface' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The listed dependencies are Lean/Mathlib foundations already present in the
project's normal audits.

Goal 1B now provides `CC20TraceModel` and
`CC20TheoremBase.dischargedTraceBase`. The constructor projects trace
source-model laws into the theorem-base fields. The finite-vanishing RH exit
object remains explicit Goal 5 data.

Axiom audit:

```text
'ConnesWeilRH.Source.cc20_source_archimedean_trace_square' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConnesWeilRH.Source.cc20_source_trace_class_template' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConnesWeilRH.Source.cc20_source_mellin_half_density_convention' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConnesWeilRH.Source.cc20_source_signs_and_normalizations' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConnesWeilRH.Source.CC20TheoremBase.dischargedTraceBase' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Required Checks

| check | current project evidence | reviewer answer |
|---|---|---|
| positive trace is used only after Hilbert-Schmidt and trace-class witnesses | `CC20TraceModel` and `cc20_source_trace_class_template` | Lean trace-base field discharged |
| every cyclic trace move has a trace-ideal witness | `CC20TraceModel` trace-class template | Lean trace-base field discharged |
| support-square scalar is the same finite-lambda scalar as the positive trace | `CC20TraceModel` and `cc20_source_archimedean_trace_square` | Lean trace-base field discharged |
| Mellin half-density convention uses the same `F_g` | `CC20TraceModel` and `cc20_source_mellin_half_density_convention` | Lean trace-base field discharged |
| local signs agree with the final CCM25-to-CC20 sign bridge | `CC20TraceModel` and `cc20_source_signs_and_normalizations` | Lean trace-base field discharged |
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
| What remains? | CC20 finite-vanishing RH exit, final sign, and downstream sign/defect packets |
| Did this pass touch Lean? | yes, source-model trace fields and constructor added |

This record opens the CC20 trace source-interface decision. It does not decide
it.
