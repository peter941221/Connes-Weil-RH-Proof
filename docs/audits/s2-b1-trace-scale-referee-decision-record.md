# S2-B1 Trace-Scale Referee Decision Record

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
  01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md

row name:
  S2-B1 trace-scale no-missing-bulk theorem

theorem candidate:
  CC20CCMTraceScaleNoBulkTheorem(S,I,lambda,g,F_g,J)

review type:
  pending external referee / independent proof check / Lean theorem
```

## Theorem To Decide

The reviewer must decide whether the sources and project bridges support:

```text
PositiveTrace^G_(S,lambda)(g)
  =
QW_lambda(g,g)
  + Rank_(S,I)(g)
  + PoleJetExtra_(S,I)(g)
  + CdefRemainder_(S,I,lambda,J)(g),

with no additional BulkScaleTerm_(S,I,lambda,g)
and no hidden finite-part subtraction.
```

## Evidence Submitted For Review

| evidence | role |
|---|---|
| `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` | primary term ledger |
| `docs/proofs/trace-scale-compatibility-proof-package.md` | project proof package for same-scale read-off |
| `docs/audits/ccm24-source-interface-accepted-source-packet.md` | fixed-S model and window packet |
| `docs/audits/ccm25-source-interface-accepted-source-packet.md` | CCM25 `QW_lambda` and finite-prime packet |
| `docs/audits/cc20-trace-source-interface-accepted-source-packet.md` | CC20 trace legality and sign packet |
| `docs/audits/sign-defect-accepted-source-packet.md` | source remainder classification packet |

## Required Checks

| check | current project evidence | reviewer answer |
|---|---|---|
| exact theorem statement matches S2-B1 | `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md`, "Theorem Candidate" | pending |
| exact hypotheses are present and sufficient | source-interface packets for CCM24, CCM25, and CC20 | pending |
| source anchors support the trace and restricted Weil objects | `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md`, "Source Anchors" | pending |
| route object equals source object | CCM24/CCM25/CC20 source-interface packets | pending |
| test object stays fixed | common `g` and `F_g` in the term ledger | pending |
| sign convention is correct | final sign and CC20 trace packets | pending |
| limit order is valid | restricted-to-full packet; no spectral input | pending |
| no non-importable shortcut enters | second external-opinion audit and restricted-to-full packet | pending |
| rejection conditions are absent | term ledger "Bulk-Entry Points" | pending |

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

If the reviewer rejects S2-B1, use the most precise obstruction name:

```text
BulkScaleTerm_(S,I,lambda,g)
HiddenFinitePartSubtraction_(S,I,lambda,g)
TraceScaleConventionMismatch_(S,I,lambda,g)
QWLambdaReadOffMismatch_(S,I,lambda,g)
CdefDoesNotDominateRemainder_(S,I,lambda,g,J)
```

## Current Judgment

| question | answer |
|---|---|
| Has S2-B1 been accepted-source? | no |
| Does this record collect the evidence for a decision? | yes |
| What remains? | external referee, independent proof, or Lean theorem decision |
| Did this pass touch Lean? | no |

This record opens the first accepted-source decision. It does not decide it.
