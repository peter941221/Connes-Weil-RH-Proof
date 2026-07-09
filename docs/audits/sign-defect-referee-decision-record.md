# Sign-Defect Referee Decision Record

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
  docs/audits/sign-defect-accepted-source-packet.md

row group:
  Rows 1-7 sign/defect classification

theorem candidate:
  SourceSignDefectClassificationTheorem(S,I,lambda,g,F_g,J)

review type:
  pending external referee / independent proof check / Lean theorem
```

## Theorem To Decide

The reviewer must decide whether the sources and project bridge packages
support this finite-lambda read-off:

```text
PositiveTrace^G_(S,lambda)(g)
  =
QW_lambda(g,g)
  + Rank_(S,I)(g)
  + PoleJetExtra_(S,I)(g)
  + R_(S,I,lambda,J)(g),

|R_(S,I,lambda,J)(g)|
  <= C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g),
```

with no source-owned positive summand outside rank, pole, and endpoint-strip
`Cdef`.

The reviewer must keep one tuple fixed:

```text
(S,I,lambda,g,F_g,J).
```

## Evidence Submitted For Review

| evidence | role |
|---|---|
| `docs/audits/sign-defect-accepted-source-packet.md` | primary packet |
| `docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md` | Rows 1-2 source orientation package |
| `docs/proofs/sonin-prolate-defect-referee-discharge.md` | Rows 3-7 referee-facing package |
| `docs/audits/sonin-prolate-defect-discharge-ledger.md` | row-by-row defect ledger |
| `docs/audits/semilocal-fourth-defect-ledger.md` | fourth-defect falsification ledger |
| `docs/audits/ccm24-source-interface-referee-decision-record.md` | fixed-S source-interface prerequisite |
| `docs/audits/cc20-trace-source-interface-referee-decision-record.md` | CC20 trace source-interface prerequisite |

## Required Checks

| check | current project evidence | reviewer answer |
|---|---|---|
| Rows 1-2 identify the CC20 source obstruction and post-`Q` image | rows 1-2 referee package | pending |
| Row 3 transports bulk, boundary, and tail before classification | Sonin/prolate referee package | pending |
| Row 3 uses the same fixed-S coordinate as the positive trace | CCM24 decision record and Row 3 packages | pending |
| Row 4 classifies only the transported source remainder | projection-defect normal-form package | pending |
| Row 5 sends every no-strip term to rank or pole | rank/pole ledger package | pending |
| Row 6 matches every endpoint-strip term to route `Cdef` | endpoint-strip `Cdef` package | pending |
| Row 7 proves no fifth positive summand remains | no-hidden-defect package and fourth-defect ledger | pending |
| no spectral or determinant convergence enters | second external-opinion audit | pending |

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

If the reviewer rejects the sign/defect row, use the most precise obstruction
name:

```text
CC20PostQSourceTermMissing(g)
FixedSTransportObjectDrift(S,I,lambda,g,F_g)
ProjectionDefectNormalFormMismatch(S,I,lambda,g,F_g,J)
RankPoleLedgerMismatch(S,I,lambda,g,F_g)
EndpointStripCdefMismatch(S,I,lambda,g,F_g,J)
SemilocalFourthDefect_(S,I,lambda,g,F_g,J)
SpectralShortcutImport
```

## Current Judgment

| question | answer |
|---|---|
| Has the sign/defect row been accepted-source? | no |
| Does this record collect the evidence for a decision? | yes |
| What remains? | external referee, independent proof, or Lean theorem decision |
| Did this pass touch Lean? | no |

This record opens the sign/defect accepted-source decision. It does not decide
it.
