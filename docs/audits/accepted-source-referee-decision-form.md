# Accepted-Source Referee Decision Form

Date: 2026-06-28

Status:

```text
decision form ready
accepted-source certification: open
Lean status: not touched
```

## Purpose

Use this form when an external reviewer, independent proof checker, or future
formalization pass evaluates one accepted-source packet.

Accepted-source status requires a written decision for the exact packet row.
Project proof packages, source-line locations, and route notation matches do
not count by themselves.

## Allowed Verdicts

Use one verdict per packet:

```text
accepted as stated
accepted after listed correction
rejected for listed obstruction
requires formalization before judgment
out of scope for this reviewer
```

Only the first two verdicts can promote a row toward accepted-source status.
If the verdict is `accepted after listed correction`, the correction must be
applied and rechecked before the project treats the row as accepted.

## Packet Under Review

```text
packet file:
row name:
reviewer:
review date:
review type:
  external referee / independent proof check / Lean theorem / other
```

## Required Checks

| check | reviewer answer | notes |
|---|---|---|
| exact theorem statement matches the packet target |  |  |
| exact hypotheses are present and sufficient |  |  |
| source anchors support the theorem statement |  |  |
| route object equals source object |  |  |
| test object stays fixed |  |  |
| sign convention is correct |  |  |
| limit order is valid |  |  |
| no non-importable shortcut enters |  |  |
| rejection conditions in the packet are absent |  |  |

## Evidence Required For Acceptance

The reviewer must cite the exact evidence used:

```text
source file and line ranges:
project packet rows accepted:
external theorem or proof reference:
Lean theorem name and #print axioms output, if formalized:
corrections required before acceptance:
```

## Decision

```text
verdict:

accepted theorem statement:

accepted hypotheses:

accepted object bridges:

accepted sign bridges:

accepted limit order:

non-importable shortcuts checked:

remaining caveats:
```

## Project Follow-Up

Project maintainer must fill this block after receiving a decision:

```text
decision recorded in status board:
README status updated:
accepted-source-certification-audit updated:
if rejected, obstruction named:
if corrected, correction committed:
if formalized, axiom audit recorded:
```

## Current Judgment

| question | answer |
|---|---|
| Does this form accept any row by itself? | no |
| Does it define the evidence needed for acceptance? | yes |
| Did this pass touch Lean? | no |

No packet should be promoted without a completed decision form or an equivalent
formal proof record.
