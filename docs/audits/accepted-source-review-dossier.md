# Accepted-Source Review Dossier

Date: 2026-06-28

Status:

```text
review dossier ready
accepted-source certification: open
Lean status: not touched
```

## Purpose

This dossier gives an external reviewer one ordered entry point for the
accepted-source review.

The dossier does not accept any packet. It lists the packets, dependency order,
decision form, and required return format.

## Review Materials

Use these control files:

```text
docs/audits/accepted-source-referee-decision-form.md
docs/audits/accepted-source-certification-status-board.md
docs/audits/accepted-source-packet-completion-audit.md
docs/audits/accepted-source-decision-evidence-matrix.md
```

The theorem-decision records are:

```text
docs/audits/ccm24-source-interface-referee-decision-record.md
docs/audits/ccm25-source-interface-referee-decision-record.md
docs/audits/cc20-trace-source-interface-referee-decision-record.md
docs/audits/s2-b1-trace-scale-referee-decision-record.md
docs/audits/sign-defect-referee-decision-record.md
docs/audits/restricted-to-full-referee-decision-record.md
docs/audits/final-sign-referee-decision-record.md
docs/audits/cc20-exit-referee-decision-record.md
docs/audits/rh-definition-referee-decision-record.md
```

Use this packet order:

| order | packet | reviewer task |
|---:|---|---|
| 1 | `docs/audits/ccm24-source-interface-accepted-source-packet.md` | certify fixed-S model, support/window, bounded comparison, and Sonin comparison |
| 2 | `docs/audits/ccm25-source-interface-accepted-source-packet.md` | certify `QW`, `Psi`, `QW_lambda`, finite-prime atoms, pole normalization, and no-spectral boundary |
| 3 | `docs/audits/cc20-trace-source-interface-accepted-source-packet.md` | certify trace legality, support-square trace, cyclicity, Mellin convention, and local signs |
| 4 | `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` | certify S2-B1: no untracked divergent bulk or hidden finite-part subtraction |
| 5 | `docs/audits/sign-defect-accepted-source-packet.md` | certify Rows 1-7 sign/defect classification |
| 6 | `docs/audits/restricted-to-full-accepted-source-packet.md` | certify fixed-test `QW_lambda(g,g)=QW(g,g)` without spectral convergence |
| 7 | `docs/audits/final-sign-accepted-source-packet.md` | certify `QW(g,g)=-sum_v W_v(F_g)` and inequality direction |
| 8 | `docs/audits/cc20-exit-accepted-source-packet.md` | certify CC20 Proposition C.1 use with `F={0,1/2,1}` |
| 9 | `docs/audits/rh-definition-accepted-source-packet.md` | certify source RH to standard RH predicate bridge |

## Required Return

For each packet, return one verdict:

```text
accepted as stated
accepted after listed correction
rejected for listed obstruction
requires formalization before judgment
out of scope for this reviewer
```

For accepted packets, cite:

```text
source lines accepted:
theorem statement accepted:
hypotheses accepted:
object/test/sign bridges accepted:
limit order accepted:
non-importable shortcuts checked:
remaining caveats:
```

For rejected packets, cite:

```text
source line or theorem causing rejection:
missing hypothesis:
object mismatch:
sign mismatch:
limit-order failure:
named obstruction:
route consequence:
```

## First Packet To Decide

The first hostile-review packet is S2-B1:

```text
01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md
```

The project has opened a decision record:

```text
docs/audits/s2-b1-trace-scale-referee-decision-record.md
```

That record is pending external decision. It cannot promote S2-B1 until a
reviewer or formal theorem supplies the required evidence.

The base source-interface rows also have decision records:

```text
docs/audits/ccm24-source-interface-referee-decision-record.md
docs/audits/ccm25-source-interface-referee-decision-record.md
docs/audits/cc20-trace-source-interface-referee-decision-record.md
```

Those records decide whether the fixed-S CCM24 model, the CCM25 Weil objects,
and the CC20 trace front end can be treated as accepted-source theorem inputs.
They are pending external decision.

The downstream rows also have decision records:

```text
docs/audits/sign-defect-referee-decision-record.md
docs/audits/restricted-to-full-referee-decision-record.md
docs/audits/final-sign-referee-decision-record.md
docs/audits/cc20-exit-referee-decision-record.md
docs/audits/rh-definition-referee-decision-record.md
```

Those records decide the Rows 1-7 sign/defect theorem, fixed-test
restricted-to-full scalar equality, final sign equality, CC20 exit, and RH
definition bridge. They are also pending external decision.

## Current Judgment

| question | answer |
|---|---|
| Does this dossier accept any packet? | no |
| Does it make the accepted-source review executable? | yes |
| Have the source-interface rows been promoted to accepted-source theorem status? | no |
| Do all nine packets have theorem-decision records? | yes |
| Has any packet received an accepted-source verdict? | no |
| Did this pass touch Lean? | no |

The dossier turns packet coverage into a review workflow. Certification still
requires returned decisions or formal theorem records.
