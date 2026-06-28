# Accepted-Source Certification Status Board

Date: 2026-06-28

Status:

```text
certification tracking board ready
accepted-source certification: open
Lean status: not touched
```

## Purpose

This board tracks accepted-source decisions for every source-facing packet.

The decision evidence matrix is:

```text
docs/audits/accepted-source-decision-evidence-matrix.md
```

It separates three states:

```text
packet written
decision received
row accepted-source
```

The project currently has packet coverage. It does not yet have accepted-source
decisions.

## Status Legend

| status | meaning |
|---|---|
| packet written | referee packet exists and can be reviewed |
| decision record opened | packet has a theorem-decision record, but no verdict |
| in review | a reviewer has the packet |
| accepted after correction | reviewer accepted after listed correction; correction not yet verified |
| accepted-source | reviewer or Lean proof accepted the exact row |
| rejected | reviewer supplied an obstruction |
| formalization required | reviewer requires Lean or equivalent formal proof before judgment |

## Board

| order | packet | row group | current status | next action |
|---:|---|---|---|---|
| 1 | `docs/audits/ccm24-source-interface-accepted-source-packet.md` | CCM24 fixed-S model, support/window, bounded comparison, Sonin comparison | decision record opened | complete `docs/audits/ccm24-source-interface-referee-decision-record.md` by external decision or theorem |
| 2 | `docs/audits/ccm25-source-interface-accepted-source-packet.md` | CCM25 `QW`, `Psi`, `QW_lambda`, finite-prime atoms, pole normalization, no-spectral boundary | decision record opened | complete `docs/audits/ccm25-source-interface-referee-decision-record.md` by external decision or theorem |
| 3 | `docs/audits/cc20-trace-source-interface-accepted-source-packet.md` | CC20 trace legality, support-square trace, cyclicity, Mellin convention, local signs | decision record opened | complete `docs/audits/cc20-trace-source-interface-referee-decision-record.md` by external decision or theorem |
| 4 | `docs/audits/trace-scale-source-term-ledger.md` | S2-B1 trace-scale no-missing-bulk theorem | decision record opened | complete `docs/audits/s2-b1-trace-scale-referee-decision-record.md` after rows 1-3 or with the same reviewer |
| 5 | `docs/audits/sign-defect-accepted-source-packet.md` | Rows 1-7 sign/defect classification | decision record opened | complete `docs/audits/sign-defect-referee-decision-record.md` after CCM24 and CC20 trace decisions |
| 6 | `docs/audits/restricted-to-full-accepted-source-packet.md` | fixed-test `QW_lambda(g,g)=QW(g,g)` | decision record opened | complete `docs/audits/restricted-to-full-referee-decision-record.md` after CCM25 decision |
| 7 | `docs/audits/final-sign-accepted-source-packet.md` | `QW(g,g)=-sum_v W_v(F_g)` and inequality direction | decision record opened | complete `docs/audits/final-sign-referee-decision-record.md` after CCM25 and CC20 sign checks |
| 8 | `docs/audits/cc20-exit-accepted-source-packet.md` | CC20 Proposition C.1 finite-vanishing exit | decision record opened | complete `docs/audits/cc20-exit-referee-decision-record.md` after final sign decision |
| 9 | `docs/audits/rh-definition-accepted-source-packet.md` | source RH to standard RH definition bridge | decision record opened | complete `docs/audits/rh-definition-referee-decision-record.md` by external definition review or Lean theorem |

## Promotion Rule

A row becomes accepted-source only after the project records one of:

```text
accepted referee decision form
accepted independent proof reference
Lean theorem with #print axioms audit
```

The status board must record the evidence before README or certification audits
claim accepted-source status.

## Rejection Handling

If a reviewer rejects a packet, record:

```text
packet:
rejected row:
source line or theorem causing rejection:
named obstruction:
route consequence:
required repair:
```

Known obstruction names include:

```text
BulkScaleTerm_(S,I,lambda,g)
SemilocalFourthDefect_(S,I,lambda,g,F_g,J)
SpectralShortcutImport
FinitePrimeSupportMismatch
FinalSignMismatch
RHDefinitionDrift
```

## Current Judgment

| question | answer |
|---|---|
| Does every packet have a tracking row? | yes |
| Do the base source-interface rows have theorem-decision records? | yes |
| Do all nine packets have theorem-decision records? | yes |
| Does every packet have a row in the evidence matrix? | yes |
| Has any packet received an accepted-source decision? | no |
| Can README claim accepted-source certification now? | no |
| Did this pass touch Lean? | no |

The next real upgrade requires external decisions or formal theorem records.
