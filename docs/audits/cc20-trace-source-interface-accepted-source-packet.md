# CC20 Trace Source-Interface Accepted-Source Packet

Date: 2026-06-28

Status:

```text
CC20 trace accepted-source packet started
accepted-source certification: open
Lean status: not touched
```

## Purpose

This packet targets the CC20 source-interface theorem candidates for:

```text
support-square trace
trace-class legality
cyclic trace moves
Mellin and half-density convention
local signs and normalizations
```

The packet supplies the accepted-source front door for S2-B1. Trace legality
alone does not prove trace-scale compatibility, but the route cannot discuss
trace-scale compatibility until these source trace statements have exact
hypotheses.

## Source Anchors

| source | anchors | role |
|---|---|---|
| archimedean support-square trace | `weil-compo.tex:378-387` | support-square trace template and `traceequa` |
| trace-class verification | `weil-compo.tex:448-464` | trace-class part used before cyclic moves |
| Mellin/Fourier half-density convention | `weil-compo.tex:2014-2030` | transform convention for final vanishing |
| quantized-calculus trace ideal | `weil-compo.tex:2106-2121` | trace-ideal template used by trace legality |
| local signs and normalizations | `weil-compo.tex:2131-2165` | `u_infty`, `qd u`, and archimedean sign |

## Certification Chain

| row | theorem candidate | current evidence | accepted-source check |
|---|---|---|---|
| support-square trace | `CC20ArchimedeanTraceSquareTheorem(g)` | `docs/proofs/cc20-trace-legality-mellin-discharge.md`; `docs/proofs/cc20-trace-object-normalization-discharge.md` | confirm the source trace template applies to the transported route test |
| trace-class square | `CC20TraceClassForPositiveSquare(g)` | `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md` | confirm Hilbert-Schmidt and trace-class hypotheses hold before positivity |
| cyclic ledger | `CC20CyclicMoveWitnessLedger(g)` | `docs/proofs/cc20-analytic-trace-legality-spine-discharge.md` | confirm every cyclic move occurs inside the trace ideal |
| support-square after legality | `CC20SupportSquareAfterLegality(g)` | `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md` | confirm the support-square scalar is the same finite-lambda scalar as the positive trace |
| Mellin convention | `CC20MellinHalfDensityTheorem(F_g)` | `docs/proofs/cc20-trace-legality-mellin-discharge.md` | confirm route triple vanishing translates to CC20 Mellin vanishing on the same half-density object |
| local signs | `CC20LocalSignConventionTheorem(F_g)` | `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md`; `docs/proofs/final-sign-bridge-proof-package.md` | confirm local signs match the final sign packet |

## Rejection Conditions

A reviewer should reject this packet if one of these conditions occurs:

```text
1. positivity is used before trace-class legality;
2. a cyclic trace move lacks a trace-ideal witness;
3. support-square trace changes the scalar normalization;
4. Mellin vanishing uses a different half-density test than `F_g`;
5. local signs conflict with the final CCM25-to-CC20 sign bridge.
```

## Current Judgment

| question | answer |
|---|---|
| Does this packet make CC20 trace input accepted-source? | no |
| Does it give an exact accepted-source review packet? | yes |
| What remains? | external acceptance of trace legality, cyclicity, Mellin convention, and sign normalization |
| Did this pass touch Lean? | no |

The CC20 trace packet now gives reviewers a single place to certify the analytic
trace front end before checking S2-B1 and the final CC20 exit.
