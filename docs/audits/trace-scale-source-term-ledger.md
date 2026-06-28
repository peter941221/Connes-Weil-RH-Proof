# Trace-Scale Source Term Ledger

Date: 2026-06-28

Status:

```text
S2-B1 accepted-source packet started
accepted-source certification: open
Lean status: not touched
```

## Purpose

This ledger attacks the second external opinion's strongest objection:

```text
PositiveTrace may contain an untracked divergent bulk term
of size C log(lambda) ||g||^2.
```

The route can pass S2-B1 only if every source-owned scalar in the positive trace
read-off lands in one of the named route classes:

```text
QW_lambda(g,g)
Rank_(S,I)(g)
PoleJetExtra_(S,I)(g)
CdefRemainder_(S,I,lambda,J)(g)
```

Any source-owned scalar outside these classes becomes:

```text
BulkScaleTerm_(S,I,lambda,g)
```

and the route stops at the positive-trace read-off.

## Theorem Candidate

Accepted-source theorem target:

```text
CC20CCMTraceScaleNoBulkTheorem(S,I,lambda,g,F_g,J):
  PositiveTrace^G_(S,lambda)(g)
    =
  QW_lambda(g,g)
    + Rank_(S,I)(g)
    + PoleJetExtra_(S,I)(g)
    + CdefRemainder_(S,I,lambda,J)(g),

  and no additional scalar term
    BulkScaleTerm_(S,I,lambda,g)
  appears in the same finite-lambda normalization.
```

This is stronger than trace legality. Trace legality says the trace and cyclic
moves make sense. This theorem says the scalar after those moves has the same
normalization as the restricted CCM25 quadratic form.

## Source Anchors

| source family | source anchors | role |
|---|---|---|
| CC20 support-square trace | `weil-compo.tex:378-387` | archimedean support-square trace template and `traceequa` |
| CC20 trace-class and trace ideal | `weil-compo.tex:448-464,2106-2121` | Hilbert-Schmidt, trace-class, and quantized-calculus trace ideal template |
| CC20 post-`Q` source remainder | `weil-compo.tex:710-719,747-761,875-878,1132-1140,1196-1199,1267-1270,1338-1360,2168-2250` | source-owned remainder itemization after finite vanishing |
| CC20 signs and local normalization | `weil-compo.tex:2131-2165` | archimedean sign and local Weil convention |
| CCM25 global `QW` and `Psi` | `mc2arXiv.tex:445-470` | `QW`, `Psi`, finite-prime, archimedean, and pole sign conventions |
| CCM25 restricted `QW_lambda` | `mc2arXiv.tex:530-540` | restricted form, pole term, finite-prime sum, and prime-power pairing |
| CCM24 fixed-S transport | `mainc2m24fine.tex:237-253,761-823,983-1003,1050-1060` | fixed semilocal model, support transport, bounded comparison, and Sonin comparison |

Source-line anchors prove location, not acceptance. A referee must still accept
that the theorem candidate below follows from these sources plus the project
bridges.

## Term Ledger

| source/route scalar | source anchor or route package | route class | accepted-source status | reviewer check |
|---|---|---|---|---|
| `PositiveTrace^G_(S,lambda)(g)` | `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md`; `docs/proofs/cc20-trace-legality-mellin-discharge.md` | starting ordinary trace scalar | theorem candidate | confirm the trace is the ordinary positive trace of the same transported operator |
| `SupportSquareTrace` | `weil-compo.tex:378-387`; `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md` | same scalar after legal cyclic moves | theorem candidate | confirm no finite-part subtraction or scalar renormalization occurs before the support-square trace |
| no-defect source main term | `docs/proofs/fixed-s-no-defect-compact-form-read-off.md`; `docs/proofs/ccm25-restricted-read-off-discharge.md` | `QW_lambda(g,g)` | project proof package | confirm the whole no-defect scalar, not a finite part after subtracting positive bulk, equals the CCM25 restricted form |
| CCM25 restricted main term | `mc2arXiv.tex:530-540`; `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md` | `QW_lambda(g,g)` | source theorem candidate | confirm the lambda window, pole term, and finite-prime cutoff match the trace read-off window |
| zero-mode / quotient channel | `docs/proofs/battle-1-test-quotient-proof-package.md`; `docs/proofs/rank-repair-finite-normal-form.md` | `Rank_(S,I)(g)` | project proof package | confirm triple vanishing kills the whole rank ledger and no rank-like scalar remains in `QW_lambda` |
| CCM25 pole functional | `mc2arXiv.tex:465-470,533-535`; `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md` | pole inside `QW_lambda` plus route `PoleJetExtra` separation | source theorem candidate plus project bridge | confirm the source pole term is not double counted between `QW_lambda` and `PoleJetExtra` |
| extra pole-jet channel | `docs/proofs/source-rank-pole-ledger-identification-proof-package.md` | `PoleJetExtra_(S,I)(g)` | project proof package | confirm triple vanishing kills the extra pole ledger after the source pole inside `QW_lambda` is separated |
| no-strip transported post-`Q` remainder | `docs/audits/cc20-post-q-remainder-term-map.md`; `docs/proofs/source-rank-pole-ledger-identification-proof-package.md` | rank or pole ledger | project proof package | confirm no no-strip channel escapes the rank/pole classification |
| endpoint-strip transported post-`Q` bulk term | `weil-compo.tex:1267-1270,1338-1346`; `docs/proofs/fixed-s-post-q-bulk-graph-transfer-proof-package.md`; `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md` | `CdefRemainder_(S,I,lambda,J)(g)` | project proof package | confirm the source bulk-looking term is endpoint-strip `Cdef`, not a global `C log(lambda)||g||^2` term outside the ledger |
| endpoint-strip transported boundary terms | `weil-compo.tex:1267-1270,1338-1360`; `docs/proofs/fixed-s-post-q-boundary-functional-transfer-proof-package.md`; `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md` | `CdefRemainder_(S,I,lambda,J)(g)` or rank/pole after Row 5 | project proof package | confirm moving and fixed endpoint evaluations are classified before ledger killing |
| source series tail | `weil-compo.tex:2168-2250`; `docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-proof-package.md`; `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md` | `CdefRemainder_(S,I,lambda,J)(g)` | project proof package | confirm source scalar convergence becomes fixed-S graph/trace-norm control for the same test |
| endpoint-strip `Cdef` exhaustion | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md`; `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md` | vanishing error term | project proof package | confirm `Cdef_(S,I,lambda,J)(g) -> 0` is pointwise for the fixed `g,S,I,J` used in the trace read-off |
| hypothetical `BulkScaleTerm_(S,I,lambda,g)` | no accepted source anchor yet | obstruction | not discharged if found | reviewer must give the source formula line and show it is outside `QW_lambda`, rank, pole, and `Cdef` |

## Bulk-Entry Points

The route must block a bulk term at four possible entry points.

| entry point | current blocking evidence | accepted-source gap |
|---|---|---|
| before support-square trace | `CC20TraceLegalityTheorem` candidate and `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md` | a referee must confirm the ordinary positive trace scalar is carried through without hidden regularization |
| during support-square transport | `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md` | a referee must confirm every projection-order leftover is either no-defect, rank, pole, or endpoint-strip |
| in no-defect read-off | `docs/proofs/fixed-s-no-defect-compact-form-read-off.md`; `docs/proofs/ccm25-restricted-read-off-discharge.md` | a referee must confirm the no-defect scalar equals full `QW_lambda`, not `QW_lambda` after subtracting an unlisted positive bulk |
| in projection defects | Rows 4-7 proof packages and `docs/audits/semilocal-fourth-defect-ledger.md` | a referee must confirm endpoint-strip `Cdef` exhausts every transported source remainder channel |

## Accepted-Source Review Questions

The B1 reviewer should answer each question with one of:

```text
accepted
accepted after listed correction
rejected for listed obstruction
requires formalization
```

Questions:

| question | why it matters |
|---|---|
| Does CC20 identify the ordinary positive trace and support-square trace as the same finite-lambda scalar? | protects positivity before any read-off |
| Does the no-defect read-off consume the same scalar normalization as CCM25 `QW_lambda`? | blocks finite-part drift |
| Is the CCM25 pole term separated from route `PoleJetExtra` without double counting? | blocks pole-sign and ledger errors |
| Are no-strip channels exhausted by rank and pole ledgers? | blocks hidden non-`Cdef` source terms |
| Are endpoint-strip channels exactly the route `Cdef` summands? | blocks fourth-defect and bulk leakage |
| Does the post-`Q` bulk-looking term become endpoint-strip `Cdef` rather than a global Weyl bulk term? | answers the second external opinion's strongest attack |
| Does the proof take a pointwise fixed-test limit, not a uniform-in-`g` or spectral limit? | protects the restricted-to-full bridge |

## Current Judgment

| question | answer |
|---|---|
| Does this ledger prove S2-B1 as an accepted-source theorem? | no |
| Does it give the first accepted-source review packet for S2-B1? | yes |
| What remains before acceptance? | referee or independent proof of each term classification above |
| Did this pass touch Lean? | no |

If any row in the term ledger is rejected, the route should name the rejected
term as a new obstruction before claiming full Weil positivity.
