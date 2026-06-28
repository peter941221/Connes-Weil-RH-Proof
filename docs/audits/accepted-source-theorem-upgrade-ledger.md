# Accepted-Source Theorem Upgrade Ledger

Date: 2026-06-28

Status:

```text
accepted-source upgrade work started
no row is marked accepted-source by this ledger
Lean status: not touched
```

## Purpose

This ledger upgrades the review shape of the source-interface rows. It does not
upgrade their proof status by assertion.

An accepted-source row must satisfy the acceptance checklist from
`docs/audits/source-import-legitimacy-audit.md`:

```text
exact theorem statement
exact hypotheses
object identity bridge
sign convention bridge
test identity bridge
limit order
proof status
```

The current target is to turn each row into a referee-checkable theorem
candidate. A row becomes accepted-source only after an external theorem,
referee report, or independently checked proof accepts that exact statement and
hypotheses.

## Certification Classes

| class | meaning | route use |
|---|---|---|
| source anchor | the source file contains the object, formula, or theorem range | location evidence only |
| theorem candidate | the repository states the exact theorem shape and hypotheses to certify | review packet |
| project proof package | the repository gives a manuscript-level derivation from source anchors | route evidence |
| accepted-source theorem | a referee or accepted proof confirms the exact theorem and bridge hypotheses | usable as certified input |
| Lean theorem | Lean proves the row with audited axioms | formal input |

Current batch status:

```text
source anchors: present for the main rows
theorem candidates: strengthened by this ledger
accepted-source theorem rows: none yet
Lean theorem rows: none yet
```

## Upgrade Matrix

| row | theorem candidate | source anchors | current evidence | upgrade blocker |
|---|---|---|---|---|
| CCM24 fixed-S model | `CCM24FixedSModelTheorem(S)` supplies the canonical semilocal Hilbert model, `U_S`, `M_S`, `V_S=M_S U_S`, and Fourier grading for the same finite place set | `mainc2m24fine.tex:237-253,786-804` | `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | exact hypotheses for the finite set `S`, Hilbert space identifications, and route coordinate equality need referee acceptance |
| CCM24 support/window transport | `CCM24WindowTransportTheorem(S,I,g)` transports support, Fourier support, and convolution-square support through one source-backed window | `mainc2m24fine.tex:761-771,983-1003` | `docs/proofs/ccm24-support-window-transport-discharge.md` | concrete support predicates must be matched to the route interval `I subset [lambda^-1,lambda]` |
| CCM24 bounded comparison | `CCM24BoundedComparisonTheorem(S)` gives the bounded comparison map and bounded inverse used before trace read-off | `mainc2m24fine.tex:806-823` | `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | trace-ideal preservation through the comparison map must be stated with the same operator class |
| CCM24 Sonin comparison | `CCM24FixedWindowSoninComparison(S,I,g)` compares the fixed-window Sonin object used by the route without changing `S`, `I`, or `g` | `mainc2m24fine.tex:1050-1060` | `docs/proofs/ccm24-support-window-transport-discharge.md` | fixed-window exhaustion must stay pointwise in `g`, not uniform over the test space |
| CCM25 `QW` and `Psi` | `CCM25QWDefinitionTheorem(g)` states `QW(g,g)=Psi(F_g)` with the route convolution square | `mc2arXiv.tex:445-470` | `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md` | source `f,g,kappa` notation must be bridged to route `g,F_g` without changing test conventions |
| CCM25 restricted form | `CCM25QWLambdaRestrictionTheorem(lambda,g)` states that `QW_lambda` is the restriction of `QW` on the source interval and gives the displayed restricted formula | `mc2arXiv.tex:530-540` | `docs/audits/restricted-to-full-qw-source-readiness-audit.md`; `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` | support containment and finite-prime support stabilization must be accepted for the same fixed test |
| CCM25 finite-prime normalization | `CCM25FinitePrimeTermTheorem(lambda,g,n)` states the prime-power atom, von Mangoldt weight, and `<g|T(n)g>` pairing before sums are formed | `mc2arXiv.tex:445-470,530-540` | `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` | symbolic index sets must be replaced or externally accepted as exact source prime-power supports |
| CCM25 pole normalization | `CCM25PoleNormalizationTheorem(lambda,g)` identifies the source pole term inside `QW_lambda` and separates it from route `PoleJetExtra` | `mc2arXiv.tex:465-470,533-535` | `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md` | pole sign and half-density convention must be checked against the final CC20 sign bridge |
| CC20 trace legality | `CC20TraceLegalityTheorem(S,I,lambda,g)` gives Hilbert-Schmidt, trace-class, cyclicity, and support-square legality for the transported source test | `weil-compo.tex:378-387,448-464,2106-2121` | `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md` | every cyclic move must name the trace ideal and the same transported operator |
| S2-B1 trace-scale equality | `CC20CCMTraceScaleNoBulkTheorem(S,I,lambda,g,J)` states the positive trace equals `QW_lambda + Rank + Pole + CdefRemainder` with no extra bulk or finite-part term | combined CC20/CCM25 anchors below | `docs/audits/trace-scale-source-term-ledger.md`; `docs/proofs/trace-scale-compatibility-proof-package.md` | this is the first critical accepted-source blocker; it needs term-by-term referee acceptance |
| CC20 post-`Q` source remainder | `CC20PostQSourceRemainderTheorem(g)` states the `D`/`E` source obstruction and the post-`Q` bulk, boundary, and tail itemization | `weil-compo.tex:710-719,747-761,875-878,1132-1140,1196-1199,1267-1270,1338-1360,2168-2250` | `docs/audits/cc20-post-q-remainder-term-map.md`; `docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md` | source itemization must be connected to fixed-S transport before classification |
| Rows 3-7 sign/defect bridge | `SourceSignDefectClassificationTheorem(S,I,lambda,g,J)` classifies the transported source remainder as rank, pole, or endpoint-strip `Cdef` and proves no hidden positive defect | CC20 source remainder anchors plus CCM24 transport anchors | `docs/proofs/sonin-prolate-defect-referee-discharge.md` | no direct source theorem exists; this remains a referee-checkable project theorem |
| Restricted-to-full bridge | `RestrictedToFullQWAcceptedTheorem(g)` proves eventual scalar equality `QW_lambda(g,g)=QW(g,g)` from CCM25 restriction plus fixed support | `mc2arXiv.tex:530-540` | `docs/audits/restricted-to-full-qw-source-readiness-audit.md` | reviewer must verify no spectral convergence or determinant convergence enters |
| Final sign bridge | `FinalCCM25CC20SignTheorem(g)` proves `QW(g,g)=-sum_v W_v(F_g)` and the inequality direction used by CC20 Proposition C.1 | `mc2arXiv.tex:445-470`; `weil-compo.tex:2131-2165` | `docs/proofs/final-sign-bridge-proof-package.md` | source sign conventions and pole terms must be checked against the same `F_g` |
| CC20 finite-vanishing exit | `CC20FiniteVanishingRHExitTheorem(F_g)` applies Proposition C.1 with the finite set `{0,1/2,1}` | `weil-compo.tex:2014-2030,2072-2085` | `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md` | route triple vanishing must match CC20 Mellin vanishing on the same half-density object |
| RH definition bridge | `SourceRHToMathlibRHTheorem` transports the source RH conclusion to the Mathlib-style zeta-zero predicate | Mathlib plus CC20 source RH conclusion | `docs/proofs/rh-definition-bridge-proof-package.md` | accepted-source review can certify source RH; Lean will still be needed for Mathlib predicate equality if formal certification is required |

## First Critical Row: S2-B1

The first row to upgrade is not a single source-paper quote. It is a cross-source
compatibility theorem:

```text
CC20CCMTraceScaleNoBulkTheorem(S,I,lambda,g,J):
  PositiveTrace^G_(S,lambda)(g)
    =
  QW_lambda(g,g)
    + Rank_(S,I)(g)
    + PoleJetExtra_(S,I)(g)
    + CdefRemainder_(S,I,lambda,J)(g),

  with no additional BulkScaleTerm_(S,I,lambda,g)
  and no hidden finite-part subtraction.
```

This theorem candidate is now split in:

```text
docs/audits/trace-scale-source-term-ledger.md
```

That file is the first accepted-source packet for B1. It records each possible
source term and where the route claims it lands.

## Next Critical Packets

Two additional packets now cover the next source-certification gates:

```text
docs/audits/sign-defect-accepted-source-packet.md
docs/audits/restricted-to-full-accepted-source-packet.md
```

The sign/defect packet asks a referee to accept Rows 1-7 as one source-owned
classification theorem: CC20 post-`Q` remainder, fixed-S transport, no-strip
rank/pole identification, endpoint-strip `Cdef` domination, and no hidden
positive defect.

The restricted-to-full packet asks a referee to accept the fixed-test scalar
identity `QW_lambda(g,g)=QW(g,g)` from the CCM25 restriction definition, support
containment, and finite-prime support stabilization. It excludes spectral
convergence, determinant convergence, and even-sector spectral assumptions.

## Final-Exit Packets

Three packets now cover the final source-certification gates:

```text
docs/audits/final-sign-accepted-source-packet.md
docs/audits/cc20-exit-accepted-source-packet.md
docs/audits/rh-definition-accepted-source-packet.md
```

The final sign packet asks a referee to accept
`QW(g,g)=-sum_v W_v(F_g)` and the inequality direction.

The CC20 exit packet asks a referee to accept the use of Proposition C.1 with
`F={0,1/2,1}`, route triple vanishing, the CC20 sign inequality, and the source
RH conclusion.

The RH definition packet asks a referee or later Lean proof to identify the
CC20 source RH conclusion with the standard zeta-zero predicate, including
zeta equality, non-trivial-zero exclusions, the pole at `1`, and `s.re=1/2`.

## What Counts As Progress

For each row, progress means replacing a broad statement like:

```text
CCM25 supplies QW_lambda.
```

with a theorem candidate:

```text
CCM25QWLambdaRestrictionTheorem(lambda,g):
  hypotheses ...
  conclusion ...
  source anchors ...
  route object bridge ...
  proof status ...
```

This ledger does that at the row level. The next layer must do it term by term
for each critical row.

## Current Judgment

| question | answer |
|---|---|
| Did this ledger upgrade any row to accepted-source theorem status? | no |
| Did it identify exact theorem candidates for accepted-source review? | yes |
| Is S2-B1 the first critical candidate? | yes |
| Do Rows 3-7 and restricted-to-full now have review packets? | yes |
| Do final sign, CC20 exit, and RH definition now have review packets? | yes |
| Did this pass touch Lean? | no |

The route remains source-conditional. The certification work has now shifted
from proof-package completion to accepted-source theorem review packets.
