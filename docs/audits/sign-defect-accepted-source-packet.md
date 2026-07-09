# Sign-Defect Accepted-Source Packet

Date: 2026-06-28

Status:

```text
Rows 3-7 accepted-source packet started
accepted-source certification: open
Lean status: not touched
```

## Purpose

This packet targets the source-facing theorem candidate:

```text
SourceSignDefectClassificationTheorem(S,I,lambda,g,F_g,J).
```

The theorem must certify the sign/defect chain used after the positive trace
has been read at the `QW_lambda` scale:

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

with no source-owned fourth positive defect.

This packet does not mark the theorem as accepted-source. It records the exact
checks a referee must accept before the route can use the sign/defect bridge as
a certified input.

## Fixed Objects

The accepted-source theorem must use one tuple throughout:

```text
S                 finite place set
I                 fixed CCM24 support window
lambda            restricted-window parameter, 1 < lambda
g                 common source test
F_g = g^* * g     common convolution square
J                 graph/order budget for endpoint-strip Cdef
V_S = M_S U_S     common fixed-S coordinate
```

Changing any of these objects creates a new theorem, not a proof of this one.

## Source Anchors

| source family | anchors | role |
|---|---|---|
| CC20 finite vanishing and `Q` | `weil-compo.tex:710-719,747-761` | support-preserving finite-vanishing operator and positivity after vanishing |
| CC20 `D` and `E` orientation | `weil-compo.tex:875-878,1132-1140,1196-1199` | source obstruction object and post-`Q` target |
| CC20 post-`Q` itemization | `weil-compo.tex:1267-1270,1338-1360` | bulk term, lower boundary term, upper boundary term |
| CC20 series control | `weil-compo.tex:2168-2250` | source convergence and tail estimates |
| CCM24 fixed-S warning and transport context | `mainc2m24fine.tex:761-823,846-852,983-1003,1050-1060` | support transport, bounded comparison, warning against automatic transport, Sonin comparison |

## Certification Chain

| row | theorem candidate | current evidence | accepted-source check |
|---|---|---|---|
| Rows 1-2 source orientation | `CC20SourceRemainderOrientationTheorem(g)` | `docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md` | confirm CC20 gives `W_infty=L-D`, `W_infty=S-E`, and the exact post-`Q` source obstruction used by Row 3 |
| Row 3 bulk transport | `FixedSPostQBulkGraphTransferAccepted(S,I,lambda,g,F_g,n)` | `docs/proofs/fixed-s-post-q-bulk-graph-transfer-proof-package.md` | confirm the source bulk term, with derivatives and graph domain, moves into the same fixed-S coordinate before Row 4 |
| Row 3 boundary transport | `FixedSPostQBoundaryTransferAccepted(S,I,lambda,g,F_g,n)` | `docs/proofs/fixed-s-post-q-boundary-functional-transfer-proof-package.md` | confirm lower moving endpoint and upper fixed endpoint functionals are transported as source-owned boundary terms |
| Row 3 series-tail transport | `FixedSPostQSeriesTailAccepted(S,I,lambda,g,F_g,N)` | `docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-proof-package.md` | confirm CC20 scalar tail control survives the fixed-S bounded comparison in the graph/trace norm used later by `Cdef` |
| Row 4 normal form | `FixedSProjectionDefectNormalFormAccepted(S,I,lambda,g,F_g,J)` | `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md` | confirm the transported source remainder splits into no-strip and endpoint-strip classes only |
| Row 5 no-strip ledger | `SourceRankPoleLedgerAccepted(S,I,lambda,g,F_g)` | `docs/proofs/source-rank-pole-ledger-identification-proof-package.md` | confirm no-strip terms are exactly rank or pole before triple vanishing kills them |
| Row 6 endpoint-strip domination | `SourceEndpointStripCdefAccepted(S,I,lambda,g,F_g,J)` | `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md` | confirm endpoint-strip source terms match route `Cdef` summands with the displayed fixed-test bound |
| Row 7 no-hidden-defect equality | `NoHiddenPositiveDefectAccepted(S,I,lambda,g,F_g,J)` | `docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md`; `docs/audits/semilocal-fourth-defect-ledger.md` | confirm the final equality has no fifth summand and no positive source-owned defect outside rank, pole, and `Cdef` |

## Rejection Conditions

A reviewer should reject the sign/defect accepted-source row if any one of
these conditions occurs:

```text
1. a CC20 post-Q source term is absent from Rows 1-3;
2. fixed-S transport changes the test, window, or coordinate;
3. a no-strip term is neither rank nor pole;
4. an endpoint-strip term does not match a route Cdef summand;
5. Row 7 leaves a fifth source-owned summand;
6. the proof uses spectral convergence or determinant convergence.
```

If a reviewer supplies such a term, the route must name it as:

```text
SemilocalFourthDefect_(S,I,lambda,g,F_g,J)
```

and stop before full Weil positivity.

## Accepted-Source Questions

| question | required answer for acceptance |
|---|---|
| Does one tuple `(S,I,lambda,g,F_g,J)` govern every row? | yes |
| Does Row 3 transport the source post-`Q` object before any classification? | yes |
| Does Row 3 handle bulk, boundary, and tail as separate source-owned channels? | yes |
| Does Row 4 classify only the transported source object? | yes |
| Does Row 5 identify no-strip terms before triple vanishing is used? | yes |
| Does Row 6 prove endpoint-strip domination by the displayed route `Cdef`? | yes |
| Does Row 7 prove equality before deriving the finite-lambda lower bound? | yes |
| Does the argument avoid finite-operator spectral convergence? | yes |

## Current Judgment

| question | answer |
|---|---|
| Does this packet make Rows 3-7 accepted-source? | no |
| Does it give an exact accepted-source review packet? | yes |
| What remains? | external referee or independent proof accepting every row above |
| Did this pass touch Lean? | no |

Rows 3-7 now have a row-by-row accepted-source packet. The status remains
source-conditional until a reviewer accepts the packet or a formal proof
discharges it.
