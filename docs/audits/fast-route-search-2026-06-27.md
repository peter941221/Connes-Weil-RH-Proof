# Fast Route Search, 2026-06-27

Status: rapid route-search audit for the two urgent blockers:

```text
1. sign/defect
2. source import legitimacy
```

This file is not a proof package. It records which search branches are worth
attacking first after the hostile criticism, and which branches should not be
used as shortcuts.

## Result

Good result:

```text
There are two fast, non-cosmetic attack routes.
```

They are:

```text
Route A:
  CC20 post-Q remainder fixed-S Sonin transport.

Route B:
  fixed-test restricted-to-full QW by CCM25 restriction definition.
```

Bad result for final certification:

```text
The sign/defect route is discharged only at route-evidence level.
The restricted-to-full route is also discharged only at route-evidence level.
```

The current proof remains:

```text
source-conditional route evidence with accepted-source, Lean, and final-exit
gates still open.
```

## External Source Scan

Primary sources checked in this fast pass:

| source | URL | route signal |
|---|---|---|
| CC20, "Weil positivity and Trace formula, the archimedean place" | https://arxiv.org/abs/2006.13771 | the Weil distribution and Sonin trace differ by a prolate-spheroidal term that must be controlled |
| CCM24, "Zeta zeros and prolate wave operators" | https://arxiv.org/abs/2310.18423 | semilocal Sonin spaces are stable under increasing finite place sets and fixed-window comparison is the transport candidate |
| CCM25, "Zeta Spectral Triples" | https://arxiv.org/abs/2511.22755 | restricted forms and numerical spectral convergence are present, but convergence to zeros is strategy/numerical, not importable |
| CC21, "Spectral Triples and Zeta-Cycles" | https://arxiv.org/abs/2106.01715 | useful prolate/zeta-cycle background, but mostly numerical/conceptual for this blocker |
| CvS25, "Quadratic Forms, Real Zeros and Echoes of the Spectral Action" | https://arxiv.org/abs/2511.23257 | useful for a finite real-zero route, but not the fastest repair for sign/defect read-off |

The scan supports the existing source-import audit:

```text
CCM25 spectral or determinant convergence must not be imported.
CC20 Sonin/prolate remainder must be controlled, not waved away.
CCM24 is the best transport source, but does not by itself prove Cdef control.
```

## Route A. CC20 Post-Q Remainder Fixed-S Sonin Transport

Current blocker row:

```text
docs/audits/sonin-prolate-defect-discharge-ledger.md
Row 3. Fixed-S Sonin Transport
```

Fast target:

```text
CC20PostQRemainderFixedSSoninTransport(S,I,lambda,g,F_g):
  CC20SourceRemainderAfterQ(F_g)
  + SourceCommonTestTupleContract(S,I,lambda,g,F_g)
  + CCM24SupportWindowTransportDischarge(S,I,lambda,g)
  + CCM24SemilocalObjectNormalization(S,I,lambda,g)
  ->
  TransportedCC20PostQRemainder(S,I,lambda,g,F_g).
```

The target is now stated as a theorem contract:

```text
docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md
```

The CC20 post-`Q` formula has now been mapped item by item:

```text
docs/audits/cc20-post-q-remainder-term-map.md
```

The CCM24 fixed-S transport fast pass is now recorded in:

```text
docs/audits/ccm24-fixed-s-post-q-transport-obstruction-audit.md
```

Its verdict is that CCM24 supports the common fixed-S model/window/Sonin
framework, but does not automatically transport the post-`Q` derivative,
boundary, or series-tail structure.

The first Row 3 subcontract is now stated in:

```text
docs/proofs/cc20-post-q-derivative-domain-compatibility-theorem-contract.md
```

This targets the bulk derivative/domain compatibility for the
`D_u xi_n` / `D_u zeta_n` term.

Its source-import decision is now recorded in:

```text
docs/audits/cc20-post-q-derivative-domain-source-decision-audit.md
```

The verdict is:

```text
project-proof-required, not source-import-discharged.
```

The project-proof target is now stated in:

```text
docs/proofs/fixed-s-post-q-bulk-graph-transfer-theorem-contract.md
```

The route-evidence proof package is now:

```text
docs/proofs/fixed-s-post-q-bulk-graph-transfer-proof-package.md
```

This advances the first Row 3 subcontract. Boundary and tail now also have
route-evidence packages, so the combined Row 3 package is the current
route-evidence closure point.

The second Row 3 subcontract is now stated in:

```text
docs/proofs/cc20-post-q-boundary-evaluation-transport-theorem-contract.md
```

This targets the lower moving endpoint and upper fixed endpoint terms created
by the CC20 domain-repair calculation.

Its source-import decision is now recorded in:

```text
docs/audits/cc20-post-q-boundary-evaluation-source-decision-audit.md
```

The verdict is:

```text
project-proof-required, not source-import-discharged.
```

The project-proof target is now stated in:

```text
docs/proofs/fixed-s-post-q-boundary-functional-transfer-theorem-contract.md
```

The route-evidence proof package is now:

```text
docs/proofs/fixed-s-post-q-boundary-functional-transfer-proof-package.md
```

The third Row 3 subcontract is now stated in:

```text
docs/proofs/cc20-post-q-series-tail-bounded-comparison-theorem-contract.md
```

This targets the passage from transported finite partial sums to the full
transported source remainder.

Its source-import decision is now recorded in:

```text
docs/audits/cc20-post-q-series-tail-source-decision-audit.md
```

The verdict is:

```text
project-proof-required, not source-import-discharged.
```

The project-proof target is now stated in:

```text
docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-theorem-contract.md
```

The route-evidence proof package is now:

```text
docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-proof-package.md
```

The combined Row 3 route-evidence proof package is now:

```text
docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md
```

Meaning:

The target should prove only that the CC20 `D circ Q` / `E circ Q` bulk and
boundary pieces are transported into the same fixed-S canonical coordinate,
same source test, same support window, same lambda parameter, and same Sonin
space as the positive trace and restricted `QW_lambda`.

It must not yet claim:

```text
TransportedCC20PostQRemainder is endpoint-strip Cdef.
```

That belongs to Rows 4 through 6.

Why this is the fastest sign/defect route:

| reason | evidence |
|---|---|
| CC20 already identifies the sign obstruction as `D circ Q` / `E circ Q` | `docs/proofs/cc20-source-remainder-orientation-theorem-contract.md` |
| CCM24 already supplies the candidate transport language | `docs/proofs/ccm24-support-window-transport-discharge.md` and `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` |
| current route packages already own projection-defect normal form after transport | `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md` |
| avoiding immediate `Cdef` claims prevents interface arbitrage | `docs/audits/sonin-prolate-defect-discharge-ledger.md` keeps Rows 3-7 as separate gates |

Fast acceptance test:

```text
Can every term in the CC20 post-Q remainder be named as a transported source
object before projection-defect classification?
```

If yes, the route moves to Row 4.

If no, the branch must name the escaped term as a new defect class.

## Route B. Fixed-Test Restricted-To-Full QW

Current blocker:

```text
QW_lambda(g,g) -> QW(g,g)
```

Rejected shortcut:

```text
CCM25 spectral convergence as N,lambda -> infinity.
```

Fast target:

```text
RestrictedToFullQWBridgeContract(S,I,lambda,g,F_g,J):
  common test
  + fixed tuple/window
  + CCM25 restriction definition
  + finite-prime support equality
  ->
  eventual scalar equality QW_lambda(g,g) = QW(g,g)
```

Why this is faster than spectral convergence:

| reason | evidence |
|---|---|
| fixed compact test has finite prime-power visibility after support is fixed | `docs/proofs/source-common-test-tuple-theorem-contract.md`; `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` |
| CCM25 restricted `QW_lambda` is a restriction of the global Weil form, not a separate spectral limit theorem for the fixed-test route | `docs/audits/restricted-to-full-qw-source-readiness-audit.md` |
| the source-import audit already rejects numerical spectral convergence | `docs/audits/source-import-legitimacy-audit.md` |

Fast acceptance test:

```text
For fixed g and F_g, does the restricted lambda window eventually contain
every prime-power and pole term that appears in the global QW formula?
```

If yes, this gate becomes a finite-support equality theorem.

If no, the route must state exactly which global term is not eventually visible.

## Routes To Reject For This Sprint

| route | reject for now because |
|---|---|
| `Tr(A^*A) >= 0 -> QW_lambda >= 0` | this is exactly the hostile sign/defect shortcut |
| CCM25 spectral convergence | the source abstract says a rigorous proof would establish RH; it is not an import |
| determinant convergence toward Xi | also a strategy/numerical route, not a source theorem |
| CvS finite real-zero theorem | useful elsewhere, but it attacks real-zero localization, not the fixed-S positive-trace read-off defect |
| generic prolate concentration | does not identify CC20 `D circ Q` / `E circ Q` with route rank, pole, or `Cdef` ledgers |

## Sprint Order

The fastest route-search order is:

```text
1. State Route A as a theorem contract:
   CC20PostQRemainderFixedSSoninTransport.  [done]

2. Check whether the CC20 post-Q bulk and boundary terms have the right
   source-owned test/window fields to enter CCM24 transport.  [term map done;
   CCM24 obstruction audit done; derivative/domain and boundary route-evidence
   packages done; tail route-evidence package done; combined Row 3 package
   done at route-evidence level]

3. Only after Route A passes, try Row 4:
   FixedSProjectionDefectNormalFormForSourceRemainder. [done at
   route-evidence level]

4. In parallel but lower risk, push Route B:
   RestrictedToFullQWBridgeContract.
```

## Current Judgment

| question | answer |
|---|---|
| Can we enter fast route-search mode? | yes |
| Is there an immediate proof closure? | no |
| Best sign/defect attack | Route A, Row 3 fixed-S transport of CC20 post-Q remainder |
| Best source-import attack | Route B, fixed-test restricted-to-full equality via source definitions |
| Biggest thing to avoid | importing numerical/spectral convergence or collapsing defect rows |
