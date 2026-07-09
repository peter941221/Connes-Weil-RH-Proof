# Pre-Lean Completion Audit

Status: local completion record for the non-Lean phase.

This audit records what can be completed before any further Lean work and what
cannot be completed by local writing alone.

## Result

Good result:

```text
All local pre-Lean proof-package rows are written, indexed, and tied to the
current external-review checklist.
```

Certification result:

```text
No row has become an accepted-source theorem, an externally certified referee
result, or a Lean theorem with audited axioms.
```

The next non-Lean work is external mathematical review or accepted-source
discharge of the rows below. A local document can prepare that review; it
cannot replace it.

## Boundary

Use this audit as the gate before reopening Lean.

```text
local proof package
        |
        v
row-by-row external verdict
        |
        v
accepted-source theorem or correction request
        |
        v
Lean interface encoding, only after Peter reopens Lean
```

Do not start new Lean scaffolding from this repository state. The local
pre-Lean package matrix is complete, but the accepted-source step is still a
mathematical certification task.

## Completed Local Work

| row | local pre-Lean artifact | current local status |
|---|---|---|
| Source object spine | `docs/proofs/source-object-definition-spine-discharge.md`; `docs/proofs/source-object-definition-theorem-contract.md`; `docs/audits/source-object-theorem-discharge-ledger.md` | proof-package and theorem-contract coverage complete |
| CCM24 fixed-S model | `docs/proofs/ccm24-support-window-transport-discharge.md`; `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | fixed `S`, window, Fourier support, comparison, and Sonin gates exposed |
| CCM25 Weil objects | `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md`; `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md`; `docs/proofs/ccm25-restricted-read-off-discharge.md` | `QW`, `Psi`, `QW_lambda`, pole, and sign interfaces exposed |
| CCM25 finite-prime normalization | `docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md`; `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` | source prime-power, lambda cut, von Mangoldt weight, pairing, and sign ownership targets exposed |
| CC20 trace legality | `docs/proofs/cc20-analytic-trace-legality-spine-discharge.md`; `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md` | operator identity, Hilbert-Schmidt, trace-class, cyclicity, support-square trace, and no-defect read-off targets exposed |
| Sign/defect bridge Rows 1-2 | `docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md` | CC20 source remainder orientation and post-`Q` image fixed at project proof-package level |
| Sign/defect bridge Rows 3-7 | `docs/proofs/sonin-prolate-defect-referee-discharge.md`; `docs/audits/sonin-prolate-defect-discharge-ledger.md` | fixed-S transport, projection-defect split, rank/pole identification, endpoint-strip `Cdef`, and no-hidden-defect chain closed at project proof-package level |
| Restricted-to-full bridge | `docs/audits/restricted-to-full-qw-source-readiness-audit.md`; `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` | fixed-test `QW_lambda(g,g)=QW(g,g)` route written without importing spectral convergence |
| Final sign bridge | `docs/proofs/final-sign-bridge-proof-package.md`; `docs/proofs/final-sign-bridge-theorem-contract.md` | `QW(g,g)=-sum_v W_v(F_g)` and the CC20 inequality direction exposed at route-evidence level |
| CC20 RH exit and definition bridge | `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md`; `docs/proofs/rh-definition-bridge-proof-package.md`; `docs/proofs/source-conditional-rh-route-closure-proof-package.md` | finite-vanishing exit and Mathlib-style RH target connected at route-evidence level |

## Remaining Non-Lean Certification

| row | required verdict before certification |
|---|---|
| CCM24 fixed-S model | External reviewer accepts the exact fixed-`S` hypotheses, windows, comparison maps, and Sonin comparison used by the route, or returns a correction. |
| CCM25 Weil objects | External reviewer accepts the route's `QW`, `Psi`, `QW_lambda`, pole, finite-prime, and sign normalizations against the source text, or returns a correction. |
| CC20 trace legality | External reviewer accepts Hilbert-Schmidt, trace-class, cyclicity, Mellin, and support-square trace use for the transported source object, or returns a correction. |
| Sign/defect bridge | External reviewer accepts that every CC20 post-`Q` remainder term lands in killed rank/pole ledgers or endpoint-strip `Cdef`, with no fourth positive defect. |
| Restricted-to-full bridge | External reviewer accepts fixed-test `QW_lambda(g,g)=QW(g,g)` from restriction definition plus support stabilization, without spectral convergence. |
| Final sign bridge | External reviewer accepts `QW(g,g)=-sum_v W_v(F_g)` and the direction `QW(g,g)>=0 -> sum_v W_v(F_g)<=0`. |
| RH definition bridge | External reviewer accepts the transport from the CC20 source RH conclusion to Mathlib's zeta, zero, exclusion, and critical-line predicates. |

## Non-Importable Claims

Keep these out of the route as accepted inputs:

| claim | status |
|---|---|
| CCM25 finite-operator spectral convergence to zeta zeros | not used; not importable as a theorem |
| determinant convergence toward Xi | not used in the route theorem |
| harmless Sonin/prolate defect | replaced by Rows 1-7 project proof chain; still needs accepted-source or external certification |
| automatic CCM24 post-`Q` transport | replaced by Row 3 bulk, boundary, and tail subcontracts |
| source statement ending in "RH" equals Mathlib RH by name | replaced by the RH definition bridge |

## Pre-Lean Stop Rule

Do not reopen Lean work until Peter explicitly asks for it after this
pre-Lean package state. The next valid non-Lean action is row-by-row external
review, accepted-source certification, or correction of a row that a reviewer
rejects.

## Current Judgment

| question | answer |
|---|---|
| Are all local pre-Lean proof-package rows written? | yes |
| Did this upgrade any row to accepted-source status? | no |
| Did this run or change Lean? | no |
| Can the route claim a completed RH proof now? | no |
| Is the repository ready for row-by-row external mathematical review before Lean? | yes |
