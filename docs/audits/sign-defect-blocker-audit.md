# Sign And Defect Blocker Audit

Status: hard-blocker audit for the positive-trace-to-Weil step.

This audit tests the strongest hostile reading of the route:

```text
Tr(A^* A) >= 0
```

does not by itself imply:

```text
QW_lambda(g,g) >= 0.
```

The route may use the positive trace only after it proves the exact read-off:

```text
PositiveTrace
  =
QW_lambda
  + killed ledgers
  + norm-controlled endpoint-strip remainder.
```

If a positive Sonin/prolate defect is actually subtracted from `QW_lambda` and
is not part of the endpoint-strip `Cdef` theorem, the route fails at this gate.

## Evidence Checked

| evidence | role |
|---|---|
| `README.md:84-89` | public spine states positive trace as `QW_lambda` plus rank, pole, and `Cdef` terms |
| `README.md:174-193` | displayed read-off equality and `Cdef` bound |
| `README.md:232-250` | derives `QW(g,g) >= 0` from `QW_lambda >= -Cdef` and exhaustion |
| `docs/audits/core-defect-gap-ledger.md:170-213` | Battle 2 rejection criterion for unsupported fixed-S transport |
| `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:225-271` | classifies leftovers as rank, pole, or endpoint-strip `Cdef` |
| `docs/proofs/battle-3-cdef-exhaustion-proof-package.md:267-341` | proves fixed-test `Cdef` exhaustion at route-evidence level |
| `docs/proofs/fixed-test-graph-cdef-exhaustion.md:13-15` | separates fixed-test exhaustion from spectral convergence to zeros |
| `docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md` | formal/import target for identifying source prolate/Sonin defects with endpoint-strip `Cdef` |
| `docs/audits/sonin-prolate-defect-discharge-ledger.md` | row-by-row discharge ledger for proving the source prolate/Sonin remainder is exactly rank, pole, or endpoint-strip `Cdef` |
| `docs/proofs/cc20-source-remainder-orientation-theorem-contract.md` | Row 1/2 source-orientation contract fixing `W_infty=L-D`, `W_infty=S-E`, and the post-`Q` remainder target |
| `docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md` | referee-facing project proof package for Rows 1-2; fixes the CC20 source obstruction, `Q` image, bulk term, boundary terms, and series tail |
| `docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md` | Row 3 theorem contract for transporting the CC20 post-`Q` remainder into the same fixed-S CCM24/Sonin/window coordinate before projection-defect classification |
| `docs/audits/cc20-post-q-remainder-term-map.md` | item-level Row 3 map splitting the CC20 `Q epsilon` formula into bulk, boundary, and series-tail transport targets |
| `docs/audits/ccm24-fixed-s-post-q-transport-obstruction-audit.md` | CCM24 fast-pass audit showing the fixed-S Sonin model helps Row 3 but does not transport post-`Q` derivative, boundary, or tail structure automatically |
| `docs/proofs/cc20-post-q-derivative-domain-compatibility-theorem-contract.md` | first Row 3 subcontract; blocks treating the `D_u xi_n` / `D_u zeta_n` bulk term as automatically transported through CCM24 |
| `docs/audits/cc20-post-q-derivative-domain-source-decision-audit.md` | source-import decision audit; classifies `PostQDerivativeDomainCompatibility` as project-proof-required, not source-import-discharged |
| `docs/proofs/fixed-s-post-q-bulk-graph-transfer-theorem-contract.md` | project-proof target for discharging the first Row 3 subcontract |
| `docs/proofs/fixed-s-post-q-bulk-graph-transfer-proof-package.md` | route-evidence proof package for the first Row 3 subcontract; does not close boundary, tail, or full sign/defect |
| `docs/proofs/cc20-post-q-boundary-evaluation-transport-theorem-contract.md` | second Row 3 subcontract; blocks treating CC20 endpoint terms as rank, pole, or Cdef before fixed-S boundary-functional transport |
| `docs/audits/cc20-post-q-boundary-evaluation-source-decision-audit.md` | source-import decision audit; classifies `PostQBoundaryEvaluationTransport` as project-proof-required, not source-import-discharged |
| `docs/proofs/fixed-s-post-q-boundary-functional-transfer-theorem-contract.md` | project-proof target for discharging the second Row 3 subcontract |
| `docs/proofs/fixed-s-post-q-boundary-functional-transfer-proof-package.md` | route-evidence proof package for the second Row 3 subcontract; does not close tail, full Row 3, or full sign/defect |
| `docs/proofs/cc20-post-q-series-tail-bounded-comparison-theorem-contract.md` | third Row 3 subcontract; blocks promoting CC20 scalar tail convergence to fixed-S graph/trace-norm convergence without a comparison theorem |
| `docs/audits/cc20-post-q-series-tail-source-decision-audit.md` | source-import decision audit; classifies `PostQSeriesTailBoundedComparison` as project-proof-required, not source-import-discharged |
| `docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-theorem-contract.md` | project-proof target for discharging the third Row 3 subcontract |
| `docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-proof-package.md` | route-evidence proof package for the third Row 3 subcontract; does not itself close downstream classification or full sign/defect |
| `docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md` | combined Row 3 route-evidence proof package; transports the source post-`Q` remainder but does not classify it as rank, pole, or Cdef |
| `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-theorem-contract.md` | Row 4 project-proof contract; targets projection-defect normal form for the transported CC20 source remainder |
| `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md` | Row 4 route-evidence proof package; proves no-strip/projection-order split and endpoint-strip shifted-kernel normal form, but not rank/pole identification or Cdef domination |
| `docs/proofs/source-rank-pole-ledger-identification-theorem-contract.md` | Row 5 project-proof contract; targets no-strip rank/pole ledger identification for the transported source remainder |
| `docs/proofs/source-rank-pole-ledger-identification-proof-package.md` | Row 5 route-evidence proof package; identifies no-strip channels as rank or pole and gates triple vanishing, but does not prove Cdef domination |
| `docs/proofs/source-endpoint-strip-cdef-domination-theorem-contract.md` | Row 6 project-proof contract; targets exact indexing of endpoint-strip source-remainder terms by route `Cdef` summands |
| `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md` | Row 6 route-evidence proof package; proves endpoint-strip `Cdef` domination and fixed-test exhaustion at project level, but does not prove Row 7 no-hidden-defect equality |
| `docs/proofs/no-hidden-positive-defect-outside-cdef-theorem-contract.md` | Row 7 project-proof contract; states the exact positive-trace read-off equality excluding a fourth positive defect |
| `docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md` | Row 7 route-evidence proof package; proves no-hidden-positive-defect equality at project level, but not accepted source-import or Lean status |
| `docs/proofs/sonin-prolate-defect-referee-discharge.md` | referee-facing project proof package composing Rows 3-7 into one sign/defect proof chain after the Rows 1-2 source-entry package |
| `docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md` | formal/import target for scalar fixed-test `QW_lambda -> QW` exhaustion |
| `docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md` | formal/import target composing common-test, window, finite-prime support, and CCM25 restriction definition into eventual `QW_lambda=QW` |
| `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` | route-evidence package for eventual scalar `QW_lambda(g,g)=QW(g,g)` without spectral convergence |
| `docs/audits/sonin-prolate-defect-source-readiness-audit.md` | source-readiness audit for the sign/defect bridge |
| `docs/audits/restricted-to-full-qw-source-readiness-audit.md` | source-readiness audit for the restricted-to-full bridge |
| arXiv:2006.13771 abstract | says Weil distribution and Sonin trace differ by a prolate-spheroidal term that must be controlled |
| arXiv:2511.22755 abstract | says rigorous spectral convergence as `N, lambda -> infinity` would establish RH |

Primary source pages:

```text
https://arxiv.org/abs/2006.13771
https://arxiv.org/abs/2511.22755
```

## Test 1. Positivity Source

The project-owned positivity source is only:

```text
PositiveTrace^G_(S,lambda)(g)
  =
Tr(A_(S,lambda,g)^* A_(S,lambda,g))
  >= 0.
```

`README.md:148-155` states this boundary.

Judgment:

| question | answer |
|---|---|
| Is `Tr(A^* A) >= 0` valid once `A` is Hilbert-Schmidt? | yes |
| Does this alone prove Weil positivity? | no |
| What must be added? | trace legality, read-off equality, defect classification, and exhaustion |

Status:

```text
pass as a positivity input;
open blocker as a Weil-positivity proof.
```

## Test 2. Read-Off Equality

The route needs:

```text
PositiveTrace^G_(S,lambda)(g)
  =
QW_lambda(g,g)
  + Rank_(S,I)(g)
  + PoleJetExtra_(S,I)(g)
  + R_(S,I,lambda)(g),

|R_(S,I,lambda)(g)|
  <= C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

The dangerous shortcut would be:

```text
positive trace exists
  therefore
QW_lambda is positive up to a small error.
```

That shortcut fails unless the route proves that every non-ledger remainder is
inside `R` and satisfies the displayed `Cdef` bound.

Current repository evidence:

| claim | current evidence | judgment |
|---|---|---|
| no-defect term is the CCM25 restricted form | `docs/proofs/ccm25-restricted-read-off-discharge.md:170-190` | source-interface proof package, not formal/import discharge |
| fixed-S leftovers are only rank, pole, or endpoint-strip `Cdef` | `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:225-271` | route-evidence proof package |
| endpoint-strip source remainders are bounded by route `Cdef` | `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md` | route-evidence proof package |
| no hidden fourth defect remains in the positive-trace read-off | `docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md` | route-evidence proof package |
| no projection-order defect enters `QW_lambda` | `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:271` | stated, not independently imported |
| using "same quantized-calculus expansion" is rejected | `docs/audits/core-defect-gap-ledger.md:203-213` | useful guardrail |

Status:

```text
Row 7 route-evidence now supplies the exact equality; accepted source-import
and Lean discharge remain open.
```

The repository has a route-evidence proof package for the target, but no
accepted source theorem or formal proof yet proves the target.

## Test 3. Defect Sign

The hostile claim says:

```text
SoninTrace = QW_lambda + Defect
```

or equivalently:

```text
QW_lambda = SoninTrace - Defect,
```

with `Defect >= 0`.

If this is the source identity, positive trace gives no sign for `QW_lambda`
unless the route proves:

```text
SoninTrace >= Defect
```

or proves that the whole defect belongs to a vanishing `Cdef` class.

Current repository response:

```text
projection-order defect
  -> endpoint-strip normal form
  -> trace-norm Cdef
  -> fixed-test exhaustion.
```

This response attacks the right point, but it remains at route-evidence level.
It does not yet prove that the CC20 prolate/Sonin defect and the fixed-S
projection-order remainder are the same controlled object.

Required theorem:

```text
SoninProlateDefectEqualsEndpointStripCdef:
  every source prolate/Sonin difference term produced by the fixed-S
  support-square read-off is either:
    1. a no-strip rank ledger,
    2. a no-strip pole ledger, or
    3. an endpoint-strip `Cdef` term with the stated trace-norm bound.
```

The detailed theorem contract is now:

```text
docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md
```

Status:

```text
route-evidence closure now exists through Row 7;
accepted-source and Lean discharge remain open.
```

The repository now answers the hostile objection at route-evidence level by
identifying the defect with killed ledgers plus endpoint-strip `Cdef`. It has
not yet answered it at accepted-source or Lean strength.

## Test 4. Fixed-Test Exhaustion Versus Spectral Convergence

The route uses a fixed-test limit:

```text
g, I, S_A, J' fixed,
lambda -> infinity.
```

`docs/proofs/fixed-test-graph-cdef-exhaustion.md:13-15` explicitly says this
does not assert spectral convergence of finite operators to zeta zeros.

CCM25's abstract says numerical spectra appear to converge to zeta zeros, and
that a rigorous proof of that convergence would establish RH. This cannot be
imported as a theorem for the route.

Judgment:

| claim | status |
|---|---|
| fixed-test endpoint-strip tails vanish | route-evidence proof package |
| global spectral convergence of finite operators to zeta zeros | not imported; not used as a theorem |
| `QW_lambda(g,g) -> QW(g,g)` for the exact route object | route-evidence bridge written; accepted source-import and Lean discharge remain open |

Status:

```text
open blocker for final certification.
```

The route must keep the fixed-test exhaustion theorem separate from spectral
convergence claims in CCM25.

## Blocker Table

| subclaim | verdict | reason |
|---|---|---|
| `Tr(A^*A) >= 0` after Hilbert-Schmidt gate | passed | standard Hilbert-space fact once the gate is proved |
| positive trace equals `QW_lambda + ledgers + R` | route-evidence only | Row 7 package exists; no accepted import or Lean theorem yet |
| all non-ledger defects lie in endpoint-strip `Cdef` | route-evidence only | Rows 4-7 package the hostile sign/defect response |
| killed ledgers vanish under triple vanishing | partially passed | theorem contracts exist; final source/import discharge still open |
| `Cdef -> 0` for fixed test and fixed `S_A` | route-evidence only | proof package exists, not accepted/imported |
| `QW_lambda -> QW` for the same source object | route-evidence only | CCM25 defines `QW_lambda` as restriction of `QW`; accepted source-import and Lean discharge remain open |
| CC20 criterion consumes the same sign as route `QW >= 0` | theorem-contract level | see `docs/proofs/final-sign-bridge-theorem-contract.md` |

## Required Next Certification Targets

The sign/defect blocker has route-evidence closure. It can move from
route-evidence to accepted discharge only after these targets become accepted
imports or formal theorems:

| target | purpose |
|---|---|
| `FixedSPositiveTraceReadOffTheorem` | identifies the positive trace with the restricted Weil form plus explicit ledgers and remainder |
| `SoninProlateDefectEqualsEndpointStripCdef` | proves no uncontrolled positive prolate/Sonin defect is subtracted from `QW_lambda` |
| `CC20PostQRemainderFixedSSoninTransport` | proves the CC20 `D circ Q` / `E circ Q` bulk and boundary pieces are transported into the exact fixed-S source model before Rows 4-6 classify them |
| `PostQDerivativeDomainCompatibility` / `PostQBoundaryEvaluationTransport` / `PostQSeriesTailBoundedComparison` | prevents using CCM24's Sonin isomorphism as a shortcut for derivative, endpoint, and series-tail transport |
| `PostQBulkFixedSEquality` | proves the fixed-S bulk object later classified by Row 4 is actually the transported CC20 source bulk object |
| `FixedSPostQBulkGraphTransfer` | project proof bridge now required for the first Row 3 subcontract; it cannot be replaced by a CC20/CCM24 source import |
| `PostQBoundaryLedgerEntryGate` | keeps source endpoint terms available for Row 5/6 without prematurely classifying them |
| `PostQFullTransportedRemainderLimit` | promotes finite termwise Row 3 transport to the full source remainder only after tail convergence survives fixed-S comparison |
| `CdefTraceNormFormula` | defines `Cdef` as a trace-norm quantity, not a role name |
| `FixedTestCdefExhaustion` | proves the fixed-test endpoint-strip remainder vanishes |
| `RestrictedToFullQWExhaustion` | proves the limit from restricted `QW_lambda` to full `QW` for the same source test |
| `RestrictedToFullQWBridgeContract` | proves that `RestrictedToFullQWExhaustion` follows from the CCM25 restriction definition plus common-test, window, and finite-prime support bridges |
| `FinalSignBridgeContract` | proves `QW(g,g) >= 0` feeds CC20 as `sum_v W_v(F_g) <= 0` |

The sign/defect targets tracked by this audit now have theorem contracts and
route-evidence packages where listed:

```text
docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md
docs/audits/sonin-prolate-defect-discharge-ledger.md
docs/proofs/cc20-source-remainder-orientation-theorem-contract.md
docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md
docs/proofs/cc20-post-q-derivative-domain-compatibility-theorem-contract.md
docs/audits/cc20-post-q-derivative-domain-source-decision-audit.md
docs/proofs/fixed-s-post-q-bulk-graph-transfer-theorem-contract.md
docs/proofs/fixed-s-post-q-bulk-graph-transfer-proof-package.md
docs/proofs/cc20-post-q-boundary-evaluation-transport-theorem-contract.md
docs/proofs/cc20-post-q-series-tail-bounded-comparison-theorem-contract.md
docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md
docs/proofs/source-rank-pole-ledger-identification-proof-package.md
docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md
docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md
docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md
docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md
docs/proofs/restricted-to-full-qw-bridge-proof-package.md
```

Their source-readiness audits split the status:

```text
docs/audits/sonin-prolate-defect-source-readiness-audit.md
  -> no direct accepted source import for the full bridge

docs/audits/restricted-to-full-qw-source-readiness-audit.md
  -> source-definition path found after bridges
```

## Current Judgment

The sign/defect criticism was the real hard blocker for the route-level
positive-trace step.

The repository now has referee-facing project proof packages for that step.
The Rows 1-2 package fixes the CC20 source obstruction and post-`Q` image. The
Rows 3-7 package transports and classifies that object. The accepted-source
certification remains open.

The current honest status is:

```text
source-conditional project proof packages with route-level sign/defect closure;
accepted-source and Lean discharge still open.
```

It is not:

```text
completed RH proof.
```
