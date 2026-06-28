# Audits

This directory holds source-readiness and proof-integrity audits for the
Connes-Weil route.

Mathematical proof packages live in `docs/proofs/`. Audit files may point to
those packages, but an audit label does not certify a proof.

Current proof packages:

| file | role |
|---|---|
| `docs/proofs/battle-1-test-quotient-proof-package.md` | Battle 1 proof package; closes the half-density, Tate pole, and rank-repair legs at route-evidence level |
| `docs/proofs/rank-repair-finite-normal-form.md` | rank-repair normal-form package; identifies the zero-mode rank and routes non-pure terms through endpoint-strip Cdef |
| `docs/proofs/semilocal-q-compact-form.md` | semilocal compact-form package; proves projection-defect boundary jets are endpoint-strip Cdef at route-evidence level |
| `docs/proofs/fixed-s-no-defect-compact-form-read-off.md` | source-normalized no-defect read-off package; discharges the remaining Battle 1 rank-repair read-off at source-interface level |
| `docs/proofs/source-test-convolution-compatibility.md` | common-test proof package; ties the CCM24 fixed-S test, CCM25 `F_g=g^* * g`, and CC20 Mellin half-density test to one source object |
| `docs/proofs/source-common-test-tuple-theorem-contract.md` | common-test and fixed-tuple theorem contract; states formal/import targets for `SourceCommonTestAndConvolution` and `SourceRouteTupleFixed` |
| `docs/proofs/source-object-definition-spine-discharge.md` | source-definition spine package; ties `g`, `F_g`, `S`, `I`, `lambda`, CCM25 Weil objects, CC20 trace objects, and the Mathlib RH exit into one source-object dependency spine |
| `docs/proofs/source-object-definition-theorem-contract.md` | source-object definition theorem contract; states the formal/import targets for the common test, fixed route tuple, restricted window, CCM25 Weil objects, CC20 trace objects, CC20 RH exit objects, and compact-record derivations |
| `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md` | CCM25 global definition-sign package; replaces symbolic `QW`, `Psi`, pole, archimedean, and global finite-prime fields with source-object bridge targets |
| `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md` | CCM25 restricted-window package; ties `QW_lambda`, `restrictedPrimeIndexSet lambda`, restricted pole pairing, and lambda-window support to the global CCM25 spine |
| `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md` | CCM25 finite-prime index package; replaces bare `Nat` coverage with source prime-power indices, lambda cuts, von Mangoldt weights, and `T(n)` pairings |
| `docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md` | CCM25 finite-prime normalization spine package; requires source prime-power indices, visibility, lambda cut, `Lambda(n)`, `<g|T(n)g>`, and pointwise term equality before finite-prime sums |
| `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` | CCM25 finite-prime theorem contract; states the formal/import targets for prime-power factorization, global support, restricted lambda cut, visibility, von Mangoldt weight, source pairing, pointwise atoms, and sign ownership |
| `docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md` | restricted-to-full theorem contract; states the scalar fixed-test `QW_lambda(g,g) -> QW(g,g)` target without importing CCM25 spectral convergence |
| `docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md` | restricted-to-full bridge contract; composes the CCM25 restriction definition with common-test, window, and finite-prime support contracts to target eventual scalar equality |
| `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` | restricted-to-full bridge proof package; proves fixed-test eventual identity `QW_lambda(g,g)=QW(g,g)` at route-evidence level only |
| `docs/proofs/ccm25-restricted-read-off-discharge.md` | first source-interface discharge package; splits the restricted CCM25 read-off into window, sign, pole, and finite-prime replacement targets |
| `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md` | finite-prime source-discharge package; splits restricted support coverage from von Mangoldt and prime-power pairing normalization |
| `docs/proofs/cc20-trace-legality-mellin-discharge.md` | CC20 source-discharge package; separates Hilbert-Schmidt, trace-class, cyclicity, support-square trace, sign, and Mellin half-density gates |
| `docs/proofs/cc20-trace-object-normalization-discharge.md` | CC20 trace-object package; replaces symbolic trace fields with source test, trace-ideal, positive trace, no-defect trace, Mellin, and sign bridge targets |
| `docs/proofs/cc20-analytic-trace-legality-spine-discharge.md` | CC20 analytic trace-legality spine package; fixes the order from operator identity through Hilbert-Schmidt, trace-class, cyclicity, positive trace, support-square trace, no-defect trace, and Weil read-off |
| `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md` | CC20 trace-legality theorem contract; states the formal/import targets for operator identity, Hilbert-Schmidt, trace-class square, cyclicity ledger, support-square read-off, no-defect read-off, and bounded-comparison transport |
| `docs/proofs/trace-scale-compatibility-theorem-contract.md` | B1 theorem contract; states same-scalar, same-cutoff, source-convention ledger, no-missing-bulk, and lambda-limit compatibility targets before positive trace can feed `QW_lambda` |
| `docs/proofs/trace-scale-compatibility-proof-package.md` | B1 route-evidence proof package; closes trace-scale compatibility at project proof-package level while leaving accepted-source, external referee, and Lean certification open |
| `docs/proofs/cc20-source-remainder-orientation-theorem-contract.md` | CC20 source-remainder orientation contract; fixes `W_infty=L-D`, `W_infty=S-E`, and the post-`Q` remainder target before fixed-S transport |
| `docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md` | Rows 1-2 referee-facing source-entry package; fixes the CC20 source obstruction, `Q` image, bulk term, boundary terms, and series tail handed to Row 3 |
| `docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md` | Row 3 sign/defect contract; states the formal/import target that transports the CC20 `D circ Q` / `E circ Q` bulk and boundary pieces into the same fixed-S CCM24/Sonin/window coordinate before any `Cdef` claim |
| `docs/proofs/cc20-post-q-derivative-domain-compatibility-theorem-contract.md` | first Row 3 subcontract; states the derivative/domain bridge needed before the CC20 post-`Q` bulk term may enter fixed-S projection-defect classification |
| `docs/proofs/fixed-s-post-q-bulk-graph-transfer-theorem-contract.md` | project-proof target for the first Row 3 subcontract; aims to prove fixed-S graph-domain transport and source-bulk equality for the CC20 post-`Q` bulk term |
| `docs/proofs/fixed-s-post-q-bulk-graph-transfer-proof-package.md` | route-evidence proof package for the first Row 3 subcontract; proves fixed-S graph-domain transport and source-bulk equality for the CC20 post-`Q` bulk term at project level |
| `docs/proofs/cc20-post-q-boundary-evaluation-transport-theorem-contract.md` | second Row 3 subcontract; states the fixed-S boundary-functional bridge needed before CC20 endpoint terms may enter rank/pole/Cdef classification |
| `docs/proofs/fixed-s-post-q-boundary-functional-transfer-theorem-contract.md` | project-proof target for the second Row 3 subcontract; aims to prove fixed-S endpoint-functional transport and source-boundary equality for the CC20 post-`Q` boundary terms |
| `docs/proofs/fixed-s-post-q-boundary-functional-transfer-proof-package.md` | route-evidence proof package for the second Row 3 subcontract; proves fixed-S endpoint-functional transport and source-boundary equality for the CC20 post-`Q` boundary terms at project level |
| `docs/proofs/cc20-post-q-series-tail-bounded-comparison-theorem-contract.md` | third Row 3 subcontract; states the bounded-comparison bridge needed before CC20 scalar tail convergence may become full fixed-S transported remainder convergence |
| `docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-theorem-contract.md` | project-proof target for the third Row 3 subcontract; aims to prove fixed-S tail Cauchy control and full transported source-remainder limit |
| `docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-proof-package.md` | route-evidence proof package for the third Row 3 subcontract; proves fixed-S tail bounded comparison and the full transported source-remainder limit at project level |
| `docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md` | combined Row 3 proof package; closes fixed-S transport of the CC20 post-`Q` source remainder at route-evidence level only |
| `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-theorem-contract.md` | Row 4 theorem contract; states the projection-defect normal-form target for the transported CC20 source remainder |
| `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md` | Row 4 proof package; closes no-strip/projection-order split and endpoint-strip shifted-kernel normal form at route-evidence level only |
| `docs/proofs/source-rank-pole-ledger-identification-theorem-contract.md` | Row 5 theorem contract; states the no-strip rank/pole ledger identification target for the transported source remainder |
| `docs/proofs/source-rank-pole-ledger-identification-proof-package.md` | Row 5 proof package; identifies no-strip channels as rank or pole and gates triple vanishing at route-evidence level only |
| `docs/proofs/source-endpoint-strip-cdef-domination-theorem-contract.md` | Row 6 theorem contract; states the endpoint-strip source-remainder domination target for route `Cdef` |
| `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md` | Row 6 proof package; matches endpoint-strip source-remainder terms to route `Cdef` summands and fixed-test exhaustion at route-evidence level only |
| `docs/proofs/no-hidden-positive-defect-outside-cdef-theorem-contract.md` | Row 7 theorem contract; states the exact positive-trace read-off equality excluding a hidden fourth positive defect |
| `docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md` | Row 7 proof package; closes the hidden-defect equality at route-evidence level only |
| `docs/proofs/sonin-prolate-defect-referee-discharge.md` | referee-facing sign/defect discharge package; composes Rows 3-7 into one project proof chain after the Rows 1-2 source-entry package |
| `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md` | CC20 final-exit package; bridges triple vanishing and full Weil positivity to Proposition C.1 with `F={0,1/2,1}` |
| `docs/proofs/cc20-rh-exit-object-normalization-discharge.md` | CC20 RH-exit object package; expands `FiniteVanishingCriterionPackage` into finite-set, Mellin-vanishing, Weil-inequality, Proposition C.1, and Mathlib-RH bridge targets |
| `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md` | final sign-bridge package; proves `QW(g,g) >= 0` feeds Proposition C.1 only through `QW(g,g) = - sum_v W_v(g * bar(g)^sharp)` |
| `docs/proofs/final-sign-bridge-spine-discharge.md` | final sign-bridge spine package; splits the CCM25-to-CC20 sign bridge into source-test, `Psi`, archimedean, finite-prime, pole, equality, and inequality-direction targets |
| `docs/proofs/final-sign-bridge-theorem-contract.md` | final sign-bridge theorem contract; states the formal/import targets for common test, `Psi` expansion, archimedean sign, finite-prime sign ownership, pole sign, `QW=-sum_v W_v`, and inequality direction |
| `docs/proofs/final-sign-bridge-proof-package.md` | final sign-bridge proof package; closes `QW(g,g)=-sum_v W_v(F_g)` and the CC20 inequality direction at route-evidence level only |
| `docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md` | final definition-bridge package; maps the CC20 source RH conclusion to Mathlib's `_root_.RiemannHypothesis` |
| `docs/proofs/rh-definition-bridge-spine-discharge.md` | RH definition-bridge spine package; transports source RH to Mathlib RH through zeta equality, zero equation, negative-even exclusion, pole exclusion, and critical-line equation |
| `docs/proofs/rh-definition-bridge-theorem-contract.md` | RH definition-bridge theorem contract; states the formal/import targets for zeta equality, zero transport, negative-even exclusion, pole exclusion, source non-trivial-zero construction, critical-line equivalence, and source-RH-to-Mathlib-RH |
| `docs/proofs/rh-definition-bridge-proof-package.md` | RH definition-bridge proof package; closes `CC20SourceRH -> _root_.RiemannHypothesis` at route-evidence level only |
| `docs/proofs/source-conditional-rh-route-closure-proof-package.md` | source-conditional route closure package; composes sign/defect, restricted-to-full, final sign, CC20 exit, and RH definition bridges into Mathlib RH at route-evidence level only |
| `docs/proofs/ccm24-support-window-transport-discharge.md` | CCM24 source-discharge package; keeps the fixed-S test, support window, Fourier window, comparison map, and Sonin exhaustion in one source-backed model |
| `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | CCM24 semilocal object package; replaces symbolic place sets, windows, support transport, comparison maps, and Sonin exhaustion with source bridge targets |
| `docs/proofs/source-object-derived-compact-records.md` | derivation package; proves expanded source-object packages can derive the compact records consumed by the current route |
| `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md` | Battle 2 proof package; expands the fixed-S support-square transport into projection transport, phase pullback, defect classification, and trace legality |
| `docs/proofs/battle-3-cdef-exhaustion-proof-package.md` | Battle 3 proof package; defines trace-norm Cdef, compares it with graph/prolate Cdef, and proves fixed-test exhaustion |
| `docs/proofs/fixed-test-graph-cdef-exhaustion.md` | fixed-test graph exhaustion package; discharges the graph/prolate Cdef exhaustion input for fixed `g` and fixed `S_A` |
| `docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md` | sign/defect theorem contract; states the formal/import target that identifies source prolate/Sonin defects with rank, pole, and endpoint-strip `Cdef` classes |

Current files:

| file | role |
|---|---|
| `source-reread-v0.2.md` | source-line map for CCM24, CCM25, and CC20 inputs |
| `pre-lean-completion-audit.md` | local non-Lean completion gate; records that the proof-package matrix is complete while accepted-source, external, and Lean certification remain open |
| `trace-scale-compatibility-audit.md` | first external-review blocker audit; records B1 trace-scale compatibility and points to the route-evidence proof package |
| `trace-scale-compatibility-discharge-attempt.md` | B1 discharge attempt; records the initial gap and the later project proof-package closure of ordinary-to-source convention ledger and no-missing-bulk theorem |
| `sonin-projection-repair-rejection-audit.md` | B2 audit; rejects replacing the current positive trace by a Sonin-projection trace unless a new same-scale compatibility theorem is proved |
| `semilocal-fourth-defect-ledger.md` | B3 ledger; classifies possible semilocal cross-term hiding places through Rows 1-7 and closes the fourth-defect risk at project proof-package level |
| `s-local-global-quantifier-audit.md` | B4 audit; checks that dynamic `S(g)` is only a fixed-test witness and that the route returns global `QW(g,g)` and the CC20 forall-g Weil inequality |
| `lean-source-interface-map.md` | Lean source-interface obligations and route bridges |
| `source-interface-discharge-audit.md` | attack plan for removing the source-conditional boundary by discharging CCM24, CCM25, and CC20 contracts |
| `source-interface-discharge-completion-audit.md` | completion audit for the mathematics-first source-interface proof-package coverage |
| `accepted-source-certification-audit.md` | external-review checklist for upgrading the proof-package matrix to accepted-source or Lean theorem strength |
| `source-object-definition-ledger.md` | definition-discharge ledger for replacing symbolic CCM24, CCM25, CC20, and RH-exit objects with concrete definitions or imported theorem interfaces |
| `source-object-theorem-discharge-ledger.md` | theorem-discharge ledger for the source-object definition gate; states row-by-row acceptance evidence for `SourceDefinitionSpineContract` |
| `source-object-replacement-consistency-audit.md` | consistency audit for the source-object replacement batch before commit or Lean interface work |
| `formal-gate-spine-consistency-audit.md` | consistency audit for the remaining formal-gate spine packages as one Lean-facing source-discharge target |
| `fast-route-search-2026-06-27.md` | rapid route-search audit for the two urgent blockers; prioritizes Row 3 fixed-S transport of the CC20 post-`Q` remainder and the fixed-test restricted-to-full `QW` bridge, while rejecting spectral-convergence shortcuts |
| `cc20-post-q-remainder-term-map.md` | Row 3 item-level audit mapping the CC20 `Q epsilon` formula into bulk, boundary, and series-tail transport targets |
| `ccm24-fixed-s-post-q-transport-obstruction-audit.md` | Row 3 CCM24 fast-pass audit; confirms model/window/Sonin transport support while splitting post-`Q` derivative, boundary, and tail transport into separate open subcontracts |
| `cc20-post-q-derivative-domain-source-decision-audit.md` | source-import decision audit for `PostQDerivativeDomainCompatibility`; classifies the first Row 3 subcontract as project-proof-required rather than source-import-discharged |
| `cc20-post-q-boundary-evaluation-source-decision-audit.md` | source-import decision audit for `PostQBoundaryEvaluationTransport`; classifies the second Row 3 subcontract as project-proof-required rather than source-import-discharged |
| `cc20-post-q-series-tail-source-decision-audit.md` | source-import decision audit for `PostQSeriesTailBoundedComparison`; classifies the third Row 3 subcontract as project-proof-required rather than source-import-discharged |
| `sign-defect-blocker-audit.md` | hard-blocker audit for the positive-trace-to-Weil sign, defect, and `Cdef` discharge gate |
| `source-import-legitimacy-audit.md` | hard-blocker audit classifying CCM24, CCM25, and CC20 inputs as import candidates, project packages, or non-importable claims |
| `sonin-prolate-defect-source-readiness-audit.md` | source-readiness audit showing the prolate/Sonin-to-`Cdef` bridge remains a hard blocker |
| `sonin-prolate-defect-discharge-ledger.md` | row-by-row discharge ledger for the sign/defect bridge, from CC20 source remainder object through fixed-S transport, rank/pole/Cdef classification, and no-hidden-defect equality |
| `restricted-to-full-qw-source-readiness-audit.md` | source-readiness audit showing fixed-test `QW_lambda=QW` has a CCM25 restriction-definition path after the bridge contract is discharged |
| `../../formalization/source-object-interface-plan.md` | documentation plan for encoding the expanded source-object packages in the next Lean interface pass |
| `../../formalization/source-object-interface-risk-audit.md` | pre-Lean risk audit and grep/build gates for the source-object interface pass |
| `../../formalization/source-object-interface-workplan.md` | file-level workplan for adding source-object package records and derivations in Lean |
| `lean-segment-build.md` | segmented Lean build and axiom-audit history |
| `core-defect-gap-ledger.md` | public ledger for the three hard positive-trace-to-Weil steps |
| `three-battle-workplan.md` | execution checklist for the three proof packages |
| `three-battle-completion-audit.md` | completion audit for the three proof packages |
| `battle-1-test-quotient-compatibility.md` | proof audit for the test conversion and quotient-ledger package |
| `battle-2-fixed-s-support-square-transport.md` | proof audit for the fixed-S support-square transport package |
| `battle-3-cdef-exhaustion.md` | proof audit for the endpoint-strip Cdef norm and fixed-test limit |

The source-conditional route now has a route-evidence composition package. The
route remains source-conditional until the CCM24, CCM25, and CC20 source
interfaces are discharged by proofs, independently accepted source theorems,
or formal imports.
