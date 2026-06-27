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
| `docs/proofs/source-object-definition-spine-discharge.md` | source-definition spine package; ties `g`, `F_g`, `S`, `I`, `lambda`, CCM25 Weil objects, CC20 trace objects, and the Mathlib RH exit into one source-object dependency spine |
| `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md` | CCM25 global definition-sign package; replaces symbolic `QW`, `Psi`, pole, archimedean, and global finite-prime fields with source-object bridge targets |
| `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md` | CCM25 restricted-window package; ties `QW_lambda`, `restrictedPrimeIndexSet lambda`, restricted pole pairing, and lambda-window support to the global CCM25 spine |
| `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md` | CCM25 finite-prime index package; replaces bare `Nat` coverage with source prime-power indices, lambda cuts, von Mangoldt weights, and `T(n)` pairings |
| `docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md` | CCM25 finite-prime normalization spine package; requires source prime-power indices, visibility, lambda cut, `Lambda(n)`, `<g|T(n)g>`, and pointwise term equality before finite-prime sums |
| `docs/proofs/ccm25-restricted-read-off-discharge.md` | first source-interface discharge package; splits the restricted CCM25 read-off into window, sign, pole, and finite-prime replacement targets |
| `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md` | finite-prime source-discharge package; splits restricted support coverage from von Mangoldt and prime-power pairing normalization |
| `docs/proofs/cc20-trace-legality-mellin-discharge.md` | CC20 source-discharge package; separates Hilbert-Schmidt, trace-class, cyclicity, support-square trace, sign, and Mellin half-density gates |
| `docs/proofs/cc20-trace-object-normalization-discharge.md` | CC20 trace-object package; replaces symbolic trace fields with source test, trace-ideal, positive trace, no-defect trace, Mellin, and sign bridge targets |
| `docs/proofs/cc20-analytic-trace-legality-spine-discharge.md` | CC20 analytic trace-legality spine package; fixes the order from operator identity through Hilbert-Schmidt, trace-class, cyclicity, positive trace, support-square trace, no-defect trace, and Weil read-off |
| `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md` | CC20 final-exit package; bridges triple vanishing and full Weil positivity to Proposition C.1 with `F={0,1/2,1}` |
| `docs/proofs/cc20-rh-exit-object-normalization-discharge.md` | CC20 RH-exit object package; expands `FiniteVanishingCriterionPackage` into finite-set, Mellin-vanishing, Weil-inequality, Proposition C.1, and Mathlib-RH bridge targets |
| `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md` | final sign-bridge package; proves `QW(g,g) >= 0` feeds Proposition C.1 only through `QW(g,g) = - sum_v W_v(g * bar(g)^sharp)` |
| `docs/proofs/final-sign-bridge-spine-discharge.md` | final sign-bridge spine package; splits the CCM25-to-CC20 sign bridge into source-test, `Psi`, archimedean, finite-prime, pole, equality, and inequality-direction targets |
| `docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md` | final definition-bridge package; maps the CC20 source RH conclusion to Mathlib's `_root_.RiemannHypothesis` |
| `docs/proofs/rh-definition-bridge-spine-discharge.md` | RH definition-bridge spine package; transports source RH to Mathlib RH through zeta equality, zero equation, negative-even exclusion, pole exclusion, and critical-line equation |
| `docs/proofs/ccm24-support-window-transport-discharge.md` | CCM24 source-discharge package; keeps the fixed-S test, support window, Fourier window, comparison map, and Sonin exhaustion in one source-backed model |
| `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | CCM24 semilocal object package; replaces symbolic place sets, windows, support transport, comparison maps, and Sonin exhaustion with source bridge targets |
| `docs/proofs/source-object-derived-compact-records.md` | derivation package; proves expanded source-object packages can derive the compact records consumed by the current route |
| `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md` | Battle 2 proof package; expands the fixed-S support-square transport into projection transport, phase pullback, defect classification, and trace legality |
| `docs/proofs/battle-3-cdef-exhaustion-proof-package.md` | Battle 3 proof package; defines trace-norm Cdef, compares it with graph/prolate Cdef, and proves fixed-test exhaustion |
| `docs/proofs/fixed-test-graph-cdef-exhaustion.md` | fixed-test graph exhaustion package; discharges the graph/prolate Cdef exhaustion input for fixed `g` and fixed `S_A` |

Current files:

| file | role |
|---|---|
| `source-reread-v0.2.md` | source-line map for CCM24, CCM25, and CC20 inputs |
| `lean-source-interface-map.md` | Lean source-interface obligations and route bridges |
| `source-interface-discharge-audit.md` | attack plan for removing the source-conditional boundary by discharging CCM24, CCM25, and CC20 contracts |
| `source-interface-discharge-completion-audit.md` | completion audit for the mathematics-first source-interface proof-package coverage |
| `source-object-definition-ledger.md` | definition-discharge ledger for replacing symbolic CCM24, CCM25, CC20, and RH-exit objects with concrete definitions or imported theorem interfaces |
| `source-object-replacement-consistency-audit.md` | consistency audit for the source-object replacement batch before commit or Lean interface work |
| `formal-gate-spine-consistency-audit.md` | consistency audit for the five remaining formal-gate spine packages as one Lean-facing source-discharge target |
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

The three core defect proof packages are now written at route-evidence level.
The route remains source-conditional until the CCM24, CCM25, and CC20 source
interfaces are discharged by proofs, independently accepted source theorems, or
formal imports.
