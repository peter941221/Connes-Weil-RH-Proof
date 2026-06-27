# Source Interface Discharge Completion Audit

Status: completion audit for the mathematics-first source-discharge phase.

This audit checks whether the CCM24, CCM25, and CC20 source-interface matrix
now has a proof-package answer for every row. It also states what this does not
prove.

## Result

Good result:

```text
Every source-interface row now has a named proof package.
```

Bad result for final certification:

```text
No source-interface row is yet discharged by a formal Lean theorem or by an
accepted imported theorem with audited hypotheses.
```

The route has moved from an open source-interface matrix to a complete
mathematical proof-package matrix. It remains source-conditional.

## Evidence Classes

| class | meaning | final-certificate strength |
|---|---|---:|
| proof package | manuscript-level proof package with source-line anchors | partial |
| source import | accepted external theorem with exact hypothesis bridge | strong |
| Lean theorem | formal theorem with audited axioms | strongest |

This audit records the first class. It does not upgrade any row to the second
or third class.

## CCM24 Matrix

| contract | source lines | proof package | package result | remaining certification work |
|---|---|---|---|---|
| `ccm24CanonicalSemilocalModel` | `mainc2m24fine.tex:237-253,786-804` | `docs/proofs/ccm24-support-window-transport-discharge.md`; `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | canonical fixed-`S` model, `V_S=M_S U_S`, and Fourier grading are tied to the route coordinate and source place set | formalize or import the CCM24 Hilbert-model theorem |
| `ccm24SupportTransport` | `mainc2m24fine.tex:761-771,983-1003` | `docs/proofs/ccm24-support-window-transport-discharge.md`; `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | support, Fourier support, and convolution-square support move through the same source-backed window | replace symbolic window predicates with concrete support definitions |
| `ccm24BoundedComparison` | `mainc2m24fine.tex:806-823` | `docs/proofs/ccm24-support-window-transport-discharge.md`; `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | bounded comparison with bounded inverse preserves the analytic class after trace-ideal input is supplied | formalize trace-ideal preservation through bounded comparison |
| `ccm24SoninComparison` | `mainc2m24fine.tex:1050-1060` | `docs/proofs/ccm24-support-window-transport-discharge.md`; `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` | fixed-window Sonin comparison keeps `g`, `I`, `S_A`, and graph order fixed before the `lambda` limit | formalize the fixed-window exhaustion bridge |

CCM24 coverage now blocks fixed-`S` drift at the proof-package level:

```text
positive trace window = restricted Weil window = Cdef exhaustion window.
```

## CCM25 Matrix

| contract | source lines | proof package | package result | remaining certification work |
|---|---|---|---|---|
| `ccm25QWDefinition` | `mc2arXiv.tex:445-470` | `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md`; `docs/proofs/ccm25-restricted-read-off-discharge.md`; `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md` | `QW(f,g)=Psi(f^* * g)` and the global sign spine are separated from route-local notation | formalize or import the exact CCM25 `QW` and `Psi` definitions |
| `ccm25QWLambdaFormula` | `mc2arXiv.tex:530-540` | `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md`; `docs/proofs/ccm25-restricted-read-off-discharge.md` | restricted `QW_lambda` uses one lambda window, the displayed pole term, and the negative finite-prime sum | formalize or import the restricted quadratic-form theorem |
| `ccm25FinitePrimeNormalization` | `mc2arXiv.tex:445-470,530-540` | `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md`; `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md` | coverage, source prime-power indexing, lambda cuts, von Mangoldt weight, prime-power pairing, and term normalization are distinct obligations | replace symbolic finite-prime fields with concrete source definitions |
| `ccm25PoleNormalization` | `mc2arXiv.tex:465-470,533-535` | `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md`; `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md`; `docs/proofs/ccm25-restricted-read-off-discharge.md` | the CCM pole functional lives inside `QW_lambda`; route `PoleJetExtra` stays outside until triple vanishing kills it | formalize the pole functional under the route half-density convention |

CCM25 coverage now blocks the main sign and finite-prime failures:

```text
wrong test
wrong finite-prime support
wrong von Mangoldt coefficient
wrong pole location
wrong inequality direction
```

The sign bridge is now explicit:

```text
QW(g,g) = - sum_v W_v(g * bar(g)^sharp).
```

## CC20 Matrix

| contract | source lines | proof package | package result | remaining certification work |
|---|---|---|---|---|
| `cc20ArchimedeanTraceSquare` | `weil-compo.tex:378-387` | `docs/proofs/cc20-trace-legality-mellin-discharge.md`; `docs/proofs/cc20-trace-object-normalization-discharge.md` | support-square trace read-off uses the CC20 source trace convention and stays separate from the positive trace until the source equality is proved | formalize or import the trace-square theorem |
| `cc20TraceClassTemplate` | `weil-compo.tex:448-464,2106-2121` | `docs/proofs/cc20-trace-legality-mellin-discharge.md`; `docs/proofs/cc20-trace-object-normalization-discharge.md` | Hilbert-Schmidt, trace-class, and cyclicity gates precede positivity and trace moves and come from one source trace-ideal template | formalize or import the analytic trace-ideal theorem |
| `cc20MellinHalfDensityConvention` | `weil-compo.tex:2014-2030` | `docs/proofs/cc20-trace-legality-mellin-discharge.md`; `docs/proofs/cc20-trace-object-normalization-discharge.md`; `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md` | route triple vanishing maps to Mellin vanishing on `F={0,1/2,1}` through the same convolution square used by CCM25 | formalize the half-density/Mellin translation |
| `cc20FiniteVanishingRhExit` | `weil-compo.tex:2072-2085` | `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md`; `docs/proofs/cc20-rh-exit-object-normalization-discharge.md`; `docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md` | Proposition C.1 applies with `F={0,1/2,1}`, route triple vanishing and full positivity are translated into CC20 hypotheses, and the conclusion is mapped toward Mathlib RH | formalize or import Proposition C.1 and the source-RH-to-Mathlib-RH bridge |
| `cc20SignsAndNormalizations` | `weil-compo.tex:2131-2165` | `docs/proofs/cc20-trace-legality-mellin-discharge.md`; `docs/proofs/cc20-trace-object-normalization-discharge.md`; `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md` | CC20 `u_infty` and `qd u` sign aligns with CCM25 `W_R=-W_infty` and the final nonpositivity inequality | formalize the local sign convention bridge |

CC20 coverage now blocks the final-exit failures:

```text
positivity before trace-class
cyclicity outside trace-class
Mellin convention mismatch
sign-flipped Proposition C.1 input
source RH name drift against Mathlib RH
```

## Remaining Formal Gates

The proof-package matrix leaves five formal gates.

| gate | what must become formal or imported |
|---|---|
| source object definitions | CCM24 windows, CCM25 `QW`, CC20 Weil sum, and source zeta objects must become explicit definitions or imported theorem interfaces; see `docs/audits/source-object-definition-ledger.md` and `docs/proofs/source-object-definition-spine-discharge.md` |
| analytic trace legality | CC20 trace-class and cyclicity theorems must be formalized or imported with exact hypotheses; see `docs/proofs/cc20-analytic-trace-legality-spine-discharge.md` and the stronger theorem contract `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md` |
| finite-prime normalization | CCM25 prime-power support, von Mangoldt weights, and pairing formulas must replace symbolic fields; see `docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md` and the stronger theorem contract `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` |
| final sign bridge | Lean must expose `QW(g,g) = - sum_v W_v(g * bar(g)^sharp)` and the inequality-direction theorem; see `docs/proofs/final-sign-bridge-spine-discharge.md` and the stronger theorem contract `docs/proofs/final-sign-bridge-theorem-contract.md` |
| RH definition bridge | CC20 source RH must be transported to Mathlib's `_root_.RiemannHypothesis` through the same zeta, zero, exclusion, and critical-line definitions; see `docs/proofs/rh-definition-bridge-spine-discharge.md` |

The source-object replacement batch has a separate consistency audit:

```text
docs/audits/source-object-replacement-consistency-audit.md
```

It checks that the CCM24, CCM25, CC20 trace, and CC20 RH-exit replacement
packages preserve one test object, one lambda window, pointwise finite-prime
terms, the sign bridge, and the Mathlib RH target.

The five remaining formal gates have a separate spine consistency audit:

```text
docs/audits/formal-gate-spine-consistency-audit.md
```

It checks that the source-definition, trace-legality, finite-prime
normalization, sign, and RH-definition spines compose as one Lean-facing
source-discharge target.

These gates are not optional polish. They are the difference between:

```text
source-conditional route evidence
```

and:

```text
proof artifact with audited source discharge.
```

## Current Judgment

| question | answer |
|---|---|
| Are all source-interface rows attacked by named proof packages? | yes |
| Is every proof package source-line anchored? | yes |
| Does this prove RH as a formal Lean theorem with discharged source interfaces? | no |
| Does this remove the broadest mathematical ambiguity in the source-interface layer? | yes |
| Is the next phase allowed to add Lean scaffolding without further math? | only if it encodes these proof packages and keeps the five formal gates visible |

The mathematics-first source-discharge phase has reached package coverage.
Certification now requires replacing packages by formal theorems or accepted
imports, without collapsing the exposed bridges back into opaque propositions.
