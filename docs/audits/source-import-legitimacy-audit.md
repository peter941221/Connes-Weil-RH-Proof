# Source Import Legitimacy Audit

Status: hard-blocker audit for CCM24, CCM25, and CC20 imports.

This audit asks whether the route imports actual theorems, definitions, and
formulae, or whether it imports strategy statements, numerical observations, or
project-local proof packages.

The route can stay source-conditional only if each imported source interface
has a precise theorem-level source. A source-line reference proves location. It
does not prove legitimacy by itself.

## Evidence Checked

| evidence | role |
|---|---|
| `docs/audits/source-reread-v0.2.md:29-52` | maps manuscript dependencies to CCM24, CCM25, and CC20 source lines |
| `docs/audits/source-interface-discharge-completion-audit.md:14-21` | says every row has a proof package, but no row is discharged by Lean theorem or accepted import |
| `docs/audits/source-interface-discharge-completion-audit.md:146-154` | confirms proof-package coverage does not prove RH |
| `docs/audits/accepted-source-certification-audit.md` | external-review checklist for upgrading proof-package rows to accepted-source or Lean theorem strength |
| `docs/proofs/ccm25-restricted-read-off-discharge.md:11-25` | says restricted CCM25 read-off remains an imported contract until formal or accepted discharge |
| `docs/proofs/ccm25-restricted-read-off-discharge.md:475-488` | marks formal/accepted source discharge as open |
| `docs/proofs/battle-3-cdef-exhaustion-proof-package.md:11-18` | says Battle 3 proves no new CCM or CC20 source theorem |
| `docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md` | formal/import target for scalar fixed-test `QW_lambda -> QW` |
| `docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md` | formal/import composition target from CCM25 restriction definition plus common-test, window, and finite-prime support contracts to eventual scalar equality |
| `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` | route-evidence proof package for fixed-test eventual scalar equality; still not a source import |
| `docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md` | formal/import target separating source prolate/Sonin control from project `Cdef` naming |
| `docs/audits/sonin-prolate-defect-discharge-ledger.md` | row-by-row acceptance criteria for discharging the source prolate/Sonin remainder bridge |
| `docs/proofs/cc20-source-remainder-orientation-theorem-contract.md` | source-orientation contract for the CC20 `D` and `E` remainders before fixed-S transport |
| `docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md` | referee-facing project proof package for Rows 1-2; still not an accepted source import |
| `docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md` | Row 3 fixed-S transport target for the CC20 post-`Q` source remainder, before projection-defect or `Cdef` classification |
| `docs/audits/cc20-post-q-remainder-term-map.md` | item-level map of the CC20 post-`Q` `epsilon` formula; source evidence for Row 3 subtargets, not a discharge theorem |
| `docs/audits/ccm24-fixed-s-post-q-transport-obstruction-audit.md` | CCM24 fast-pass audit separating importable model/window/Sonin comparison from non-importable derivative, boundary, and tail transport shortcuts |
| `docs/proofs/cc20-post-q-derivative-domain-compatibility-theorem-contract.md` | first Row 3 subcontract; states what an import must prove before the CC20 post-`Q` bulk derivative term can enter fixed-S projection-defect classification |
| `docs/audits/cc20-post-q-derivative-domain-source-decision-audit.md` | decision audit classifying the first Row 3 subcontract as project-proof-required rather than source-import-discharged |
| `docs/proofs/fixed-s-post-q-bulk-graph-transfer-theorem-contract.md` | project-proof contract for the first Row 3 subcontract; not a source import |
| `docs/proofs/fixed-s-post-q-bulk-graph-transfer-proof-package.md` | route-evidence proof package for the first Row 3 subcontract; still not a source import |
| `docs/proofs/cc20-post-q-boundary-evaluation-transport-theorem-contract.md` | second Row 3 subcontract; states what an import must prove before CC20 endpoint terms can enter rank/pole/Cdef classification |
| `docs/audits/cc20-post-q-boundary-evaluation-source-decision-audit.md` | decision audit classifying the second Row 3 subcontract as project-proof-required rather than source-import-discharged |
| `docs/proofs/fixed-s-post-q-boundary-functional-transfer-theorem-contract.md` | project-proof contract for the second Row 3 subcontract; not a source import |
| `docs/proofs/fixed-s-post-q-boundary-functional-transfer-proof-package.md` | route-evidence proof package for the second Row 3 subcontract; still not a source import |
| `docs/proofs/cc20-post-q-series-tail-bounded-comparison-theorem-contract.md` | third Row 3 subcontract; states what an import must prove before CC20 source-tail convergence can become fixed-S graph/trace-norm convergence |
| `docs/audits/cc20-post-q-series-tail-source-decision-audit.md` | decision audit classifying the third Row 3 subcontract as project-proof-required rather than source-import-discharged |
| `docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-theorem-contract.md` | project-proof contract for the third Row 3 subcontract; not a source import |
| `docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-proof-package.md` | route-evidence proof package for the third Row 3 subcontract; still not a source import |
| `docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md` | combined Row 3 route-evidence package; still not a source import or sign/defect discharge |
| `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-theorem-contract.md` | Row 4 project-proof contract; not a source import |
| `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md` | Row 4 route-evidence proof package; still not a source import or sign/defect discharge |
| `docs/proofs/source-rank-pole-ledger-identification-theorem-contract.md` | Row 5 project-proof contract; not a source import |
| `docs/proofs/source-rank-pole-ledger-identification-proof-package.md` | Row 5 route-evidence proof package; still not a source import or sign/defect discharge |
| `docs/proofs/source-endpoint-strip-cdef-domination-theorem-contract.md` | Row 6 project-proof contract; not a source import |
| `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md` | Row 6 route-evidence proof package; still not a source import or sign/defect discharge |
| `docs/proofs/no-hidden-positive-defect-outside-cdef-theorem-contract.md` | Row 7 project-proof contract; not a source import |
| `docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md` | Row 7 route-evidence proof package; closes sign/defect only at project level |
| `docs/proofs/sonin-prolate-defect-referee-discharge.md` | referee-facing project proof package composing Rows 3-7; still not an accepted source import |
| `docs/audits/restricted-to-full-qw-source-readiness-audit.md` | finds a CCM25 restriction-definition path for fixed-test `QW_lambda=QW` after bridges |
| `docs/audits/sonin-prolate-defect-source-readiness-audit.md` | finds no direct source theorem for the fixed-S prolate/Sonin-to-`Cdef` bridge |
| arXiv:2511.22755 abstract | frames CCM25 as a strategy and numerical investigation; spectral convergence remains a proof target |
| arXiv:2006.13771 abstract | frames the Sonin/Weil difference as a term to control |

Primary source pages:

```text
https://arxiv.org/abs/2511.22755
https://arxiv.org/abs/2006.13771
```

## Evidence Classes

| class | meaning | route use |
|---|---|---|
| source definition | source paper defines notation or object | usable only after matching route objects |
| source theorem/formula | source paper proves or states a formula with hypotheses | candidate import |
| project proof package | this repository supplies a manuscript-level derivation | not an accepted import by itself |
| strategy/numerical claim | source paper describes a program, experiment, or expected convergence | not importable as theorem |
| unsupported interface | route names a theorem shape with no source theorem or project proof | blocker |

## CCM24 Imports

| interface | current source evidence | class | legitimacy judgment |
|---|---|---|---|
| canonical semilocal model | `mainc2m24fine.tex:237-253,786-804`; `docs/audits/source-reread-v0.2.md:37` | source definition/theorem candidate | import candidate, hypotheses still need audit |
| support and Fourier transport | `mainc2m24fine.tex:761-771,983-1003`; `docs/audits/source-reread-v0.2.md:38` | source theorem/formula candidate | import candidate, must match route window |
| bounded comparison | `mainc2m24fine.tex:806-823`; `docs/audits/source-reread-v0.2.md:39` | source theorem candidate | import candidate, trace-ideal preservation still separate |
| Sonin comparison | `mainc2m24fine.tex:1050-1060`; `docs/audits/source-reread-v0.2.md:40` | source theorem candidate | import candidate, cannot replace `Cdef -> 0` without fixed-test bridge |

CCM24 currently looks like the cleanest import family, but it does not discharge
the sign/defect problem by itself. It controls the model and windows. The route
still needs a theorem that the same window controls restricted `QW_lambda`,
finite-prime visibility, and endpoint-strip `Cdef`.

For Row 3 specifically, CCM24's positive import candidates stop at model,
window, Fourier, bounded-comparison, and Sonin-space transport. The warning at
`mainc2m24fine.tex:846-852` means derivative/domain compatibility, boundary
evaluation transport, and series-tail bounded-comparison transport remain
separate theorem targets.

The derivative/domain target is also not an importable CC20 theorem by itself:
CC20 states the archimedean bulk formula and its domain warning, but it does
not transport the `D_u xi_n` / `D_u zeta_n` graph terms through finite `S`.
The decision audit classifies this target as project-proof-required through a
future `FixedSPostQBulkGraphTransfer` bridge.
That bridge now has a project-proof contract; it does not change the source
import status.
The route-evidence proof package also does not change the source import
status. It is project evidence until formalized or externally certified.

The boundary-evaluation target is in the same category. CC20 states and
estimates the endpoint terms, but it does not transport their endpoint
functionals through the finite-S CCM24 model.
The decision audit classifies this target as project-proof-required through a
future `FixedSPostQBoundaryFunctionalTransfer` bridge.
That bridge now has a project-proof contract and a route-evidence proof
package. Neither changes the source import status.

The series-tail target is also in this category. CC20 gives a source-side
uniform scalar tail estimate, but it does not prove the fixed-S graph or
trace-norm tail preservation needed before route `Cdef` domination.
The decision audit classifies this target as project-proof-required through a
future `FixedSPostQSeriesTailBoundedComparison` bridge.
That bridge now has a project-proof contract and a route-evidence proof
package. Neither changes the source import status.

The combined Row 3 package closes fixed-S post-`Q` transport only at
route-evidence level. It does not discharge the source-import status because
accepted external certification or Lean proof remains absent.

Row 4 is also project evidence rather than source import. The project now has a
route-evidence package showing that the transported source remainder splits
into no-strip channels and endpoint-strip projection-defect normal forms, but
that package still needs formalization or external certification before it
counts as an accepted source discharge.

Row 5 remains in the same category. The project now has a route-evidence
package identifying the no-strip channels as `Rank_(S,I)` and
`PoleJetExtra_(S,I)`, but this is still project proof evidence until formalized
or externally certified.

Row 6 remains in the same category. The project now has a route-evidence
package matching endpoint-strip source-remainder terms to route `Cdef`
summands and fixed-test exhaustion, but this is still project proof evidence
until formalized or externally certified. It also does not supply the Row 7
exact read-off equality.

Row 7 remains in the same category. The project now has a route-evidence
package proving the exact positive-trace read-off equality and excluding a
hidden fourth defect. The referee-facing sign/defect package composes Rows 3
through 7 into one project proof chain, but this is still project proof
evidence until formalized or externally certified.

## CCM25 Imports

| interface | current source evidence | class | legitimacy judgment |
|---|---|---|---|
| `QW(f,g)=Psi(f^* * g)` and sign split | `mc2arXiv.tex:445-470`; `docs/audits/source-reread-v0.2.md:41` | source definition/formula candidate | import candidate, must preserve common test and signs |
| restricted `QW_lambda` formula | `mc2arXiv.tex:530-540`; `docs/audits/source-reread-v0.2.md:42` | source formula candidate | import candidate, finite-prime and pole normalizations remain visible obligations |
| finite-prime normalization | `mc2arXiv.tex:445-470,530-540`; `docs/audits/source-interface-discharge-completion-audit.md:62-66` | mixed source formula plus project proof packages | not discharged |
| pole normalization | `mc2arXiv.tex:465-470,533-535`; `docs/audits/source-interface-discharge-completion-audit.md:67` | source formula candidate | not discharged until matched to route pole ledger |
| spectral convergence to zeros | arXiv:2511.22755 abstract | strategy/numerical claim | not importable |
| determinant convergence toward Xi | arXiv:2511.22755 abstract | strategy/numerical claim | not importable |

CCM25 is the highest-risk import family.

The abstract of arXiv:2511.22755 says the work proposes and investigates a
strategy toward RH, reports numerical spectral convergence, and says a
rigorous proof of that convergence would establish RH. Those words do not give
the route a theorem that can be imported as:

```text
QW_lambda(g,g) -> QW(g,g)
```

or:

```text
finite spectral convergence holds unconditionally.
```

The fixed-test scalar exhaustion target is now:

```text
docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md
docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md
```

The route may import the displayed source formulae only after it audits their
hypotheses, signs, test object, pole convention, and finite-prime support.

## CC20 Imports

| interface | current source evidence | class | legitimacy judgment |
|---|---|---|---|
| archimedean support-square trace | `weil-compo.tex:378-387`; `docs/audits/source-reread-v0.2.md:43` | source theorem/formula candidate | import candidate, operator identity must match route object |
| trace-class template | `weil-compo.tex:448-464,2106-2121`; `docs/audits/source-reread-v0.2.md:44,48` | source theorem candidate | import candidate, per-move cyclicity still must be exposed |
| Mellin half-density convention | `weil-compo.tex:2014-2030`; `docs/audits/source-reread-v0.2.md:45` | source convention/formula | import candidate |
| finite-vanishing RH exit | `weil-compo.tex:2072-2085`; `docs/audits/source-reread-v0.2.md:46` | source theorem candidate | import candidate, Mathlib bridge remains separate |
| signs and normalizations | `weil-compo.tex:2131-2165`; `docs/audits/source-reread-v0.2.md:49` | source convention/formula | import candidate, must match CCM25 sign bridge |
| Weil distribution equals Sonin trace with harmless error | arXiv:2006.13771 abstract | not stated | not importable |

CC20 supplies the final criterion only if the route feeds it the same local
Weil inequality with the same sign and test object. The final sign bridge
therefore remains mandatory.

## Source-Line Reference Versus Import Legitimacy

The current `source-reread-v0.2.md` result is useful for locating source
material. It is not enough for import legitimacy.

```text
source line exists
        |
        v
object/formula located
        |
        v
hypotheses matched?
        |
        v
same test/sign/window?
        |
        v
accepted theorem or formal proof?
```

The route reaches the second box for many rows. It has not reached the last
box for any row; `docs/audits/source-interface-discharge-completion-audit.md:20-21`
says this directly.

## Non-Importable Claims

These claims must not enter the route as source imports:

| claim | reason |
|---|---|
| CCM25 spectral convergence of finite operators to zeta zeros | arXiv abstract frames it as numerical and says a rigorous proof would establish RH |
| determinant convergence toward Xi as an established theorem | arXiv abstract says the paper computes determinants and discusses their analytic role |
| harmless Sonin/prolate defect | CC20 abstract says the difference must be controlled |
| project proof-package labels such as `closed at route-paper level` | repository labels are not accepted source theorems |
| compact symbolic Lean fields | they test route composition only; they do not prove source analysis |

The route now has separate theorem contracts for the two most dangerous
non-importable shortcuts:

| shortcut | theorem contract that must replace it |
|---|---|
| harmless Sonin/prolate defect | `docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md`; `docs/audits/sonin-prolate-defect-discharge-ledger.md`; `docs/proofs/cc20-source-remainder-orientation-theorem-contract.md`; `docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md` |
| CCM25 spectral convergence as `QW_lambda -> QW` | `docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md`; `docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md` |
| CCM24 Sonin isomorphism as automatic post-`Q` transport | `docs/audits/ccm24-fixed-s-post-q-transport-obstruction-audit.md` |
| CC20 bulk `D_u` formula as automatic fixed-S graph transport | `docs/proofs/cc20-post-q-derivative-domain-compatibility-theorem-contract.md` |
| CC20 endpoint terms as automatic rank, pole, or Cdef ledgers | `docs/proofs/cc20-post-q-boundary-evaluation-transport-theorem-contract.md` |
| CC20 scalar tail convergence as automatic fixed-S Cdef-norm convergence | `docs/proofs/cc20-post-q-series-tail-bounded-comparison-theorem-contract.md` |

## Import Acceptance Checklist

An import row counts as legitimate only when it supplies:

| requirement | why it matters |
|---|---|
| exact theorem statement | prevents importing broad source context as a route theorem |
| exact hypotheses | blocks missing support, window, trace-class, or finite-prime assumptions |
| object identity bridge | proves source object equals route object |
| sign convention bridge | prevents inequality reversal |
| test identity bridge | prevents proving positivity for one test and feeding another to CC20 |
| limit order | separates fixed-test exhaustion from spectral convergence |
| proof status | distinguishes accepted theorem, project package, and numerical observation |

## Current Judgment

| source family | verdict |
|---|---|
| CCM24 | import candidates exist; hypotheses and route-object bridges remain open |
| CCM25 | formula candidates exist; `QW_lambda=QW` has an import-ready restriction-definition path after the bridge contract; spectral convergence and determinant convergence are not importable |
| CC20 | criterion and trace candidates exist; sign/test/Mathlib bridges remain open |

The current honest status is:

```text
source lines located;
proof-package coverage written;
accepted-source or Lean discharge still open.
```

The immediate source-import work should now attack accepted-source or Lean
discharge for the sign/defect contract, the restricted-to-full bridge, the
final sign bridge, and the RH definition bridge:

```text
docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md
docs/audits/sonin-prolate-defect-discharge-ledger.md
docs/proofs/cc20-source-remainder-orientation-theorem-contract.md
docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md
docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md
docs/proofs/source-endpoint-strip-cdef-domination-theorem-contract.md
docs/proofs/no-hidden-positive-defect-outside-cdef-theorem-contract.md
docs/proofs/sonin-prolate-defect-referee-discharge.md
docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md
docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md
docs/proofs/restricted-to-full-qw-bridge-proof-package.md
docs/proofs/final-sign-bridge-theorem-contract.md
docs/proofs/final-sign-bridge-proof-package.md
docs/proofs/rh-definition-bridge-theorem-contract.md
docs/proofs/rh-definition-bridge-proof-package.md
docs/proofs/source-conditional-rh-route-closure-proof-package.md
docs/audits/accepted-source-certification-audit.md
```

The route-level composition is now written, but source-import legitimacy still
requires accepted theorem status or formal proofs for the named source
interfaces. The route must not claim a completed RH proof until those source
imports pass this legitimacy audit and the sign/defect audit.
