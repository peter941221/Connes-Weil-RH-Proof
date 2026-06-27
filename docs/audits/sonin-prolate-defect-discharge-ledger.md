# Sonin Prolate Defect Discharge Ledger

Status: discharge ledger for the sign/defect hard blocker.

This ledger refines:

```text
docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md
```

from one large theorem target into row-by-row acceptance criteria. It now
records route-evidence closure for Rows 3 through 7, but it does not discharge
the target at accepted-source, referee-proof, or Lean-theorem strength. Those
stronger layers remain required before the positive trace can be used as a
certified Weil-positivity input.

## Result

Good result:

```text
The sign/defect blocker now has a row-by-row discharge ledger.
```

Bad result for final certification:

```text
No row below is yet discharged by a Lean theorem or by an accepted imported
source theorem with audited hypotheses.
```

The current status remains:

```text
route-evidence bridge written;
accepted-source and Lean discharge not yet supplied.
```

## Source And Route Inputs

| input | current evidence | status |
|---|---|---|
| CC20 local prolate/Sonin remainder | `docs/audits/sonin-prolate-defect-source-readiness-audit.md:26-32` | source ingredient located |
| CCM24 fixed-window Sonin comparison | `docs/audits/sonin-prolate-defect-source-readiness-audit.md:33` | source ingredient located |
| fixed-S support-square transport package | `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md` | route-evidence only |
| endpoint-strip `Cdef` norm and exhaustion | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md`; `docs/proofs/fixed-test-graph-cdef-exhaustion.md` | route-evidence only |
| projection-defect `Q` stability | `docs/proofs/semilocal-q-compact-form.md` | route-evidence only |
| CC20 source remainder orientation | `docs/proofs/cc20-source-remainder-orientation-theorem-contract.md` | theorem contract added |
| CC20 post-`Q` fixed-S transport | `docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md` | Row 3 theorem contract added |
| CC20 post-`Q` item map | `docs/audits/cc20-post-q-remainder-term-map.md` | Row 3 term map added |
| CCM24 post-`Q` transport obstruction | `docs/audits/ccm24-fixed-s-post-q-transport-obstruction-audit.md` | Row 3 split into derivative/domain, boundary, and tail subcontracts |
| CC20 post-`Q` derivative/domain subcontract | `docs/proofs/cc20-post-q-derivative-domain-compatibility-theorem-contract.md` | first Row 3 subcontract stated |
| fixed-S post-`Q` bulk graph transfer | `docs/proofs/fixed-s-post-q-bulk-graph-transfer-theorem-contract.md` | project-proof target for the first Row 3 subcontract |
| fixed-S post-`Q` bulk graph transfer proof package | `docs/proofs/fixed-s-post-q-bulk-graph-transfer-proof-package.md` | first Row 3 subcontract closed at route-evidence level only |
| CC20 post-`Q` boundary-evaluation subcontract | `docs/proofs/cc20-post-q-boundary-evaluation-transport-theorem-contract.md` | second Row 3 subcontract stated |
| CC20 post-`Q` boundary-evaluation source decision | `docs/audits/cc20-post-q-boundary-evaluation-source-decision-audit.md` | second Row 3 subcontract classified as project-proof-required |
| fixed-S post-`Q` boundary functional transfer | `docs/proofs/fixed-s-post-q-boundary-functional-transfer-theorem-contract.md` | project-proof target for the second Row 3 subcontract |
| fixed-S post-`Q` boundary functional transfer proof package | `docs/proofs/fixed-s-post-q-boundary-functional-transfer-proof-package.md` | second Row 3 subcontract closed at route-evidence level only |
| CC20 post-`Q` series-tail subcontract | `docs/proofs/cc20-post-q-series-tail-bounded-comparison-theorem-contract.md` | third Row 3 subcontract stated |
| CC20 post-`Q` series-tail source decision | `docs/audits/cc20-post-q-series-tail-source-decision-audit.md` | third Row 3 subcontract classified as project-proof-required |
| fixed-S post-`Q` series-tail bounded comparison | `docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-theorem-contract.md` | project-proof target for the third Row 3 subcontract |
| fixed-S post-`Q` series-tail bounded comparison proof package | `docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-proof-package.md` | third Row 3 subcontract closed at route-evidence level only |
| CC20 post-`Q` remainder fixed-S transport proof package | `docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md` | Row 3 closed at route-evidence level only |
| fixed-S source-remainder projection-defect normal-form contract | `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-theorem-contract.md` | Row 4 project-proof target |
| fixed-S source-remainder projection-defect normal-form proof package | `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md` | Row 4 closed at route-evidence level only |
| source rank/pole ledger identification contract | `docs/proofs/source-rank-pole-ledger-identification-theorem-contract.md` | Row 5 project-proof target |
| source rank/pole ledger identification proof package | `docs/proofs/source-rank-pole-ledger-identification-proof-package.md` | Row 5 closed at route-evidence level only |
| source endpoint-strip Cdef domination contract | `docs/proofs/source-endpoint-strip-cdef-domination-theorem-contract.md` | Row 6 project-proof target |
| source endpoint-strip Cdef domination proof package | `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md` | Row 6 closed at route-evidence level only |
| no hidden positive defect contract | `docs/proofs/no-hidden-positive-defect-outside-cdef-theorem-contract.md` | Row 7 project-proof target |
| no hidden positive defect proof package | `docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md` | Row 7 closed at route-evidence level only |

These inputs are useful, but they do not by themselves prove the sign/defect
bridge. The missing theorem must identify the source remainder object with the
route's rank, pole, and endpoint-strip `Cdef` ledger.

## Contract Dependency Graph

```text
CC20 source prolate/Sonin remainder
        |
        +-- source object and sign
        |
        +-- Q trace-remainder image
        |
        v
CCM24 fixed-S Sonin transport
        |
        v
fixed-S canonical projection normal form
        |
        +-- no-strip rank/pole channels
        |
        +-- endpoint-strip projection defects
        |
        v
Cdef trace-norm domination and exhaustion
        |
        v
NoHiddenPositiveDefectOutsideCdef
        |
        v
PositiveTrace = QW_lambda + killed ledgers + Cdef remainder
```

Every arrow must be theorem-backed. A route note saying "the defect is small"
does not satisfy any row.

## Row 1. Source Remainder Object And Orientation

Target:

```text
CC20SourceProlateRemainderObject(f):
  identify the exact source term by which the positive Sonin trace differs
  from W_infty, including its sign and test convention.
```

Acceptance evidence:

| component | required evidence |
|---|---|
| source object | exact CC20 remainder term, not a project-defined placeholder |
| sign orientation | theorem states whether the source formula is `L = W_infty + error`, `W_infty = L - error`, or another convention |
| test convention | the source test is the same half-density/convolution object used downstream |
| positivity boundary | the row does not infer Weil positivity from `L >= 0` |

Current repository evidence:

```text
docs/audits/sonin-prolate-defect-source-readiness-audit.md:26-31
docs/proofs/cc20-source-remainder-orientation-theorem-contract.md
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md
docs/proofs/final-sign-bridge-theorem-contract.md
```

Reject:

```text
SoninTrace is positive, therefore W_infty is positive.
```

Current status:

```text
source orientation contract added; exact object bridge not discharged.
```

## Row 2. Q Image Of The Source Remainder

Target:

```text
CC20SourceRemainderAfterQ(f):
  after the CC20 Q trace-remainder operation and the finite vanishing
  conditions, the source prolate/Sonin remainder has a named image with a
  theorem-level formula.
```

Acceptance evidence:

| component | required evidence |
|---|---|
| `Q` domain | trace-class or source-regularized legality before applying `Q` |
| formula after `Q` | theorem states the resulting bulk and boundary terms |
| finite vanishing interface | no use of triple vanishing before the terms it kills are identified |
| no global negativity shortcut | no assumption that `D circ Q` or `E circ Q` is globally nonpositive |

Current repository evidence:

```text
docs/audits/sonin-prolate-defect-source-readiness-audit.md:28-32
docs/proofs/cc20-source-remainder-orientation-theorem-contract.md
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md
docs/proofs/semilocal-q-compact-form.md
```

Reject:

```text
Q makes the error harmless.
```

without a displayed theorem for the `Q` image.

Current status:

```text
source post-Q orientation contract added; source-to-route Q image not discharged.
```

## Row 3. Fixed-S Sonin Transport

Target:

```text
CCM24FixedSSoninTransport(S,I,lambda,g):
  transport the source Sonin/prolate remainder through the CCM24 fixed-S
  model using the same test, same support window, and same lambda parameter.
```

Acceptance evidence:

| component | required evidence |
|---|---|
| same test | the transported object consumes the common source `g` and `F_g=g^* * g` |
| same window | the CCM24 support window is the one used by `QW_lambda` and `Cdef` |
| same Sonin space | the source Sonin comparison applies to the exact fixed-S space used by the positive trace |
| bounded comparison | the transport preserves the trace/norm class after trace-legality inputs are supplied |

Current repository evidence:

```text
docs/proofs/source-common-test-tuple-theorem-contract.md
docs/proofs/source-object-definition-theorem-contract.md
docs/proofs/ccm24-support-window-transport-discharge.md
docs/proofs/ccm24-semilocal-object-normalization-discharge.md
docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md
docs/audits/cc20-post-q-remainder-term-map.md
```

Reject:

```text
CCM24 has a Sonin isomorphism, so the route defect is the source defect.
```

unless the same test/window/trace class is carried through.

Current status:

```text
formal/import target stated; not discharged.
```

The `E circ Q` side is now itemized into:

```text
bulk integral term,
moving lower-boundary term,
fixed upper-boundary term,
series tail.
```

This itemization is useful evidence for Row 3, but it is not the fixed-S
transport theorem.

The CCM24 fast pass adds a hard caution: the source supports the common
fixed-S model and Sonin comparison, but `mainc2m24fine.tex:846-852` blocks the
naive inference that the semilocal Hermite, derivative, multiplication, and
boundary structures commute with the archimedean ones. Row 3 must therefore
prove:

```text
PostQDerivativeDomainCompatibility
PostQBoundaryEvaluationTransport
PostQSeriesTailBoundedComparison
```

before Row 4 can classify transported source terms by projection-defect normal
form.

The first of these is now stated as a theorem contract. It is required because
CC20 says at `weil-compo.tex:1260-1264` that the formal `D_u` identity cannot
be applied directly to `xi_n,zeta_n`; the source formula is obtained only
after explicit boundary repair.

The second is now stated as a theorem contract. It keeps the lower moving
endpoint and upper fixed endpoint terms source-owned until Row 5/6 decide
rank, pole, or endpoint-strip `Cdef`.

The third is now stated as a theorem contract. It keeps the CC20 source
tail estimate separate from fixed-S graph/trace-norm convergence until a
bounded-comparison theorem supplies that bridge.

The first subcontract now has a route-evidence proof package through
`FixedSPostQBulkGraphTransfer`.

The second subcontract now has a route-evidence proof package through
`FixedSPostQBoundaryFunctionalTransfer`.

The third subcontract now has a route-evidence proof package through
`FixedSPostQSeriesTailBoundedComparison`.

The combined Row 3 route-evidence package now proves
`CC20PostQRemainderFixedSSoninTransport` at route-evidence level. Rows 4
through 6 now also have route-evidence packages. The active sign/defect work is
therefore Row 7, the exact equality excluding a hidden fourth positive defect.

## Row 4. Fixed-S Projection Defect Normal Form

Target:

```text
FixedSProjectionDefectNormalFormForSourceRemainder(S,I,lambda,g,J):
  every fixed-S transport defect in the source remainder contains one of

    [P,M_S], [P_hat,M_S], [P,M_S^*], [P_hat,M_S^*]

  and therefore has endpoint-strip normal form.
```

Acceptance evidence:

| component | required evidence |
|---|---|
| common coordinate | all commutators are formed after moving to the same fixed-S canonical coordinate |
| exhaustive expansion | every non-no-strip transport term contains a listed commutator |
| endpoint-strip support | each commutator expands into finite endpoint-strip shifted kernels |
| source remainder ownership | the terms being classified are the source remainder terms from Rows 1 and 2, not only route-local leftovers |

Current repository evidence:

```text
docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:131-271
docs/proofs/semilocal-q-compact-form.md:150-217
docs/proofs/battle-3-cdef-exhaustion-proof-package.md:61-189
docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-theorem-contract.md
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md
```

Reject:

```text
the same quantized-calculus expansion applies.
```

This phrase is a proof obligation, not evidence.

Current status:

```text
closed at route-evidence level for the transported source remainder;
not a Lean theorem or accepted source import.
```

## Row 5. Rank And Pole Ledger Identification

Target:

```text
SourceRankPoleLedgerIdentification(S,I,g):
  every no-strip term in the transported source remainder is exactly one of:
    Rank_(S,I)(g),
    PoleJetExtra_(S,I)(g),
  with the same evaluation points killed by triple vanishing.
```

Acceptance evidence:

| component | required evidence |
|---|---|
| rank object | no-strip rank term is a scalar multiple of `|hat g(0)|^2` |
| pole object | no-strip pole terms are only the Tate evaluations at `+i/2` and `-i/2` |
| CCM25 pole separation | route `PoleJetExtra` is not confused with the CCM25 pole term already inside `QW_lambda` |
| vanishing order | triple vanishing is applied only after the ledgers are identified |

Current repository evidence:

```text
docs/proofs/battle-1-test-quotient-proof-package.md
docs/proofs/rank-repair-finite-normal-form.md
docs/proofs/ccm25-restricted-read-off-discharge.md
docs/proofs/final-sign-bridge-theorem-contract.md
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md
docs/proofs/source-rank-pole-ledger-identification-theorem-contract.md
docs/proofs/source-rank-pole-ledger-identification-proof-package.md
```

Reject:

```text
triple vanishing kills the remainder.
```

before the remainder is identified as rank or pole.

Current status:

```text
closed at route-evidence level for the transported source remainder;
not a Lean theorem or accepted source import.
```

## Row 6. Endpoint-Strip Cdef Domination

Target:

```text
SourceEndpointStripRemainderCdefDomination(S,I,lambda,g,J):
  every transported source remainder term that is not rank or pole is an
  endpoint-strip term and satisfies the route `Cdef` trace-norm bound.
```

Acceptance evidence:

| component | required evidence |
|---|---|
| normal form | every non-ledger term has endpoint-strip factor before boundary evaluation |
| trace ideal | theta-smoothed terms are trace-class before cyclicity or read-off |
| `Q` stability | applying CC20 `Q` preserves the endpoint-strip factor modulo rank/pole ledgers |
| norm equality | the exact terms appear as summands in route `Cdef_(S,I,lambda,J)(g)` |
| fixed-test exhaustion | after `S_A`, `I`, `g`, and graph order are fixed, `Cdef -> 0` |

Current repository evidence:

```text
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md
docs/proofs/source-rank-pole-ledger-identification-proof-package.md
docs/proofs/battle-3-cdef-exhaustion-proof-package.md
docs/proofs/fixed-test-graph-cdef-exhaustion.md
docs/proofs/semilocal-q-compact-form.md
docs/proofs/source-endpoint-strip-cdef-domination-theorem-contract.md
docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md
```

Reject:

```text
compact remainder
small prolate error
controlled defect
```

unless the displayed trace-norm `Cdef` bound is proved.

Current status:

```text
closed at route-evidence level for the transported source remainder;
not a Lean theorem, accepted source import, or final read-off equality.
```

## Row 7. No Hidden Positive Defect Outside Cdef

Target:

```text
NoHiddenPositiveDefectOutsideCdef(S,I,lambda,g,J):
  PositiveTrace^G_(S,lambda)(g)
    =
  QW_lambda(g,g)
    +
  Rank_(S,I)(g)
    +
  PoleJetExtra_(S,I)(g)
    +
  R_(S,I,lambda,J)(g),

  |R_(S,I,lambda,J)(g)|
    <= C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Acceptance evidence:

| component | required evidence |
|---|---|
| equality | exact read-off equality, not only inequality |
| exhaustive remainder split | no fourth defect class remains |
| sign consequence | positive trace gives only `QW_lambda >= -Cdef` after ledgers vanish |
| source import legitimacy | every imported source item is a theorem/formula candidate, not strategy or numerical convergence |

Current repository evidence:

```text
docs/audits/sign-defect-blocker-audit.md
docs/audits/source-import-legitimacy-audit.md
docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md
docs/proofs/no-hidden-positive-defect-outside-cdef-theorem-contract.md
docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md
```

Reject:

```text
Tr(A^*A) >= 0
therefore
QW_lambda(g,g) >= 0.
```

Current status:

```text
closed at route-evidence level;
not a Lean theorem, accepted source import, restricted-to-full bridge, or RH.
```

## Discharge Order

The fastest honest attack order is:

```text
1. Row 1: source remainder object and sign
2. Row 2: source remainder after Q
3. Row 3: same fixed-S Sonin transport
4. Row 4: projection-defect normal form for the source remainder
5. Row 5: no-strip rank/pole identification
6. Row 6: endpoint-strip Cdef domination
7. Row 7: no hidden positive defect
```

Rows 3 through 7 now have route-evidence packages. The remaining risk is
certification strength: Rows 1 and 2 still enter as source-orientation
contracts, Row 3 is project evidence rather than accepted import, and Row 7
has not been formalized. If a later source import or Lean proof identifies an
extra source remainder term, the branch fails or needs a new defect class.

## Current Judgment

| question | answer |
|---|---|
| Does this ledger prove the sign/defect bridge at route-evidence level? | yes |
| Does this ledger prove the sign/defect bridge at accepted-source or Lean level? | no |
| Does it identify the exact rows needed to prove it? | yes |
| Which rows are source-risk rows? | Rows 1, 2, and 3; Rows 1 and 2 have a source-orientation contract, and Row 3 has a route-evidence fixed-S transport package but no accepted proof/import discharge |
| Which rows have route-evidence packages? | Rows 3, 4, 5, 6, and 7 |
| Which row decides the hostile objection? | Row 7, now closed at route-evidence level only |
| Can the route treat `SoninProlateDefectEqualsEndpointStripCdef` as accepted-source or Lean discharged? | no |

The next mathematical pass should attack the post-Row-7 gates:
restricted-to-full `QW_lambda -> QW` for the same source object, accepted
source-import legitimacy for the sign/defect bridge, and the final CC20 sign
exit. Row 7 now answers the hostile hidden-defect objection only at
route-evidence level.
