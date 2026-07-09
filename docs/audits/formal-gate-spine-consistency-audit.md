# Formal Gate Spine Consistency Audit

Status: consistency audit for the remaining formal-gate spine packages.

This audit checks whether the spine packages can be read as one
Lean-facing source-discharge target. It does not certify RH. It checks that the
packages preserve the same objects, order of use, sign convention, and final RH
predicate before the next Lean or source-import phase.

## Result

Good result:

```text
The formal-gate spine packages form one coherent dependency chain.
```

Bad result for final certification:

```text
The chain remains proof-package evidence. No spine package is yet a formal Lean
theorem or an accepted imported theorem with audited hypotheses.
```

## Packages Checked

| gate | spine package | target |
|---|---|---|
| source object definitions | `docs/proofs/source-object-definition-spine-discharge.md`; `docs/proofs/source-object-definition-theorem-contract.md` | `SourceDefinitionSpine(S,I,lambda,g)`; `SourceDefinitionSpineContract(S,I,lambda,g)` |
| analytic trace legality | `docs/proofs/cc20-analytic-trace-legality-spine-discharge.md`; `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md` | `CC20AnalyticTraceLegalitySpine(S,I,lambda,g)`; `CC20AnalyticTraceLegalityContract(S,I,lambda,g)` |
| finite-prime normalization | `docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md`; `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` | `CCM25FinitePrimeNormalizationSpine(lambda,g)`; `CCM25FinitePrimeNormalizationContract(lambda,g)` |
| sign/defect read-off | `docs/audits/sign-defect-blocker-audit.md`; `docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md`; `docs/audits/sonin-prolate-defect-discharge-ledger.md`; `docs/proofs/cc20-source-remainder-orientation-theorem-contract.md`; `docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md` | `SoninProlateDefectEqualsEndpointStripCdef(S,I,lambda,g,J)` by the seven-row discharge ledger, with Row 3 split out as `CC20PostQRemainderFixedSSoninTransport(S,I,lambda,g,F_g)` |
| restricted-to-full exhaustion | `docs/audits/source-import-legitimacy-audit.md`; `docs/audits/restricted-to-full-qw-source-readiness-audit.md`; `docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md`; `docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md`; `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` | `RestrictedToFullQWBridgeContract(S,I,lambda,g,F_g,J) -> RestrictedToFullQWExhaustionContract(g)` |
| final sign bridge | `docs/proofs/final-sign-bridge-spine-discharge.md`; `docs/proofs/final-sign-bridge-theorem-contract.md`; `docs/proofs/final-sign-bridge-proof-package.md` | `FinalSignBridgeSpine(g)`; `FinalSignBridgeContract(g)` |
| RH definition bridge | `docs/proofs/rh-definition-bridge-spine-discharge.md`; `docs/proofs/rh-definition-bridge-theorem-contract.md`; `docs/proofs/rh-definition-bridge-proof-package.md` | `RHDefinitionBridgeSpine`; `RHDefinitionBridgeContract` |

## Dependency Shape

The packages have to compose in this order:

```text
SourceDefinitionSpineContract(S,I,lambda,g)
        |
        v
CC20AnalyticTraceLegalityContract(S,I,lambda,g)
        |
        v
CCM25FinitePrimeNormalizationContract(lambda,g)
        |
        v
SoninProlateDefectEqualsEndpointStripCdef(S,I,lambda,g,J)
        |
        v
RestrictedToFullQWExhaustionContract(g)
        |
        v
FinalSignBridgeContract(g)
        |
        v
RHDefinitionBridgeContract
        |
        v
SourceConditionalRHRouteClosure
        |
        v
_root_.RiemannHypothesis
```

The order matters. The source-definition spine fixes the objects. Trace
legality proves that the positive trace and trace moves are legal. Finite-prime
normalization fixes the arithmetic atoms before summation. The sign/defect
read-off proves that positive trace gives the restricted Weil lower bound with
only killed ledgers and endpoint-strip `Cdef`. The restricted-to-full
exhaustion theorem turns the restricted lower bound into full `QW`
nonnegativity without importing CCM25 spectral convergence. The sign bridge
translates the CCM25 positivity output into the CC20 inequality input. The RH
definition bridge transports the CC20 source conclusion to Mathlib's predicate.
The source-conditional closure package composes these gates at route-evidence
level and records that accepted-source and Lean discharge remain open.

## Cross-Spine Invariants

### Invariant 1. One Test Object

Required statement:

```text
The same source test g feeds CCM24 support, CCM25 F_g=g^* * g, CC20 trace,
CC20 Mellin vanishing, and the final sign bridge.
```

Evidence:

```text
docs/proofs/source-object-definition-spine-discharge.md
docs/proofs/cc20-analytic-trace-legality-spine-discharge.md
docs/proofs/final-sign-bridge-spine-discharge.md
```

Judgment:

```text
consistent at proof-package level.
```

Failure if broken:

```text
the route can prove positivity for one test, read off a Weil form for another,
and apply the RH exit to a third.
```

### Invariant 2. One Route Tuple And One Window

Required statement:

```text
The same tuple (S,I,lambda,g) controls the fixed-S trace, the CCM24 support
window, the restricted CCM25 form QW_lambda, and the finite-prime visibility
cut.
```

Evidence:

```text
docs/proofs/source-object-definition-spine-discharge.md
docs/proofs/cc20-analytic-trace-legality-spine-discharge.md
docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md
```

Judgment:

```text
consistent at proof-package level.
```

Failure if broken:

```text
the positive trace can use one support window while QW_lambda and the
finite-prime cut use another.
```

### Invariant 3. Trace Legality Comes Before Read-Off

Required chain:

```text
operator identity
  -> Hilbert-Schmidt
  -> trace-class
  -> per-move cyclicity
  -> ordinary positive trace
  -> support-square trace
  -> no-defect trace
  -> CCM25 read-off
```

Evidence:

```text
docs/proofs/cc20-analytic-trace-legality-spine-discharge.md
docs/proofs/source-object-definition-spine-discharge.md
```

Judgment:

```text
consistent at proof-package level.
```

Failure if broken:

```text
read-off can create trace legality instead of consuming trace legality.
```

### Invariant 4. Finite-Prime Atoms Precede Finite Sums

Required chain:

```text
source prime-power index n
  -> visibility in F_g
  -> restricted lambda cut 1 < n <= lambda^2
  -> Lambda(n)
  -> <g|T(n)g>
  -> pointwise finite-prime term equality
  -> global and restricted finite-prime sums
```

Evidence:

```text
docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md
docs/proofs/final-sign-bridge-spine-discharge.md
```

Judgment:

```text
consistent at proof-package level.
```

Failure if broken:

```text
sum equality can hide a wrong prime-power support set, weight, pairing, or
local sign.
```

### Invariant 5. Finite-Prime Sign Belongs To Psi And QW

Required statement:

```text
finite-prime atoms carry their source normalization first; the global sign of
their contribution belongs to the Psi/QW formula.
```

Evidence:

```text
docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md
docs/proofs/final-sign-bridge-spine-discharge.md
```

Judgment:

```text
consistent at proof-package level.
```

Failure if broken:

```text
a local atom can absorb the minus sign and flip the final inequality silently.
```

### Invariant 6. Equality Precedes Inequality Direction

Required statement:

```text
QW(g,g) = - sum_v W_v(F_g)
```

must be established before deriving:

```text
QW(g,g) >= 0
  ->
sum_v W_v(F_g) <= 0.
```

Evidence:

```text
docs/proofs/final-sign-bridge-spine-discharge.md
docs/proofs/cc20-analytic-trace-legality-spine-discharge.md
```

Judgment:

```text
consistent at proof-package level.
```

Failure if broken:

```text
the positive trace can feed CC20 Proposition C.1 with the wrong inequality
direction.
```

### Invariant 7. Source RH Transports To Mathlib RH

Required chain:

```text
source zeta
  -> Mathlib riemannZeta
  -> source zero
  -> riemannZeta s = 0
  -> negative-even exclusion
  -> s != 1 exclusion
  -> source critical line
  -> s.re = 1/2
  -> _root_.RiemannHypothesis
```

Evidence:

```text
docs/proofs/rh-definition-bridge-spine-discharge.md
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:166-169
```

Judgment:

```text
consistent at proof-package level.
```

Failure if broken:

```text
the route can prove a source-named RH while the final Lean theorem claims
Mathlib's canonical RH predicate.
```

## Lean Or Source-Import Gate

The next certification phase should encode or import these theorem targets
without collapsing them into opaque fields:

| target | blocked shortcut |
|---|---|
| `SourceDefinitionSpineContract(S,I,lambda,g)` | route-local source objects or a single `objectsCompatible : Prop` without the common test, fixed tuple, source window, source-object projections, and compact-record derivations |
| `CC20AnalyticTraceLegalityContract(S,I,lambda,g)` | `trace_eq_qw : Prop` without operator identity, trace-class square, and per-move cyclicity inputs |
| `CCM25FinitePrimeNormalizationContract(lambda,g)` | sum-level finite-prime equality without source prime-power indices, lambda cut, pointwise atom normalization, and sign ownership |
| `SoninProlateDefectEqualsEndpointStripCdef(S,I,lambda,g,J)` | treating the prolate/Sonin difference as harmless without proving it is rank, pole, or endpoint-strip `Cdef` |
| `CC20PostQRemainderFixedSSoninTransport(S,I,lambda,g,F_g)` | applying projection-defect normal form to route-local leftovers before proving the CC20 post-`Q` source remainder is in the same fixed-S model and window |
| `RestrictedToFullQWBridgeContract(S,I,lambda,g,F_g,J)` | importing CCM25 spectral convergence or determinant convergence instead of composing the restriction definition with common-test, support-window, and finite-prime support bridges |
| `FinalSignBridgeContract(g)` | using `QW(g,g) >= 0` as CC20 nonpositivity without common-test equality, source sign expansion, `QW=-sum_v W_v`, and inequality-direction theorem |
| `RHDefinitionBridgeContract` | treating source RH as Mathlib RH by name without zeta equality, zero transport, exclusions, source non-trivial-zero construction, and critical-line equivalence |

## Current Judgment

| question | answer |
|---|---|
| Do the spine packages share one `g` and one `F_g=g^* * g`? | yes |
| Do they share one `(S,I,lambda)` tuple and CCM24 support window? | yes |
| Does trace legality precede positive trace, cyclicity, and read-off? | yes |
| Do finite-prime pointwise terms precede finite-prime sums? | yes |
| Does sign/defect read-off block uncontrolled prolate/Sonin defect? | theorem contracts added through Row 3; not discharged |
| Does restricted-to-full exhaustion avoid importing spectral convergence? | source-definition path found; route-evidence bridge written; accepted-source and Lean discharge still open |
| Does final sign bridge expose the inequality direction? | route-evidence package written; accepted-source and Lean discharge still open |
| Does RH definition bridge target Mathlib RH exactly? | route-evidence package written; accepted-source and Lean discharge still open |
| Does the final sign bridge expose equality before inequality direction? | yes |
| Does the RH bridge target Mathlib's `_root_.RiemannHypothesis` through its definition? | yes |
| Does this prove RH as a formal theorem or accepted source import? | no |

The formal gates now have one consistency-checked spine target. The next
phase may encode these gates in Lean or discharge them by accepted imports, but
it must keep the named bridges visible.

For the source-object definition gate, the stronger theorem contract is:

```text
docs/proofs/source-object-definition-theorem-contract.md
```

It fixes the formal/import targets for the common source test and convolution
square, one fixed `(S,I,lambda,g)` route tuple, the CCM24 window controlling the
restricted route, CCM25 Weil objects, CC20 trace objects, CC20 RH-exit objects,
and derivations of the compact records consumed by the current route.

The discharge ledger for those targets is:

```text
docs/audits/source-object-theorem-discharge-ledger.md
```

It records the proof or import evidence required before
`SourceDefinitionSpineContract` can count as discharged.

Rows 1 and 2 of that ledger now have a stronger theorem contract:

```text
docs/proofs/source-common-test-tuple-theorem-contract.md
```

It fixes the common-test, convolution-square, fixed-tuple, and tuple-to-window
ownership targets before Row 3 through Row 7 consume those objects.

For the analytic trace-legality gate, the stronger theorem contract is:

```text
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md
```

It fixes the formal/import targets that must replace the proof-package spine
before the trace-legality gate can count as discharged.

For the finite-prime normalization gate, the stronger theorem contract is:

```text
docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md
```

It fixes the formal/import targets for prime-power indices, global support,
restricted lambda cut, visibility, `Lambda(n)`, `<g|T(n)g>`, pointwise term
normalization, and finite-prime sign ownership.

For the final sign bridge gate, the stronger theorem contract is:

```text
docs/proofs/final-sign-bridge-theorem-contract.md
```

It fixes the formal/import targets for common source test, `Psi` sign
expansion, archimedean sign bridge, finite-prime sign ownership, source pole
sign in the CC20 local sum, `QW(g,g)=-sum_v W_v(F_g)`, and the final
inequality direction.

For the RH definition bridge gate, the stronger theorem contract is:

```text
docs/proofs/rh-definition-bridge-theorem-contract.md
```

It fixes the formal/import targets for source zeta equality with Mathlib
`riemannZeta`, zero transport, negative-even exclusion, pole exclusion,
construction of the source non-trivial-zero witness from Mathlib hypotheses,
critical-line equivalence, and the forward source-RH-to-Mathlib-RH theorem.
