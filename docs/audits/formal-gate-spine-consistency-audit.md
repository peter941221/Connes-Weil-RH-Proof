# Formal Gate Spine Consistency Audit

Status: consistency audit for the five remaining formal-gate spine packages.

This audit checks whether the five spine packages can be read as one
Lean-facing source-discharge target. It does not certify RH. It checks that the
packages preserve the same objects, order of use, sign convention, and final RH
predicate before the next Lean or source-import phase.

## Result

Good result:

```text
The five formal-gate spine packages form one coherent dependency chain.
```

Bad result for final certification:

```text
The chain remains proof-package evidence. No spine package is yet a formal Lean
theorem or an accepted imported theorem with audited hypotheses.
```

## Packages Checked

| gate | spine package | target |
|---|---|---|
| source object definitions | `docs/proofs/source-object-definition-spine-discharge.md` | `SourceDefinitionSpine(S,I,lambda,g)` |
| analytic trace legality | `docs/proofs/cc20-analytic-trace-legality-spine-discharge.md` | `CC20AnalyticTraceLegalitySpine(S,I,lambda,g)` |
| finite-prime normalization | `docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md` | `CCM25FinitePrimeNormalizationSpine(lambda,g)` |
| final sign bridge | `docs/proofs/final-sign-bridge-spine-discharge.md` | `FinalSignBridgeSpine(g)` |
| RH definition bridge | `docs/proofs/rh-definition-bridge-spine-discharge.md` | `RHDefinitionBridgeSpine` |

## Dependency Shape

The packages have to compose in this order:

```text
SourceDefinitionSpine(S,I,lambda,g)
        |
        v
CC20AnalyticTraceLegalitySpine(S,I,lambda,g)
        |
        v
CCM25FinitePrimeNormalizationSpine(lambda,g)
        |
        v
FinalSignBridgeSpine(g)
        |
        v
RHDefinitionBridgeSpine
        |
        v
_root_.RiemannHypothesis
```

The order matters. The source-definition spine fixes the objects. Trace
legality proves that the positive trace and trace moves are legal. Finite-prime
normalization fixes the arithmetic atoms before summation. The sign bridge
translates the CCM25 positivity output into the CC20 inequality input. The RH
definition bridge transports the CC20 source conclusion to Mathlib's predicate.

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
| `SourceDefinitionSpine(S,I,lambda,g)` | route-local source objects or a single `objectsCompatible : Prop` |
| `CC20AnalyticTraceLegalitySpine(S,I,lambda,g)` | `trace_eq_qw : Prop` without trace-class and cyclicity inputs |
| `CCM25FinitePrimeNormalizationSpine(lambda,g)` | sum-level finite-prime equality without pointwise atom normalization |
| `FinalSignBridgeSpine(g)` | using `QW(g,g) >= 0` as CC20 nonpositivity without the sign equality |
| `RHDefinitionBridgeSpine` | treating source RH as Mathlib RH by name |

## Current Judgment

| question | answer |
|---|---|
| Do the five spine packages share one `g` and one `F_g=g^* * g`? | yes |
| Do they share one `(S,I,lambda)` tuple and CCM24 support window? | yes |
| Does trace legality precede positive trace, cyclicity, and read-off? | yes |
| Do finite-prime pointwise terms precede finite-prime sums? | yes |
| Does the final sign bridge expose equality before inequality direction? | yes |
| Does the RH bridge target Mathlib's `_root_.RiemannHypothesis` through its definition? | yes |
| Does this prove RH as a formal theorem or accepted source import? | no |

The five formal gates now have one consistency-checked spine target. The next
phase may encode these gates in Lean or discharge them by accepted imports, but
it must keep the named bridges visible.
