# Source Object Definition Spine Discharge

Status: proof package for the source-object definition spine.

This package attacks the first remaining formal gate from:

```text
docs/audits/source-interface-discharge-completion-audit.md
```

The gate is:

```text
source object definitions
```

The package does not define the analytic CCM24, CCM25, or CC20 objects in Lean.
It records the mathematical spine that a later Lean or source-import pass must
make explicit before the route can treat source objects as discharged.

## Evidence Boundary

| object | evidence |
|---|---|
| source-object definition ledger | `docs/audits/source-object-definition-ledger.md` |
| common test and convolution square | `docs/proofs/source-test-convolution-compatibility.md` |
| CCM24 semilocal object package | `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` |
| CCM25 global definition and sign package | `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md` |
| CCM25 restricted window package | `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md` |
| CCM25 finite-prime object package | `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md` |
| CC20 trace object package | `docs/proofs/cc20-trace-object-normalization-discharge.md` |
| CC20 RH exit object package | `docs/proofs/cc20-rh-exit-object-normalization-discharge.md` |
| sign bridge | `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md` |
| Mathlib RH bridge | `docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md` |

## Target Statement

The source-object definition pass must expose one package:

```text
SourceDefinitionSpine(S,I,lambda,g)
```

with these source-owned components:

```text
common source test g
source convolution square F_g = g^* * g
CCM24 fixed-S place set S and support window I
CCM25 QW, Psi, QW_lambda, prime-power support, Lambda(n), and <g|T(n)g>
CC20 trace test, support-square trace, no-defect trace, and Weil sum
CC20 finite set F={0,1/2,1}
CC20 source zeta and source non-trivial-zero predicate
Mathlib RH target predicate
```

The route may derive compact objects from this spine. The route must not supply
the same names as independent route-local fields.

The dependency shape is:

```text
                         SourceDefinitionSpine(S,I,lambda,g)
                                      |
        +-----------------------------+-----------------------------+
        |                             |                             |
        v                             v                             v
 CCM24 support window          CCM25 Weil objects             CC20 trace objects
        |                             |                             |
        +-------------+---------------+---------------+-------------+
                      |                               |
                      v                               v
              finite-prime read-off           CC20 Weil inequality
                      |                               |
                      +---------------+---------------+
                                      |
                                      v
                         CC20 Proposition C.1
                                      |
                                      v
                         Mathlib _root_.RiemannHypothesis
```

## Lemma 1. The Spine Fixes The Route Tuple

Statement:

```text
SourceDefinitionSpineTuple(S,I,lambda,g):
  every CCM24, CCM25, and CC20 source object used by the route is indexed by
  the same tuple (S,I,lambda,g).
```

Proof.

The common-test package fixes `g` and:

```text
F_g = g^* * g.
```

The CCM24 package fixes the finite place set `S`, the support window `I`, and
the support/Fourier/convolution transport for the same test. The CCM25
restricted package uses the same `lambda` and the same window containment
before it reads `QW_lambda`. The CC20 trace and exit packages use the same
test through the half-density and Mellin conventions.

Therefore the tuple must be a field of the source-definition spine. A later
formal interface may expose projections, but the projections must not allocate
new independent tests, windows, or lambda parameters.

Failure blocked:

```text
CCM24 proves support for one test, CCM25 reads finite primes for a second
test, and CC20 applies Proposition C.1 to a third test.
```

## Lemma 2. The Spine Owns The Weil Object

Statement:

```text
SourceDefinitionSpineWeilObject(S,I,lambda,g):
  the global CCM25 QW, restricted QW_lambda, finite-prime terms, pole terms,
  and CC20 Weil sum all evaluate the same F_g.
```

Proof.

The CCM25 full definition package supplies:

```text
QW(g,g) = Psi(F_g).
```

The restricted package supplies:

```text
QW_lambda(g,g)
```

through the same source window and the same prime-power support cut. The
finite-prime package keeps the pointwise atom:

```text
finitePrimeTerm n F_g = Lambda(n)<g|T(n)g>
```

for each source prime-power index `n`.

The final sign bridge identifies the route positivity form with the CC20 Weil
sum only through:

```text
QW(g,g) = - sum_v W_v(F_g).
```

Thus the source-definition spine must own the common `F_g`, the CCM25 Weil
objects, and the CC20 Weil sum. A compact `FullWeilPositivity` proposition can
only be a derived view.

Failure blocked:

```text
QW(g,g) >= 0 is proved for a CCM25-looking form while Proposition C.1 receives
a different CC20 Weil sum.
```

## Lemma 3. The Spine Owns The Restricted Window

Statement:

```text
SourceDefinitionSpineRestrictedWindow(S,I,lambda,g):
  the support window I controls CCM24 transport, CCM25 QW_lambda, finite-prime
  visibility, and fixed-window Cdef exhaustion.
```

Proof.

The CCM24 package supplies one source support window and proves support,
Fourier-support, and convolution-support transport for the source test. The
restricted CCM25 package consumes the same window before applying the lambda
cut. The finite-prime package then uses:

```text
1 < n <= lambda^2
```

for restricted source prime-power support. The Cdef exhaustion package keeps
the test, finite set, graph order, and window fixed before the exhaustion
limit.

Therefore the source-definition spine must store one window leg:

```text
I subset [lambda^-1, lambda].
```

Every downstream compact record must project from that leg.

Failure blocked:

```text
the positive trace can use one cutoff, QW_lambda another, and Cdef exhaustion
a third.
```

## Lemma 4. The Spine Owns Trace Legality Before Read-Off

Statement:

```text
SourceDefinitionSpineTraceLegality(S,I,lambda,g):
  the CC20 support-square trace, no-defect trace, positive trace, and cyclic
  trace moves are source objects tied to F_g after trace legality has been
  proved.
```

Proof.

The CC20 trace package separates these stages:

```text
Hilbert-Schmidt gate
  -> trace-class and cyclicity
  -> positive trace Tr(A^*A)
  -> support-square trace
  -> no-defect source trace
```

The read-off package then identifies the no-defect source trace with the CCM25
Weil form. The spine must therefore place trace legality before the read-off
equality. If the package exposes only a scalar equality, the route can use
cyclicity before the operator belongs to the trace ideal.

Failure blocked:

```text
positivity or cyclicity is applied to an operator before the CC20 trace-class
gate has fired.
```

## Lemma 5. The Spine Owns The RH Exit Predicate

Statement:

```text
SourceDefinitionSpineRHExit(S,I,lambda,g):
  the CC20 finite-vanishing criterion and the Mathlib RH conclusion use the
  same zeta function, zero predicate, exclusions, and critical-line equation.
```

Proof.

The CC20 RH exit package fixes:

```text
F={0,1/2,1}
```

and translates route triple vanishing into CC20 Mellin vanishing on that finite
set. The same package feeds route full Weil positivity into CC20 Proposition
C.1 only after the sign bridge has converted `QW(g,g) >= 0` into the CC20
nonpositivity hypothesis.

The RH-definition bridge then transports the CC20 source conclusion to:

```text
_root_.RiemannHypothesis.
```

through the same zeta function, non-trivial-zero predicate, negative-even
trivial-zero exclusion, pole exclusion at `s=1`, and critical-line equation
`s.re = 1/2`.

Failure blocked:

```text
the route proves a source-named RH while the final theorem claims Mathlib RH.
```

## Combined Result

Combining Lemmas 1 through 5 gives:

```text
SourceObjectDefinitionsDischargedAtPackageLevel:
  SourceDefinitionSpine(S,I,lambda,g)
    ->
  the current compact source records are projections from one source object
  spine.
```

This closes the `source object definitions` gate only at proof-package level.
It supplies the exact mathematical shape that a Lean or source-import pass must
encode.

The package strengthens the earlier ledger result:

```text
individual source-object rows are named
```

to:

```text
the rows share one source-definition spine.
```

## Formalization Consequence

A later interface pass should introduce:

```text
CommonTestObject
CCM24SemilocalObjectPackage
CCM25WeilObjectPackage
CC20TraceObjectPackage
CC20RHExitObjectPackage
SourceObjectPackage
```

and prove projections:

```text
SourceObjectPackage -> SemilocalModelSymbols
SourceObjectPackage -> WeilFormSymbols
SourceObjectPackage -> ArchimedeanTraceSymbols
SourceObjectPackage -> FiniteVanishingCriterionPackage
```

Those projections should consume this spine, not reconstruct the compact
records from unrelated fields.

## Remaining Boundary

| task | reason |
|---|---|
| formalize or import the source objects | this package is still manuscript-level evidence |
| prove trace-class and cyclicity in the source object model | trace legality remains an analytic theorem |
| prove pointwise finite-prime normalization over source indices | finite-prime data still needs a formal source definition |
| expose the sign bridge as a theorem | Proposition C.1 depends on the inequality direction |
| expose the source-RH-to-Mathlib-RH bridge | the final theorem must conclude Mathlib RH |

This package does not prove RH. It removes one broad ambiguity from the next
certification phase: the source objects must come from one definition spine.
