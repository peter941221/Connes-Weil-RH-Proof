# CC20 Analytic Trace Legality Spine Discharge

Status: proof package for the analytic trace-legality spine.

This package attacks the second remaining formal gate from:

```text
docs/audits/source-interface-discharge-completion-audit.md
```

The gate is:

```text
analytic trace legality
```

The package does not formalize CC20 operator theory in Lean. It records the
order in which the later source-import or Lean pass must expose the analytic
trace theorems before the route can read a positive trace as a Weil form.

The stronger formal/import theorem contract is:

```text
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md
```

It names the theorem targets that must replace this proof-package spine before
the analytic trace-legality gate can count as discharged.

## Evidence Boundary

| object | evidence |
|---|---|
| CC20 trace-class source range | `weil-compo.tex:448-464` |
| CC20 quantized-calculus trace ideal template | `weil-compo.tex:2106-2121` |
| CC20 support-square trace formula | `weil-compo.tex:378-387` |
| CC20 Mellin and sign conventions | `weil-compo.tex:2014-2030,2131-2165` |
| source reread audit | `docs/audits/source-reread-v0.2.md:49-54` |
| route trace legality package | `docs/proofs/cc20-trace-legality-mellin-discharge.md` |
| CC20 trace object package | `docs/proofs/cc20-trace-object-normalization-discharge.md` |
| source definition spine | `docs/proofs/source-object-definition-spine-discharge.md` |
| fixed-S support-square transport | `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md` |
| endpoint-strip Cdef control | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md` |

## Target Statement

The analytic trace-legality target is:

```text
CC20AnalyticTraceLegalitySpine(S,I,lambda,g):
  the theta-smoothed fixed-S operator is Hilbert-Schmidt;
  its square is trace-class;
  every cyclic trace move carries a named trace-class witness;
  positiveTrace is the ordinary trace Tr(A^*A);
  the support-square trace and no-defect trace are read only after those
  legality witnesses exist.
```

The dependency order is:

```text
source test g and F_g
      |
      v
theta-smoothed fixed-S operator A
      |
      v
Hilbert-Schmidt witness for A
      |
      v
trace-class witness for A^*A and moved summands
      |
      v
legal cyclic trace moves
      |
      v
ordinary positive trace Tr(A^*A)
      |
      v
CC20 support-square trace
      |
      v
CC20 no-defect source trace
      |
      v
CCM25 Weil-form read-off
```

The key rule is:

```text
read-off never creates trace legality.
```

## Lemma 1. Operator Identity Comes Before Estimates

Statement:

```text
TraceOperatorFixedBeforeLegality(S,I,lambda,g):
  the operator A whose positivity is used is fixed before Hilbert-Schmidt,
  trace-class, or cyclicity claims are made.
```

Proof.

The route uses the theta-smoothed fixed-S support-square operator:

```text
A = P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g).
```

The support-square transport package ties this operator to the CCM24 window,
the fixed-S coordinate, and the source test. The source-definition spine ties
the same `g` and `F_g=g^* * g` to CCM25 and CC20.

Therefore the later trace theorem must take this operator as input. It cannot
prove trace-class membership for a different CC20 test and then identify the
result after the fact.

Failure blocked:

```text
trace-class is proved for one operator while positivity is taken for another.
```

## Lemma 2. Hilbert-Schmidt Generates Trace-Class Positivity

Statement:

```text
HilbertSchmidtToOrdinaryPositiveTrace(A):
  a Hilbert-Schmidt witness for A gives trace-class membership for A^*A and
  identifies positiveTrace with the ordinary trace Tr(A^*A).
```

Proof.

The CC20 trace-object package already records:

```text
SourceHilbertSchmidtGate
SourcePositiveTraceNonnegative
```

This package adds the ordering constraint. The source theorem must first prove
the Hilbert-Schmidt gate for the fixed operator `A`. Then the route may form:

```text
A^*A
```

as a trace-class operator and use:

```text
Tr(A^*A) >= 0.
```

The positivity step must use an ordinary trace-class trace. It must not use a
regularized trace, a formal scalar field, or a source trace that has not yet
been identified with `A^*A`.

Failure blocked:

```text
positiveTrace is accepted as a nonnegative scalar without an operator-level
Hilbert-Schmidt witness.
```

## Lemma 3. Cyclicity Carries A Witness For Each Move

Statement:

```text
TraceCyclicityWitnessLedger(S,I,lambda,g):
  every cyclic trace rearrangement used in Theorem 1 has a named trace-class
  witness for the moved product.
```

Proof.

CC20 supplies a trace-ideal template for the archimedean summand:

```text
weil-compo.tex:448-464
weil-compo.tex:2106-2121
```

The route also has endpoint-strip defect terms. Battle 3 keeps those terms in
the `Cdef` ledger with trace-norm control. The route must not move them by
cyclicity unless the relevant trace-class product has been proved.

The formal interface should therefore expose a ledger:

```text
cyclicMove_i:
  traceClass(left_i * right_i)
    ->
  Tr(left_i * right_i) = Tr(right_i * left_i).
```

The route can bundle these witnesses, but it must not collapse them into:

```text
cyclicLegal : Prop.
```

Failure blocked:

```text
a cyclic trace move treats boundedness or formal symmetry as trace-class
legality.
```

## Lemma 4. Support-Square Read-Off Waits For Trace Legality

Statement:

```text
SupportSquareReadOffAfterLegality(S,I,lambda,g):
  the CC20 support-square trace formula is applied only after the positive
  trace and cyclicity witnesses have been established.
```

Proof.

The CC20 support-square trace source range is:

```text
weil-compo.tex:378-387
```

That source formula identifies a trace distribution for the correct test. It
does not prove by itself that the route's theta-smoothed fixed-S operator has
already entered the trace ideal. The route obtains that legality from the
Hilbert-Schmidt and trace-class stages.

So the proof order must be:

```text
Hilbert-Schmidt witness
  -> trace-class/cyclicity witness
  -> positive ordinary trace
  -> support-square trace formula.
```

Failure blocked:

```text
the route invokes the CC20 support-square formula as a substitute for proving
ordinary trace-class legality.
```

## Lemma 5. No-Defect Read-Off Waits For Support-Square Read-Off

Statement:

```text
NoDefectReadOffAfterSupportSquare(S,I,lambda,g):
  the no-defect source trace can feed CCM25 only after CC20 has identified the
  route trace with the support-square trace.
```

Proof.

The trace-object package separates:

```text
supportSquareTrace
sourceNoDefectTrace
positiveTrace
```

The restricted CCM25 read-off identifies the no-defect source trace with the
restricted Weil form. It does not identify the positive trace directly with
`QW_lambda`.

The source legality spine forces this path:

```text
positive trace
  -> support-square trace
  -> no-defect source trace
  -> QW_lambda read-off.
```

The route should reject any interface that jumps from:

```text
Tr(A^*A) >= 0
```

directly to:

```text
QW_lambda(g,g) >= 0.
```

Failure blocked:

```text
positivity of one trace is transferred to a Weil form without the CC20
support-square and no-defect equalities.
```

## Lemma 6. Bounded Comparison Transports Classes, It Does Not Create Them

Statement:

```text
BoundedComparisonAfterTraceEstimate(S,I,lambda,g):
  CCM24 bounded comparison may transport Hilbert-Schmidt and trace-class
  estimates only after the CC20 or endpoint-strip estimates provide them.
```

Proof.

The CCM24 source package supplies bounded comparison maps and inverses. Those
maps preserve analytic classes under bounded left and right multiplication.
They do not prove that the original product lies in a trace ideal.

Therefore the formal proof must distinguish:

```text
source estimate:
  A is Hilbert-Schmidt or trace-class

transport theorem:
  B A C is Hilbert-Schmidt or trace-class when B and C are bounded
```

This distinction matters because the route uses CCM24 comparison to align
coordinates before the CCM25 read-off.

Failure blocked:

```text
a bounded coordinate comparison is treated as the analytic trace-class proof.
```

## Combined Result

Combining Lemmas 1 through 6 gives:

```text
CC20AnalyticTraceLegalitySpine(S,I,lambda,g)
```

with these Lean-facing theorem targets:

```text
SourceTraceOperatorFixed
SourceHilbertSchmidtForPositiveTrace
SourceTraceClassForPositiveSquare
SourceCyclicMoveWitnessLedger
SourceSupportSquareReadOffAfterLegality
SourceNoDefectReadOffAfterSupportSquare
SourceBoundedComparisonTraceIdealTransport
```

This strengthens the older CC20 packages:

```text
CC20TraceLegalityMellinDischarge(g)
CC20TraceObjectNormalization(g)
```

The older packages name the trace objects and source conventions. This package
fixes the order in which a formal proof must consume them.

## Formalization Consequence

A later Lean interface should not expose only:

```text
traceClass : Test -> Prop
cyclicLegal : Test -> Prop
positiveTrace : Test -> Real
supportSquareTrace : Test -> Real
sourceNoDefectTrace : Test -> Real
```

as unrelated fields.

It should expose a package shaped like:

```text
TraceLegalitySpine
  +-- operator A tied to (S,I,lambda,g)
  +-- Hilbert-Schmidt witness for A
  +-- trace-class witness for A^*A
  +-- per-move cyclicity witness ledger
  +-- positiveTrace_eq_ordinary_trace
  +-- supportSquareTrace_eq_source_trace
  +-- noDefectTrace_eq_supportSquareTrace
```

Then the current compact statements can project from that package.

## Remaining Boundary

| task | reason |
|---|---|
| formalize or import the CC20 trace-ideal theorem | this package records the dependency order only |
| define the route operator `A` in the source model | the current proof package names it but does not define it in Lean |
| formalize each cyclic move witness | a single `cyclicLegal` field remains too coarse for certification |
| formalize support-square and no-defect equalities | needed before CCM25 read-off can consume the trace |
| audit the axiom boundary after implementation | no new route-local trace axiom may enter the final theorem |

This package does not prove RH. It removes a specific loophole: the route must
earn trace legality before it uses positivity, cyclicity, or Weil-form read-off.
