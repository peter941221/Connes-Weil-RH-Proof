# CC20 Trace Object Normalization Discharge

Status: source-object replacement package for CC20 trace objects, trace-class
gates, cyclicity legality, Mellin convention, and archimedean sign data.

This package sharpens:

```text
docs/proofs/cc20-trace-legality-mellin-discharge.md
```

The earlier package proves the route-level legality chain:

```text
Hilbert-Schmidt gate
  -> trace-class
  -> cyclic legality
  -> source trace read-off
  -> Mellin half-density compatibility
```

This package records the source definitions that must replace the symbolic
fields in:

```text
ConnesWeilRH.ArchimedeanTraceSymbols
```

## Evidence Boundary

| claim | evidence |
|---|---|
| symbolic CC20 trace fields | `ConnesWeilRH/Basic.lean:109-140` |
| source-interface obligations | `ConnesWeilRH/Source/CC20.lean:19-69` |
| route trace consumers | `ConnesWeilRH/Route/Theorem1.lean:22-34,125-168,206-240` |
| support-square trace source range | `weil-compo.tex:378-387`; `docs/audits/source-reread-v0.2.md:49` |
| trace-class source range | `weil-compo.tex:448-464`; `docs/audits/source-reread-v0.2.md:50` |
| quantized-calculus trace ideal template | `weil-compo.tex:2106-2121`; `docs/proofs/cc20-trace-legality-mellin-discharge.md` |
| Mellin half-density convention | `weil-compo.tex:2014-2030`; `docs/audits/source-reread-v0.2.md:51` |
| CC20 sign normalization | `weil-compo.tex:2131-2165`; `docs/manuscripts/connes-weil-rh-proof-draft.md:1349-1366` |
| Theorem 1 trace read-off | `docs/manuscripts/connes-weil-rh-proof-draft.md:1025-1048,1059-1068,1338-1345` |

## Problem

The current symbolic trace record is useful for route composition:

```text
supportSquareTrace : Test -> Real
sourceNoDefectTrace : Test -> Real
positiveTrace : Test -> Real
traceClass : Test -> Prop
cyclicLegal : Test -> Prop
hilbertSchmidtGate : Test -> Prop
```

It does not yet identify the source operator behind each field. A final proof
cannot accept these fields as primitive facts. It must prove or import the CC20
objects and then show that the route fields read those same objects.

The main risk is a trace identity drift:

```text
positive trace
  |
  v
support-square trace
  |
  v
source no-defect trace
  |
  v
QW_lambda read-off
```

Each arrow requires a source-backed theorem. A sum-level or route-local equality
does not prove that all four traces refer to the same CC20 object.

## Target Statement

For a source-backed fixed-`S` test `g`, the trace-object normalization target is:

```text
CC20TraceObjectNormalization(g):
  the route test is the CC20 source test;

  hilbertSchmidtGate, traceClass, and cyclicLegal are the CC20 trace-ideal
  hypotheses and conclusions for that test;

  positiveTrace is the ordinary trace of A^*A;

  supportSquareTrace and sourceNoDefectTrace are the CC20 support-square and
  no-defect source trace of the same operator;

  Mellin and sign normalizations match the CCM25 test and Weil-form
  conventions.
```

Lean-facing replacement outputs:

```text
SourceCC20TraceTestCompatibility
SourceHilbertSchmidtGate
SourceTraceClassCyclicityTemplate
SourcePositiveTraceNonnegative
SourceSupportSquareTraceReadOff
SourceNoDefectTraceReadOff
SourceMellinHalfDensityCompatibility
SourceCC20SignNormalizations
```

## Lemma 1. Trace Test Compatibility

Statement:

```text
SourceCC20TraceTestCompatibility(g):
  the route archimedean trace test is the CC20 test attached to the same
  source half-density used by CCM25.
```

Proof.

The source-test package ties the CCM24 fixed-`S` test, the CCM25 test, and the
CC20 Mellin/Fourier test to one source-backed object:

```text
docs/proofs/source-test-convolution-compatibility.md
```

The CC20 trace package then applies the trace-class and Mellin conventions to
that same object:

```text
docs/proofs/cc20-trace-legality-mellin-discharge.md
```

Thus:

```text
ArchimedeanTraceSymbols.Test
```

must be replaced by a source-backed test object, or by a bridge from the common
test object to the CC20 trace test.

Failure blocked:

```text
trace-class can be proved for one test while QW_lambda is read from another.
```

## Lemma 2. Hilbert-Schmidt Gate Owns The Positive Trace

Statement:

```text
SourcePositiveTraceNonnegative(g):
  hilbertSchmidtGate g proves the operator A is Hilbert-Schmidt, so
  positiveTrace g is the ordinary trace Tr(A^*A) and is nonnegative.
```

Proof.

The manuscript makes the order explicit:

```text
P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g) in S_2
```

before it uses:

```text
Tr(A^*A) >= 0.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1059-1068
docs/proofs/cc20-trace-legality-mellin-discharge.md:55-99
```

Therefore:

```text
positiveTrace : Test -> Real
```

cannot remain a bare nonnegative scalar. It must be tied to the ordinary trace
of the CC20 theta-smoothed support-square operator after the Hilbert-Schmidt
gate has been proved.

Failure blocked:

```text
positivity is applied before the operator is trace-class.
```

## Lemma 3. Trace-Class And Cyclicity Are One Source Template

Statement:

```text
SourceTraceClassCyclicityTemplate(g):
  traceClass g and cyclicLegal g come from the same CC20 trace-ideal theorem.
```

Proof.

CC20 supplies the trace-class source range and the quantized-calculus trace
ideal template:

```text
weil-compo.tex:448-464
weil-compo.tex:2106-2121
```

The route currently packages this as:

```text
TraceClassTemplateStatement A:
  hilbertSchmidtGate g -> traceClass g and cyclicLegal g.
```

Evidence:

```text
ConnesWeilRH/Basic.lean:131-133
ConnesWeilRH/Route/Theorem1.lean:206-240
```

The replacement theorem should not allow `traceClass` and `cyclicLegal` to be
proved by unrelated assumptions. The same source theorem must supply both, or
the cyclic trace move can outrun the analytic trace-ideal hypotheses.

Failure blocked:

```text
cyclicity is imported as a free route-local permission.
```

## Lemma 4. Support-Square Trace And No-Defect Trace Are Source Equal

Statement:

```text
SourceNoDefectTraceReadOff(g):
  supportSquareTrace g equals sourceNoDefectTrace g because CC20 identifies
  the support-square trace with the no-defect source trace for the same test.
```

Proof.

The source support-square range is:

```text
weil-compo.tex:378-387
```

The route reads the no-defect trace through:

```text
Tr(theta_S(g)^*
   [-P_(S,G)(1/2)u_S^(-1)d^-u_S P_(S,G)]
   theta_S(g))

= Trace_source,no-defect(R_lambda U(F_g))

= QW_lambda(g,g).
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1025-1041
docs/manuscripts/connes-weil-rh-proof-draft.md:1338-1345
```

The first equality must be owned by the CC20 source trace object plus the
fixed-S transport package. The second equality belongs to CCM25 restricted
read-off. Keeping the two equalities separate prevents the proof from jumping
directly from a positive trace to `QW_lambda`.

Failure blocked:

```text
the route proves positivity of one trace and identifies a different trace with
the Weil form.
```

## Lemma 5. Mellin Convention Uses The Same Convolution Square

Statement:

```text
SourceMellinHalfDensityCompatibility(g):
  the CC20 Mellin test and the CCM25 test produce the same
  F_g = g^* * g.
```

Proof.

CC20 gives the Mellin/Fourier half-density convention in:

```text
weil-compo.tex:2014-2030
```

The current symbolic statement is:

```text
mellinHalfDensityMatched : Prop
```

Evidence:

```text
ConnesWeilRH/Basic.lean:117,135-137
docs/proofs/source-test-convolution-compatibility.md
```

The replacement theorem must state the actual map between the source Mellin
test and the route half-density test. It must also state that convolution and
involution transport to the same:

```text
F_g=g^* * g.
```

Failure blocked:

```text
triple vanishing can be checked for one Mellin test while finite-prime support
uses another convolution square.
```

## Lemma 6. Sign Normalization Is Source-Owned

Statement:

```text
SourceCC20SignNormalizations:
  uInfinityNormalized, qduNormalized, and archimedeanSignNormalized are the
  CC20 sign conventions that match the CCM25 Weil-form sign bridge.
```

Proof.

CC20 fixes the archimedean unitary phase and quantized differential sign in:

```text
weil-compo.tex:2131-2165
```

The manuscript sign audit records the interaction with CCM25:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1349-1366
```

The final sign bridge then requires:

```text
QW(g,g) = - sum_v W_v(g * bar(g)^sharp).
```

Evidence:

```text
docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md
```

Thus the three Boolean-looking fields:

```text
uInfinityNormalized
qduNormalized
archimedeanSignNormalized
```

must become source theorem outputs, not route-local assumptions.

Failure blocked:

```text
the final CC20 positivity criterion receives a sign-flipped Weil sum.
```

## Combined Result

The six lemmas give:

```text
CC20TraceObjectNormalization(g):
  SourceCC20TraceTestCompatibility g
  SourceHilbertSchmidtGate g
  SourceTraceClassCyclicityTemplate g
  SourcePositiveTraceNonnegative g
  SourceSupportSquareTraceReadOff g
  SourceNoDefectTraceReadOff g
  SourceMellinHalfDensityCompatibility g
  SourceCC20SignNormalizations
```

This strengthens:

```text
TraceSquareStatement A
TraceClassTemplateStatement A
MellinHalfDensityConventionStatement A
SignsAndNormalizationsStatement A
```

by naming the source objects behind their fields.

## Formalization Consequence

A later Lean pass should not keep:

```text
supportSquareTrace
sourceNoDefectTrace
positiveTrace
traceClass
cyclicLegal
hilbertSchmidtGate
mellinHalfDensityMatched
uInfinityNormalized
qduNormalized
archimedeanSignNormalized
```

as unrelated assumptions. It should expose a package with source-backed
theorems shaped like:

```text
source_trace_test_matches_common_test
source_hilbert_schmidt_gate
source_trace_class_and_cyclicity
source_positive_trace_eq_Tr_AstarA
source_support_square_trace_eq_no_defect_trace
source_mellin_half_density_matches_convolution_square
source_cc20_signs_match_ccm25_weil_sum
```

The route can then derive the current symbolic statements from these theorems,
rather than accepting the symbolic statements as final source evidence.

## Remaining Boundary

| task | reason |
|---|---|
| define or import the CC20 trace test | current `Test` is abstract |
| define the theta-smoothed support-square operator | needed for `positiveTrace = Tr(A^*A)` |
| formalize the trace-ideal theorem | needed for trace-class and cyclicity |
| formalize the no-defect trace read-off | needed before CCM25 read-off |
| formalize the Mellin half-density bridge | needed for final triple vanishing |
| formalize the CC20 sign convention bridge | needed before Proposition C.1 |

This package does not prove RH. It blocks a trace-object drift: the route must
use one CC20 source test and one CC20 source trace chain before reading the
result as the CCM25 Weil form.
