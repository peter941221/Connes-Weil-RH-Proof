# CC20 Analytic Trace Legality Theorem Contract

Status: theorem contract for the CC20 analytic trace-legality gate.

This file converts:

```text
docs/proofs/cc20-analytic-trace-legality-spine-discharge.md
```

from a proof-package spine into precise theorem targets for a future Lean pass
or accepted source import. It does not formalize CC20 operator theory. It fixes
the statements that must be proved, imported, or rejected before the route can
use positive trace as a Weil-form input.

## Evidence Lock

| item | evidence |
|---|---|
| CC20 paper | Alain Connes and Caterina Consani, "Weil positivity and Trace formula, the archimedean place", arXiv:2006.13771, `https://arxiv.org/pdf/2006.13771` |
| support-square trace formula | `weil-compo.tex:378-387`; `docs/audits/source-reread-v0.2.md:49` |
| trace-class verification | `weil-compo.tex:448-464`; `docs/audits/source-reread-v0.2.md:50` |
| quantized-calculus trace ideal template | `weil-compo.tex:2106-2121`; `docs/audits/source-reread-v0.2.md:53` |
| route trace operation ledger | `docs/manuscripts/connes-weil-rh-proof-draft.md:640-724,1059-1116,1332-1345` |
| source-object trace package | `docs/proofs/cc20-trace-object-normalization-discharge.md:78-109,389-456` |
| analytic spine package | `docs/proofs/cc20-analytic-trace-legality-spine-discharge.md` |
| formal-gate consistency audit | `docs/audits/formal-gate-spine-consistency-audit.md:132-158,303-314` |

The public arXiv lookup confirms the paper identity and PDF location. The
project-local audits keep the exact source-line references used by this
contract.

## Boundary

This contract gives a stronger target than the current proof package:

```text
proof-package spine
  |
  v
formal/import theorem contract
```

It still gives weaker evidence than a completed proof:

```text
formal/import theorem contract
  |
  v
Lean theorem or accepted source theorem with audited hypotheses
```

The final RH route cannot treat this contract as discharge. A later phase must
replace each target below with a Lean theorem or an accepted imported theorem.

## Objects Fixed Before Any Estimate

For fixed route data:

```text
S       finite source place set
I       CCM24 source support window
lambda  restricted CCM25 parameter
g       common source test
F_g     source convolution square g^* * g
```

the trace theorem must define one operator:

```text
A_(S,I,lambda,g)
  =
P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g)
```

inside the common fixed-S source Hilbert coordinate. The theorem cannot accept
an abstract positive scalar or a route-local trace field as input.

The required object bridge is:

```text
SourceTraceOperatorIdentity(S,I,lambda,g):
  A_(S,I,lambda,g) is the theta-smoothed fixed-S operator whose positive
  square is used by Theorem 1, and the same g and F_g are consumed by the CC20
  support-square trace and the CCM25 read-off.
```

Blocked shortcut:

```text
positiveTrace : Test -> Real
```

as a primitive field with no operator identity.

## Contract Theorem 1. Hilbert-Schmidt Gate

Target:

```text
SourceHilbertSchmidtForThetaSmoothedOperator:
  SourceTraceOperatorIdentity(S,I,lambda,g)
  -> SourceWindowAdmissible(S,I,lambda,g)
  -> HilbertSchmidt(A_(S,I,lambda,g)).
```

Meaning:

The CC20 trace-class source range and route smoothing estimates must prove that
the exact operator used for positivity is Hilbert-Schmidt.

Evidence used:

```text
weil-compo.tex:448-464
docs/manuscripts/connes-weil-rh-proof-draft.md:648-659
docs/manuscripts/connes-weil-rh-proof-draft.md:1059-1074
docs/manuscripts/connes-weil-rh-proof-draft.md:1337-1338
```

Blocked shortcut:

```text
traceClass g
```

without a theorem naming `A_(S,I,lambda,g)`.

## Contract Theorem 2. Positive Square Is Trace-Class

Target:

```text
SourceTraceClassForPositiveSquare:
  HilbertSchmidt(A_(S,I,lambda,g))
  -> TraceClass(A_(S,I,lambda,g)^* A_(S,I,lambda,g)).
```

Target equality:

```text
SourcePositiveTraceEqualsOrdinaryTrace:
  PositiveTrace(S,I,lambda,g)
    =
  Tr(A_(S,I,lambda,g)^* A_(S,I,lambda,g)).
```

Target inequality:

```text
SourcePositiveTraceNonnegative:
  0 <= Tr(A_(S,I,lambda,g)^* A_(S,I,lambda,g)).
```

Meaning:

Positivity must come from an ordinary trace of a trace-class positive operator.
The route must not derive nonnegativity from a regularized source trace before
the ordinary trace-class square exists.

Evidence used:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:652-659
docs/manuscripts/connes-weil-rh-proof-draft.md:1065-1074
docs/proofs/cc20-trace-object-normalization-discharge.md:89-90,396-399
```

Blocked shortcut:

```text
positiveTrace_nonnegative : 0 <= positiveTrace g
```

with no `A^*A` trace equality.

## Contract Theorem 3. Per-Move Cyclicity Ledger

Target:

```text
SourceCyclicMoveWitnessLedger(S,I,lambda,g):
  for each cyclic move C_i used by Theorem 1,
    the moved product is trace-class before cyclicity is applied,
    and the equality Tr(X_i Y_i) = Tr(Y_i X_i) uses that witness.
```

The route ledger has five named moves:

| move | contract requirement |
|---|---|
| `C1` positive trace square rewrite | trace-class witness for `A^*A` |
| `C2` support-square decomposition | operator identity in the common fixed-S coordinate |
| `C3` theta-smoothed phase derivative trace | trace-class witness for the theta-smoothed phase derivative |
| `C4` projection-order defect routing | trace-norm `Cdef` witness before any trace rearrangement |
| `C5` no-strip boundary extraction | no cyclic move after rank and pole jets are extracted |

Evidence used:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:661-724
docs/manuscripts/connes-weil-rh-proof-draft.md:1096-1112
docs/proofs/cc20-analytic-trace-legality-spine-discharge.md:161-203
```

Blocked shortcut:

```text
cyclicLegal : Test -> Prop
```

unless it projects from the five named witnesses.

## Contract Theorem 4. Support-Square Read-Off After Legality

Target:

```text
SourceSupportSquareTraceAfterLegality:
  SourcePositiveTraceEqualsOrdinaryTrace(S,I,lambda,g)
  -> SourceCyclicMoveWitnessLedger(S,I,lambda,g)
  -> SupportSquareTrace(S,I,lambda,g)
       =
     CC20SupportSquareTrace(S,I,lambda,g).
```

Meaning:

The CC20 support-square formula consumes trace legality. It does not supply
trace legality.

Evidence used:

```text
weil-compo.tex:378-387
docs/manuscripts/connes-weil-rh-proof-draft.md:1076-1094
docs/manuscripts/connes-weil-rh-proof-draft.md:1332-1345
docs/proofs/cc20-trace-object-normalization-discharge.md:91-92,399-400
```

Blocked shortcut:

```text
supportSquareTrace_eq_sourceTrace : Prop
```

with no hypotheses for positive trace and cyclicity.

## Contract Theorem 5. No-Defect Read-Off After Support Square

Target:

```text
SourceNoDefectTraceAfterSupportSquare:
  SourceSupportSquareTraceAfterLegality(S,I,lambda,g)
  -> NoDefectSourceTrace(S,I,lambda,g)
       =
     CC20NoDefectTrace(S,I,lambda,g).
```

Meaning:

The no-defect source trace can feed the CCM25 read-off only after the route
trace has passed through the support-square trace.

Evidence used:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1114-1116
docs/proofs/cc20-trace-object-normalization-discharge.md:91-92,399-400
docs/proofs/cc20-analytic-trace-legality-spine-discharge.md:245-295
```

Blocked shortcut:

```text
Tr(A^*A) >= 0 -> QW_lambda(g,g) >= 0
```

with no support-square and no-defect equalities.

## Contract Theorem 6. Bounded Comparison Preserves Trace Ideals

Target:

```text
SourceBoundedComparisonTraceIdealTransport:
  TraceIdealClass(T)
  -> Bounded(B)
  -> Bounded(C)
  -> TraceIdealClass(B * T * C).
```

Required specialization:

```text
the CCM24 bounded comparison maps may transport Hilbert-Schmidt and trace-class
facts between source coordinates after the source estimate has produced those
facts.
```

Evidence used:

```text
mainc2m24fine.tex:806-823
docs/proofs/cc20-analytic-trace-legality-spine-discharge.md:297-329
docs/audits/source-interface-discharge-audit.md:52-54,318-342
```

Blocked shortcut:

```text
boundedComparisonMap : Prop
```

as the analytic trace-class proof.

## Combined Contract

The formal/import target for this gate is:

```text
CC20AnalyticTraceLegalityContract(S,I,lambda,g):
  SourceTraceOperatorIdentity(S,I,lambda,g)
  SourceHilbertSchmidtForThetaSmoothedOperator(S,I,lambda,g)
  SourceTraceClassForPositiveSquare(S,I,lambda,g)
  SourcePositiveTraceEqualsOrdinaryTrace(S,I,lambda,g)
  SourcePositiveTraceNonnegative(S,I,lambda,g)
  SourceCyclicMoveWitnessLedger(S,I,lambda,g)
  SourceSupportSquareTraceAfterLegality(S,I,lambda,g)
  SourceNoDefectTraceAfterSupportSquare(S,I,lambda,g)
  SourceBoundedComparisonTraceIdealTransport(S,I,lambda,g)
```

Projection target:

```text
CC20AnalyticTraceLegalityContract(S,I,lambda,g)
  ->
CC20AnalyticTraceLegalitySpine(S,I,lambda,g).
```

Route consumption target:

```text
CC20AnalyticTraceLegalityContract(S,I,lambda,g)
  ->
positive trace may feed the restricted CCM25 Weil-form read-off.
```

only through:

```text
ordinary trace
  -> support-square trace
  -> no-defect source trace
  -> CCM25 QW_lambda read-off.
```

## Import Acceptance Checklist

A source import can discharge this contract only if it supplies these items:

| item | required evidence |
|---|---|
| exact operator | names the theta-smoothed fixed-S operator or proves equivalence to it |
| Hilbert-Schmidt gate | proves Hilbert-Schmidt membership for that operator |
| trace-class square | proves `A^*A` is trace-class before positivity |
| cyclic ledger | names every cyclic move or supplies theorem instances for each moved product |
| support-square formula | identifies the route trace with the CC20 support-square trace after legality |
| no-defect trace | identifies the support-square trace with the no-defect source trace used downstream |
| bounded comparison | preserves trace ideals; does not create them |
| source test | uses the same `g` and `F_g=g^* * g` as CCM25 |

If an import supplies only a scalar inequality, it fails this contract.

## Lean Interface Consequence

A later Lean interface should define a structure with fields equivalent to the
combined contract. The compact current fields:

```text
hilbertSchmidtGate
traceClass
cyclicLegal
positiveTrace
supportSquareTrace
sourceNoDefectTrace
```

should become projections from that structure. They should not remain primitive
source evidence.

The first Lean pass may keep theorem bodies as source-interface assumptions.
It must still expose the names above so that `#print axioms` shows exactly
which source theorem contracts the final route consumes.

## Current Judgment

| question | answer |
|---|---|
| Does this contract prove the CC20 trace theorem? | no |
| Does it specify the theorem shape needed to discharge the trace-legality gate? | yes |
| Does it block positivity before trace-class? | yes |
| Does it block cyclicity without per-move witnesses? | yes |
| Does it block direct `Tr(A^*A) -> QW_lambda` jumps? | yes |
| Can a later Lean/source-import pass use this as a checklist? | yes |

The trace-legality gate is now stated as a theorem contract. The next work is
to write matching contracts for finite-prime normalization or to encode this
contract in the future source-interface layer after Peter reopens Lean work.
