# CC20 Trace Legality And Mellin Discharge

Status: proof package for the CC20 trace-legality and Mellin-convention part of
the source-interface discharge.

This package attacks four CC20 source-interface contracts:

```text
cc20ArchimedeanTraceSquare
cc20TraceClassTemplate
cc20MellinHalfDensityConvention
cc20SignsAndNormalizations
```

It does not prove the final CC20 finite-vanishing RH exit. That exit remains a
separate target because it must bridge the source positivity criterion to the
final `RiemannHypothesis` statement after the route has fixed the exact
positive Weil form.

## Evidence Boundary

Official source package:

```text
https://arxiv.org/e-print/2006.13771
```

The relevant source file is `weil-compo.tex`.

| claim | evidence |
|---|---|
| support-square trace formula and source trace `traceequa` | `weil-compo.tex:378-387`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:85`, `1338-1341` |
| trace-class proof for the archimedean summand | `weil-compo.tex:448-464`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:86`, `1338` |
| quantized-calculus trace ideal template | `weil-compo.tex:2106-2121`; source reread `docs/audits/source-reread-v0.2.md:53` |
| Mellin/Fourier half-density convention | `weil-compo.tex:2014-2030`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:87`, `1224-1238` |
| archimedean sign and `u_infty` normalization | `weil-compo.tex:2131-2165`; manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:89`, `1349-1361` |
| Theorem 1 trace legality ledger | manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:1059-1112`, `1332-1345` |

## Target Statement

For the source-backed fixed-`S` test `g`, let:

```text
F_g = g^* * g.
```

The CC20 discharge target is:

```text
CC20TraceLegalityMellinDischarge(g):
  the fixed-S positive trace is an ordinary trace-class square before
  positivity is used; every cyclic trace move in Theorem 1 occurs after the
  relevant summand is trace-class; the no-defect archimedean trace uses the
  CC20 support-square and sign convention; and the source Mellin convention
  sends the test to the same half-density convolution F_g used by CCM25.
```

Equivalently, the route must pass this dependency chain:

```text
theta-smoothed square
      |
      v
Hilbert-Schmidt gate
      |
      v
ordinary trace-class positive trace
      |
      v
legal cyclic trace moves
      |
      v
CC20 source trace read-off
      |
      v
CCM25 test F_g = g^* * g under the same half-density convention
```

## Lemma 1. Hilbert-Schmidt Gate Before Positivity

Statement:

```text
CC20PositiveTraceDomain(g):
  the operator used to define PositiveTrace(g) is Hilbert-Schmidt before the
  proof takes Tr(A^* A).
```

Proof.

The route defines the positive trace through the theta-smoothed support-square
operator:

```text
A = P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g).
```

The manuscript records this gate in Theorem 1 Step 1:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1059-1074
```

CC20 supplies the analytic template used to prove trace-class membership after
theta smoothing. The source proof shows that the relevant archimedean summand
is trace-class by reducing it to a Schwartz quantized differential calculation
and then reading the trace from the kernel diagonal:

```text
weil-compo.tex:448-464
```

The quantized-calculus lemma gives the trace-ideal input:

```text
weil-compo.tex:2106-2121
```

The route-side smoothing and endpoint-strip packages supply the fixed-`S`
transport and defect quarantine:

```text
docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md
docs/proofs/battle-3-cdef-exhaustion-proof-package.md
```

Therefore the positive trace is defined as an ordinary trace:

```text
PositiveTrace(g) = Tr(A^* A) >= 0.
```

No source regularized trace is used for the positivity step.

Remaining discharge burden:

```text
Replace the route-level Hilbert-Schmidt assertions by a formal or imported
CC20 trace-ideal theorem after the theta_S(g) smoothing is expressed in the
same operator model.
```

## Lemma 2. Trace-Class Before Cyclicity

Statement:

```text
CC20CyclicityLegality(g):
  each cyclic trace move used by Theorem 1 is applied only to trace-class
  summands.
```

Proof.

The manuscript isolates the cyclic trace chain in:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:663-727
docs/manuscripts/connes-weil-rh-proof-draft.md:1096-1112
```

The legal moves split into two classes:

| move type | why cyclicity is legal |
|---|---|
| theta-smoothed no-defect term | CC20 trace-class template gives the trace-class archimedean summand before the trace is read |
| endpoint-strip defect term | Battle 3 factors the defect through a trace-norm `Cdef` summand before any cyclic rearrangement |

No-strip rank and pole jets are not moved by regularized cyclicity. Battle 1
extracts them as finite-dimensional ledgers before the CCM read-off:

```text
docs/proofs/battle-1-test-quotient-proof-package.md
docs/proofs/rank-repair-finite-normal-form.md
```

This proves the failure mode is blocked:

```text
cyclicity outside trace-class hypotheses
```

Output:

```text
cc20TraceClassTemplate can be consumed by Theorem 1 only through a
trace-class/cyclicity ledger, not through a bare symbolic equality.
```

## Lemma 3. Source Trace Square Read-Off

Statement:

```text
CC20SourceTraceSquareReadOff(g):
  the no-defect archimedean source summand read by Theorem 1 is the CC20
  support-square trace, with the CC20 trace convention.
```

Proof.

CC20 identifies the trace distribution for the archimedean support-square
summand and states the trace formula for compactly supported tests:

```text
weil-compo.tex:378-387
```

The route reaches that source summand only after Battle 2 has transported the
fixed-`S` support square into the no-defect quantized differential form:

```text
docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md
```

The no-defect read-off package then identifies the main term with the
CCM-normalized restricted form:

```text
docs/proofs/fixed-s-no-defect-compact-form-read-off.md
docs/proofs/ccm25-restricted-read-off-discharge.md
```

Thus the route does not invent a new trace convention. It uses the CC20 source
trace for the archimedean no-defect term and keeps rank, pole, and `Cdef`
outside that term until their ledgers are killed or exhausted.

Output:

```text
cc20ArchimedeanTraceSquare supplies the source trace leg used by
TraceWeilCompatibility.
```

## Lemma 4. Archimedean Sign Normalization

Statement:

```text
CC20ArchimedeanSign(g):
  the archimedean quantized differential contributes with the CC20 sign, and
  that sign matches the CCM25 convention used in QW_lambda.
```

Proof.

CC20 fixes the unitary phase by the archimedean local factor ratio on the
critical line and records the diagonal sign of the quantized differential:

```text
weil-compo.tex:2131-2165
```

The source reread and manuscript sign audit connect this with the CCM25 sign
normalization:

```text
docs/audits/source-reread-v0.2.md:47,54
docs/manuscripts/connes-weil-rh-proof-draft.md:1349-1361
```

The sign rule is:

```text
CC20 archimedean trace
  =
CCM25 W_R term
  =
- W_infty in the source convention.
```

The restricted CCM25 read-off then places the positive archimedean density in
`QW_lambda(g,g)` with the finite-prime sum subtracted:

```text
docs/proofs/ccm25-restricted-read-off-discharge.md
```

This separates the two signs that a wrong proof can conflate:

| sign | owned by |
|---|---|
| archimedean quantized differential sign | CC20 `u_infty` and `qd u` normalization |
| restricted finite-prime subtraction | CCM25 `QW_lambda` formula |

Output:

```text
cc20SignsAndNormalizations is consumed before the final trace-Weil
identification.
```

## Lemma 5. Mellin Half-Density Compatibility

Statement:

```text
CC20MellinHalfDensityCompatibility(g):
  the source Mellin test and the route half-density test define the same
  convolution square F_g = g^* * g.
```

Proof.

CC20 records the multiplicative convolution and involution, then relates the
Mellin transform of `k` to the multiplicative Fourier transform of the
half-density `f` through:

```text
f(x) = x^(1/2) k(x)
```

with the sign convention in the Fourier variable:

```text
weil-compo.tex:2014-2030
```

Therefore the route test conversion has three required consequences:

```text
1. convolution is preserved by the half-density map;
2. the natural source involution becomes f -> f^*;
3. vanishing conditions stated in Mellin variables translate with the recorded
   Fourier sign.
```

The CCM25 restricted form is applied to:

```text
F_g = g^* * g.
```

The finite-vanishing RH exit will later use the source Mellin zeros. This lemma
keeps that exit compatible with the test used inside `QW_lambda`; it does not
yet prove Proposition C.1 as a Mathlib theorem.

Output:

```text
cc20MellinHalfDensityConvention bridges the source Mellin convention to the
route half-density convention used by CCM25.
```

## Integrated Discharge Result

Combine Lemmas 1 through 5:

```text
CC20TraceLegalityMellinDischarge(g)
```

for every source-backed fixed-`S` test `g` satisfying the admissible-window and
finite-prime visibility conditions used by Theorem 1.

The result proves, at source-interface proof-package level:

```text
PositiveTrace(g) is an ordinary trace-class positive trace
      |
      v
Theorem 1 cyclicity uses only trace-class summands
      |
      v
the no-defect source trace is the CC20 archimedean trace square
      |
      v
the archimedean sign matches the CCM25 restricted Weil form
      |
      v
the Mellin half-density convention sends the route test to F_g=g^* * g
```

## Remaining Boundary

This package upgrades the CC20 trace-legality and convention layer from a
matrix row to a proof package. It leaves two tasks open:

| remaining task | reason |
|---|---|
| formal or accepted import of the CC20 analytic trace theorems | the package cites CC20 source lines but does not formalize the analysis inside Lean |
| `cc20FiniteVanishingRhExit` bridge | Proposition C.1 must still be connected to the final `RiemannHypothesis` statement after the exact positivity input is fixed |

The route remains source-conditional until those source interfaces are
discharged by proof, accepted imports, or formalization.
