# CC20 RH Exit Object Normalization Discharge

Status: source-object replacement package for the CC20 finite-vanishing RH
exit and the final source-RH-to-Mathlib-RH bridge.

This package sharpens two existing proof packages:

```text
docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md
```

The earlier packages prove the route-level exit:

```text
triple vanishing
  -> CC20 finite vanishing on F={0,1/2,1}
  -> CC20 Weil inequality
  -> CC20 Proposition C.1
  -> source RH
  -> Mathlib RH
```

This package records the source objects that must replace:

```text
ConnesWeilRH.FiniteVanishingCriterionPackage
```

before final certification.

## Evidence Boundary

| claim | evidence |
|---|---|
| symbolic final-exit package | `ConnesWeilRH/Basic.lean:202-210` |
| CC20 source-interface wrapper | `ConnesWeilRH/Source/CC20.lean:45-51,61-69` |
| final route consumer | `ConnesWeilRH/Route/RouteTheorem.lean:26-33` |
| CC20 Proposition C.1 source range | `weil-compo.tex:2072-2085`; `docs/audits/source-reread-v0.2.md:52` |
| route finite set `F={0,1/2,1}` | `docs/manuscripts/connes-weil-rh-proof-draft.md:1229-1291` |
| final-exit package | `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md` |
| source RH definition bridge | `docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md` |
| Mathlib RH predicate | `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:165-168` |

## Problem

The current Lean package is deliberately small:

```text
structure FiniteVanishingCriterionPackage where
  finiteSetAdmissible : Prop
  criterion :
    forall input : WeilPositivityInput,
      input.tripleVanishing -> input.fullWeilPositivity -> RH
```

This shape lets the route compose. It does not yet expose the source objects
that make the conclusion trustworthy:

```text
finite set F
non-trivial-zero exclusion
Mellin vanishing on F
CC20 Weil inequality
CC20 Proposition C.1
source RH predicate
Mathlib RH predicate
```

The final certification cannot hide those objects inside a single theorem
field named `criterion`.

## Target Statement

For any route input satisfying triple vanishing and full Weil positivity, the
final-exit object replacement target is:

```text
CC20RHExitObjectNormalization(input):
  finiteSetAdmissible is the source side condition for F={0,1/2,1};

  input.tripleVanishing is exactly CC20 Mellin vanishing on that F;

  input.fullWeilPositivity is exactly the CC20 nonpositivity inequality after
  the CCM25-to-CC20 sign bridge;

  CC20 Proposition C.1 produces the source RH predicate;

  the source RH predicate is transported to Mathlib's
  _root_.RiemannHypothesis.
```

Lean-facing replacement outputs:

```text
SourceFiniteSetAdmissibility
SourceTripleVanishingOnF
SourceCC20WeilInequality
SourceCC20PropositionC1
SourceRHToMathlibRH
SourceFiniteVanishingCriterionToMathlibRH
```

## Lemma 1. The Finite Set Is A Source Object

Statement:

```text
SourceFiniteSetF:
  the finite vanishing set is the concrete CC20 source set F={0,1/2,1}.
```

Proof.

The manuscript fixes:

```text
F={0,1/2,1}.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1229-1238
docs/manuscripts/connes-weil-rh-proof-draft.md:1262-1291
docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md:111-150
```

CC20 Proposition C.1 allows a finite set containing `{0,1}` and disjoint from
the non-trivial zero set:

```text
weil-compo.tex:2075-2078
```

Therefore:

```text
finiteSetAdmissible : Prop
```

must become a theorem about this exact set. It is not a permission to choose a
different finite set after the proof has fixed the three route vanishings.

Failure blocked:

```text
the criterion applies to an admissible finite set unrelated to the route's
three vanishing points.
```

## Lemma 2. Finite-Set Admissibility Uses The Source Zero Predicate

Statement:

```text
SourceFiniteSetAdmissibility:
  F={0,1/2,1} is finite, contains {0,1}, and is disjoint from the CC20
  non-trivial zero set.
```

Proof.

The manuscript proves the `1/2` exclusion through Dirichlet eta:

```text
eta(s) = (1 - 2^(1-s)) zeta(s).
```

At `s=1/2`, the alternating eta series is positive and the scalar
`1 - sqrt(2)` is nonzero, so:

```text
zeta(1/2) != 0.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1240-1260
docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md:111-150
```

The points `0` and `1` are not non-trivial zeros by the source definition:
`0` lies outside the source non-trivial zero set, and `1` is the pole excluded
by the RH predicate.

The formal replacement must state which zeta object and which non-trivial-zero
predicate it uses. This lemma must connect to the source-RH definition bridge,
not to a route-local zero predicate.

Failure blocked:

```text
the finite set is certified against one zero predicate while Proposition C.1
uses another.
```

## Lemma 3. Route Triple Vanishing Is CC20 Vanishing On F

Statement:

```text
SourceTripleVanishingOnF(input):
  input.tripleVanishing is the CC20 Mellin vanishing condition on
  F={0,1/2,1}.
```

Proof.

CC20 uses the coordinate:

```text
s = 1/2 - i t.
```

The manuscript maps the route vanishing points:

```text
t=0     -> s=1/2
t=+i/2  -> s=1
t=-i/2  -> s=0.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1273-1285
docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md:166-226
```

The Mellin half-density package supplies the convention bridge:

```text
docs/proofs/cc20-trace-object-normalization-discharge.md
docs/proofs/cc20-trace-legality-mellin-discharge.md
```

Thus:

```text
input.tripleVanishing : Prop
```

must be replaced by a theorem that expands the route predicate into the three
source vanishings on `F`.

Failure blocked:

```text
the route kills three centered evaluations while CC20 Proposition C.1 receives
different Mellin vanishings.
```

## Lemma 4. Full Positivity Is The CC20 Weil Inequality

Statement:

```text
SourceCC20WeilInequality(input):
  input.fullWeilPositivity is the source inequality
  sum_v W_v(g * bar(g)^sharp) <= 0.
```

Proof.

The route proves:

```text
QW(g,g) >= 0.
```

CC20 Proposition C.1 uses:

```text
sum_v W_v(g * bar(g)^sharp) <= 0.
```

The sign bridge identifies them through:

```text
QW(g,g) = - sum_v W_v(g * bar(g)^sharp).
```

Evidence:

```text
docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md
docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md:229-278
docs/proofs/ccm25-finite-prime-index-normalization-discharge.md
docs/proofs/cc20-trace-object-normalization-discharge.md
```

Therefore:

```text
fullWeilPositivity : Prop
```

must not remain an opaque positive-looking proposition. It must expose the
CCM25 `QW` object, the CC20 Weil sum, and the sign equality between them.

Failure blocked:

```text
the final criterion receives a sign-flipped or route-local positivity input.
```

## Lemma 5. Proposition C.1 Is The Source Exit Theorem

Statement:

```text
SourceCC20PropositionC1:
  the exit theorem is CC20 Proposition C.1 with the source finite set F.
```

Proof.

The source range is:

```text
weil-compo.tex:2072-2085
```

The proof package records the exact role:

```text
docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md:79-109
```

The source theorem says:

```text
RH
  iff
sum_v W_v(g * bar(g)^sharp) <= 0
for all compactly supported smooth multiplicative tests vanishing on F.
```

where `F` is finite, contains `{0,1}`, and is disjoint from the non-trivial
zero set.

The route uses only the forward application from the inequality criterion to
RH. It should not replace Proposition C.1 by an invented density result or a
local route theorem.

Failure blocked:

```text
the route proves a similar-looking finite-vanishing criterion that is not the
CC20 source theorem.
```

## Lemma 6. Source RH Is Transported To Mathlib RH

Statement:

```text
SourceFiniteVanishingCriterionToMathlibRH:
  the CC20 source RH conclusion is transported to _root_.RiemannHypothesis.
```

Proof.

Mathlib defines:

```text
RiemannHypothesis :=
  forall s,
    riemannZeta s = 0 ->
    not (exists n, s = -2 * (n + 1)) ->
    s != 1 ->
    s.re = 1/2.
```

Evidence:

```text
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:165-168
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md
```

The bridge requires three source-definition theorems:

```text
sourceZeta = riemannZeta
source non-trivial zero = Mathlib zero with exclusions
source critical line = s.re = 1/2
```

The current final theorem already targets Mathlib RH:

```text
ConnesWeilRH/Route/RouteTheorem.lean:26-33
```

The missing work is not the theorem target. The missing work is the object
transport from the CC20 conclusion to that target.

Failure blocked:

```text
the route concludes "RH" in source notation while the Lean theorem claims
Mathlib's predicate.
```

## Combined Result

The six lemmas give:

```text
CC20RHExitObjectNormalization(input):
  SourceFiniteSetF
  SourceFiniteSetAdmissibility
  SourceTripleVanishingOnF input
  SourceCC20WeilInequality input
  SourceCC20PropositionC1
  SourceFiniteVanishingCriterionToMathlibRH
```

This strengthens:

```text
FiniteVanishingCriterionPackage.finiteSetAdmissible
FiniteVanishingCriterionPackage.criterion
```

by naming the source objects and definition bridges that must produce those
fields.

## Formalization Consequence

A later Lean pass should avoid leaving the final exit as:

```text
finiteSetAdmissible : Prop
criterion : input -> tripleVanishing -> fullWeilPositivity -> RH
```

without source-owned components. A replacement package should expose fields or
theorems shaped like:

```text
sourceFiniteSet_eq_insert_half
sourceFiniteSet_admissible_for_CC20
sourceTripleVanishing_iff_mellinVanishesOnF
sourceFullWeilPositivity_iff_CC20WeilInequality
sourceCC20PropositionC1_applies
sourceRH_implies_mathlibRH
```

The current route can still derive the compact `FiniteVanishingCriterionPackage`
from this package. Certification should consume the expanded package, not the
compact wrapper alone.

## Remaining Boundary

| task | reason |
|---|---|
| formalize or import CC20 Proposition C.1 | the source theorem is cited, not proved here |
| formalize the finite-set zero exclusion | `zeta(1/2) != 0` and the source non-trivial-zero predicate must become Lean-visible |
| formalize the triple-vanishing to Mellin bridge | the route points must map to `F={0,1/2,1}` under the source convention |
| formalize the sign bridge | `QW(g,g) >= 0` must become the CC20 nonpositivity inequality |
| formalize source RH to Mathlib RH | the final theorem target must use Mathlib's exact predicate |

This package does not prove RH. It removes one final-exit ambiguity: the compact
criterion package must come from CC20 Proposition C.1 and the source-to-Mathlib
definition bridge, not from an opaque route-local RH axiom.
