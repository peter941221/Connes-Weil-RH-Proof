# RH Definition Bridge Theorem Contract

Status: theorem contract for the source-RH-to-Mathlib-RH definition bridge.

This file converts:

```text
docs/proofs/rh-definition-bridge-spine-discharge.md
```

from a proof-package spine into precise theorem targets for a future Lean pass
or accepted source import. It does not formalize CC20 or Mathlib. It fixes the
definition bridges that must be proved, imported, or rejected before the CC20
source conclusion can count as Mathlib's canonical:

```text
_root_.RiemannHypothesis.
```

## Evidence Lock

| item | evidence |
|---|---|
| Mathlib canonical RH predicate | `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:166-169` |
| Mathlib negative-even trivial zeros | `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:156-158` |
| route final theorem target | `ConnesWeilRH/Route/RouteTheorem.lean:26-33` |
| project RH abbreviation is definitional | `ConnesWeilRH/Basic.lean:20-23` |
| existing source-to-Mathlib bridge package | `docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md` |
| RH definition bridge spine | `docs/proofs/rh-definition-bridge-spine-discharge.md` |
| CC20 RH-exit object package | `docs/proofs/cc20-rh-exit-object-normalization-discharge.md` |
| source-object definition ledger | `docs/audits/source-object-definition-ledger.md:166-204` |
| formal-gate consistency audit | `docs/audits/formal-gate-spine-consistency-audit.md:259-317` |

Mathlib's local definition is:

```text
def RiemannHypothesis : Prop :=
  forall (s : Complex),
    riemannZeta s = 0 ->
    not (exists n : Nat, s = -2 * (n + 1)) ->
    s != 1 ->
    s.re = 1 / 2
```

The contract below follows that order.

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

## Objects Fixed Before The Final Predicate

The bridge compares two predicates:

```text
CC20SourceRH
```

and:

```text
_root_.RiemannHypothesis.
```

The bridge must not identify them by name. It must compare:

```text
source zeta object
source zero predicate
source non-trivial-zero predicate
source critical-line predicate
```

against Mathlib's:

```text
riemannZeta s = 0
not exists n, s = -2 * (n + 1)
s != 1
s.re = 1/2.
```

Blocked shortcut:

```text
sourceRH_to_mathlibRH : Prop
```

as the only final evidence.

## Contract Theorem 1. Zeta Object Equality

Target:

```text
SourceZetaEqualsMathlibZeta:
  forall s, sourceZeta(s) = riemannZeta(s).
```

Meaning:

The source theorem and Mathlib theorem must talk about the same zeta function.
The bridge must state the object equality before it transports zeros.

Evidence used:

```text
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md:92-133
docs/proofs/rh-definition-bridge-spine-discharge.md:99-129
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:146-164
```

Blocked shortcut:

```text
source zeta is the Riemann zeta
```

with no theorem tying it to Mathlib `riemannZeta`.

## Contract Theorem 2. Source Zero To Mathlib Zero

Target:

```text
SourceZeroToMathlibZero:
  sourceZetaZero(s)
  -> riemannZeta(s) = 0.
```

Reverse target for definition audit:

```text
MathlibZeroToSourceZero:
  riemannZeta(s) = 0
  -> sourceZetaZero(s).
```

Meaning:

Mathlib's first RH hypothesis is the equation `riemannZeta s = 0`. The bridge
must not translate only the phrase "non-trivial zero" while leaving the zero
equation implicit.

Evidence used:

```text
docs/proofs/rh-definition-bridge-spine-discharge.md:132-159
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md:140-198
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:168-169
```

Blocked shortcut:

```text
sourceNontrivialZero(s)
```

with no Mathlib zero equation.

## Contract Theorem 3. Negative-Even Exclusion

Target:

```text
SourceNontrivialZeroNoNegativeEven:
  sourceNontrivialZero(s)
  -> not (exists n : Nat, s = -2 * (n + 1)).
```

Reverse target for definition audit:

```text
MathlibZeroNoNegativeEvenToSourceNontrivialLeg:
  riemannZeta(s) = 0
  -> not (exists n : Nat, s = -2 * (n + 1))
  -> sourceNotNegativeEvenTrivialZero(s).
```

Meaning:

Mathlib excludes the negative-even trivial zeros as a separate hypothesis. CC20
source language must unpack "non-trivial" into this exclusion.

Evidence used:

```text
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:156-158
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:168-169
docs/proofs/rh-definition-bridge-spine-discharge.md:159-198
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md:140-198
```

Blocked shortcut:

```text
nontrivialZero(s)
```

without the explicit `not exists n` theorem.

## Contract Theorem 4. Pole Exclusion At s=1

Target:

```text
SourceNontrivialZeroNoPole:
  sourceNontrivialZero(s)
  -> s != 1.
```

Reverse target for definition audit:

```text
MathlibZeroNoPoleToSourceNontrivialLeg:
  riemannZeta(s) = 0
  -> s != 1
  -> sourceNotPole(s).
```

Meaning:

Mathlib's RH predicate excludes `s=1` in a separate hypothesis. The bridge must
not assume the pole exclusion follows from the negative-even exclusion.

Evidence used:

```text
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:168-169
docs/proofs/rh-definition-bridge-spine-discharge.md:200-225
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md:140-198
```

Blocked shortcut:

```text
s is non-trivial
```

with no explicit `s != 1` theorem.

## Contract Theorem 5. Mathlib Hypotheses To Source Non-Trivial Zero

Target:

```text
MathlibHypothesesToSourceNontrivialZero:
  riemannZeta(s) = 0
  -> not (exists n : Nat, s = -2 * (n + 1))
  -> s != 1
  -> sourceNontrivialZero(s).
```

Meaning:

The forward proof of `_root_.RiemannHypothesis` starts with Mathlib's
hypotheses. The bridge must turn those hypotheses into the source
non-trivial-zero input consumed by CC20 source RH.

Evidence used:

```text
docs/proofs/rh-definition-bridge-spine-discharge.md:261-295
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md:248-282
```

Blocked shortcut:

```text
CC20SourceRH applies to s
```

without constructing the source non-trivial-zero witness from Mathlib's three
hypotheses.

## Contract Theorem 6. Critical Line Equivalence

Target:

```text
SourceCriticalLineIffReEqHalf:
  sourceCriticalLine(s) <-> s.re = 1/2.
```

Meaning:

The route may use a centered Mellin coordinate such as `z=1/2-it` internally.
The final Mathlib predicate concludes `s.re = 1/2`. The bridge must expose the
equivalence.

Evidence used:

```text
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:168-169
docs/proofs/rh-definition-bridge-spine-discharge.md:227-259
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md:206-245
```

Blocked shortcut:

```text
s lies on the critical line
```

with no theorem producing `s.re = 1/2`.

## Contract Theorem 7. Source RH Implies Mathlib RH

Target:

```text
SourceRHImpliesMathlibRH:
  CC20SourceRH -> _root_.RiemannHypothesis.
```

Required proof order:

```text
take s
take hzero : riemannZeta(s)=0
take hneg : not exists n, s=-2*(n+1)
take hpole : s != 1
derive sourceNontrivialZero(s)
apply CC20SourceRH
rewrite sourceCriticalLine(s) to s.re=1/2
```

Meaning:

The final route needs the forward direction. It must consume Mathlib's
hypotheses in Mathlib's order and return Mathlib's conclusion.

Evidence used:

```text
ConnesWeilRH/Route/RouteTheorem.lean:26-33
docs/proofs/rh-definition-bridge-spine-discharge.md:261-327
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md:248-282
```

Blocked shortcut:

```text
CC20SourceRH = _root_.RiemannHypothesis
```

as a name-level rewrite.

## Contract Theorem 8. Mathlib RH Implies Source RH

Target:

```text
MathlibRHImpliesSourceRH:
  _root_.RiemannHypothesis -> CC20SourceRH.
```

Meaning:

The route does not need this theorem to exit to Mathlib. It remains useful for
definition audit because it proves the bridge is not one-way by accident.

Evidence used:

```text
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md:285-320
```

Blocked shortcut:

```text
definition audit passes by forward implication only
```

when a later review needs equivalence of the source and Mathlib predicates.

## Combined Contract

The formal/import target for this gate is:

```text
RHDefinitionBridgeContract:
  SourceZetaEqualsMathlibZeta
  SourceZeroToMathlibZero
  MathlibZeroToSourceZero
  SourceNontrivialZeroNoNegativeEven
  SourceNontrivialZeroNoPole
  MathlibHypothesesToSourceNontrivialZero
  SourceCriticalLineIffReEqHalf
  SourceRHImpliesMathlibRH
  MathlibRHImpliesSourceRH
```

Projection target:

```text
RHDefinitionBridgeContract
  ->
RHDefinitionBridgeSpine.
```

Route consumption target:

```text
RHDefinitionBridgeContract
  ->
CC20 source RH may close _root_.RiemannHypothesis.
```

only through:

```text
source zeta = Mathlib riemannZeta
  -> source zero = Mathlib zero equation
  -> source non-trivial zero = Mathlib zero plus exclusions
  -> source critical line = s.re = 1/2
  -> CC20SourceRH -> _root_.RiemannHypothesis.
```

## Import Acceptance Checklist

A source import can discharge this contract only if it supplies these items:

| item | required evidence |
|---|---|
| zeta object | theorem equating source zeta with Mathlib `riemannZeta` |
| zero equation | source zero maps to `riemannZeta s = 0` |
| reverse zero leg | Mathlib zero maps to source zero when applying source RH |
| negative-even exclusion | source non-trivial zero excludes `s=-2*(n+1)` |
| pole exclusion | source non-trivial zero excludes `s=1` |
| source non-trivial witness | Mathlib zero plus exclusions builds source non-trivial zero |
| critical line | source critical line is `s.re = 1/2` |
| forward exit | `CC20SourceRH -> _root_.RiemannHypothesis` |
| reverse audit | `_root_.RiemannHypothesis -> CC20SourceRH` or a documented reason it is not needed |

If an import supplies only a theorem named `RH`, it fails this contract.

## Lean Interface Consequence

A later Lean interface should define a structure with fields equivalent to the
combined contract. The compact current field:

```text
sourceRH_to_mathlibRH
```

should become a projection from that structure. It should not remain primitive
source evidence.

The first Lean pass may keep theorem bodies as source-interface assumptions.
It must still expose the names above so that `#print axioms` shows exactly
which RH-definition source contracts the final route consumes.

## Current Judgment

| question | answer |
|---|---|
| Does this contract prove RH? | no |
| Does it specify the theorem shape needed to discharge the RH definition gate? | yes |
| Does it prove the RH definition bridge at route-evidence level? | yes, via `docs/proofs/rh-definition-bridge-proof-package.md` |
| Does it target Mathlib's canonical `_root_.RiemannHypothesis`? | yes |
| Does it expose the Mathlib zero equation? | yes |
| Does it expose negative-even and pole exclusions separately? | yes |
| Does it expose critical line as `s.re = 1/2`? | yes |
| Can a later Lean/source-import pass use this as a checklist? | yes |

The RH definition gate now has a route-evidence proof package. The next work is
accepted-source or Lean discharge for the same named theorem targets.
