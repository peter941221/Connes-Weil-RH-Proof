# RH Definition Bridge Proof Package

Status: route-evidence proof package for transporting the CC20 source RH
conclusion to Mathlib's canonical `_root_.RiemannHypothesis`.

This package proves the project-level target stated in:

```text
docs/proofs/rh-definition-bridge-theorem-contract.md
```

It strengthens and reuses:

```text
docs/proofs/rh-definition-bridge-spine-discharge.md
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md
```

It is not a Lean theorem. It does not formalize CC20's source zero predicate or
Mathlib's zeta theory. It does not prove RH by itself.

## Result

Good result:

```text
RHDefinitionBridgeContract is closed at route-evidence level.
```

Boundary:

```text
Accepted source-import status remains open.
Lean proof status remains open.
CC20 Proposition C.1 remains an imported final-exit theorem.
The RH proof is not complete.
```

## Target

Prove the project bridge:

```text
CC20SourceRH -> _root_.RiemannHypothesis.
```

The bridge must unpack Mathlib's predicate:

```text
forall s,
  riemannZeta s = 0
  -> not (exists n : Nat, s = -2 * (n + 1))
  -> s != 1
  -> s.re = 1 / 2.
```

It must not identify "RH" by name alone.

## Evidence Boundary

| claim | evidence |
|---|---|
| Mathlib RH predicate shape | `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:166-169`; `docs/proofs/rh-definition-bridge-theorem-contract.md` |
| source-to-Mathlib bridge spine | `docs/proofs/rh-definition-bridge-spine-discharge.md` |
| source zeta / zero bridge package | `docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md` |
| CC20 RH-exit object package | `docs/proofs/cc20-rh-exit-object-normalization-discharge.md` |
| route final theorem target | `ConnesWeilRH/Route/RouteTheorem.lean:26-33` |

## Proof Skeleton

```text
Mathlib hypotheses:
  riemannZeta s = 0
  not negative-even trivial zero
  s != 1
        |
        v
source non-trivial zero of source zeta
        |
        v
CC20SourceRH
        |
        v
source critical line
        |
        v
s.re = 1/2
```

## Lemma 1. Source Zeta Is Mathlib Riemann Zeta

Statement:

```text
SourceZetaEqualsMathlibZeta:
  sourceZeta(s) = riemannZeta(s).
```

Proof.

The RH definition contract requires an object-level equality before any zero
transport. The source-to-Mathlib bridge package records that CC20's zeta
object is the Riemann zeta function and that the Lean target uses Mathlib's
`riemannZeta`.

Output:

```text
same_zeta_object
zero_transport_allowed
no_name_only_RH_bridge
```

## Lemma 2. Mathlib Hypotheses Build A Source Non-Trivial Zero

Statement:

```text
MathlibHypothesesToSourceNontrivialZero:
  riemannZeta(s) = 0
  -> not (exists n : Nat, s = -2 * (n + 1))
  -> s != 1
  -> sourceNontrivialZero(s).
```

Proof.

Use Lemma 1 to turn:

```text
riemannZeta(s) = 0
```

into the source zero equation. The negative-even hypothesis excludes the
trivial zeros that Mathlib writes as:

```text
s = -2 * (n + 1).
```

The pole hypothesis:

```text
s != 1
```

excludes the zeta pole. Together these three Mathlib hypotheses are exactly
the source non-trivial-zero input needed by `CC20SourceRH`.

## Lemma 3. Source Critical Line Means `s.re = 1/2`

Statement:

```text
SourceCriticalLineIffReEqHalf:
  sourceCriticalLine(s) <-> s.re = 1 / 2.
```

Proof.

The route sometimes uses centered Mellin variables such as:

```text
z = 1/2 - i t.
```

The final Mathlib predicate does not use that centered notation. It asks for:

```text
s.re = 1 / 2.
```

The definition bridge spine identifies the source critical line with this
Mathlib equation.

## Lemma 4. Source RH Implies Mathlib RH

Statement:

```text
SourceRHImpliesMathlibRH:
  CC20SourceRH -> _root_.RiemannHypothesis.
```

Proof.

Assume:

```text
hRH : CC20SourceRH.
```

To prove Mathlib RH, take an arbitrary `s` with:

```text
hzero : riemannZeta(s) = 0
hneg  : not (exists n : Nat, s = -2 * (n + 1))
hpole : s != 1.
```

By Lemma 2:

```text
sourceNontrivialZero(s).
```

Apply `hRH` to get:

```text
sourceCriticalLine(s).
```

Use Lemma 3 to conclude:

```text
s.re = 1 / 2.
```

This matches Mathlib's predicate exactly.

## Lemma 5. Reverse Audit Direction

Statement:

```text
MathlibRHImpliesSourceRH:
  _root_.RiemannHypothesis -> CC20SourceRH.
```

Proof.

The route does not need this direction to exit. It remains a definition audit:
if a source non-trivial zero supplies a Mathlib zero equation plus the
negative-even and pole exclusions, then Mathlib RH gives `s.re=1/2`, and Lemma
3 transports that result back to the source critical-line predicate.

This blocks an accidental one-way bridge that proves a weaker Mathlib-facing
statement than CC20's source RH.

## Theorem. RH Definition Bridge

Statement:

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
  MathlibRHImpliesSourceRH.
```

Proof.

Combine Lemmas 1 through 5 with the source-zero transport and exclusion
projections recorded in the theorem contract.

The proof uses:

```text
same zeta object,
same zero equation,
negative-even exclusion,
pole exclusion,
source non-trivial-zero construction,
critical-line equivalence,
Mathlib RH predicate order.
```

It does not use:

```text
name-level RH identification,
project-local RH replacement,
or a route-local critical-line predicate.
```

## Output To The Route

This package supplies, at route-evidence level:

```text
RHDefinitionBridgeContract
SourceRHImpliesMathlibRH
MathlibRHImpliesSourceRH
```

It does not supply:

```text
accepted_source_import_discharge
Lean_theorem
CC20PropositionC1Proof
RiemannHypothesis
```

## Current Status

```text
Source zeta equals Mathlib zeta:        route-evidence available
Mathlib zero to source zero:            proved at route-evidence level
Mathlib hypotheses to source zero:      proved at route-evidence level
Critical-line equivalence:              proved at route-evidence level
Source RH implies Mathlib RH:           proved at route-evidence level
Reverse audit direction:                proved at route-evidence level

Accepted source-import status:          open
Lean proof status:                      open
CC20 Proposition C.1 import:            open
RH proof:                               not complete
```
