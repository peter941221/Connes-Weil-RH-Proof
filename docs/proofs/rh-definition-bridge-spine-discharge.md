# RH Definition Bridge Spine Discharge

Status: proof package for the source-RH-to-Mathlib-RH definition spine.

This package attacks the fifth remaining formal gate from:

```text
docs/audits/source-interface-discharge-completion-audit.md
```

The gate is:

```text
RH definition bridge
```

The package does not formalize Mathlib or CC20 inside Lean. It records the
definition-level theorem chain that a later source-import or Lean pass must
expose before the CC20 source conclusion can count as Mathlib's canonical:

```text
_root_.RiemannHypothesis.
```

The stronger formal/import theorem contract is:

```text
docs/proofs/rh-definition-bridge-theorem-contract.md
```

It names the theorem targets that must replace this proof-package spine before
the RH definition bridge gate can count as discharged.

## Evidence Boundary

| object | evidence |
|---|---|
| existing source-to-Mathlib bridge | `docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md` |
| CC20 RH-exit object package | `docs/proofs/cc20-rh-exit-object-normalization-discharge.md` |
| CC20 finite-vanishing exit package | `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md` |
| Mathlib RH definition | `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:166-169` |
| Mathlib trivial zero theorem | `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:156-158` |
| route final theorem target | `ConnesWeilRH/Route/RouteTheorem.lean:26-33` |
| project RH abbreviation | `ConnesWeilRH/Basic.lean:18-23` |
| source-object definition ledger | `docs/audits/source-object-definition-ledger.md:149-174` |

## Target Statement

The RH definition bridge target is:

```text
RHDefinitionBridgeSpine:
  CC20 source RH
    ->
  Mathlib's _root_.RiemannHypothesis
```

where Mathlib's predicate is:

```text
forall s : Complex,
  riemannZeta s = 0 ->
  not (exists n : Nat, s = -2 * (n + 1)) ->
  s != 1 ->
  s.re = 1/2.
```

Evidence:

```text
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:166-169
```

The dependency order is:

```text
CC20 source RH conclusion
      |
      v
source zeta object
      |
      v
Mathlib riemannZeta
      |
      v
source non-trivial-zero predicate
      |
      v
Mathlib zero plus negative-even and pole exclusions
      |
      v
source critical-line predicate
      |
      v
Mathlib equation s.re = 1/2
      |
      v
_root_.RiemannHypothesis
```

The key rule is:

```text
"RH" is not a theorem target until its zeta, zero, exclusions, and line are
transported.
```

## Lemma 1. Zeta Object Is Transported First

Statement:

```text
SourceZetaTransport(s):
  sourceZeta s = riemannZeta s.
```

Proof.

CC20 Proposition C.1 states the conclusion for the Riemann zeta function and
its non-trivial zeros. Mathlib's target predicate uses the concrete object:

```text
riemannZeta.
```

The formal bridge must therefore expose a theorem tying the source zeta object
to Mathlib's object before it translates zeros. A proof cannot start from a
source zero predicate and silently treat it as:

```text
riemannZeta s = 0.
```

Failure blocked:

```text
the route proves RH for a source-named zeta object while the final theorem
claims Mathlib's riemannZeta.
```

## Lemma 2. Zero Predicate Includes The Mathlib Zero Equation

Statement:

```text
SourceZeroToMathlibZero(s):
  sourceZetaZero s -> riemannZeta s = 0.
```

Proof.

After Lemma 1, a source zeta zero becomes a Mathlib zeta zero. The bridge should
name this theorem separately from the non-trivial-zero exclusions. The equation:

```text
riemannZeta s = 0
```

is the first hypothesis in Mathlib's `RiemannHypothesis` predicate.

Failure blocked:

```text
the proof transports exclusions and critical-line language but never proves
the Mathlib zero equation.
```

## Lemma 3. Non-Trivial Means Negative-Even Exclusion

Statement:

```text
SourceNontrivialZeroNoNegativeEven(s):
  sourceNontrivialZero s
    ->
  not (exists n : Nat, s = -2 * (n + 1)).
```

Proof.

Mathlib excludes the trivial zeros by the second hypothesis:

```text
not (exists n : Nat, s = -2 * (n + 1)).
```

It also records the negative even zeros:

```text
riemannZeta (-2 * (n + 1)) = 0.
```

Evidence:

```text
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:156-169
```

CC20's phrase "non-trivial zero" must unpack to this exclusion. The bridge
should not rely on the English word "non-trivial" once it enters Lean.

Failure blocked:

```text
a source zero is treated as non-trivial while still matching a Mathlib
negative-even trivial zero.
```

## Lemma 4. Non-Trivial Also Excludes The Pole At s=1

Statement:

```text
SourceNontrivialZeroNoPole(s):
  sourceNontrivialZero s -> s != 1.
```

Proof.

Mathlib's predicate has a separate pole exclusion:

```text
s != 1.
```

The source zeta theory excludes the pole from the non-trivial zero set. The
bridge must make that exclusion explicit because Mathlib does not fold it into
the negative-even trivial-zero hypothesis.

Failure blocked:

```text
the source zero predicate and Mathlib RH disagree at the pole-exclusion input.
```

## Lemma 5. Critical Line Is The Mathlib Real-Part Equation

Statement:

```text
SourceCriticalLineToMathlib(s):
  sourceCriticalLine s <-> s.re = 1/2.
```

Proof.

Mathlib concludes:

```text
s.re = 1/2.
```

The source route uses the standard critical line, and the Mellin-coordinate
translation uses:

```text
z = 1/2 - i t.
```

The final theorem cannot keep the centered route coordinate. It must conclude
the Mathlib real-part equation.

Failure blocked:

```text
the route proves that a centered coordinate vanishes on a line while Mathlib
requires the real part of s to equal 1/2.
```

## Lemma 6. Source RH Supplies Mathlib RH In Definition Order

Statement:

```text
SourceRHToMathlibRHSpine:
  CC20SourceRH -> _root_.RiemannHypothesis.
```

Proof.

Assume CC20 source RH. To prove Mathlib RH, take an arbitrary complex number
`s` with Mathlib's three hypotheses:

```text
riemannZeta s = 0
not (exists n : Nat, s = -2 * (n + 1))
s != 1.
```

The reverse directions of Lemmas 1 through 4 identify `s` as a CC20 source
non-trivial zero. CC20 source RH gives the source critical-line statement.
Lemma 5 rewrites it as:

```text
s.re = 1/2.
```

This proves:

```text
_root_.RiemannHypothesis.
```

The proof order must match Mathlib's definition. The final bridge should not
consume a bundled proposition:

```text
sourceRH_to_mathlibRH : Prop.
```

It should expose the zeta, zero, exclusion, and critical-line components.

Failure blocked:

```text
the final route concludes a source-named RH theorem and relies on naming
similarity to satisfy Mathlib RH.
```

## Combined Result

Combining Lemmas 1 through 6 gives:

```text
RHDefinitionBridgeSpine
```

with these Lean-facing theorem targets:

```text
SourceZetaEqualsMathlibZeta
SourceZeroToMathlibZero
SourceNontrivialZeroNoNegativeEven
SourceNontrivialZeroNoPole
SourceCriticalLineIffReEqHalf
SourceRHImpliesMathlibRH
```

This strengthens the older package:

```text
SourceRHToMathlibRH.
```

The older package proves the bridge at proof-package level. This package fixes
the theorem targets and the order in which the final Lean/import pass must use
them.

## Formalization Consequence

A later Lean interface should not expose only:

```text
sourceRH_to_mathlibRH : SourceRH -> _root_.RiemannHypothesis
```

as final evidence.

It should expose a package shaped like:

```text
RHDefinitionBridge
  +-- sourceZeta_eq_riemannZeta
  +-- sourceZero_iff_riemannZeta_zero
  +-- sourceNontrivialZero_no_negative_even
  +-- sourceNontrivialZero_no_pole_one
  +-- sourceCriticalLine_iff_re_eq_half
  +-- sourceRH_implies_mathlibRH
```

Then the compact CC20 exit package can consume the derived Mathlib target.

## Remaining Boundary

| task | reason |
|---|---|
| define the CC20 source zeta object in Lean or import it | the bridge needs an object on the source side |
| formalize source non-trivial-zero equivalence | the phrase must unpack to Mathlib zero plus exclusions |
| formalize the pole exclusion | Mathlib has `s != 1` as a separate hypothesis |
| formalize the critical-line equivalence | the final target is `s.re = 1/2` |
| audit the final axiom boundary after implementation | no route-local RH axiom may replace the bridge |

This package does not prove RH. It removes the final naming loophole: the route
may use the CC20 source conclusion only after it transports that conclusion to
Mathlib's exact RH predicate.
