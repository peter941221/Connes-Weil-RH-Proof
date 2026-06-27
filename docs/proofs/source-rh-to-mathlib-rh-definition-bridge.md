# Source RH To Mathlib RH Definition Bridge

Status: proof package for the final definition bridge between the CC20 source
criterion and Mathlib's canonical `RiemannHypothesis`.

This package attacks the remaining definition-drift risk in the final route:

```text
CC20 Proposition C.1 concludes "RH"
```

while the Lean theorem must conclude:

```text
_root_.RiemannHypothesis
```

The bridge must prove that these are the same predicate after fixing the zeta
function, zero set, trivial-zero exclusion, pole exclusion, and critical-line
coordinate.

## Evidence Boundary

Local Mathlib source:

```text
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:146-168
```

CC20 source package:

```text
https://arxiv.org/e-print/2006.13771
```

Relevant source file:

```text
weil-compo.tex
```

| claim | evidence |
|---|---|
| Mathlib zeta analytic-continuation object is `riemannZeta` | `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:146-154` |
| Mathlib records trivial zeros `riemannZeta (-2 * (n + 1)) = 0` | `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:156-158` |
| Mathlib canonical RH predicate | `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:165-168` |
| CC20 Proposition C.1 uses the set `Z` of non-trivial zeros | `weil-compo.tex:2075-2078` |
| route final theorem targets Mathlib RH | `ConnesWeilRH/Route/RouteTheorem.lean:24-33` |
| project wrapper is definitional | `ConnesWeilRH/Basic.lean:18-23` |
| current exit package leaves this bridge open | `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md:393-405` |

## Target Statement

The source-to-Mathlib definition bridge is:

```text
SourceRHToMathlibRH:
  CC20_RH_source
    ->
  _root_.RiemannHypothesis.
```

where `CC20_RH_source` means:

```text
every non-trivial zero rho of the source Riemann zeta function lies on
the critical line Re(rho)=1/2.
```

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
```

## Lemma 1. Same Zeta Function

Statement:

```text
SourceZetaEqualsMathlibZeta:
  the source zeta function in CC20 Proposition C.1 is Mathlib's
  analytic-continuation function `riemannZeta`.
```

Proof.

CC20 Proposition C.1 refers to:

```text
the Riemann zeta function
```

and its non-trivial zeros:

```text
weil-compo.tex:2075-2078
```

Mathlib's file defines and uses:

```text
riemannZeta
```

as the analytic-continuation zeta function, with supporting lemmas for
differentiability away from `s=1`, the value at `0`, and the functional
equation:

```text
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:146-164
```

Therefore a formal bridge should introduce a theorem-source equality or
definition bridge:

```text
sourceZeta s = riemannZeta s.
```

This lemma is not optional. Without it, a proof could conclude RH for a
source-named zeta object while the Lean theorem targets Mathlib's zeta object.

## Lemma 2. Same Trivial-Zero Exclusion

Statement:

```text
SourceNontrivialZeroToMathlibHypotheses(s):
  if s is a CC20 non-trivial zero, then Mathlib's two exclusion hypotheses hold:

    not (exists n, s = -2 * (n + 1))
    s != 1.
```

Proof.

Mathlib's RH predicate quantifies over all zeroes and excludes the trivial
zeros with:

```text
not exists n : Nat, s = -2 * (n + 1).
```

It separately assumes:

```text
s != 1.
```

Evidence:

```text
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:165-168
```

Mathlib also proves the negative even zeros:

```text
riemannZeta (-2 * (n + 1)) = 0.
```

Evidence:

```text
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:156-158
```

CC20's phrase "non-trivial zeros" in Proposition C.1 excludes those negative
even trivial zeros. The point `1` is a pole of the zeta function in the source
theory and Mathlib's RH predicate excludes it directly.

Thus the bridge must map:

```text
s in Z_source
```

to:

```text
riemannZeta s = 0,
not exists n, s = -2 * (n + 1),
s != 1.
```

The formal statement should not rely on the phrase "non-trivial" without this
unpacking.

## Lemma 3. Same Critical Line

Statement:

```text
SourceCriticalLineEqualsMathlibReHalf(s):
  the source statement "s lies on the critical line" is Mathlib's equation
  s.re = 1/2.
```

Proof.

Mathlib's predicate concludes:

```text
s.re = 1 / 2.
```

Evidence:

```text
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:165-168
```

CC20 Proposition C.1 works with non-trivial zeros of the Riemann zeta function
and states RH in the standard critical-line sense. The route's Mellin
translation already uses the same complex coordinate:

```text
z = 1/2 - i t.
```

Evidence:

```text
docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md:166-226
```

Thus the formal bridge should prove:

```text
sourceCriticalLine s <-> s.re = 1/2.
```

No centered `t`-coordinate may appear in the final Mathlib predicate. The final
target is a statement about the real part of the zero `s`.

## Lemma 4. Source RH Implies Mathlib RH

Statement:

```text
SourceRHImpliesMathlibRH:
  if every CC20 non-trivial zero lies on the source critical line, then
  _root_.RiemannHypothesis.
```

Proof.

Assume `CC20_RH_source`. To prove Mathlib RH, take an arbitrary complex number
`s` with:

```text
riemannZeta s = 0,
not exists n, s = -2 * (n + 1),
s != 1.
```

By Lemma 1, this is a source zeta zero. By Lemma 2, the two exclusions say that
`s` is a source non-trivial zero. Apply `CC20_RH_source` to get the source
critical-line conclusion. Lemma 3 rewrites it as:

```text
s.re = 1/2.
```

This is exactly Mathlib's predicate.

Output:

```text
_root_.RiemannHypothesis.
```

## Lemma 5. Mathlib RH Implies Source RH

Statement:

```text
MathlibRHImpliesSourceRH:
  _root_.RiemannHypothesis -> CC20_RH_source.
```

Proof.

This reverse direction is not needed to finish the route, but it is useful for
definition audit.

Take a source non-trivial zero `rho`. Lemma 1 turns it into a Mathlib zeta zero.
Lemma 2 supplies the Mathlib trivial-zero and pole exclusions. Apply
`_root_.RiemannHypothesis` and then use Lemma 3 to translate:

```text
rho.re = 1/2
```

back into the source critical-line statement.

Output:

```text
CC20_RH_source.
```

## Integrated Definition Bridge

Combining Lemmas 1 through 5 gives:

```text
CC20_RH_source <-> _root_.RiemannHypothesis.
```

For the final route, the required forward direction is:

```text
CC20 Proposition C.1 conclusion
      |
      v
CC20_RH_source
      |
      v
_root_.RiemannHypothesis
```

The dependency graph is:

```text
same zeta function
      |
      v
same zero predicate
      |
      v
same trivial-zero exclusions
      |
      v
same critical-line equation
      |
      v
source RH = Mathlib RH
```

## Formalization Consequence

Before final certification, `FiniteVanishingCriterionPackage` should not hide
the source-to-Mathlib bridge inside:

```text
criterion : input -> ... -> RH
```

without proof fields for:

```text
sourceZeta_eq_mathlibRiemannZeta
sourceNontrivialZero_iff_mathlibZeroWithExclusions
sourceCriticalLine_iff_re_eq_half
```

The current route already targets Mathlib RH directly:

```text
ConnesWeilRH/Route/RouteTheorem.lean:24-33
```

The missing certification work is to replace the abstract CC20 exit package by
a theorem whose conclusion has been transported through this definition bridge.

## Remaining Boundary

This package closes the source-to-Mathlib RH bridge at proof-package level. It
leaves these stronger evidence tasks:

| task | reason |
|---|---|
| formalize `sourceZeta = riemannZeta` | Mathlib and CC20 notation must be tied by theorem, not prose |
| formalize the non-trivial-zero equivalence | the word "non-trivial" must unpack to Mathlib's negative-even exclusion and `s != 1` |
| formalize the critical-line equivalence | the source critical-line statement must become `s.re = 1/2` |

The route remains source-conditional until these definition bridges are proved
or imported.
