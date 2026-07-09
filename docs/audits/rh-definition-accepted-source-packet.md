# RH Definition Accepted-Source Packet

Date: 2026-06-28

Status:

```text
RH definition accepted-source packet started
accepted-source certification: open
Lean status: not touched
```

## Purpose

This packet targets the theorem candidate:

```text
SourceRHToStandardRHTheorem:
  CC20 source RH
  ->
  standard Riemann Hypothesis predicate.
```

For later Lean certification, the standard predicate is Mathlib's:

```text
_root_.RiemannHypothesis
```

The packet prevents the route from treating the phrase "RH" as a definition
bridge.

## Source And Local Anchors

| source | anchors | role |
|---|---|---|
| CC20 source RH conclusion | `weil-compo.tex:2072-2085` | Proposition C.1 conclusion and non-trivial zero set |
| Mathlib zeta object | `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:146-154` | canonical `riemannZeta` object |
| Mathlib trivial zeros | `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:156-158` | negative-even trivial zeros |
| Mathlib RH predicate | `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:165-168` | target predicate shape |
| route target | `ConnesWeilRH/Route/RouteTheorem.lean:24-33` | final theorem target after future Lean work |

## Theorem Shape

The accepted-source theorem must expose these bridges:

```text
SourceZetaEqualsStandardZeta
SourceZeroToStandardZero
StandardZeroToSourceZero
SourceNontrivialZeroNoNegativeEven
SourceNontrivialZeroNoPole
StandardHypothesesToSourceNontrivialZero
SourceCriticalLineIffReEqHalf
SourceRHImpliesStandardRH
```

For Mathlib, the target predicate is:

```text
forall s,
  riemannZeta s = 0
  -> not (exists n : Nat, s = -2 * (n + 1))
  -> s != 1
  -> s.re = 1 / 2.
```

## Certification Chain

| row | theorem candidate | current evidence | accepted-source check |
|---|---|---|---|
| zeta object | `SourceZetaEqualsStandardZeta` | `docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md` | confirm CC20's zeta is the same analytic-continuation object as the standard zeta |
| zero predicate | `SourceZeroIffStandardZeroWithExclusions` | `docs/proofs/rh-definition-bridge-proof-package.md` | confirm source non-trivial zeros match standard zeros after excluding negative-even trivial zeros and the pole at `1` |
| critical line | `SourceCriticalLineIffReEqHalf` | `docs/proofs/rh-definition-bridge-spine-discharge.md` | confirm the source critical line is exactly `s.re = 1/2` |
| source RH to standard RH | `SourceRHImpliesStandardRH` | `docs/proofs/rh-definition-bridge-proof-package.md` | confirm the source conclusion from CC20 Proposition C.1 proves the standard predicate |
| reverse audit direction | `StandardRHImpliesSourceRH` | `docs/proofs/rh-definition-bridge-proof-package.md` | confirm the bridge is not hiding a weaker or stronger zero predicate |

## Rejection Conditions

A reviewer should reject this row if one of these conditions occurs:

```text
1. CC20's zeta object differs from the standard Riemann zeta function;
2. the source non-trivial zero set omits a Mathlib zero hypothesis;
3. negative-even trivial zeros are not excluded in the same way;
4. the pole at s=1 is handled differently;
5. the source critical line is not exactly s.re = 1/2;
6. the final theorem concludes a project-local RH predicate instead of the standard one.
```

## Current Judgment

| question | answer |
|---|---|
| Does this packet make the RH definition bridge accepted-source? | no |
| Does it give an exact accepted-source review packet? | yes |
| What remains? | external acceptance or Lean proof of the zeta, zero-set, exclusion, and critical-line bridges |
| Did this pass touch Lean? | no |

The RH definition bridge now has a review packet. The route should still treat
formal Mathlib equality as future Lean work unless an accepted external proof
certifies the same predicate bridge.
