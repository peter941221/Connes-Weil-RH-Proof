# Proof 800: Finite-S permutation invariance

Date: 2026-08-03

Status: axiom-clean representation invariance. This proof does not estimate
the Gate 3U scalar.

## Problem

`FinitePrimePowerFamily.visiblePrimes` is derived with `Finset.toList`:

```lean
(family.terms.attach.image fun pm => ...).toList
```

The order is a `Multiset.out` choice. Deleting a term can therefore produce a
list that is a permutation of the expected suffix rather than that suffix as
a literal list.

Source definitions:

```text
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSProjectionTrace.lean:46-53
.lake/packages/mathlib/Mathlib/Data/Multiset/Basic.lean:33-38
```

## Result

For `first.visiblePrimes.Perm second.visiblePrimes`, Lean proves equality of:

```text
finiteEulerFrame
finiteEulerGramInv
sourceBandGramResponse
rawCompletePhysicalHermitianTrace.
```

It also proves the literal-list invariances needed by the causal ledger:

```text
finiteEulerLowerFactor(S) = finiteEulerLowerFactor(T)
normalizedFiniteEulerInverseList(S) = normalizedFiniteEulerInverseList(T)
normalizedListActualBandSoninResponse(S)
  = normalizedListActualBandSoninResponse(T).
```

Lean owners:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovPermutationInvariance.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovPermutationInvarianceAudit.lean
```

## Scope

Permutation invariance identifies different list representatives of one
finite place set. It does not bound the completed forcing, prove the finite-S
sign, prove Burnol's identity, or prove `_root_.RiemannHypothesis`.
