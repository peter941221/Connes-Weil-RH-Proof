# Proof 793: Completed physical one-prime difference

## Result

Let `K_S` be the literal completed Hardy--prolate Hermitian trace used by the
Gate-facing physical readout.  Lean first proves

```text
K_S = - Re Tr(B_S).
```

Combining this with Proof 792 gives the physical one-prime identity

```text
K_(p::S) - K_S
  = - Re Tr(C_(p,S)) + Re Tr(R_(p::S) - R_S).          (793.1)
```

Every quantity in `(793.1)` is the actual source object.  In particular,
`K_S` is not an auxiliary finite-list model or an independently cycled trace.

## Why It Matters

This is the same completed outer/reflected-second-support/prolate scalar that
Proof 788 requires to have lower-factor-square decay.  The candidate
cancellation now occurs inside that literal physical scalar.

```text
completed physical K increment
        |
        +-- negative Markov trace
        |
        +-- completed remainder trace
```

The two branches remain coupled until compact root support has been applied.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovCompletedPhysicalDifference.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovCompletedPhysicalDifferenceAudit.lean
```

Key declaration:

```text
completePhysicalHermitianTrace_re_sub_eq_neg_coboundary_re_add_remainder
```

## Scope

Equation `(793.1)` is an exact identity, not a support-polynomial estimate.
It does not prove Gate 3U, the finite-S sign, Burnol's identity, or RH.
