# Proof 803: Raw forcing deletion-order invariance

Date: 2026-08-03

Status: axiom-clean endpoint-potential identity. It provides no analytic
estimate for the raw signed forcing sum.

## Result

Let a permutation-aware deletion chain store the actual finite prime-power
family at each node. Its raw forcing scalar is the finite signed sum

```text
ForcingChain = sum over prime-block deletions of
  [-Re Tr(MarkovCoboundary) + Re Tr(CompletedRemainderIncrement)].
```

If two such chains start from families whose visible-prime lists are
permutations, Lean proves that their complete forcing sums are equal:

```text
same root visible-prime set
        |
        v
any compatible deletion order
        |
        v
the same complete signed raw forcing sum.
```

For the canonical selected family, this yields the Gate readout in every
chosen target-list order:

```text
canonicalRealGate3UAt(owner, lambda, basis, bound)
<->
abs(raw forcing sum in the chosen compatible order) <= bound.
```

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovRawPermutationOrderInvariance.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovRawPermutationOrderInvarianceAudit.lean
```

Key declarations:

```text
rawCompletePhysicalPermutationForcingChain_eq_of_root_visiblePrimes_perm
rawCompletePhysicalPermutationForcingChain_eq_of_targetList_perm
canonicalRawPermutationForcingChain_eq_of_order
canonicalRealGate3UAt_iff_abs_permutationForcingChainOf_le
```

## Scope

This is order freedom, not analytic cancellation. It authorizes a future
compact-support-first proof to choose a support-adapted deletion order, but it
does not bound an individual forcing, does not permit branchwise absolute
values, and does not prove the support-polynomial Gate 3U estimate, the
finite-S sign, Burnol's identity, or `_root_.RiemannHypothesis`.
