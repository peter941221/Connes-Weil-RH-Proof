# Proof 801: Permutation-aware raw one-prime ledger

Date: 2026-08-03

Status: axiom-clean exact ledger and actual prime-block deletion. No
support-polynomial Gate 3U estimate is proved.

## Result

For actual families with

```text
new.visiblePrimes Perm (p :: S)
old.visiblePrimes Perm S,
```

Lean proves the unchanged raw physical recurrence:

```text
K(new) = K(old) + F(p, S, new, old).
```

`F` is still the one signed recombination

```text
-Re Tr(MarkovCoboundary) + Re Tr(CompletedRemainderIncrement).
```

No branch is bounded independently.

The module also defines `removeVisiblePrime family p` by filtering out every
prime-power term with base `p`, and proves:

```text
visiblePrimes(removeVisiblePrime family p)
  Perm visiblePrimes(family).erase p.
```

If the old visible list represents `p :: S`, the deleted family represents
`S`. This is the exact bridge that the prior literal-tail chain lacked.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovPermutationLedger.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovPermutationLedgerAudit.lean
```

Key declarations:

```text
removeVisiblePrime_visiblePrimes_perm_tail
rawCompletePhysicalHermitianTrace_cons_eq_add_forcing_of_visiblePrimeLists_perm
```

## Scope

This resolves a finite representation obstruction only. The remaining
analytic task is a compact-support-first uniform bound for the complete
signed forcing sum, before taking its first absolute value.
