# Proof 802: Canonical raw permutation chain

Date: 2026-08-03

Status: axiom-clean canonical-chain construction and Gate readout. The raw
signed sum remains unbounded by the current source theory.

## Result

The canonical selected family now has a concrete finite deletion tower:

```text
canonical family
        |
        | delete all p-power terms at each head p
        v
actual permutation-aware family chain
        |
        v
signed raw forcing sum.
```

Lean proves:

```text
rawCompletePhysicalHermitianTrace(canonicalFamily)
  = rawCompletePhysicalPermutationForcingChain(canonical chain),

canonicalRealGate3UAt(owner, lambda, basis, bound)
  <->
abs(rawCompletePhysicalPermutationForcingChain(canonical chain)) <= bound.
```

The chain is recursively indexed by a literal target list while each stored
family carries only a `List.Perm` proof. It never assumes that
`Finset.toList` exposes a literal suffix.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovRawPermutationCumulativeLedger.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovRawPermutationCumulativeLedgerAudit.lean
```

Key declarations:

```text
rawCompletePhysicalPermutationFamilyChainOf
rawCompletePhysicalHermitianTrace_canonical_eq_permutationForcingChain
canonicalRealGate3UAt_iff_abs_permutationForcingChain_le
```

## Scope

This closes the canonical-chain producer missing from Proofs 798--799. It
does not supply the support-polynomial bound for the signed forcing sum, the
finite-S sign, Burnol's identity, or `_root_.RiemannHypothesis`.
