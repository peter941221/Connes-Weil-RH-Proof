# Proof 806: Raw renewal operator ledger

Date: 2026-08-04

Status: axiom-clean operator-level telescoping and order invariance. The
support-polynomial Gate 3U estimate remains open.

## Result

For a permutation-aware finite-prime deletion tower, let `R_T` be Proof 805's
complete inverse-lower-factor physical renewal response. Each raw step is the
signed operator `R_old - R_new`. Proof 806 defines their finite cumulative
operator sum and proves

```text
sum_over_deletion_tower (R_old - R_new) = -R_root.
```

The terminal family has no visible primes, so its renewal response is zero.
The identity is an equality of operators on the actual source Sonin carrier,
before an ordinary trace or real part is taken.

For any two compatible deletion towers whose root lists are permutation
equivalent, Lean also proves their cumulative renewal-response operators are
equal. Under the existing Hardy--prolate pair-data assumptions, the cumulative
operator is trace class and its real ordinary trace is exactly the existing
raw forcing chain.

```text
operator telescope
        |
        v
signed cumulative renewal operator
        |
        v
Re ordinary trace
        |
        v
raw cumulative forcing scalar
```

## Why It Matters

Proofs 803--804 established deletion-order algebra only after reducing to the
real scalar forcing. Proof 806 preserves the complete physical renewal owner
before that reduction. A future compact-support-first argument may therefore
reorder or pair a deletion tower while retaining the operator-level
cancellation, rather than bounding individual steps or physical branches.

## Boundary

The operator telescope is an exact potential identity, not an analytic bound.
It does not control the trace norm of `R_root`, and a uniform absolute bound
for individual deletion steps remains insufficient as their count grows with
the finite family.

Proof 806 does not prove Gate 3U, the finite-S sign, Burnol's identity, or
`_root_.RiemannHypothesis`.

## Lean Owner

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovRawRenewalCumulativeLedger.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovRawRenewalCumulativeLedgerAudit.lean
```

Key declarations:

```text
rawPhysicalRenewalPermutationForcingResponseChain_eq_neg_root
rawPhysicalRenewalPermutationForcingResponseChain_eq_of_root_visiblePrimes_perm
rawCompletePhysicalPermutationForcingChain_eq_rawPhysicalRenewalResponseChainTrace_re
```
