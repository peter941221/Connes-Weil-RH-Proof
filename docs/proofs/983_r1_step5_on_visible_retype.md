# 983 — R1 Step5: the on-visible arithmetic normalization re-type seam

Status: execution record.  RH NOT claimed.

## Goal

The 653 wall in `FixedLambdaFinitePrimeArithmeticCertificate.atomsWithSourceTest`
demands a `∀ n : ℕ` normalization
(`SourceFinitePrimeArithmeticNormalizationForSourceTest`) whose leaf requires
`IsPrimePow n` at every `n` including composites — uninhabitable.  The
documented re-type is: make the arithmetic live over the FINITE visible
indices, keyed by `sourceTest.sourceAtomVisible n`, instead of a bare `∀n`.

## Result — axiom-clean

`Dev/R1Step5Probe983.lean` (build 2952 jobs green, `#print axioms` =
`[propext, Classical.choice, Quot.sound]`, 0 sorry):

- `visibleFromReduce : SourceVisibleFinitePrimeArithmeticData W0 f0 f0 sourceIface`
  — the on-visible arithmetic supplied by the reduce-lane `gd` (probe 982),
  keyed by the source-visible predicate.
- `visible_mem (n : ℕ) (hn : sourceIface.sourceAtomVisible n) : n ∈ W0.globalPrimeIndexSet`
  — the membership guard: visible at the square → membership in the exact `{2}`.
- `visibleFromReduce_at_two` : at the visible prime `2`, the on-visible object
  agrees `rfl`-level with the direct on-`{2}` object.

The `visible_mem` guard is built from the concrete additive carrier's exact
support:

```
visible at square (f0+f0)
   └─ (f0+f0) x = 2 • f0 x   (additive carrier, convolutionStar = +)
   └─ term n (f0+f0) ≠ 0  ⟺  term n f0 ≠ 0        [sourceFinitePrimeTerm_square_ne_zero_iff]
   └─ forward_mem pins n = 2                          [ConcreteP1SupportProbe.forward_mem]
   └─ globalSetTwo gives 2 ∈ {2} = W0.globalPrimeIndexSet
```

## The key insight

On the concrete additive carrier, `(f0 + f0) x = 2 • f0 x`.  So the evaluation
value at the square is twice the bare value, the finite-prime terms share the
same support, and the visible atom at the square is exactly the bare bump's.
This makes the *finite* on-visible arithmetic
(`SourceVisibleFinitePrimeArithmeticData`) constructible from the reduce-lane
`gd` object, with the guard `visible → membership` proved from the exact
`{2}` index set.

## Honest scope

- This constructs the **on-visible** restriction of the arithmetic — the prime
  data any `∀n` normalization would project onto.  It does NOT construct a
  `∀ n : ℕ` normalization over all naturals (that remains the 653 wall, needing
  the on-index-set finite-conjunction re-type of the *structure field* itself).
- Carrier-specific: relies on the additive concrete carrier.
- No RH, no new axiom.

## Next steps

1. Re-type `FixedLambdaArithmeticCertificateSourceTestData.atoms` field to
   the on-index-set finite conjunction (the actual 653 structure change).
2. Feed `visibleFromReduce`/`gd_reduce_global_sum_positive` into the
   `CommonFinitePrimeArithmeticSourceData` / `ccm25ArithmeticPackage` rows.
3. Assemble the R1 `FullWeilPositivity` witness (979/980/981 + 982/983) →
   L1552 C1→RH exit.