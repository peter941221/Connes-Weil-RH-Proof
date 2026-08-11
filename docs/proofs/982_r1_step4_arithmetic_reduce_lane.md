# 982 — R1 Step4: the on-`{2}` arithmetic package reduce-lane seam (definitional)

Status: execution record.  RH NOT claimed.

## Goal

Attacking L653 (the `ccm25ArithmeticPackage` / fixed-lambda finite-prime
arithmetic bottom), the documented 922 reduce-lane is: from `E :
SourceEvaluationData` build the on-`{2}` global arithmetic
`SourceGlobalFinitePrimeArithmeticData W f f` WITHOUT building a
`∀ n : ℕ` normalization (the 653 wall).

`L657DiagProbe` already built the on-`{2}` global arithmetic `gd` directly from
the per-`2` atom.  This step proves the same global arithmetic can be rebuilt
through `SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData`
(the pairing / weight / term read-offs at the convolution square) and that the
two objects agree at the prime `2` **definitionally**.

## Result — axiom-clean

`Dev/R1Step4Probe982.lean` (build `2951` jobs green, `#print axioms` =
`[propext, Classical.choice, Quot.sound]`, 0 sorry):

- `gd_reduce : SourceGlobalFinitePrimeArithmeticData W0 f0 f0` — the same data
  carried by the reduce-lane `ofSourceEvaluationData`, with membership witnesses
  discharged by the exact index set `{2}`.
- `gd_reduce_at (n : ℕ) (hn : n ∈ W0.globalPrimeIndexSet)` :
  `(gd_reduce.atIndex n hn) = (gd.atIndex n hn)` — the `rfl` seam: at every
  member of the exact index set, the reduce-lane arithmetic is the SAME object
  as the direct per-`2` atom.
- `gd_reduce_at_two (h : 2 ∈ W0.globalPrimeIndexSet)` : the seam at the prime.
- `gd_reduce_sMaxSum_eq_gd_maxSum` — the `MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet`
  of the reduce-lane object equals the direct object's.
- `gd_reduce_global_sum_positive` : `0 < … gd_reduce` — the reduce-lane global
  sum is strictly positive at the prime `2`.

All four lemmas `#print axioms = [propext, Classical.choice, Quot.sound]`.

## The key fact: only the exact index set matters

The `ofSourceEvaluationData` reduce-lane needs, per member `n`:

| Row | Requirement | How closed |
|---|---|---|
| `sourcePrimePowerIndex` | `n ∈ indexSet → IsPrimePow n` | `globalSetTwo` (`W0.globalPrimeIndexSet = {2}`) forces `n = 2`; `Nat.prime_2.isPrimePow` |
| `visible` | `n ∈ indexSet → AtomVisible(W, _)` | `globalSetTwo` → subst; `visible_two` (bump square at 2 nonzero) |
| `pairingReadOff`, `weightReadOff`, `termReadOff` | arithmetic at `2` | `rfl` on the concrete carrier (L657DiagProbe does the same) |

So the entire on-`{2}` arithmetic is constructible without needing a `∀ n`
normalization.  The global sum over the singleton `{2}` is positive because the
per-`2` term is positive (`Λ(2) > 0`, value `2` at the square).

## Honest scope

- This CLOSES per-index arithmetic; the remaining L653 wall is the certificate's
  `∀ n` `atomsWithSourceTest`
  (`SourceFinitePrimeArithmeticNormalizationForSourceTest`,
  `PrimePowerArithmetic.lean:293`).  The seam here is the concrete per-`{2}`
  evidence any re-type of that field will need — but it does NOT itself construct
  the `∀ n` normalization.
- Concretely: this proof is on the concrete additive carrier
  (`convolutionStar = +`), where the square of the bump is visible at `2`.
  On the ambient Schwarz carrier (fourier convolution) the square is NOT visible,
  so the reduce-lane is carrier-specific — it does not claim a general Mellin
  carrier version.
- No RH, no new axiom.

## Next steps

1. Re-type `FixedLambdaArithmeticCertificateSourceTestData.atoms` to
   `SourceFinitePrimeArithmeticDataOnIndexSet` (finite conjunction over
   `{globalPrimeIndexSet}`), exactly the 653-re-type of memory `653-retype-verdict`.
2. Wire `gd_reduce_global_sum_positive` into the certificate
   `commonFinitePrimeArithmeticSourceData` / `finitePrimeCerificateRows` assembly.
3. Assemble the R1 `FullWeilPositivity` witness (979/980/981 + this) and the
   `ccm25ArithmeticPackage` l2 row.