# 984 — R1 Step6: the `ccm25ArithmeticPackage` assembly seam is structurally blocked on the concrete `{2}` carrier

Status: execution record (negative result).  RH NOT claimed.  Axiom-clean
(`[propext, Classical.choice, Quot.sound]`, 0 sorry).

## Goal

Feed the reduce-lane arithmetic (982) and the on-visible re-type (983) into
`CommonFinitePrimeArithmeticSourceData` / `ccm25ArithmeticPackage` on the
concrete carrier `W0` (the "wire-in" step of the R1 route toward the arithmetic
`qw`/`psi` sign), then assemble toward the `FullWeilPositivity` exit.

## Result — the assembly seam is **blocked**, axiom-cleanly

`Dev/R1Step6Probe984_assembly.lean` (build 2952 jobs green) proves:

```lean
theorem common_source_data_f0_uninhabited
    (h : CommonFinitePrimeArithmeticSourceData W0)
    (hcomm : h.commonTestFunction = f0) : False

theorem no_common_source_data_with_f0 :
    ¬ (∃ h : CommonFinitePrimeArithmeticSourceData W0, h.commonTestFunction = f0)
```

`CommonFinitePrimeArithmeticSourceData W0` demands a field

```lean
scopedArchimedeanContributionBalance :
  ∀ lambda, ∀ globalData, ∀ restrictedData, balance W0 common lambda globalData restrictedData
```

but probe 983b showed `balance W0 f0 0 gd rd` is refuted (this is precise), so
at `commonTestFunction = f0` the field is uninhabited and the record cannot
be built.  `#print axioms` on both theorems = `[propext, Classical.choice,
Quot.sound]`.

## The two walls the `ccm25ArithmeticPackage` seam crosses

| Seam                         | Content                                                                  | Status on `{2}` carrier |
|------------------------------|--------------------------------------------------------------------------|--------------------------|
| scoped balance leaf           | `CommonFinitePrimeArithmeticSourceData.scopedArchimedeanContributionBalance` (`∀λ ∈ ∀gd ∈ ∀rd`) | **REFUTED** (983b): λ=0 family empty |
| finite-prime arithmetic certs | `FixedLambdaArithmeticSourceTestCertificatesForAllTests = ∀ f g, ... atomsWithSourceTest (∀n IsPrimePow)` | **L653 wall** (∀n uninhabitable at composites) |
| `ConcreteCCM25ArithmeticPackage.rows` needs both |  | blocked on concrete `{2}` |

This **closes** the earlier "wire the reduce-lane into `ccm25ArithmeticPackage`"
target (R1 step-6 original): it is structurally impossible on the concrete
carrier, at TWO independent seams (scoped balance leaf AND all-tests
`∀n`).

## What the reduce-lane DOES provide (still defensive, unaffected)

The 982/983 finite objects remain valid, axiom-clean, finite data-layer
achievements:

- `gd_reduce_global_sum_positive : 0 < Σ over {2}` (982) — the finite-prime
  arithmetic is genuinely non-degenerate at prime `2`.
- `visibleFromReduce : SourceVisibleFinitePrimeArithmeticData` (983) — on-visible
  re-type, membership guard `visible → {2}`.

But neither can be lifted into the infinite/∀n bills (`ccm25ArithmeticPackage`,
`CommonFinitePrimeArithmeticSourceData`) without resolving the L653 structure
retype (the Level-1 on-index-set re-type) or the canonical-Weil sign decision
(847b/912 seam).

## Note on `FullWeilPositivity`

`FullWeilPositivity inputs g L` (Route/Exhaustion) is **arch-trace-driven**
(`FixedSPositiveTraceReadOff `: `CC20PositiveTraceNonnegative` from the 980/981
`(Re arch)^2 ≥ 0`, strictly `>0` at the bump). It does NOT consume the reduce-lane
arithmetic sum; wiring that is a level-mix. The C1 data still gets a
`healthyWeilInput :: Wall2C1InputAssembled` when the strict-diagonal positivity
witness (Wall-1) is fed — that route is already axiom-clean.

## Honest bottom line

- The concrete `{2}` carrier cannot serve as the arithmetic-package base for
  the R1 `qw` sign path: both the scoped-balance leaf and the `∀n`
  finite-atomic family are home of `False` or `∀n` walls.
- The positive, still-live vectors to C1→RH stay:
  1. Re-type `FixedLambdaArithmeticCertificateSourceTestData.atoms` to the
     on-index-set finite conjunction (true 653 structural fix),
  2. the canonical-Weil sign decision (847b/912),
  3. feed the healthy strict-diagonal positivity (already axiom-clean for the
     C1 data) through `healthyCC20C1InputData`.
- RH NOT claimed at any point.

## Next steps

1. Attack (1) — the sole structural fix that unlocks `ccm25ArithmeticPackage`
   (`∀n` → finite conjunction, style 914b).
2. Revisit the `Wall2-1` strict-diagonal route for the C1 exit (already green),
   independent of the arithmetic package.
3. Pull the reduce-lane sum parity into the `qw` sign — only once the
   L653 re-type allows it.