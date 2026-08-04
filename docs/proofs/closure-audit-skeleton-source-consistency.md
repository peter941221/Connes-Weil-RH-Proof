# Closure Audit: THE SKELETON'S SOURCE CORE PROVES `False` — A Soundness Break, Not an Open Bottom

Date: 2026-08-04 · Status: **critical (source-level inconsistency)** · Owner lane: RH-skeleton closure audit

## Result

The RH skeleton `Dev/UnconditionalSkeleton.lean` rests at its apex on an axiom
whose *existence claim* is **refuted by a theorem in the same file**.  This is
not merely an open analytic bottom that a future estimate could close — it is a
**soundness container**: the moment the axiom is used, the theory derives
`False`.  A green `unconditional_rh_skeleton : RiemannHypothesis` therefore does
NOT evidence RH; it only reports that RH is derivable in an inconsistent theory
(in Lean, `False` proves anything).

## The contradiction (statement-level, same algebra)

| File:line | Declaration | Statement |
|---|---|---|
| `UnconditionalSkeleton.lean:137` | **axiom** `normalizedCoreSourceWeilFormDataRoot` | `SourceWeilFormData normalizedCoreSourceTestAlgebraFromTheorems` |
| `UnconditionalSkeleton.lean:152-157` | **theorem** `not_nonempty_normalizedCoreSourceWeilFormData` | `¬ Nonempty (SourceWeilFormData normalizedCoreSourceTestAlgebraFromTheorems)` |
| `CCM25SourceDataGuards.lean:30-57` | `not_nonempty_concreteSourceWeilFormData` | `¬ Nonempty (SourceWeilFormData concreteTestAlgebra)` |

Both the axiom and the theorem are over the **same** type argument:

```text
normalizedCoreSourceTestAlgebraFromTheorems = concreteTestAlgebra
                                     (UnconditionalSkeleton.lean:54-56)
```

So from the axiom we get `⟨root⟩ : Nonempty (SourceWeilFormData …)`; applying
`not_nonempty_normalizedCoreSourceWeilFormData ⟨root⟩` yields `False`.

## Why the axiom was needed, and why the library refutes it

`normalizedCoreSourceAnalyticCoreFromTheorems` (an `SourceAnalyticCore` structure,
:318-323) has a required field:

```lean
weilForm := normalizedCoreSourceWeilFormDataFromTheorems   -- = axiom root
```

Without this axiom there is **no** `SourceWeilFormData` to fill the field, so the
entire `SourceAnalyticCore` cannot be built.  The guard
`CCM25SourceDataGuards.not_nonempty_concreteSourceWeilFormData` shows that "build
one for real" is impossible: `sourceFinitePrimeTerm F` is forced to be **zero on
every test** while evaluation reads it as `vonMangoldt p · |v(t)|/√t > 0` at `t = 2`
for a compact smooth bump nonzero at 2.  Finite-prime exact support and the
evaluation are contradictory at the very first prime.

**Field-level culprit (which type must be re-typed).** `SourceWeilFormData` has a
**mandatory** field `finitePrime : SourceFinitePrimeData A evaluation`
(`AnalyticCore.lean:7746-7748`), which in turn carries a mandatory
`exactSupport : SourceFinitePrimeExactSupportData A E` (`:7460-7462`).  That
exact-support record forces the contradiction ring:

```text
sourceVisibleGlobalIndex :  E.sourceFinitePrimeTerm n F ≠ 0 → n ∈ carrier      (:7382)
carrier.2 of globalPrimeIndexCarrier :  n ∈ carrier → E.sourceFinitePrimeTerm n F ≠ 0   (:7364)
```

For a bump test `v` with `v(2) ≠ 0`, `sourceVisibleGlobalIndex` puts `2` in the
carrier; `carrier.2 (0-test) 2` then demands `sourceFinitePrimeTerm 2 0 ≠ 0`,
which `concrete_sourceFinitePrimeTerm_zero` refutes (`:7390-7393`,
`simp`ed since `valueAt` is a `norm`).  The only escape is to make the
**support carrier non-exact** (drop the `F : A.Test` universal quantifier / the
carrier witness), but `exactSupport` is a **structure field, not a field witness**,
so weakening is not a local patch — it is a source-data model re-type.  There is
currently **no** non-axiom construction of `SourceWeilFormData`/`SourceFinitePrimeData`
over `concreteTestAlgebra` in the codebase; every real finite-prime term is read
from `evaluation` (e.g. `FinitePrimeSourceDataBridge.lean:348-357`), i.e. the very
quantity the exact-support ring forces to zero.
(`CCM25SourceDataGuards.lean:38-57`, `AnalyticCore.lean:7390-7412`.)

## Consequence for the RH route

```text
unconditional_rh_skeleton : RiemannHypothesis
    ← rhDefinitionBridgeToMathlibFromTheorems        (:8042-8046)
    ← cc20FiniteVanishingExitFromTheorems            (:8036-8040)
    ← normalizedSelectedFinalRouteSourceRHFrom08AFromTheorems
    ← selected_final_route_detector_criterion_coverage_…
    ← NormalizedContractBackedLane machinery
    ← normalizedCoreSourceAnalyticCoreFromTheorems    (:318-322)
    ← normalizedCoreSourceWeilFormDataFromTheorems     (:141-144 = axiom :137)
    ::  PROVED FALSE by :152 (same type, same algebra)
```

Because :137 feeds the analytic core that feeds every downstream route input,
the inconsistency is at the **root** of the closure, not a leaf.  Every
directive that says "replace each axiom by a real proof" (AGENTS §11/§13) must
therefore first find a **consistent replacement for `SourceWeilFormData`** on
the concrete algebra — i.e. decide what "finite-prime Weil data over the
concrete test algebra" should actually be, before any per-axiom proof can be
trusted.

## What closure would require (honest, no shortcut)

1. **Resolve `SourceWeilFormData` finitely-prime contradiction.** The guard is a
   *math* proof that the current `exactSupport`/`evaluation.sourceFinitePrimeTerm`
   model is inconsistent with evaluation-as-norm. Either:
   - change the concrete evaluation/support model so a real (nonzero-at-2)
     finite-prime term is allowed (new data model → new proof obligations), or
   - drop the finite-prime-exact half and take the finite-prime term from a
     genuinely independent quantity (new analytic content).
   This is *new* route construction, not a Lean reassembly.
2. **Only after (1)** can the remaining ~26 skeleton axioms (`…PackageTermMass`,
   `…FinitePrimeEvaluator`, `…CanonicalSquareTrace…`, `…DetectorCriterionCoverage`,
   etc.) be triaged axiom-by-axiom.
3. `CC20YoshidaDetectorExists`, the detector ladder, is **fully proven**
   (`CC20YoshidaConstruction.lean:2482-2672` via the *proved*
   `weighted_mellin_kernel_log_line_independence` :942), not axiomatized — so it
   is NOT the analytic bottom.  The criterion-coverage axiom :7786 resolves by the
   off-line contradiction guard `CC20RouteRealization.lean:20190-20196`
   (`weilSumPositiveIfOffLine` vs `hopesNonpositive`), consistent with AGENTS's
   "detector-only coverage is not a lower producer".

## Judgment

- **Not blocked-on-a-lemma**: the road stops at a **logical contradiction in the
  imported source material**, which a well-typed `axiom` can wallpaper but cannot
  make true.
- Green build ≠ RH, and here a green build would also be **unsound** unless the
  `axiom` + `not_nonempty_…` pairing is reconciled (removed or one side replaced).
- Ownership: this is a *source-data model* seam, not the physical Gate 3U seam
  that the previous docs tracked.

## Handoff fields

- RH status: **blocked — source-relevant consistency break at `weilForm` field of
  `SourceAnalyticCore` (axiom vs. guard refutation, same algebra)**.
- Files read: `UnconditionalSkeleton`, `CCM25SourceDataGuards`,
  `CC20Yosh` sensor *Declaration*, `CC20RouteRealization`, `AnalyticCore`,
  `Bridge`, `S2B1TraceScale`.
- Declarations changed: none (audit round; no Lean edit).
- Active root: for this round, the `weilForm` field of the source analytic core.
- Build / audit: no build run this round (pure reads + report).
- Next safe action: **(a)** decide the fate of the `weilForm` field — re-type or
  remove, so the skeleton independent of an axiomatized refuted existence claim;
  then **(b)** re-run the closure audit on the remaining roots over a consistent
  core.