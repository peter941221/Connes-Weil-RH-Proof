# L653 retype — non-breaking two-step refactor plan (方案A, on-index-set)

Date: 2026-08-09. Type: implementation plan. Author: Claude (Peter's engineer).
Predecessor: `docs/proofs/920_l653_archimedean_retype_verdict.md` (root cause),
route-state 917 (blast radius measured). RH is NOT claimed.

## TL;DR

The redundant, `∀n`-quantified `atoms` field is the sole occupant of the L653
wall. Everything the route actually consumes is `index-set`-keyed. Plan: add the
on-index-set primitive, migrate the 29 consumers, delete the redundant `∀n`
field. Three commits, each building green, non-breaking (835 style).

## Why the `atoms` (∀n) field is removable

`SourceFinitePrimeArithmeticNormalizationForSourceTest` is `∀ n : ℕ. …Data…`,
demanding `IsPrimePow n` at composites/1 → uninhabitable (route 917). But the
two things `atoms` feeds only ever need on-index-set values:

- `SourceFinitePrimeEvaluatorSum W f g indexSet h := ∑ n ∈ indexSet.
  SourceFinitePrimeEvaluatorAtom … (h.atIndex n)` (PrimePowerArithmetic:384-387)
  → ranges over a `Finset`, so only `atIndex n` for `n ∈ indexSet` is used.
- `scopedGlobalBalance`/`scopedArchimedean` already type at the on-index-set
  abbrev `SourceGlobalFinitePrimeArithmeticData` (= `…DataOnIndexSet W f g
  W.globalPrimeIndexSet`) and take it as `globalData`.

The on-index-set analogue already exists as `SourceFinitePrimeArithmeticDataOnIndexSet`
(PrimePowerArithmetic:350) with `atIndex : ∀ n, n ∈ indexSet → …`, `n=2`
feature-complete on the concrete `{2}` via `SourceEvaluationFunctional.ofSourceEvaluationData`
(PrimePowerEvaluationBridge:27-35).

## History sanctioned scope

- `FinitePrimeSourceData.lean`: `atoms : NormalizationForSourceTest` (L207-209)
  used in `DirectAtomVisibleReadOff` / `…FunctionReadOff` (L228-250, keyed on
  `sourceAtomVisible n`, NOT the same index as `globalIndexSet` — needs a
  `routeVisibleGlobalIndex` bridge) and two constructors +
  `[simp]` statements (L404/451/501).
- Ripple (measured 917): `Rows.lean`, `Package.lean`, `Interface.lean`,
  `FormulaComponents.lean`, `FinitePrimeSourceDataBridge.lean`,
  `FinitePrimeInterface.lean`, `FinitePrimeCertificate.lean`,
  `Route/CC20RoueRealization.lean`, `Dev/Parallel09C_…`.

## The non-breaking shape (方案A final)

Keep the `∀n` `SourceFinitePrimeArithmeticNormalization…` type (it appears
~17 files but as a *lower-level* shape). Do NOT delete it. Instead:

**Step 1 — add an on-index-set projection (additive).**
In `PrimePowerArithmetic.lean` add
`SourceFinitePrimeArithmeticDataOnIndexSet.ofNormalization` mirroring the
existing lowering but at the certificate's consumer, plus a bridge lemma that
the evaluator sum over an index set equals the sum over its on-index-set
stuck with the same witness. Nothing changes; new definitions only.

**Step 2 — relax the certificate field (single-site).**
In `FinitePrimeSourceData.lean`, change `FixedLambdaArithmeticCertificateSourceTestData.atoms`'s
type to `SourceGlobalFinitePrimeArithmeticData` (=on-index-set). Fix the
consumers listed, using `onIndexSet.narrow` instead of `atoms.atIndex`.
This localizes the `∀n` demand to only ONE remaining place.

**Step 3 — unbind the remaining `∀n` gate.**
Remove/neutralize the last place that forces `∀n` demand (the `…ForSourceTest`
-typed certificate) so `atoms` no longer needs `IsPrimePow` at every `n`, and
L653's certificate becomes constructible on the concrete `{2}` carrier.

Each step must `lake build` green before the next. This matches 835's
"two (here three) non-destructive steps".

## Execution order / files to touch

| # | step | files |
|---|------|-------|
| 1 | on-index primitive + eval-sum lemmas | PrimePowerArithmetic.lean (+ bridge) |
| 2 | certificate field type swap | FinitePrimeSourceData.lean host + 9 consumer files |
| 3 | remove ∀n demand | FinitePrimeSourceData.lean / bridge |

Each commit: build `lake build ConnesWeilRH` 全绿, WSL cp, note axiom-state.
RH NOT claimed. Each known `#print axioms` unchanged trio unless a Root is
replaced.

## Risks / gates

- `DirectAtomVisibleReadOff` (L228-250) is keyed at `sourceAtomVisible`, which
  is NOT the same index set as `globalPrimeIndexSet` — replacing with the
  on-set projection changes the CONTENT it asserts. Must preserve the original
  statement as a derived `:…` of the new field, else the RHS (visible:
  `atVisibleIndex`) comparison breaks.
- Two `[simp]` theorems (`ofArithmeticSupportSkeleton_atoms`,
  `ofConcreteObject_atoms`) need names/statements adjusted when the field type
  changes; if a consumer pattern-matches the field, it must adapt.
- Semantics of "removing the ∀n demand": the `atomReadOff`/`scopedGlobalData`
  consumer must switch from `.atIndex n (everywhere)` to `.atIndex n (∈globalSet)`
  — this is where `routeVisibleGlobalIndex` provides the `∈globalSet` proof.
- If Step 3 touches `CC20RouteRealization` (the ~30-site), this is the heaviest;
  keep it last and isolated. If after Step 3 L653 still forces a ∀n via the
  `scoped balance` (archimedean λ-independence — 920), that is the REMAINING
  non-cube, separate from this retype (equation-typed, needs the truncated
  redefinition, not a field swap).