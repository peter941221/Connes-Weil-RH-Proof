# Quarantined source-carrier rows are blocked by a design-level zero-test contradiction (not merely missing proofs)

> **SUPERSEDED (2026-08-12).** This audit applies to the retired
> global-reverse-support model. The S2 per-common refactor removed the zero-test
> contradiction, and the former `SourceWeilFormData` root now has an axiom-clean
> constructor. See `docs/proofs/835_s2_percommon_refactor_landed.md`. The current
> all-pairs finite-prime and RH-criterion gaps are different obligations.

Date: 2026-08-06
Status: sweep result — the 26 quarantined Dev source inputs rest on a concrete
evaluation carrier that is already inconsistent with the very data they are to
instantiate; not fixable by adding proofs.
Branch: `proof/gate3u-completed-readout`
RELATED: `docs/proofs/812_dev_skeleton_inconsistency.md`,
`external-opinions/003-unconditional-rh-completion-plan.md` (groups A-E)

## Sweep: what the 26 quarantined inputs are

`003-unconditional-rh-completion-plan.md` groups the 26 `Dev/UnconditionalSkeleton`
inputs as:

| Group | model rows                 | count |
|-------|----------------------------|-------|
| A | CCM24 source model         | 5 |
| B | CCM25 source model         | 6 |
| C | CC20/S2-B1 seed + scalars  | 5 |
| D | object/bridge/RH-exit      | 9 |
| E | fixed-test input (triple vanishing) | 1 |

Each is written in `Dev/UnconditionalSkeleton.lean` as a project `axiom` of a
concrete source-model type (the file has 40 such `axiom`s).

## The design-level contradiction

`Source/AnalyticCore.lean:7399`

```
concrete_all_sourceFinitePrimeTerms_zero (E) (S : SourceFinitePrimeExactSupportData … E)
    (F : TestFunction) (n : ℕ) :
    E.sourceFinitePrimeTerm n F = 0
```

Key lemma feeding it (:7390) is `concrete_sourceFinitePrimeTerm_zero`:
`E.sourceFinitePrimeTerm n (0:TestFunction) = 0` — the Von-Mangoldt prime term
evaluates to zero on the **zero test** for every `n`.

`concrete_all_sourceFinitePrimeTerms_zero` then leverages the exact-support
carrier's contract `globalPrimeIndexCarrier.2`, which requires the term to be
nonzero at the *zero* test whenever `n` is in the global carrier (`n ∈
globalPrimeIndexCarrier.1`). Combining "if term ≠ 0 then n in carrier" with
"carrier ⇒ term ≠ 0 at zero test" against "term n 0 = 0" yields `sourceFinitePrimeTerm n F = 0` for all F.

Consequence: any concrete source model whose `SourceFinitePrimeExactSupportData`
demands "every visible test has a nonzero term on every test" is inconsistent
when instantiated on the zero test. The concrete base layer makes Von-Mangoldt
terms vanish on `0 : TestFunction`; the carrier contract requires them nonzero
on `0`. The two are mutually exclusive by design.

`Dev/CCM25SourceDataGuards.not_nonempty_concreteSourceWeilFormData` only spells out
this one (group B) instance; groups A, D and parts of C/E use the same
`SourceFinitePrimeExactSupportData` global-support carrier and are killed by the
same lemma. `Dev/UnconditionalSkeleton.lean` simultaneously posts the positive
`axiom` (:137) and the proved `¬ Nonempty` (:152) — making that Dev theory
inconsistent (`False` derivable).

## Judgment

- These 26 rows rest on a concrete source-evaluation spec whose "all tests
  nonzero in carrier" and "zero test has zero terms" are incompatible.  This is
  a structural model-design question, not a missing-lemma gap.
- No "just add a theorem" completes group A-E as written; and the Dev skeleton
  that reads them is already unsound (see `812`).

## Options (require sign-off, model-boundary changes)

1. Relax the exact-support carrier contract so zero-test does not force nonzero
   terms (change `SourceFinitePrimeExactSupportData` / the concrete base layer's
   global-carrier guarantee).  Blast radius: the finite-prime Weil-form rows that
   depend on the exact-support contract.
2. Make the concrete source never require the carrier on the zero test (guard
   the concrete evaluator), accepting that some finite-prime rows become
   provably `¬Nonempty` and the Weil-form rows move off that carrier.
3. Treat `Dev/UnconditionalSkeleton` as dead quarantine (as `812` does) and
   center RH work on `Source/`+`Route/`, where the open frontier is the
   Proof-717 cancellation + transport-radial defect.

## Judgment

Route forward is option 3; options 1–2 are model redesigns needing owner
sign-off and are out of scope for a sink-fill session.

## Handoff

- RH status: conditional; Dev skeleton quarantined as unsound-see `812`.
- Declarations: none in `Source/`/`Route/` changed.
