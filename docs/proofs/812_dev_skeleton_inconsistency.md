# Dev/UnconditionalSkeleton is internally inconsistent (axiom vs ¬Nonempty) and is not the source frontier

> **SUPERSEDED (2026-08-12).** This audit describes the pre-S2
> global-reverse-support model. The S2 per-common refactor removed the empty
> type, and `ConcreteP1SupportProbe.concreteWeilForm` now constructs the former
> L137 type axiom-clean. See `docs/proofs/835_s2_percommon_refactor_landed.md`
> and `Dev/UnconditionalSkeleton.lean`. Keep the analysis below only as history;
> it is not a statement about the current source model.

Date: 2026-08-06
Status: audit finding — quarantined Dev layer is unsound, does NOT enter the main library proof graph
Branch: `proof/gate3u-completed-readout`

## Finding

`ConnesWeilRH/Dev/UnconditionalSkeleton.lean` contains, for the same type
`Source.AnalyticCore.SourceWeilFormData`, both a positive axiom and an
independently-proved negation:

```
:137  axiom normalizedCoreSourceWeilFormDataRoot :
          SourceWeilFormData (normalizedCoreSourceTestAlgebraFromTheorems)
:152  theorem normalizedCoreSourceWeilFormData_not_nonempty :
          ¬ Nonempty (SourceWeilFormData (normalizedCoreTestAlgebraFromTheorems))
          -- proved from CCM25SourceDataGuards.not_nonempty_concreteSourceWeilFormData
```

Line 322 feeds the axiom into `normalizedCoreSourceAnalyticCoreFromTheorems.weilForm`,
so the poisoned input is load-bearing in that Dev `SourceAnalyticCore`.

## Consequence

The theory of `Dev/UnconditionalSkeleton.lean` is **inconsistent**: the axiom
gives `Nonempty P`, the theorem gives `¬ Nonempty P`. From
`(not_nonempty … (Nonempty.intro axiom))` one obtains `False`, hence via `exfalso`
any statement — including the intended `unconditional_rh_contract_skeleton`.
So that Dev route cannot ever validate RH; it is a designed quarantine, not a
provable target.

## Isolation (verified)

- `UnconditionalSkeleton.lean` is imported only by `Dev/UnifiedRemainingGapsRouteAudit.lean`.
- `CCM25SourceDataGuards.lean` is imported only by `UnconditionalSkeleton.lean`.
- `ConnesWeilRH.lean` (the main library root) **does not** import either, so the
  contradiction does not reach the verified `Source/` / `Route/` proof chain.

## Judgment

The unconditional-RH "skeleton" is not the active frontier: it is an
internally-inconsistent development scaffold, quarantined as `Dev/`. Credible RH
work proceeds only in `Source/` + `Route/` + the verified trace front end. The
opened frontier remains the Proof-717 cancellation / transport-radial defect, not
this skeleton.

## Handoff

- RH status: conditional; the unconditional Dev skeleton is unsound-by-design and
  excluded from the proof chain.
- Files: none changed in `Source/`/`Route/` (this is a read-only finding).
