# 09E Source-Weil-Form Carrier

Date: 2026-07-09

Status:
  Parallel manual-AI lane.  This document owns only the same-symbol
  source-Weil-form carrier.


## Result First

Current result:

```text
Open.
```

Target:

```lean
NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration
```

Source shape in `ConnesWeilRH/Route/CC20RouteRealization.lean`:

```lean
∀ r : NormalizedRouteBackedCC20SquareRestrictedTest,
  Σ A : Source.AnalyticCore.SourceTestAlgebra,
    { sourceWeilForm : Source.AnalyticCore.SourceWeilFormData A //
      r.inputs.ccm25.weilSymbols = sourceWeilForm.toWeilFormSymbols }
```


## What It Is

This lane checks whether each route carrier has a source-Weil-form object whose
symbols are exactly the same object as `r.inputs.ccm25.weilSymbols`.

```text
r.inputs.ccm25.weilSymbols
        |
        | must be equal
        v
sourceWeilForm.toWeilFormSymbols
```


## Why It Matters

Without the same-symbol equality, lower support, visible arithmetic, atom, and
mass rows can be proved over the wrong symbol object.  The equality is not
decorative; it is the carrier invariant for the finite-prime path.


## How To Attack

1. Trace how `r.inputs.ccm25.weilSymbols` is produced.

2. Trace existing `SourceWeilFormData` constructors.

3. Check whether the source-Weil-form carrier can be selected without changing
   the symbol object.

4. If construction is impossible with existing APIs, identify the exact missing
   source object or field.


## Files

Allowed:

```text
plan/09E_2026-07-09_source_weil_form_carrier.md
ConnesWeilRH/Dev/Parallel09E_SourceWeilFormCarrier.lean
```

Read-only evidence files:

```text
ConnesWeilRH/Route/CC20RouteRealization.lean
ConnesWeilRH/Route/RouteTheorem.lean
ConnesWeilRH/Source/AnalyticCore.lean
ConnesWeilRH/Source/Objects.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```

Forbidden:

```text
ConnesWeilRH/Route/CC20RouteRealization.lean
ConnesWeilRH/Dev/UnconditionalSkeleton.lean
plan/08A_2026-07-08_D1_restricted_test_cc20_sufficiency_plan.md
MEMORY.md
AGENTS.md
```


## Acceptance Gate

Accepted if the lane provides one of:

```text
Good:
  A named theorem constructing the same-symbol source-Weil-form carrier, with
  no sorryAx.

Rejected:
  A precise audit showing that current route inputs do not carry enough data
  to construct `SourceWeilFormData` with the same symbols.
```

Do not use `True`, `Set.univ`, an arbitrary source-Weil-form object, or a
carrier whose symbols are only morally similar.


## Verification

Smallest WSL command:

```text
flock /tmp/connes-weil-rh-lake.lock -c \
  'lake env lean ConnesWeilRH/Dev/Parallel09E_SourceWeilFormCarrier.lean'
```

Focused audit:

```lean
#check <09E theorem name>
#print axioms <09E theorem name>
```


## Handoff Template

```text
AI session handoff:
  status:
  files changed:
  declarations changed:
  old paths removed:
  remaining blockers:
  WSL build:
  focused axiom audit:
  next safe action:
```

