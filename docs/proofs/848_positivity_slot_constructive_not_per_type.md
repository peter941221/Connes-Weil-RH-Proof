# 848 — positivity slot: the refutation is PER-VALUE, the constructive `Exhaustion` input is type-compatible (probe `CC24PositivitySlotProbe848.lean`, build-verified)

Date: 2026-08-07 · Status: WSL build-green `#check` audit (all resolve) + decisive verdict
Continuation of 847b: settle the "sign switch" framing and pin the *real* decision point —
whether a constructive `FullWeilPositivity` input can actually occupy the criterion's
`fullWeilPositivity` slot.

## 0. 结论

**是被证伪的 per-VALUE, 不是 per-TYPE。** The two ways to fill `WeilPositivityInput`
(1) the refuted finite-vanishing input `normalizedCC20FiniteVanishingWeilCriterionInput`
and (2) the constructive `Exhaustion.toWeilPositivityInput … = { fullWeilPositivity := FullWeilPositivity inputs g L }` —
have the **same type** `WeilPositivityInput` and are both legal for the criterion slot.
- The refutation hits **that one input's own field**:
```
not_...Input_fullWeilPositivity : normalizedCC20FiniteVanishingWeilCriterionInput.fullWeilPositivity → False
```
- It does **not** "poison" the type. The other input's field `FullWeilPositivity …` is a
  **type/value** (constructive), which is exactly what the criterion's `fullWeilPositivity : input.fullWeilPositivity`
  (CC20PropositionC1InputData) demands to witness.

So 848 terminates the "sign" direction with a positive-engineering answer: **there is no
dead type; there is a difference in whether you can *produce* a `fullWeilPositivity`
witness for the chosen F.** The n real runtime block — and the thing the concrete positive
object (`weilLocalSum>0`, detector) supports — is the **two extra rows of
`CC20PropositionC1RouteInputData`**: `tripleVanishingMatchesMellin` and
`finiteSetDisjointFromNontrivialZeros` at the *concrete* F. Not the sign.

## 1. What the probe pinned (`CC24PositivitySlotProbe848.lean`, build-green)

```
WeilPositivityInput                       : Type 1        (slot)
normalizedCC20FiniteVanishingWeilCriterionInput : WeilPositivityInput   (refuted value)
  fullWeilPositivity = PLift (CC20FiniteVanishingWeilCriterion …)          -- refuted
not_…_Input_fullWeilPositivity : ∀ a, …fullWeilPositivity → False        -- per-VALUE

toWeilPositivityInput : RouteInputs → SourceBackedFixedSTest → RouteLedgers → WeilPositivityInput
  fullWeilPositivity := FullWeilPositivity inputs g L        -- Type, constructive, TRUE-as-field
FullWeilPositivity … : Type

CC20PropositionC1InputData (B, F, input) : … fullWeilPositivity : input.fullWeilPositivity   (witness field)
CC20PropositionC1SourceCriterion (F) (input) : CC20PropositionC1InputData B F input → B.SourceRH
```
- The two competing inputs are **the same type**, so the criterion (which is `∀ input, …`)
  does **not** structurally exclude the constructive one.
- The refutation kills the finite-vanishing value's field (`∀ a : … , False`), not the slot.

## 2. The real remaining 2 rows (both carrier questions, not a sign)

`CC20PropositionC1RouteInputData.c1InputData : CC20PropositionC1InputData B F input` carries:
1. `tripleVanishingMatchesMellin : RouteTripleVanishingMatchesCC20Mellin F input`
2. `finiteSetDisjointFromNontrivialZeros B F`
plus the input's own `tripleVanishing` and `fullWeilPositivity` witness — the last one is
**constructible** for an Exhaustion input; rows 1&2 at the **concrete P** are the genuinely
open per-F facts, shared with the finite-vanishing route (this is the same F used by both).
So choosing Exhaustion does **not** get you rows 1&2 for free at a nontrivial F; it only
(legitimately) avoids "I need a finite-vanishing ≤0 universal to feed the criterion", which
was already dead.

## 3. Honest state after 848

- The sign "decision" is **NOT** between `≤0` and `>0` (both sides are separate shapes;
  847ab). It is the **slot compatibility result**: a *constructive* `fullWeilPositivity`
  (=a `FullWeilPositivity` value) fills the criterion slot, and the "≤0 refutation" is a
  *value-level* rejection of one particular input, not a type-level barrier.
- RH not claimed; nothing closed. The genuinely open arithmetic stays the **per-F carrier**
  rows 1&2 (tripleVanishingMatchesMellin, finiteSetDisjointFromNontrivialZeros) — this is the
  real floor, common to both the finite-vanishing and constructive routes.

## Repro

```
lake build ConnesWeilRH.Route.CC20RouteRealization ConnesWeilRH.Route.Exhaustion
lake env lean ConnesWeilRH/Dev/CC24PositivitySlotProbe848.lean   # build-green
```

## Evidence

```
Source/CC20RHExit.lean:66-92    CC20PropositionC1InputData / SourceCriterion / …Data
Route/CC20RouteRealization.lean:28-80  refuted finite-vanishing input
Route/Exhaustion.lean:19-31     Exhaustion FullWeilPositivity (constructive producer)
Source/CC20Yoshida…:2218,2227/…2482,2715  detector positive per-g
```