# 847b — CORRECTION: detector-positive is EXISTENTIAL, not the flipped canonical ≤0; the "sign switch" is a quantifier/carrier mismatch, not an inequality flip

Date: 2026-08-07 · Status: WSL-build-verified `#check` audit (`CC24SignSwitchAudit847.lean`)

I must correct an overclaim from 847. There I wrote the sign decision as "abandon the `≤0`
criterion for the `>0` detector-positive side", as if the two were one inequality flipped.
**Reading the real axioms shows they are NOT one predicate with a flipped inequality — they
differ in quantifier AND carrier shape.** No single sign-flip connects them.

## 1. The Lean-verified shapes (build-green, all `#check` resolve)

```
CC20WeilNonpositive (C) (g) : Prop   =   C.weilLocalSum (C.starConvolution g) ≤ 0

CC20FiniteVanishingWeilCriterion (C) (F) : Prop =
  ∀ g : C.Test, C.compactSupportSmooth g →
    CC20VanishesOn C F g → CC20WeilNonpositive C g        -- UNIVERSAL, ≤ 0

normalizedCC20FiniteVanishingWeilCriterionInput.fullWeilPositivity =
  PLift (CC20FiniteVanishingWeilCriterion normalizedTestSpace cc20TripleFiniteVanishingSet)
not_normalizedCC20FiniteVanishingWeilCriterionInput_fullWeilPositivity :
  ∀ (a : ...fullWeilPositivity), False                     -- the route input is REFUTED

normalizedCC20YoshidaDetectorExists : CC20YoshidaDetectorExists ...                       -- PROVEN
  (CC20YoshidaDetectorExists = ∃ g, ... vanishesOn F g ∧ ... weilLocalSum g > 0)           -- EXISTENTIAL, > 0
concreteYoshidaMomentData_weilLocalSum_positive {rho g} (h) : 0 < weilLocalSum g          -- per-g, > 0

CC20PropositionC1SourceCriterion (F) (input) : CC20PropositionC1InputData F input → B.SourceRH
```

## 2. The double (quantifier + carrier) mismatch

| the supposed sign | actual | quantifier | inequality | state |
|---|---|---|---|---|
| canonical `≤ 0` (criterion) | `∀ g, ... weilLocalSum g ≤ 0` | ∀ (universal) | ≤ 0 | **refuted** (RouteRealization:54) |
| detector-positive | `∃ g, ... weilLocalSum g > 0` | ∃ (per-g) | > 0 | **proven** (Yoshida:2218) |

Flipping `≤` to `>` on the universal criterion would give `∀ g, > 0` — that is NOT what the
proof gives (the proof is a per-g `∃`). And negating the refuted universal gives `∃ g, >0` only
via classical logic, **not** a constructive per-g positive that simultaneously kills all needed
off-line zeros. So "change sign" was the wrong frame.

## 3. Where the real "positive assumption" lives

The only *constructive* producer of `fullWeilPositivity` in the repo is the exhaustion route:
```
Exhaustion.toWeilPositivityInput : RouteInputs → SourceBackedFixedSTest → RouteLedgers → WeilPositivityInput
Exhaustion.toWeilPositivityInput ...:
  fullWeilPositivity := FullWeilPositivity inputs g L          -- positive BY CONSTRUCTION, not refuted
full_weil_positivity_input_holds {inputs g L} (h) : (toWeilPositivityInput ...).fullWeilPositivity
FiniteVanishingCriterionPackage.criterion : ∀ input, tripleVanishing → fullWeilPositivity → RH
```
Here **"`fullWeilPositivity` is a *value* (a sort/type testimonial), not a refuted universal**.
The switch that "clears the sign" is therefore **not** "flip canonical ≤0", it is:

> choose the *constructive* `FullWeilPositivity` (`Exhaustion`) as the `fullWeilPositivity` of
> the input that feeds the criterion, instead of the *refuted* `CC20FiniteVanishingWeilCriterion`.

## 4. Honest status after 847b

- The structural 3U collapse (outer=0, |Tr(sourceBand)≤1|, axiom-clean) is TRUE and unchanged.
- "Canonical ≤0 refuted on concrete" is TRUE (Yoshida `-8<0`, Detector:2227) — but the refuted
  object is a *universal→≤0 criterion*, not the constructive positivity.
- **The real "sign" gap is a carrier/quantifier mismatch, not a flip**: the repository has both
  the *refuted* universal-≤0 (finite-vanishing input) and the *constructive* `FullWeilPositivity`
  (exhaustion). Which one must satisfy the standard `CC20PropositionC1SourceCriterion`'s required
  `fullWeilPositivity` is the actual decision point — and 847b shows that any "flip only" is the
  wrong lever.
- **No RH claim; nothing closed.** This is a correction to keep the honest ledger straight.

## Repro

```
lake build ConnesWeilRH.Route.CC20RouteRealization ConnesWeilRH.Route.Exhaustion
lake env lean ConnesWeilRH/Dev/CC24SignSwitchAudit847.lean   # build-green, all #check
```

## Evidence

```
Source/CC20TestSpace.lean:35-46       CC20WeilNonpositive / CC20FiniteVanishingWeilCriterion
Source/CC20YoshidaConstruction.lean:2218,2227,2482,2715   weilLocalSum>0 / halfDensity<0 / detector-exists
Source/CC20RHExit.lean:89    CC20PropositionC1SourceCriterion = InputData → SourceRH
Route/CC20RouteRealization.lean:28-80  finite-vanishing input + its negation
Route/Exhaustion.lean:19-95             exhausting route (constructive producer)
Basic.lean:421-429         WeilPositivityInput / FiniteVanishingCriterionPackage
```