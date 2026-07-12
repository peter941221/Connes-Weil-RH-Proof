# 05B2 D1 CC20 Mellin And Compact Predicate Plan

Date: 2026-07-07

Status: planning shard under 05B.  This shard supplies the Mellin and
compact-smooth fields for the concrete CC20 test-space owner.


## 1. Result First

Hard completion gate:

```text
Good:
  The concrete owner supplies:

    mellinAt : Test -> ℂ -> ℂ
    compactSupportSmooth : Test -> Prop

  Both fields come from named lower analytic objects or from a named first
  non-Mathlib black box.

Partial:
  The shard finds the carrier and states the missing Mellin or compact-smooth
  API, but cannot implement a non-dummy field.

Rejected:
  mellinAt := fun _ _ => 0.
  compactSupportSmooth := fun _ => True.
  compactSupportSmooth := fun _ => Set.univ-style membership.
  A raw field restates all Mellin vanishing rows needed by 05C.
```


## 2. Evidence

Current interface:

```text
ConnesWeilRH/Source/CC20TestSpace.lean
  mellinAt : Test -> ℂ -> ℂ
  compactSupportSmooth : Test -> Prop

ConnesWeilRH/Source/CC20TestSpace.lean
  CC20VanishesOn C F g :=
    forall p in F, C.mellinAt g (criticalVanishingPointValue p) = 0
```

Current route bridge:

```text
ConnesWeilRH/Source/CC20RHExit.lean
  RouteTripleVanishingMatchesCC20Mellin F input := input.tripleVanishing

ConnesWeilRH/Source/CC20RHExit.lean
  CC20PropositionC1InputData.tripleVanishingMatchesMellin
```

This means 05B2 cannot prove the route bridge by itself.  It only supplies the
Mellin function and compact predicate that 05C and 05D can reference.


## 3. Dependency Tree

```text
05B2 Mellin/compact data
|
+-- Mellin evaluation
|   |
|   +-- input:
|   |     concrete carrier from 05B1
|   |
|   +-- output:
|         mellinAt g s
|
+-- compact-smooth predicate
|   |
|   +-- input:
|   |     concrete carrier from 05B1
|   |
|   +-- output:
|         compactSupportSmooth g
|
+-- downstream use
    |
    +-- 05C:
    |     detector must prove vanishesOnF and detectsRho using mellinAt
    |
    +-- 05D:
          route tripleVanishing must imply CC20VanishesOn for compact tests
```


## 4. Implementation Route

Preferred owner shape:

```lean
structure CC20MellinCompactData
    (Carrier : Type) where
  mellinAt : Carrier -> ℂ -> ℂ
  compactSupportSmooth : Carrier -> Prop
```

Acceptance depends on field provenance, not the record shape.  If the current
project lacks a real Mellin API for `TestFunction = SchwartzMap ℝ ℂ`, report:

```text
first non-Mathlib black box:
  exact declaration/type:
    <missing Mellin transform or compact-support/smooth theorem>

why the path stops:
  <which field cannot be supplied without a dummy>

next lower definition needed:
  <Lean-ish declaration>
```


## 5. Rejection Scans

```text
rg -n "mellinAt := fun .*=> 0|compactSupportSmooth := fun .*=> True|compactSupportSmooth := fun .*=> Set\.univ|Mellin.*Accepted|Vanishing.*Accepted|stored.*Mellin|\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH/Source/CC20ConcreteTestSpace.lean ConnesWeilRH/Source/CC20Concrete.lean
```


## 6. WSL Build Gate

Use the main WSL ext4 mirror.

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.CC20ConcreteTestSpace'
```


## 7. Focused Axiom Audit

```lean
import ConnesWeilRH.Source.CC20ConcreteTestSpace

#check ConnesWeilRH.Source.normalizedCC20MellinCompactData
#print axioms ConnesWeilRH.Source.normalizedCC20MellinCompactData
```


## 8. Acceptance Text

```text
Result:
  Good / partial / rejected.

Mellin field:
  <exact declaration and lower source>

Compact-smooth predicate:
  <exact declaration and lower source>

Rejected shortcuts scanned:
  <scan output>

Remaining 05B dependency:
  convolution, Weil local sum, and final owner assembly.
```
