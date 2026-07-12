# A1 support/window raw kernel hard-gate plan

Date: 2026-07-06

Scope: `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` lane A1.

Status: planning only. This file is ignored by Git through `plan/`.


## 1. Result Target

We solve A1 only when the active CCM24 source route traces through a concrete
raw support kernel, not through an arbitrary function stored in a record field.

```text
_root_.RiemannHypothesis route
  |
  +-- SourceModelConstructorInput / SourceSemilocalRows
      |
      +-- SourceFixedWindowCoordinateRows
          |
          +-- SourceSupportClosedWindowZeroKernelModel
              |
              +-- concrete rawSupportKernel
                  |
                  +-- Mathlib / Lean facts about norm, if-then-else cutoff,
                      closedWindowZeroSet, pointInConcreteWindow
```

The target is not a new wrapper around `SourceFixedWindowCoordinateRows`. The
target is a proof path that makes the raw kernel concrete before the
fixed-window rows feed Source and Route consumers.


## 2. Evidence Snapshot

Ledger source:

```text
01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md:68
  A1. support/window raw kernel

01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md:70-72
  SourceFixedWindowCoordinateRows
  SourceSupportClosedWindowZeroKernelModel
  rawSupportKernel

01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md:193
  SourceFixedWindowCoordinateRows appears in the CCM24 country map.
```

Current generic owner:

```lean
structure SourceSupportClosedWindowZeroKernelModel
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) where
  rawSupportKernel : A.Test -> ℝ × ℝ -> ℝ
  supportValue_eq_cutoffKernel :
    forall (f : A.Test) (x : S.SupportPoint),
      S.supportValue f x =
        closedWindowZeroKernel S I rawSupportKernel f
          (S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate
              x I,
            S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x)
```

Source evidence:

```text
ConnesWeilRH/Source/AnalyticCore.lean:128
  rawSupportKernel : A.Test -> ℝ × ℝ -> ℝ

ConnesWeilRH/Source/AnalyticCore.lean:139
  supportKernel := closedWindowZeroKernel S I M.rawSupportKernel

ConnesWeilRH/Source/AnalyticCore.lean:517
  SourceFixedWindowCoordinateRows stores sourceSupportClosedWindowZeroKernelModel.

ConnesWeilRH/Source/AnalyticCore.lean:430
  concreteBaseLayer currently sets rawSupportKernel :=
    SourceConcreteBaseLayer.concreteSupportValue I
```

Current memory says the previous cut did not finish A1:

```text
MEMORY.md:404-409
  supportFootprint is now pinned to the closed-window zero-kernel, but the raw
  support kernel itself and broader SourceFixedWindowCoordinateRows semantics
  remain the next owners to drill.

MEMORY.md:1480-1487
  remaining black boxes include supportValue_eq_kernel /
  kernel_support_subset_closedWindowZero and the next useful cut is a concrete
  lower support-kernel provider.
```


## 3. Current Problem

The current concrete provider is useful but still too weak as an A1 completion
claim.

```text
current concreteBaseLayer
  rawSupportKernel := concreteSupportValue I
        |
        +-- concreteSupportValue I f x already contains the window cutoff
```

That shape proves cutoff facts, but it hides the raw kernel behind the same
cutoff support value that the model should derive.

The next cut must expose a pre-cutoff raw expression and prove that the
closed-window-zero cutoff recovers the concrete support value.

```text
recommended lower owner
  concreteRawSupportKernel f z := ‖f z.1‖
        |
        v
  closedWindowZeroKernel S I concreteRawSupportKernel f z
        |
        v
  if pointInConcreteWindow I z then ‖f z.1‖ else 0
        |
        v
  concreteSupportValue I f z
```


## 4. Hard Completion Gate

A1 is solved only if all gates below pass.

### Gate A. Raw kernel is no longer the cutoff value

Required:

```text
concreteBaseLayer.rawSupportKernel
  = concreteRawSupportKernel

concreteRawSupportKernel f z
  = ‖f z.1‖
```

Rejected:

```text
rawSupportKernel := concreteSupportValue I
rawSupportKernel := 0
rawSupportKernel := fun _ _ => 0
rawSupportKernel hidden behind a new unconstrained field
rawSupportKernel justified by True, Set.univ, or a renamed Prop
```

If `rg -n "rawSupportKernel := SourceConcreteBaseLayer.concreteSupportValue"`
still hits the active concrete provider after the patch, A1 is not solved.

### Gate B. Cutoff theorem connects raw kernel to support value

Required theorem shape:

```lean
theorem concreteClosedWindowZeroKernel_rawSupportKernel_eq_supportValue
    (I : ConcreteWindow := defaultWindow)
    (sourceTest f : ConcreteTest := defaultSourceTest)
    (z : ConcreteSupportPoint) :
    SourceSupportWindowData.closedWindowZeroKernel
        (concreteSupportWindowData I sourceTest) I
        concreteRawSupportKernel f z =
      concreteSupportValue I f z
```

The proof must split on `pointInConcreteWindow I z` or the equivalent
`closedWindowZeroSet` membership. It should reduce to existing base facts:

```text
pointInConcreteWindow
closedWindowZeroSet
closedWindowZeroKernel
concreteSupportValue
Real.norm_eq_zero / norm_ne_zero facts when needed
```

### Gate C. SourceFixedWindowCoordinateRows consumes the concrete provider

Required:

```text
concreteFixedWindowCoordinateRows
  -> concreteBaseLayer
  -> concreteRawSupportKernel
  -> concreteClosedWindowZeroKernel_rawSupportKernel_eq_supportValue
```

The active concrete Source route must keep using:

```text
concreteSemilocalRows
concreteFixedWindowExhaustionCompatible
normalizedCoreCCM24SourceFixedWindowCoordinateRowsFromTheorems
normalizedCoreCCM24SemilocalRowsFromTheorems
```

Those producers may keep the generic record API, but the concrete path must
trace to the raw-kernel theorem above.

### Gate D. Generic abstraction stays as interface only

The generic field `SourceSupportClosedWindowZeroKernelModel.rawSupportKernel`
may remain. A generic `S : SourceSupportWindowData A` cannot produce a concrete
raw kernel without assumptions.

The solved claim applies to the active CCM24 concrete source route. It does not
claim that every arbitrary `SourceSupportWindowData` has a Mathlib-derived raw
kernel.

### Gate E. Consumer path removes the old weak endpoint

Required scan after implementation:

```text
rg -n "sourceSupportInWindowData|sourceFourierSupportInWindowData|sourceFixedWindowSoninComparison" ConnesWeilRH -g "*.lean"
rg -n "rawSupportKernel := SourceConcreteBaseLayer.concreteSupportValue" ConnesWeilRH -g "*.lean"
rg -n "\(concreteSupportValue I\)|concreteClosedWindowZeroKernel_eq_raw_of_mem|concreteSupportKernel_eq_raw_of_mem|concreteSupportValue_eq_kernel_raw_of_pointInWindow" ConnesWeilRH/Source/AnalyticCore.lean
rg -n "concreteRawSupportKernel|concreteClosedWindowZeroKernel_rawSupportKernel_eq_supportValue" ConnesWeilRH/Source/AnalyticCore.lean
```

The first command may find compatibility accessors outside the active route.
It must not find active structure fields or active constructor inputs.

The third command checks stale cutoff-as-raw theorem paths. Current source has
readback theorems whose raw-kernel argument is `(concreteSupportValue I)`.
Those names must be rewritten to the new `concreteRawSupportKernel` path,
renamed/demoted as compatibility-only if still useful, or proven absent from
the accepted A1 dependency path. A patch that only removes the structure-field
assignment but leaves these theorem paths active has not solved A1.


## 5. Implementation Batches

### Batch 1. Pin local types

Before editing, run a scratch Lean check in WSL:

```lean
import ConnesWeilRH.Source.AnalyticCore

#check SourceSupportWindowData.closedWindowZeroKernel
#check SourceSupportWindowData.closedWindowZeroSet
#check SourceSupportWindowData.SourceSupportClosedWindowZeroKernelModel
#check SourceConcreteBaseLayer.pointInConcreteWindow
#check SourceConcreteBaseLayer.concreteSupportValue
#check SourceConcreteBaseLayer.concreteFixedWindowCoordinateRows
```

Expected result:

```text
The local elaborator confirms the exact implicit arguments and concrete types.
No accepted code keeps these scratch #check lines.
```

### Batch 2. Add concrete raw kernel owner

Owner module:

```text
ConnesWeilRH/Source/AnalyticCore.lean
namespace SourceConcreteBaseLayer
```

Add:

```lean
noncomputable def concreteRawSupportKernel
    (f : ConcreteTest) (z : ℝ × ℝ) : ℝ :=
  ‖f z.1‖
```

Then add direct facts:

```text
concreteRawSupportKernel_eq_norm
concreteRawSupportKernel_ne_zero_iff
```

The second theorem should prove:

```lean
concreteRawSupportKernel f z ≠ 0 ↔ f z.1 ≠ 0
```

Use Mathlib norm facts. Do not introduce a new `Prop` field for this theorem.

### Batch 3. Prove the cutoff equivalence

Add the theorem that makes the lane meaningful:

```text
concreteClosedWindowZeroKernel_rawSupportKernel_eq_supportValue
```

Proof plan:

```text
by_cases hz : pointInConcreteWindow I z
  true branch:
    closedWindowZeroSet membership follows from hz
    closedWindowZeroKernel unfolds to concreteRawSupportKernel
    concreteSupportValue unfolds to ‖f z.1‖

  false branch:
    closedWindowZeroSet membership contradicts hz
    closedWindowZeroKernel unfolds to 0
    concreteSupportValue unfolds to 0
```

This theorem is the semantic center of A1. If it does not elaborate, do not
replace it with a projection theorem.

### Batch 4. Rewire concreteBaseLayer

Change:

```lean
rawSupportKernel := SourceConcreteBaseLayer.concreteSupportValue I
```

to:

```lean
rawSupportKernel := SourceConcreteBaseLayer.concreteRawSupportKernel
```

Then rewrite `supportValue_eq_cutoffKernel` to use:

```text
concreteClosedWindowZeroKernel_rawSupportKernel_eq_supportValue
```

The proof should become a small rewrite or `simpa`, not a duplicated proof
with a hidden arbitrary raw kernel.

### Batch 5. Add route-facing readback theorems

Add only the readbacks needed for audits and consumer trace:

```text
concreteBaseLayer_rawSupportKernel_eq_concreteRawSupportKernel
concreteSupportKernel_eq_concreteRawSupportKernel_of_mem
concreteSupportKernel_eq_zero_of_not_mem
concreteSupportKernel_ne_zero_iff_closedWindow_raw_ne_zero
concreteSupportValue_eq_supportKernel
```

Some names already exist with weaker statements. Reuse existing names when the
statement already matches the stronger path. Do not add aliases that only
repeat old facts.

Current weak names that must not remain as active cutoff-as-raw readbacks:

```text
concreteClosedWindowZeroKernel_eq_raw_of_mem
concreteSupportKernel_eq_raw_of_mem
concreteSupportValue_eq_kernel_raw_of_pointInWindow
```

For each one, choose exactly one outcome:

```text
1. strengthen it so the raw-kernel argument is concreteRawSupportKernel;
2. rename it as an explicit compatibility theorem and exclude it from the
   accepted A1 dependency path; or
3. remove it if no active consumer needs it.
```

Do not keep these names silently pointing at
`closedWindowZeroKernel ... (concreteSupportValue I) ...`, because that is
precisely the cutoff-as-raw path this plan is meant to delete.

### Batch 6. Rebuild active consumers

Check the concrete route:

```text
concreteFixedWindowCoordinateRows
concreteSourceSupportCarrier_subset_windowCarrier
concreteFourierSupportCarrier_subset_windowCarrier
concreteSourceSupportInWindow
concreteFourierSupportInWindow
concreteConvolutionSupportTransported
concreteSourceSoninSpaceComparison
concreteSemilocalRows
concreteFixedWindowExhaustionCompatible
normalizedCoreCCM24SourceFixedWindowCoordinateRowsFromTheorems
normalizedCoreCCM24SemilocalRowsFromTheorems
```

If any of these names still trace through an arbitrary raw kernel supplier in
the concrete source route, the lane remains open.


## 6. Focused Axiom Audit Targets

Run one scratch file after the smallest owning build passes:

```lean
import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.AnalyticSourceModel
import ConnesWeilRH.Source.CCM24SourceModel
import ConnesWeilRH.Dev.UnconditionalSkeleton

#print axioms SourceConcreteBaseLayer.concreteRawSupportKernel_eq_norm
#print axioms SourceConcreteBaseLayer.concreteRawSupportKernel_ne_zero_iff
#print axioms SourceConcreteBaseLayer.concreteClosedWindowZeroKernel_rawSupportKernel_eq_supportValue
#print axioms SourceConcreteBaseLayer.concreteBaseLayer_rawSupportKernel_eq_concreteRawSupportKernel
#print axioms SourceConcreteBaseLayer.concreteSupportKernel_eq_concreteRawSupportKernel_of_mem
#print axioms SourceConcreteBaseLayer.concreteSupportKernel_ne_zero_iff_closedWindow_raw_ne_zero
#print axioms SourceConcreteBaseLayer.concreteSupportValue_eq_supportKernel
#print axioms SourceConcreteBaseLayer.concreteSourceSupportInWindow
#print axioms SourceConcreteBaseLayer.concreteFourierSupportInWindow
#print axioms SourceConcreteBaseLayer.concreteConvolutionSupportTransported
#print axioms SourceConcreteBaseLayer.concreteSemilocalRows
#print axioms normalizedCoreCCM24SourceFixedWindowCoordinateRowsFromTheorems
#print axioms normalizedCoreCCM24SemilocalRowsFromTheorems
```

Accepted output:

```text
[propext, Classical.choice, Quot.sound]
```

Rejected output:

```text
sorryAx
project-local axiom
constant
opaque
unsafe
any new free Prop field used as a theorem source
```


## 7. Build And Static Gates

Use WSL Ubuntu-24.04 only.

Sync:

```bash
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'
```

Smallest build sequence:

```bash
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake env lean ConnesWeilRH/Source/AnalyticCore.lean'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.AnalyticCore ConnesWeilRH.Source.AnalyticSourceModel ConnesWeilRH.Source.CCM24SourceModel'
```

Then build the route-facing consumer target. A1 is a source-to-route hard gate,
so source-only builds are not sufficient evidence:

```bash
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Route.RouteTheorem'
```

Only then check Dev skeleton as evidence for active normalized constructor use:

```bash
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake env lean ConnesWeilRH/Dev/UnconditionalSkeleton.lean'
```

Static gates:

```powershell
git diff --check
rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b|\bTrue\b|Set\.univ" ConnesWeilRH\Source\AnalyticCore.lean ConnesWeilRH\Source\AnalyticSourceModel.lean ConnesWeilRH\Source\CCM24SourceModel.lean
rg -n "rawSupportKernel := SourceConcreteBaseLayer.concreteSupportValue" ConnesWeilRH -g "*.lean"
rg -n "\(concreteSupportValue I\)|concreteClosedWindowZeroKernel_eq_raw_of_mem|concreteSupportKernel_eq_raw_of_mem|concreteSupportValue_eq_kernel_raw_of_pointInWindow" ConnesWeilRH/Source/AnalyticCore.lean
rg -n "sourceSupportInWindowData|sourceFourierSupportInWindowData|sourceFixedWindowSoninComparison" ConnesWeilRH -g "*.lean"
```

The `True` scan may report pre-existing archimedean placeholders outside this
lane. The implementation report must name those hits and show they did not
enter the A1 dependency path.


## 8. Acceptance Map

Use this exact block when reporting completion:

```text
final or route-level obligation:
  CCM24 source/window/model rows feeding SourceModelConstructorInput,
  SourceSemilocalRows, CCM24SourceModel, and the route-facing normalized core.

current weak statement / old path:
  SourceFixedWindowCoordinateRows -> SourceSupportClosedWindowZeroKernelModel
  with rawSupportKernel supplied as an arbitrary field.  Current concrete
  provider uses rawSupportKernel := concreteSupportValue I, which is already
  cutoff.

why the current statement is insufficient:
  It proves properties of a cutoff kernel but does not expose a raw kernel below
  the cutoff.  A1 asks for raw kernel semantics.

stronger semantic owner/API needed:
  SourceConcreteBaseLayer.concreteRawSupportKernel plus the theorem that
  closedWindowZeroKernel applied to it equals concreteSupportValue.

consumer that will be rewired:
  SourceSupportClosedWindowZeroKernelModel.concreteBaseLayer,
  concreteFixedWindowCoordinateRows, concreteSemilocalRows,
  concreteFixedWindowExhaustionCompatible, and normalizedCoreCCM24* rows.

old path that will be deleted or demoted:
  rawSupportKernel := concreteSupportValue I in the active concrete provider.
  Generic rawSupportKernel remains an interface field.

why the new statement can feed the RH route:
  The fixed-window support rows now derive window membership from a concrete
  raw norm kernel and closed-window cutoff, then feed the CCM24 semilocal rows
  used by the route input.

smallest WSL build:
  lake env lean ConnesWeilRH/Source/AnalyticCore.lean
  lake build ConnesWeilRH.Source.AnalyticCore
    ConnesWeilRH.Source.AnalyticSourceModel
    ConnesWeilRH.Source.CCM24SourceModel
  lake build ConnesWeilRH.Route.RouteTheorem

focused axiom audit targets:
  concreteRawSupportKernel_eq_norm
  concreteRawSupportKernel_ne_zero_iff
  concreteClosedWindowZeroKernel_rawSupportKernel_eq_supportValue
  concreteBaseLayer_rawSupportKernel_eq_concreteRawSupportKernel
  concreteSemilocalRows
  normalizedCoreCCM24SourceFixedWindowCoordinateRowsFromTheorems
  normalizedCoreCCM24SemilocalRowsFromTheorems
```


## 9. Rejection Rules

Reject the batch if any item is true:

```text
1. The active concrete provider still sets rawSupportKernel to
   concreteSupportValue I.

2. The patch proves more facts about SourceSupportClosedWindowZeroKernelModel
   while leaving rawSupportKernel arbitrary in the concrete route.

3. The patch adds a new record field whose type is the desired theorem.

4. The patch uses True, Set.univ, 0-kernel, endpoint package evidence, or a
   compatibility accessor to satisfy the support claim.

5. The patch changes only Dev/UnconditionalSkeleton.lean and does not rewire
   Source/AnalyticCore.lean.

6. The build passes but focused #print axioms shows sorryAx or a project-local
   theorem-source axiom on any listed A1 target.

7. The final report says "A1 solved" while the generic record field remains the
   only evidence for supportValue_eq_cutoffKernel in the concrete route.
```


## 10. Completion Statement

After implementation, use one of these labels.

```text
A1 solved:
  active concrete CCM24 source route uses concreteRawSupportKernel and proves
  closedWindowZeroKernel concreteRawSupportKernel = concreteSupportValue.
  Source, CCM24SourceModel, and normalized route-facing rows build and focused
  axioms are clean.

A1 project-bottom accepted-candidate:
  active consumer moved lower, but the first non-Mathlib black box is still a
  named concrete owner that needs one more theorem.

A1 not solved:
  rawSupportKernel remains arbitrary, equals concreteSupportValue I directly,
  or the route reaches a project-local Prop field.
```
