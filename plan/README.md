# Plan Writing README

This directory stores ignored planning artifacts.  Plans here guide work, but
they do not count as accepted Lean progress.


## 1. Why This README Exists

The CCM24 Fourier lane exposed a planning failure:

```text
Plan said:
  move below line / identity provider

Implementation did:
  line owner -> coordinate owner

But the concrete transform law still said:
  current operator = intended operator

and intended operator was defined as:
  intended operator := current operator
```

The build passed.  The axiom audit passed.  The lane still did not close.

The missing check was semantic:

```text
Did the new theorem prove a stronger mathematical statement,
or did it only rename the same weak object?
```


## 2. Required Shape For Every Plan

Every future plan in this directory must start with a hard gate.

Use this order:

```text
1. Result first
2. What counts as solved
3. What does not count
4. Current evidence
5. First-principles dependency chain
6. Implementation route
7. Static rejection scans
8. WSL build gate
9. Focused axiom audit
10. Final acceptance text
```

Do not start with a broad roadmap.  Start with the exact condition that would
make the work accepted or rejected.


## 3. Solved Means A Stronger Statement

A lane is solved only when the active proof path gets a stronger statement that
feeds the route toward `_root_.RiemannHypothesis`.

This shape can count:

```text
old weak path removed or demoted
  -> new semantic owner/API
  -> real consumer rewired
  -> smallest owning build passes
  -> focused axiom audit is clean
  -> next route dependency is stronger than before
```

This shape does not count:

```text
old weak path
  -> wrapper
  -> renamed field
  -> compatibility theorem
  -> same consumer
```

The plan must name the active consumer that moves.  If no consumer moves, call
the work prep-only.


## 4. Alias And Wrapper Red Flags

Plans must reject same-object aliases.

Bad shape:

```text
intendedObject := currentObject

theorem current_realizes_intended :
  currentObject = intendedObject := rfl
```

Good shape:

```text
transportedObject := object induced by lower source/model semantics

theorem current_eq_transported :
  currentObject = transportedObject := ...
```

The difference matters:

```text
same-object alias
  proves naming consistency

transport theorem
  proves semantic connection
```

Every plan must include a scan that catches the bad shape.

Example:

```text
rg -n "intended.*:=.*current|realizes.*:= rfl|toIdentity.*toFourier|Set\\.univ|\\bTrue\\b" ConnesWeilRH -g "*.lean"
```

Tune the scan to the lane.  The plan must show the exact old path that must
disappear or become compatibility-only.


## 5. Build Passing Is Not Enough

A plan must separate three gates:

```text
type gate:
  Lean elaborates and the smallest owning build passes

axiom gate:
  focused #print axioms has no sorryAx or project-local axiom

semantic gate:
  the statement is strong enough for the next route/RH dependency
```

The first two gates do not imply the third gate.

The Fourier mistake came from treating this as enough:

```text
build passed
#print axioms returned [propext, Classical.choice, Quot.sound]
```

Those facts certify Lean trust.  They do not certify mathematical usefulness.


## 6. Route-Facing Gate

Every plan must answer:

```text
Which route/source theorem consumes the new statement?
```

If the new theorem only feeds a local compatibility predicate, the plan must
say whether that predicate is enough for the next route step.

Required search pattern:

```text
rg -n "<old name>|<new owner>|<compatibility predicate>|<route theorem>" ConnesWeilRH -g "*.lean"
```

If route-facing files can be affected, the plan must include the route build:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Source-only builds are not enough for a route-facing hard gate.


## 7. Focused Axiom Audit

Every plan must list exact audit targets.

Use:

```lean
#check theorem_name
#print theorem_name
#print axioms theorem_name
```

Acceptable output is usually:

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
free Prop field that states the target theorem
endpoint package theorem
certificate atom
```

Do not audit only the wrapper.  Audit the theorem that carries the new
semantic content.


## 8. Hard-Gate Template

Copy this block into new plans and fill it before implementation:

```text
Hard completion gate:
  The lane is solved only if:
    1. <old weak path> is deleted or compatibility-only.
    2. <new semantic owner/API> supplies the active proof object.
    3. <named theorem> proves the semantic connection to the lower object.
    4. <consumer declarations> use the new owner.
    5. WSL build passes:
         <exact command>
    6. Focused axiom audit passes for:
         <exact theorem list>

Rejected as not solved if:
  - <same-object alias pattern> remains.
  - <old wrapper path> remains active.
  - The new theorem only projects a field.
  - The route consumer still sees only the old weak statement.
```


## 9. Final Acceptance Template

Use this shape after implementation:

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  <exact path>

New semantic owner:
  <exact declaration>

Semantic theorem:
  <exact theorem>

Consumer rewires:
  <exact declarations>

Semantic sufficiency:
  Why this statement is strong enough for the next route/RH step,
  or the exact remaining boundary.

Build:
  <exact WSL command>
  <result>

Focused axiom audit:
  <theorem list>
  <axiom output>

Remaining black box:
  <exact declaration/type>
```


## 10. Rule Of Thumb

If a plan cannot name the old weak path, the new semantic owner, the consumer,
and the rejection scan, the plan is not ready.

Write the gate first.  Then write the implementation.

## Current Candidate Index

```text
024  metric Sonin projection and fixed-S compact remainder
     umbrella: Plan 016 Contract M3B
     status: mathematical candidate; final restricted Rayleigh gate open
```
