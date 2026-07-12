# 09 Parallel Lightning Coordination

Date: 2026-07-09

Status:
  Coordination document only.  It does not prove RH, close 08A, or remove any
  final `sorryAx`.


## Result First

Current result:

```text
Not an unconditional RH proof.
```

This split exists so Peter can run several manual AI sessions without semantic
overlap.  It is not a restoration of automatic subagents.  Each lane owns one
proof target family, one plan file, and at most one optional scratch Lean file.
Production route integration is intentionally left to a later coordinator pass.


## Current Route Picture

```text
unconditional RH
|
+-- final target:
|     _root_.RiemannHypothesis
|
+-- final no-argument route:
|     still has sorryAx in Dev.UnconditionalSkeleton
|
+-- 08A current finite-prime/source-data package bottom:
|     SourceWeilFormCarrier
|     + VisibleAtomForSourceTestNormalization
|     + PackageSourceDataCommonTestRows
|     + PackageSourceDataCertificateFamilyRows
|     + VisibleAtomSourceDataRows
|     + DirectTermMassRows
|
+-- 05A independent analytic blocker:
      half-point Abel-boundary / analytic-continuation identification
```

Evidence:
  - `MEMORY.md` says the current result is not an unconditional RH proof.
  - `ConnesWeilRH/Basic.lean` fixes the final target as
    `_root_.RiemannHypothesis`.
  - `plan/08A_2026-07-08_D1_restricted_test_cc20_sufficiency_plan.md` records
    the split package source-data rows as the current 08A bottom.
  - `plan/05A_2026-07-07_D1_cc20_zeta_half_disjointness_plan.md` records the
    half-point Abel-boundary as the active 05A blocker.


## Lane Matrix

```text
+------+----------------------------------------------+-------------------------+
| lane | target                                       | may run in parallel     |
+------+----------------------------------------------+-------------------------+
| 09A  | package source-data common-test row          | yes, with 09B-09F       |
| 09B  | package source-data certificate-family row   | yes, with 09A,09C-09F   |
| 09C  | visible atom source-data row                 | yes, with 09A,09B,09D-F |
| 09D  | direct term mass rows                        | yes, with 09A-09C,09E-F |
| 09E  | same-symbol source-Weil-form carrier         | yes, read-only to 09A-D |
| 09F  | 05A half-point Abel-boundary                 | yes, independent lane   |
+------+----------------------------------------------+-------------------------+
```

Final integration is not a parallel lane.  It may start only after a lane
handoff says `accepted` and the coordinator has checked for file overlap.


## Non-Interference Contract

All manual AI sessions must follow this contract:

```text
Allowed by default:
  - read any Lean/source/plan file;
  - edit only the lane's own 09X plan file;
  - create or edit only the lane's optional scratch Lean file if the lane
    document names one;
  - run focused WSL verification for that lane.

Forbidden during parallel work:
  - editing ConnesWeilRH/Route/CC20RouteRealization.lean directly;
  - editing ConnesWeilRH/Dev/UnconditionalSkeleton.lean directly;
  - editing another 09X plan file;
  - editing plan/08A_2026-07-08_D1_restricted_test_cc20_sufficiency_plan.md;
  - editing MEMORY.md or AGENTS.md from worker lanes;
  - running a broad `lake build` without the WSL lock;
  - claiming accepted progress from a scratch proof alone.
```

Reason:
  The current active 08A declarations live mostly in one large route module.
  If several agents edit that file directly, they will collide at the text
  level and at the semantic owner level.  Scratch files let each lane find the
  proof or counterexample independently.  The coordinator ports only the exact
  accepted semantic change.


## Required Session Header

Each manual AI session must begin by writing this in its own transcript or
handoff note:

```text
AI session start:
  owner:
  cwd:
  lane: 09?
  old weak path:
  files allowed:
  files forbidden:
  smallest WSL build:
  focused axiom audit:
  expected output:
```


## Required Handoff

Each lane must end with:

```text
AI session handoff:
  status: accepted / partial / blocked / rejected / analysis-only
  files changed:
  declarations changed:
  old paths removed:
  remaining blockers:
  WSL build:
  focused axiom audit:
  next safe action:
```


## Coordinator Acceptance Gate

A lane is accepted only if all are true:

```text
1. The lane target is proved or rejected by named Lean evidence.
2. The lane did not edit forbidden files during parallel work.
3. The smallest WSL build for the touched module passes under:
     /tmp/connes-weil-rh-lake.lock
4. Focused import-facing #check / #print axioms sees the new declarations.
5. The axiom audit shows no sorryAx.
6. The coordinator ports the result into the production route module in a
   separate, non-parallel pass.
```


## Next Safe Action

Start with 09A and 09B because they test whether the route package source-data
provenance is definitional.  If either row is false for current constructors,
reject the package-source path early instead of spending time on lower mass
rows.

