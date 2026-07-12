# 09F Half-Point Abel Boundary

Date: 2026-07-09

Status:
  Production closed.  This document owns only the 05A half-point analytic
  blocker.  It is independent from the 08A finite-prime source-data lanes.


## Result First

Current result:

```text
Closed in production.
```

Target family from the 05A plan:

```lean
HurwitzZeta.cosZeta (ZMod.toAddCircle (1 : ZMod 2)) (1 / 2 : C)
  =
-(dirichletEtaRealHalfOrdered : C)
```

Equivalent active formulation:

```lean
dirichletEtaAnalytic (1 / 2 : C) =
  (dirichletEtaRealHalfOrdered : C)
```


## What It Is

This lane tries to bridge the ordered real eta value at `1/2` to the analytic
continuation value used by Mathlib's zeta/cosZeta API.

```text
ordered eta sums for sigma > 0
        |
        | already has partial infrastructure
        v
orderedEtaValue (1/2)
        |
        | 09F target
        v
dirichletEtaAnalytic (1/2)
```


## Why It Matters

The CC20 disjointness/nonvanishing route still depends on this half-point
analytic-continuation identification.  Existing LSeries/cosZeta bridges are
clean sockets, but they do not prove the boundary theorem by themselves.


## How To Attack

1. Work inside the canonical 05A file and its Lean owner:
   `ConnesWeilRH/Source/DirichletEta.lean`.

2. Reuse existing ordered partial-sum convergence theorems.

3. Do not use unordered `tsum`, `Summable`, `HasSum`, or raw `LSeries` at the
   half point as the owner.  The 05A plan explicitly rejects that route.

4. If Mathlib lacks the needed analytic-continuation theorem, isolate the
   smallest missing Mathlib-style statement rather than filling it with a raw
   project axiom.


## Files

Allowed:

```text
plan/09F_2026-07-09_half_point_abel_boundary.md
ConnesWeilRH/Dev/Parallel09F_HalfPointAbelBoundary.lean
```

Read-only evidence files:

```text
plan/05A_2026-07-07_D1_cc20_zeta_half_disjointness_plan.md
ConnesWeilRH/Source/DirichletEta.lean
ConnesWeilRH/Source/CC20.lean
ConnesWeilRH/Source/RHDefinition.lean
```

Forbidden during parallel work:

```text
ConnesWeilRH/Source/DirichletEta.lean
ConnesWeilRH/Dev/UnconditionalSkeleton.lean
plan/05A_2026-07-07_D1_cc20_zeta_half_disjointness_plan.md
MEMORY.md
AGENTS.md
```

Coordinator note:
  If 09F finds a clean proof, the coordinator later ports it into
  `ConnesWeilRH/Source/DirichletEta.lean` in a non-parallel pass.


## Acceptance Gate

Accepted if the lane provides one of:

```text
Good:
  A named theorem proving the half-point Abel-boundary / eta analytic
  identification, with no sorryAx.

Partial:
  A smaller named Mathlib/API bottom that exactly explains the missing bridge.

Rejected:
  Evidence that the current ordered owner cannot identify with Mathlib's
  analytic continuation under the existing definitions.
```

Do not close this lane with accepted-source theorem fields, raw RH, raw zeta
nonvanishing, or a theorem that simply renames the target.


## Verification

Smallest WSL command:

```text
flock /tmp/connes-weil-rh-lake.lock -c \
  'lake env lean ConnesWeilRH/Dev/Parallel09F_HalfPointAbelBoundary.lean'
```

Focused audit:

```lean
#check <09F theorem name>
#print axioms <09F theorem name>
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


## 2026-07-09 Execution Update

Result:
  Accepted scratch candidate after correction.  The first scratch version
  incorrectly added an audit-only closure through the existing final
  `dirichletEtaAnalytic_half_eq_ordered` theorem; that was not real 09F
  progress and was removed.  The current scratch proves the strict
  Abel-boundary socket from lower paired-term owner declarations, without
  citing the final half-point theorem directly.

Declarations:

```text
ConnesWeilRH.Dev.Parallel09F.HalfPeriodCosZetaFullLSeriesAbelBoundary

ConnesWeilRH.Dev.Parallel09F.
  halfPeriodCosZetaFullLSeriesAbelBoundary_closes_09F

ConnesWeilRH.Dev.Parallel09F.
  halfPeriodCosZetaFullLSeriesAbelBoundary_iff_value

ConnesWeilRH.Dev.Parallel09F.
  dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos_from_pair_owner

ConnesWeilRH.Dev.Parallel09F.
  dirichletEtaAnalytic_half_eq_ordered_from_positive_strip

ConnesWeilRH.Dev.Parallel09F.
  halfPeriodCosZetaFullLSeriesAbelBoundary_from_positive_strip
```

Meaning:

```text
strict 09F owner:
  proved in scratch by `halfPeriodCosZetaFullLSeriesAbelBoundary_from_positive_strip`

Lean availability:
  the useful lower theorem is the positive-strip eta agreement:
  `dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos_from_pair_owner`

route-policy issue:
  the proof uses lower paired-term analytic continuation, not the final
  half-point theorem name.  Coordinator should decide whether to port the
  positive-strip theorem into `Source.DirichletEta` as the clean reusable API.
```

Verification:

```text
WSL persistent mirror:
  lake build ConnesWeilRH.Source.DirichletEta
  lake env lean ConnesWeilRH/Dev/Parallel09F_HalfPointAbelBoundary.lean

Focused axiom audit:
  halfPeriodCosZetaFullLSeriesAbelBoundary_closes_09F
    [propext, Classical.choice, Quot.sound]
  halfPeriodCosZetaFullLSeriesAbelBoundary_iff_value
    [propext, Classical.choice, Quot.sound]
  dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos_from_pair_owner
    [propext, Classical.choice, Quot.sound]
  dirichletEtaAnalytic_half_eq_ordered_from_positive_strip
    [propext, Classical.choice, Quot.sound]
  halfPeriodCosZetaFullLSeriesAbelBoundary_from_positive_strip
    [propext, Classical.choice, Quot.sound]
```

AI session handoff:

```text
status: accepted scratch candidate
files changed:
  ConnesWeilRH/Dev/Parallel09F_HalfPointAbelBoundary.lean
  plan/09F_2026-07-09_half_point_abel_boundary.md
declarations changed:
  added the strict socket, the positive-strip paired-owner theorem, and the
  strict socket proof from that theorem
old paths removed:
  removed the misleading audit-only closure through the existing tsum identity
remaining blockers:
  coordinator still needs to port the scratch proof into the canonical source
  file in a non-parallel pass, then run import-facing build/audit there.
WSL build:
  passed after rebuilding ConnesWeilRH.Source.DirichletEta artifacts
focused axiom audit:
  passed; no sorryAx in the listed 09F declarations
next safe action:
  port `dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos_from_pair_owner`
  into `ConnesWeilRH/Source/DirichletEta.lean` as
  `dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos`, then derive the
  existing half-point and Abel-boundary declarations from that positive-strip
  API.
```


## 2026-07-09 Production Closure

Result:
  Closed in `ConnesWeilRH/Source/DirichletEta.lean`.  This is not an
  unconditional RH proof; it closes the 09F / 05A half-point Abel-boundary
  blocker by moving the scratch route into the canonical source file.

Production declarations:

```text
ConnesWeilRH.Source.dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos

ConnesWeilRH.Source.dirichletEtaAnalytic_half_eq_ordered

ConnesWeilRH.Source.cosZeta_half_period_eq_neg_dirichletEtaRealHalfOrdered

ConnesWeilRH.Source.
  tendsto_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt_cosZeta

ConnesWeilRH.Source.
  tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries
```

Dependency shape:

```text
paired eta term tsum = dirichletEtaAnalytic on Re(s) > 0
        +
paired eta term tsum over real sigma = orderedEtaValue sigma
        |
        v
dirichletEtaAnalytic (sigma : C) = orderedEtaValue sigma, for sigma > 0
        |
        v
half-point eta analytic = ordered real eta
        |
        v
cosZeta half-period value
        |
        v
strict Abel-boundary theorem
```

Meaning:
  The previous bad route was the self-referential one: proving the socket by
  citing the already-final half-point theorem.  The production route now uses
  the lower paired-term owner over the whole positive real strip and derives
  the half-point theorem as a specialization.

Verification:

```text
WSL persistent mirror:
  lake env lean ConnesWeilRH/Source/DirichletEta.lean
  lake env lean ConnesWeilRH/Dev/Parallel09F_HalfPointAbelBoundary.lean
  lake env lean ConnesWeilRH/Source/ZetaHalfNonvanishing.lean
  lake build ConnesWeilRH.Source.ZetaHalfNonvanishing

Focused import-facing axiom audit:
  dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos
    [propext, Classical.choice, Quot.sound]
  cosZeta_half_period_eq_neg_dirichletEtaRealHalfOrdered
    [propext, Classical.choice, Quot.sound]
  tendsto_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt_cosZeta
    [propext, Classical.choice, Quot.sound]
  tendsto_neg_cosZeta_half_period_abel_etaHalfPowerSeries
    [propext, Classical.choice, Quot.sound]
  riemannZeta_half_ne_zero
    [propext, Classical.choice, Quot.sound]
```

AI session handoff:

```text
status: accepted production closure
files changed:
  ConnesWeilRH/Source/DirichletEta.lean
  ConnesWeilRH/Dev/Parallel09F_HalfPointAbelBoundary.lean
  plan/09F_2026-07-09_half_point_abel_boundary.md
declarations changed:
  added the positive-strip eta agreement and direct cosZeta / Abel-boundary
  production closures
old paths removed:
  the half-point theorem no longer proves itself through the final theorem
  name; it specializes the positive-strip API
remaining blockers:
  none for 09F
WSL build:
  passed for ConnesWeilRH.Source.ZetaHalfNonvanishing
focused axiom audit:
  passed; no sorryAx in the listed production declarations
next safe action:
  return to the remaining 08A / 10A finite-prime source-data lane
```
