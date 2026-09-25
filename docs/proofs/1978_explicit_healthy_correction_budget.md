# 1978 — Explicit correction budget on the complete healthy owner

Date: 2026-09-25.

Status: FORMAL quantitative reduction. No determinant sign, joint tail margin,
or RH claim.

## Consumer and removed premise

The owner is the exact finite interpolation set used by
`exists_smallSupport_healthyDetectorData_of_heightDecay`:

```text
killSet = sourceNontrivialZerosInClosedBallFinset rho
    (2^(N+1) + 2 + dist 2 rho) union routeNodes

nodes = killSet union healthyUnscaledTargetNodes rho
```

Record 1977 bounded an explicit correction for an arbitrary finite node set.
The missing connection was that no theorem instantiated that bound on the
complete `killSet` owner of the healthy detector consumer. This record removes
that premise without changing the owner or dropping collisions.

## Formal result

`C1ExplicitHealthyCorrectionBudget.lean` defines
`explicitHealthyCorrection rho N routeNodes` using `smoothSeed` on the exact
`nodes` above and proves:

1. `explicitHealthyCorrection_targets`: every healthy target receives its
   committed `healthyUnscaledTargetValue`;
2. `explicitHealthyCorrection_kills`: every non-target point of the complete
   `killSet` is zero;
3. `explicitHealthyCorrection_support`: support remains in `[-2, 2]`;
4. `l1Mass_explicitHealthyCorrection_le_budget`: the correction has the 1977
   seed-ladder L1 bound with its actual node differences and normalization
   denominators.

For `nodes.card = M`, only derivative orders `4 <= j < M` remain as inputs.
The whole finite zero prefix and every route node remain present.

## Verification

```text
lake build ConnesWeilRH.Dev.C1ExplicitHealthyCorrectionBudgetAudit

build-logs/1978_explicit_healthy_correction.log
Build completed successfully (3658 jobs).
error lines: 0
sorryAx lines: 0
new-module warning lines: 0
```

All four audited declarations depend exactly on:

```text
[propext, Classical.choice, Quot.sound]
```

## Remaining obligation

The actual cardinality, separation products, higher seed orders required by
that cardinality, and the correction's quadratic decay constant are still
open. They must be evaluated on this same `healthyCorrectionNodes` owner before
screening the determinant and same-index tail margin.
