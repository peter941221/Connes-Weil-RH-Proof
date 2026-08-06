# Proof 717 / Gate-3U strong-route survey: routes 3 and 2 certified closed, only analytic routes remain

Date: 2026-08-06
Status: survey/verdict — two borrowed routes closed with machine evidence; the
wall's only remaining content is genuinely new analytic work.
Branch: `proof/gate3u-completed-readout`
RELATED: `docs/proofs/808_metric_wall_outer_channel_budget.md`,
`docs/proofs/gate3u-right-energy-leakage-norm-bottom.md`

## Result

Every closing of the real Gate 3U (`canonicalRealGate3UAt`, via
`canonicalRealGate3UAt_of_completedKernelRightEnergy`,
`CCM24FiniteSCanonicalAdjointEnergyGate.lean:375`) is one hypothesis short:

```
hright : sourcePhysicalCoframeCompletedKernelRightEnergy ≤ fixedPhysicalEnergyMajorant
```

and that hypothesis is the off-Sonin cancellation
`(I−Q)(forward + M) = 0` (Proof 717). Two in-library "escape" routes to it were
proposed and are now **proven dead by the machine**, not by opinion:

| Route | Idea | Verdict | Machine evidence |
|-------|------|---------|------------------|
| 3 (borrow forward-preserves-radial) | use `(I−R)∘T∘R = 0` to kill wall `(I−R)∘T†∘R` | **closed** | adjoint-mirror `R∘T†∘(I−R)=0` proved axiom-clean; the two directions are orthogonal, neither implies the other |
| 2 (footprint + trace, no `=0`) | show both footprint diag sums finite ⇒ `hright` without requiring `=0` | **closed** | `tsum_normSq_precomp_le` forces `‖leakage‖` as the only new scale; biorthogonality + Proof-717 equivalence turn `‖leakage‖≤1` into `=0` |

## 1. Route 3 closed (adjoint mirror) — committed

New theorem in `ConnesWeilRH/Dev/CCM24FiniteSEndpointResidualProbe.lean`
(committed as `67c4fe1`), audited in
`ConnesWeilRH/Dev/CCM24FiniteSEndpointResidualAudit.lean`:

```
radialSupport_comp_transportAdjoint_comp_radialComplement (lambda) (family) :
    radialSupportProjection λ ∘L adjoint(finiteEulerTransportOperator family) ∘L
      radialComplementProjection λ = 0
```

i.e. `R∘T†∘(I−R) = 0`.

- **Full build through**: `lake build ConnesWeilRH.Dev.CCM24FiniteSEndpointResidualAudit` = 3413 jobs, EXIT=0.
- **Axiom audit**: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

Why it closes the route: it is the **mirror** of the in-library forward collapse
`(I−R)∘T∘R = 0` (`radialComplementProjection_comp_transport_comp_radialSupport`).
The wall is `(I−R)∘T†∘R`; the proved fact is `R∘T†∘(I−R)=0`. Taking adjoints of
`(I−R)∘T∘R=0` yields the complement-side collapse, not the wall. The two
cross-blocks are orthogonal and neither implies the other. So route 3 — borrowing
forward-preserves-radial to kill the wall — is structurally impossible inside the
library: the forward fact certifies only the complement block, never the wall
block `(I−R)∘T†∘R=0`.

## 2. Route 2 closed (footprint + trace) — independently re-verified

The footprint idea: show the two diagonal series
`Σ‖row∘D(bᵢ)‖²` and `Σ‖K∘(bᵢ)‖²` are **finite** (not merely bounded to 0), so the
diagonal of the completed-boundary pairing is summable and `hright` is a real
finite majorant, *without* ever needing metric collapse.

Closed because of the precomp HS bound (`HilbertSchmidtIdeal.lean:88`)

```
tsum_normSq_precomp_le sourceBasis targetBasis newSourceBasis operator bounded
    (hoperator : Summable (fun k => ‖operator (source k)‖²)) :
    Σ' k ‖(operator ∘L bounded)(newSource k)‖² ≤ ‖bounded‖² · (Σ' ‖operator sᵢ‖²)²
```

Applied to `rightEnergy`:

```
RightEnergy = Σ' ‖pair.right ∘L sourcePhysicalCoframeLeakage(basis i)‖²
    ≤ ‖sourcePhysicalCoframeLeakage‖² · (Σ' ‖pair.right(globalBasis)‖²)
```

The right factor is exactly the **already-provable fixed majorant**
(`sourceThreeBranchPairData_right_basisEnergy_le_fixedMajorant`). So the footprint
finiteness route-2 claimed to need is **not** missing — it is already the
majorant. The **only new scale** is `‖sourcePhysicalCoframeLeakage‖`, and:

- **Biorthogonal obstruction**: `sourceInclusionAdjoint_comp_metricCoframe`
  gives `J†∘D = id`, so `1 = ‖id‖ ≤ ‖J‖·‖D‖ ≤ 1·‖D‖`, hence `‖metricCoframe‖ ≥ 1`
  (the un-scaled metric coframe is never a contraction).
- **Proof-717 equivalence** (`CCM24FiniteSEndpointContractionGuard.lean:245-252`):
  `‖combined endpoint‖ ≤ 1  ↔  forward + physicalLeakage = 0`.

So `‖sourcePhysicalCoframeLeakage‖ ≤ 1` is **not** an isolated provable fact: it is
exactly the forward+physical cancellation that is the open Proof 717 target. The
footprint ("finite but not zero") idea is a false freedom: the finiteness is
already covered by the fixed majorant, and the one scale that could close the
Gate (`‖leakage‖ ≤ 1`) is forced equivalent to `= 0`.

## 3. What genuinely remains

Both "borrowed" routes reduce to needing new analytic control on the
transport-radial defect `(I−R)∘T†∘R`. Honest options:

1. **Route 1 (quantitative)**: a decay `‖(I−R)∘T†∘R‖ ≤ δ` (new estimate on the
   prolate adjoint — not in-library), pushed into the right-energy budget.
2. **(b) band-limited / operator estimate** for the leakage leg (new math)
   — the "genuinely new band-limited" route in the prior gate norm bottom.
3. **Proof 717 itself** zero the forward+physical leakage — the target RH
   equality.

None is a Lean re-assembly; each is an analytic theorem not present in the
library. This survey is the honest frontier: `hright` remains open and equals
the open Proof 717 cancellation.

## 4. What changed / kept

- Committed: route-3 adjoint-mirror theorem + Audit (67c4fe1), full
  3413-module build clean.
- Survived (reusable): the probe bundle that pegs the wall — all axiom-clean
  (`radialSupportProjection_comp_finiteEulerDualFrame`,
  `sourceOuterCoframeLeakage_eq_radialSupportScore_...comp...`, `norm_finite...adj`).
- Kept the route2/route3 closures INSTEAD of re-advertising earlier guesses.
- No `sorry`/`admit`/`axiom` anywhere in the new lean.

## Handoff fields

- RH status: conditional (Gate 3U open); the open object is the Proof-717
  cancellation.
- Files read: `CCM24FiniteSCanonicalAdjointEnergyGate`,
  `CCM24FiniteSPhysicalCancellationGateBridge`, `CCM24FiniteSCombinedPhysicalEnergy
  ContractionReduction`, `CCM24FiniteSFixedQuotientContractionBound`,
  `CCM24FiniteSForwarded...ContractionGuard`, `HilbertSchmidtIdeal`,
  `docs/proofs/808...`, `docs/proofs/gate3u-right-energy...`.
- Declarations changed: +1 theorem in Probe (.lean), +Audit lines.
- Next safe action: route 1 quantitative leak bound, or New expl. band estimate