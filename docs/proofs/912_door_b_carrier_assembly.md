# 912 (Door B) — the CC20 per-F rows assemble axiom-clean; the FULL positivity witness is the single remaining B-lane slot

Status: build-verified (probe `ConnesWeilRH/Dev/CC24DoorBCarrierAssemblyProbe912.lean`). No RH claimed.

The A-lane closure (911) reduced the A-lane to one wall (generic-lambda prolate
HS). This is the B-lane counterpart: it takes the finite-vanishing CC20 exit
`CC20PropositionC1InputData` and separates its four fields into "closed
carrier data" vs "one honest open witness". The conclusion is constructive and
precise.

## The record and its four fields

```lean
structure CC20PropositionC1InputData (B) (F) (input : WeilPositivityInput)
    -- finiteSetIsTriple : RouteFiniteVanishingSetIsCC20Triple F
    -- finiteSetDisjointFromNontrivialZeros : SourceFiniteSetDisjointFromNontrivialZeros B F
    -- tripleVanishingMatchesMellin : RouteTripleVanishingMatchesCC20Mellin F input
    -- fullWeilPositivity : input.fullWeilPositivity
```

## Axiom status of each field on the concrete triple (this probe, `#print axioms`)

| field | source | axiom status |
| `finiteSetIsTriple` | `cc20_triple_finite_set_admissibility` | CLOSED (rfl-class) |
| `finiteSetDisjointFromNontrivialZeros` | `cc20_triple_disjoint_..._nontrivial_zeros` (849, via `riemannZeta_half_ne_zero` / Dirichlet-eta) | CLOSED |
| `tripleVanishingMatchesMellin` | `RouteTripleVanishingMatchesCC20Mellin F input = input.tripleVanishing` | CLOSED (dbf) |
| `fullWeilPositivity` | — | **the only open field** |

So three of the four per-F rows are already sourced by the repo's arithmetic
(849 closed the disjointness; the triple-is-CC20 and triple-matches are
definitional). The probe proves the **iff**

```
c1InputData_exists_iff_positivity :
    Nonempty input.fullWeilPositivity
        ↔ Nonempty (CC20PropositionC1InputData standard cc20TripleFiniteVanishingSet input)
```

i.e. the whole `CC20PropositionC1InputData` exists EXACTLY when the positivity
witness exists: all the carrier data can be lifted, the only gating field is
`fullWeilPositivity`.

## Why this is the honest B-lane door (not a re-claim)

- The refuted finite-vanishing input sets
  `fullWeilPositivity := PLift (CC20FiniteVanishingWeilCriterion …)` whose
  universal `≤ 0` is REFUTED on the concrete orbit (847b/848). So for THAT
  `WeilPositivityInput` there is no witness and no input data.
- The constructive candidate `Route.FullWeilPositivity` (Exhaustion.lean) is a
  `Sort 1` value, positive by construction, and NOT refuted per-type (848).
  Supplying it (or any other `Sort 1` witness) makes the input data build.

Hence the B-lane's genuine remaining work is the SAME single positive-canonical
decision 842/847b shifted to the finite-vanishing slot: choose/prove a
constructive `FullWeilPositivity` at a concrete `g`. Everything else in the
carrier is already axiom-clean.

## Scope / honesty

- No RH claimed. Zero `sorry`.
- All axioms are library-level
  `[propext, Classical.choice, Quot.sound]` (probe records the `#print axioms`
  of `cc20TripleDisjoint`, `cc20TripleAdmissibleForBridge`, and
  `c1InputData_exists_iff_positivity`).
- The finite-vanishing universal `≤0` remains refuted; nothing here negates
  847/848.