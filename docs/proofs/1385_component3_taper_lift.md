# 1385 — Component 3: smooth taper lift to the (1 + eps) local budget

Date: 2026-09-13.

Status: FORMAL. This closes N2beta component 3 of the 009 contract (smooth
taper with perturbed-Gram inverse stability). It does not prove the
Young/convolution same-owner budget (component 4), the quantitative F1/F2
recast or any N1c margin (component 5), a global decay rate, an orbit
instantiation, or RH.

## What component 3 had to deliver

The 009 contract's deliverable theorem body (target, verbatim modulo the
closed form of `K_loc`):

```text
∃ f : CompactLogTest,
  Function.support f.test ⊆ Set.Ioo a b ∧
    (∀ i, laplaceAt f (nodes i) = y i) ∧
    compactLogL2sq f ≤ (1 + ε) * K_loc
```

for an open window `(a, b)`, a DISTINCT-node family `nodes : ι → ℂ`, any
target values `y : ι → ℂ`, and any `ε > 0`. Component 2c certified
`K_loc = y* G⁻¹ y` as a lower bound for moment-realizing tests; component 3
shows the bound is essentially SHARP: the cost can be pushed within any
multiplicative `(1 + ε)` of it by an actual owner. The key analytic point
(1377 Lemma A′) is that the untapered exponential combination cannot be
localized below `K_loc`, so the only route is to taper and control the
cost the taper's sliver region adds.

## Formal owner and theorem anatomy

Two leaves, each with a paired audit.

`ConnesWeilRH/Dev/C1WindowTaperCore.lean` (prior wave, committed with this
one): the tapered window Gram `windowTaperGram a b τ s t`, its matrix, the
quadratic identity `(star c ⬝ᵥ (T c)).re = ∫ τ ‖W_c‖²`, the per-node
trivial-kernel law and hence `IsUnit` of the tapered Gram for distinct
nodes, and the solve lemma `windowTaperGram_solve_mulVec`.

`ConnesWeilRH/Dev/C1WindowTaperLift.lean` (19 public declarations):

- `windowTaperComb_norm_bound`: every representer combination is uniformly
  bounded on the window by `‖coeff‖ * windowTaperBound a b nodes` with the
  explicit finite node-norm sum `windowTaperBound`.
- `windowExpGram_energy_strict_pos` + `windowExpGram_energy_continuous`:
  the untapered energy `v ↦ (star v ⬝ᵥ (G v)).re` is strictly positive off
  the origin (via the 1384 finite-exponential distinctness lemma) and
  continuous.
- `windowExpGram_gap`: the sphere-minimum spectral gap `α > 0` with
  `α * ‖v‖² ≤ (star v ⬝ᵥ (G v)).re` for all `v` (`IsCompact.exists_isMinOn`
  on the unit sphere of `ι → ℂ`).
- `windowTaperSliver_bound`: for a continuous nonnegative taper equal to
  one on a sub-window `Icc p q`, the sliver energy satisfies
  `∫ (1 - τ) ‖W_c‖² ≤ ((b - a) - (q - p)) * TB² * ‖c‖²`. Note the `τ ≤ 1`
  hypothesis is NOT needed for this estimate; the leaf states exactly what
  the proof uses.
- `windowTaperCorrection`: the actual `CompactLogTest` owner — a
  `ContDiffBump` taper times the solved combination, built through
  `HasCompactSupport.toSchwartzMap` in the repo's `∞` idiom. Its four
  interface lemmas: pointwise evaluation (`rfl` through the SchwartzMap
  coercion chain), support in `Ioo a b`, exact node values
  `laplaceAt (owner) (nodes j) = y j` whenever the tapered system is
  solved, and cost `compactLogL2sq f ≤ (star c ⬝ᵥ (T c)).re`.
- `windowTaperCorrection_budget`: the squeeze
  `(α - η) * compactLogL2sq f ≤ α * (star z ⬝ᵥ y).re` between the tapered
  solve `c` and the untapered solve `z`, consumed with the 1379 Cauchy-
  Schwarz pairing `‖star c ⬝ᵥ y‖² ≤ (star c ⬝ᵥ G c).re * (star z ⬝ᵥ y).re`.
- `exists_windowTaperCorrection_cost_le_one_plus_eps`: the wrapper. With
  `m = (a + b)/2`, `hw = (b - a)/2`, taper budget
  `Δ = ε * α / (4 * (1 + ε) * TB²)`, bump radii `rIn = hw - δ`,
  `rOut = hw - δ/2`, sliver cost `η = 2 * δ * TB² ≤ ε * α / (2 * (1 + ε))`,
  the gap comparison `α ≤ (1 + ε) * (α - η)` and the gap theorem's
  `hgaphyp` feed the budget theorem at the solved coefficient
  `c = T⁻¹ y` and the untapered solve `z = G⁻¹ y`, and `y = T c` realizes
  all values. For ANY `y` and ANY `ε > 0` this produces the owner.

The perturbed-Gram inverse is consumed through the trivial-kernel
invertibility (1384 law at the tapered weight), so "inverse stability" is
machine-checked, not assumed.

## Why the proof shape is right (first principles)

The cost of a tapering is exactly its non-platform region times the energy
density it multiplies: `η ~ (sliver width) * TB²`, while the gap `α` is a
window-and-node-only constant. Choosing the taper platform as the
`rIn`-ball inside the window drives the sliver width `2δ` to zero while
keeping support strictly inside `(a, b)`; the `(1 + ε)` factor is the
price of the gap comparison `α/(α - η) ≤ 1 + ε`. No polynomial or
exponential slack appears anywhere: the only losses are the explicit ones
above, each machine-checked.

## Evidence

Focused WSL runner logs: `009_taperlift_probe1.log` through
`009_taperlift_probe7.log` and the acceptance
`009_taperlift_accept.log` (repository build-log naming; kept in the
Linux-side verification environment). Error trajectory: 62 → 19 → 19 → 11 →
2 → 1 → 0 across seven probe iterations.

Acceptance build (both targets named explicitly, law of 1384):
`lake build ConnesWeilRH.Dev.C1WindowTaperLift
ConnesWeilRH.Dev.C1WindowTaperLiftAudit` — EXIT=0, zero `error:` lines,
zero `sorryAx`, no Dev-file warnings (only the three accepted lake
"has local changes" environment notes), and all 17 audit prints exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Boundary and next consumer

FORMAL lane only: no rate claim, no numeric margin, no orbit instantiation,
no RH-adjacent conclusion. The leaf supplies the budget PRODUCER for
component 4 (Young/convolution assembly: composing this owner with the
xi-side correction must keep the same-owner budget) and component 5
(quantitative F1/F2 recast presenting `K_loc` to the N1c joint-feasibility
interface of 1379: `(J1) x* > 2 C_min / δ` becomes checkable once a
healthy detector with computable `K_loc` and norm budget exists).
Map sync: 009 §4 component-3 flip, docs/map/README item 17.
