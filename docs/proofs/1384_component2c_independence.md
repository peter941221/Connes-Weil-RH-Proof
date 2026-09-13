# 1384 — Component 2c tail: window independence, Gram invertibility, and K_loc

Date: 2026-09-13 (record written retrospectively; the leaf went green and was
committed on 2026-09-13 without a record file — this closes that documentation
gap, see [009](../map/009_n2beta_core_bone_completion_contract.md) item 1).

Status: FORMAL. This completes N2beta component 2c and therefore contract 009
ladder item 1 (finite Hilbert interpolation: representers identified, minimum
L2 cost proved, inverse used only after nonsingularity). It does not prove a
feasibility margin against the N1c budget (item 2), construct a taper (item 3),
or assemble an owner (item 4).

## What 2c tail had to deliver

The 2c core ([1383](1383_component2c_window_gram.md)) proved the cost
comparison `(star coeff ⬝ᵥ y).re ≤ compactLogL2sq f` for every *solved* Gram
system, and deliberately registered no independence, existence, or
invertibility claim. Contract 009 item 1 forbids using an inverse before
proving the Gram matrix nonsingular. The tail therefore owes four things:

1. linear independence of the window exponential family;
2. the bridge from a vanishing Gram quadratic form to a vanishing combination;
3. trivial kernel, hence `IsUnit`, of the concrete window Gram for distinct
   nodes;
4. the `K_loc` instantiation of the 2c-core cost comparison at the inverse
   solve `coeff = G⁻¹ y` (record [1379](1379_n1c_joint_feasibility.md),
   Lemma E).

## Formal owner and theorem anatomy

One leaf, paired with one audit.

`ConnesWeilRH/Dev/C1WindowMellinIndependence.lean` (7 public declarations):

- `hasDerivAt_exp_mul_coe (μ : ℂ) (x : ℝ)` — pointwise derivative of a pure
  complex exponential along the real axis; the analytic kernel of the
  independence induction;
- `finiteExp_windowComb_eq_zero` — the independence proof: a `Finset` induction
  whose step shifts the vanishing combination by `exp (-nodesⱼ x)` and then
  kills the remaining analytic combination by pointwise differentiation and
  uniqueness of the derivative;
- `continuous_nonneg_windowIntegral_zero` — a continuous nonnegative function
  with zero window integral vanishes pointwise on the window;
- `windowExpGramMatrix_mulVec_eq_zero` — trivial kernel: a Gram matrix times a
  vector is zero only when the vector is zero, for distinct nodes on an open
  window;
- `windowExpGramMatrix_isUnit_of_injective` — `IsUnit` of the concrete window
  Gram for an injective node family, via
  `Matrix.mulVec_injective_iff_isUnit` with `A` pinned explicitly;
- `solvedWindowGram_cost_le_compactLogL2sq` — the 2c-core cost comparison with
  invertibility as an EXPLICIT hypothesis `hG : IsUnit G` (not a `let`
  binding), so the proof term never enters the statement type;
- `windowGramInverse_cost_le_compactLogL2sq` — **the deliverable**: the
  record-1379 local-mass quantity is a machine-checked lower bound,

  ```text
  K_loc = (star (G⁻¹ y) ⬝ᵥ y).re ≤ compactLogL2sq f
  ```

  for every supported test realizing the target values `y` on distinct nodes.

## Why the proof shape is right (first principles)

Two design decisions carry the weight.

**No Vandermonde route.** The Gram entries here are WINDOW INTEGRALS
`(e^{λb} - e^{λa})/λ`, not pure powers `λ^k`, so the classical
Vandermonde-determinant argument does not apply. Independence is proved from
scratch on the difference family by `Finset` induction; Mathlib has no
`linearIndependent_exp` to borrow.

**Invertibility as a hypothesis, not a `let`.** Binding
`let hG := windowExpGramMatrix_isUnit_of_injective ...` inside a statement type
forces whnf of a proof term containing `Classical.choose` plus a tactic block,
and dies on a deterministic timeout (heartbeat 200000). Splitting the solve
into a standalone `have hsolve : G.mulVec w = y` and taking `hG` as an explicit
hypothesis removes the whnf pressure entirely. A thin corollary supplies the
invertibility from injectivity.

The rank-deficient branch is characterized rather than assumed away: it occurs
only for coinciding nodes. That is the honest content of "use an inverse only
after proving nonsingularity".

## Evidence

Focused WSL runner logs (repository build-log naming, kept in the Linux-side
verification environment): probes `009_independence_probe1.log` through
`009_independence_probe6.log`, build `009_independence_build1.log`, acceptance
`009_independence_build2.log`, audit `009_independence_audit2.log`. The
preceding abstract-Gram series is `009_gram_quadratic_try11-14`,
`009_gram_strictpos_try15-16`, `009_gram_kernel_try17-18`,
`009_gram_kernel_semantics_try19`, `009_gram_kernel_implication_try20-23`,
`009_gram_moments_try24-25`, `009_gram_minnorm_try26-30`.

Acceptance log read back on 2026-09-13 (this record's writing pass):

```text
Build completed successfully (3549 jobs).
^error: lines = 0     sorryAx = 0     'Quot.sound' prints = 7
```

7 prints = the 7 declarations of `C1WindowMellinIndependenceAudit.lean`, each
exactly `[propext, Classical.choice, Quot.sound]`.

Environment law established on this leaf and forwarded to AGENTS §7a: the
default `lake build` does NOT compile new Dev leaves (nothing imports them), so
the acceptance build must name BOTH modules explicitly
(`lake build Dev.X Dev.XAudit`), and `lake env lean` on the Audit errors
"olean does not exist" until the leaf is built — build before audit.

Trap ledger forwarded to AGENTS §7b: `dotProduct` and `dotProduct_zero` are
BARE top-level names (`Matrix.dotProduct` is unknown); `Finset.induction_on`
over a family carrying `[DecidableEq ι]` needs `classical` at the very start;
`𝓝` needs `open scoped Topology`; `filter_upwards` is the neighborhood-transport
idiom; `Matrix.mulVec_injective_iff_isUnit` must be pinned `(A := ...)`; and
the whnf heartbeat killer above.

## Boundary and next consumer

FORMAL lane only: no feasibility margin, no numeric digit, no decay rate, no
orbit instantiation, no RH. The value-realization hypothesis of
`solvedWindowGram_cost_le_compactLogL2sq` is the open analytic interface
inherited from the orbit package; it is consumed, not proved, here.

The consumer chain is
[1385](1385_component3_taper_lift.md) (smooth taper lift to
`(1 + ε) · K_loc`, which uses the trivial-kernel law above to consume the
perturbed-Gram inverse) and then
[1386](1386_component4_young_assembly.md) (same-owner Young assembly), whose
budget is expressed in exactly the `K_loc` certified here.
