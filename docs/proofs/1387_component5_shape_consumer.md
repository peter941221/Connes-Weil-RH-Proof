# 1387 — Component 5 shape layer: route (A) locked, the N1c margin consumer

Date: 2026-09-13.

Status: FORMAL (shape layer only). This opens N2beta component 5 of the
[009](../map/009_n2beta_core_bone_completion_contract.md) contract and locks
the route-(A) branch of record
[1379](1379_n1c_joint_feasibility.md) section 4 as an owner decision. It does
NOT close component 5: the two quantitative premises (`hfit`, `hJ1`) remain
undischarged hypotheses, no orbit is instantiated, no numeric digit is
registered, and no healthy-detector field is produced. No RH claim.

## Owner decision: route (A), not route (B)

Record 1379 section 4 resolved the vertical bridge into a construction-class
question and left exactly two branches, explicitly marked as an owner-facing
route decision:

```text
(A)  design a visible-anchor family with an explicit NORM BUDGET
     ||g||^2 <= delta/(2 C_min)  — a new producer target (N2-beta);
(B)  restrict the closure to the near-line band, where the budget
     condition is replaced by the ratio condition alone.
```

**Ruling: route (A).** Rationale, first-principles:

- Components 1–4 of the 009 ladder already produce exactly what (A) asks for
  and nothing that (B) needs. The record-1386 deliverable is an UPPER bound
  `compactLogL2sq g ≤ (d − c) · ‖u‖₂² · ((1 + ε) · K_loc)`; route (B) never
  consumes an upper bound at all. Choosing (B) would strand four green
  components.
- Route (A) is the branch that escapes the [1371] invisible-anchor floor, so
  condition (J2) drops and (J1) alone decides. Route (B) survives only inside
  the near-line band `dR ≲ 0.53`, which is a MODEL-lane regime restriction,
  not a theorem.
- (A) keeps the falsifier honest: it produces a budget that can FAIL against
  real digits, which is what makes the eventual margin a certificate rather
  than a hope.

Consequence for the ladder: component 5 splits into a digit-free SHAPE layer
(this record) and a digit-bearing DISCHARGE layer (open, prereg-gated).

## What the shape layer had to deliver

Contract 009 item 5 asks for the F1/F2 recast with the same detector's
support, healthy data, values, and L2 upper bound, substituted into N1c to
yield a positive local-mass margin. The formal part of that is a consumption
chain, and the chain has a natural cut point:

```text
   record 1386 owner                (J1) ceiling test            N1c delivery
  ┌──────────────────────┐        ┌──────────────────────┐     ┌──────────────┐
  │ compactLogL2sq g     │  FIT   │ ceiling < δ/(2·C_min) │     │ 0 < B_δ      │
  │  ≤ (d−c)·‖u‖₂²·      │ ─────> │                      │ ──> │              │
  │    ((1+ε)·K_loc)     │        │  ⇒ 0 < δ/2 − C_min·  │     │ via Lemma D  │
  │                      │        │      compactLogL2sq g │     │ bridge bound │
  └──────────────────────┘        └──────────────────────┘     └──────────────┘
        FORMAL (1386)                  FORMAL (this record)      PAPER hypothesis
```

Keeping `FIT` and `(J1)` as SEPARATE premises is the design decision. `FIT` is
the construction side — it is where the orbit instantiation and the digits will
land. `(J1)` is the analysis side — it is the single inequality the whole
route-(A) branch hangs on. Merging them into one hypothesis would hide which
half a future failure belongs to.

## Formal owner and theorem anatomy

One leaf, paired with one audit.

`ConnesWeilRH/Dev/C1QuantitativeConsumer.lean` (7 public declarations):

- `margin_pos_of_cost_le_ceiling` — the abstract (J1) consumer:
  `cost ≤ ceiling` and `ceiling < δ / (2 · C_min)` with `0 < C_min` give
  `0 < δ / 2 − C_min · cost`. The proof is the two-step squeeze, the second
  step being (J1) read after clearing the positive denominator `2 · C_min`.
  `C_min > 0` is genuinely required: at `C_min = 0` the ceiling
  `δ / (2 · C_min)` is `0` in `ℝ` and (J1) would be vacuous for a nonnegative
  cost.
- `margin_pos_of_owner_cost_fits` — the same statement on the genuine
  `compactLogL2sq` accessor, so a `CompactLogTest` owner can be fed directly.
- `bandBridge_pos_of_margin_pos` — the record-1378 Lemma-D consumption step:
  a delivery bound `B_δ ≥ (δ/2)·|G(s_v)|² − C_min·‖g‖²` with the forced
  normalization `|G(s_v)|² = 1` turns a positive margin into `0 < B_δ`. The
  bridge inequality is PAPER-lane analysis and stays a hypothesis; nothing here
  proves Plancherel, localization, or a damping split.
- `laplaceAt_assembled_eq_zero_of_target_eq_zero` — the F1/F2 VANISHING hook:
  because record 1386 makes node values MULTIPLY, a zero target value kills the
  assembled owner at that node with no hypothesis on the base value.
- `laplaceAt_assembled_ne_zero_of_target_ne_zero` — the F1/F2 DETECTION hook
  (`detectsRho` side): nonvanishing base value times nonvanishing target keeps
  the assembled owner nonvanishing at the node.
- `exists_assembledOwner_margin_pos` — **the consumer deliverable**: the SAME
  single owner `u.convolution f` of record 1386, with its summed support window
  `Ioo (c + a) (d + b)` and its node values `laplaceAt u (nodes i) * y i`, now
  carrying a strictly positive N1c local-mass margin under `hfit` + `hJ1`.
- `exists_assembledOwner_bandBridge_pos` — the shape-layer endpoint: that owner
  delivers `0 < B_δ` through any record-1378-shaped bridge bound available on
  its summed window class.

The budget expression in `hfit` is spelled byte-identically to the way record
1386 emits it, so the two premises chain by `le_trans` with no cast and no
defeq bridge.

## Why the proof shape is right (first principles)

The consumer is arithmetic, and the arithmetic is trivial once the cut point is
chosen correctly. That triviality is the point: it localizes ALL remaining risk
into two named hypotheses instead of spreading it through a proof.

Two traps were designed around rather than fought:

- **The whnf heartbeat killer of record 1384.** `K_loc` contains
  `(windowExpGramMatrix_isUnit_of_injective ...).unit⁻¹`, i.e. a proof term
  inside a statement type. Record 1386 already carries that spelling in its
  conclusion and compiles, so the consumer mirrors the spelling exactly instead
  of introducing a `def` wrapper that would need a defeq bridge back.
- **The division-inequality naming split at this pin.** The positive-denominator
  form is `lt_div_iff₀` (`Mathlib/Algebra/Order/GroupWithZero/Unbundled/
  Basic.lean:1131`); a bare `lt_div_iff` is an Unknown identifier. This cost
  one build iteration (try1 → try2) and is forwarded to AGENTS §7b.

## Evidence

Focused WSL runner logs (repository build-log naming, kept in the Linux-side
verification environment): `009_consumer_try1.log` (2 errors, both
`Unknown identifier lt_div_iff`), acceptance `009_consumer_try2.log`. Error
trajectory: 2 → 0.

Acceptance build (both targets named explicitly, law of 1384):

```text
lake build ConnesWeilRH.Dev.C1QuantitativeConsumer
           ConnesWeilRH.Dev.C1QuantitativeConsumerAudit

Build completed successfully (3553 jobs).
^error: lines = 0     sorryAx = 0     leaf warnings = 0
'Quot.sound' prints = 7  (= the 7 declarations of the audit leaf)
```

All seven declarations print exactly `[propext, Classical.choice, Quot.sound]`,
including both deliverables:

```text
'ConnesWeilRH.Source.C1QuantitativeConsumer.exists_assembledOwner_margin_pos'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'ConnesWeilRH.Source.C1QuantitativeConsumer.exists_assembledOwner_bandBridge_pos'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

Source-level cross-check: zero `sorry` / `admit` / `axiom` occurrences in the
leaf.

## Boundary and next consumer

What this record does NOT do:

- it does not discharge `hfit` — that needs the orbit instantiation (actual
  `nodes`, actual `y`) plus the digits;
- it does not discharge `hJ1` — that needs `δ` and `C_min`, which are
  MODEL-lane quantities requiring rig confirmation under the
  prereg-before-digits protocol of record 1373;
- it does not produce any field of `HealthyYoshidaDetectorData`. The two value
  hooks above are the interface, but the kill set is
  `cc20TripleFiniteVanishingSet` (fixed by the register, not chosen here), so
  wiring demands a node family that contains it — an orbit instantiation;
- it does not prove the record-1378 band bridge, spectral nonnegativity, any
  N3/N4 input, or RH.

Component 5 therefore remains OPEN. Its remaining content is exactly:
(i) the prereg document fixing `δ`, the window `(a, b)`, `d = Re s_v`, the node
family and the value pattern `y` BEFORE any digit is computed; (ii) the orbit
instantiation discharging `hfit`; (iii) the rig-confirmed digits discharging
`hJ1`; (iv) the healthy-data wiring through the two value hooks.

Map sync: [009](../map/009_n2beta_core_bone_completion_contract.md) gains a
route-(A) ruling section and a component-5 shape-layer entry;
`docs/map/README` gains this record.
