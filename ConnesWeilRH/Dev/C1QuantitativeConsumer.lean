/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1WindowTaperAssembly

/-!
# C1QuantitativeConsumer - route-(A) margin consumer (N2beta component 5, shape layer)

Contract 009 item 5 requires the F1/F2 construction to be recast with the same
detector's support, healthy data, values, and L2 upper bound, and the result to
be substituted into the record-1379 joint-feasibility test so that a positive
local-mass margin comes out.  Route (A) of record 1379 section 4 is the branch
now locked by the owner: a visible-anchor family carrying an EXPLICIT NORM
BUDGET, so the [1371] invisible-anchor floor never binds, condition (J2)
drops, and (J1) alone decides.

This leaf builds the digit-free formal shape of that consumption.  It
separates the two inputs route (A) needs and keeps them apart on purpose:

- `hfit`  (FIT):   the record-1386 factorized budget of the assembled owner,
                   `(d - c) · ‖u‖₂² · ((1 + ε) · K_loc)`, fits under a ceiling.
                   This is the CONSTRUCTION side; it is where the orbit
                   instantiation and the numeric digits will land.
- `hJ1`   (J1):    that ceiling sits strictly below the record-1379 budget
                   ceiling `δ / (2 · C_min)`.  This is the ANALYSIS side; it
                   is the single inequality the whole route-(A) branch hangs on.

Deliverables, in dependency order:

- `margin_pos_of_cost_le_ceiling`: the abstract (J1) consumer — any cost under
  a ceiling satisfying (J1) leaves `δ / 2 - C_min · cost` strictly positive;
- `margin_pos_of_owner_cost_fits`: the same statement on the genuine
  `compactLogL2sq` accessor, so a `CompactLogTest` owner can be fed directly;
- `bandBridge_pos_of_margin_pos`: the record-1378 Lemma-D consumption step —
  a delivery bound `B_δ ≥ (δ/2)·|G(s_v)|² - C_min·‖g‖²` with the forced
  normalization `|G(s_v)|² = 1` turns a positive margin into positive
  delivered band mass.  The bridge inequality itself is the paper-lane input
  and stays a hypothesis; nothing here proves Plancherel or localization;
- `laplaceAt_assembled_eq_zero_of_target_eq_zero` and
  `laplaceAt_assembled_ne_zero_of_target_ne_zero`: the two F1/F2 recast hooks
  on the multiplicative value law of record 1386 — a zero target value kills
  the assembled owner at that node (the vanishing side of the healthy-data
  package), a nonvanishing base value times a nonvanishing target keeps the
  owner detecting the node (the `detectsRho` side);
- `exists_assembledOwner_margin_pos`: the consumer deliverable — the SAME
  single owner `u.convolution f` of record 1386, with its summed support
  window and its node values, now carrying a strictly positive N1c local-mass
  margin;
- `exists_assembledOwner_bandBridge_pos`: the endpoint — that owner delivers
  strictly positive band mass `0 < B_δ` through any record-1378-shaped bridge
  bound on its window class.

Lane discipline: FORMAL only.  No decay rate, no orbit instantiation, no
numeric digit, no `C_min` or `δ` value, no N3/N4 input, no spectral
nonnegativity, no RH-adjacent conclusion.  The two premises `hfit` and `hJ1`
are exactly the open interfaces; discharging them is the remaining work of
contract 009 item 5 and is governed by the prereg-before-digits protocol.

Design record: docs/map/009_n2beta_core_bone_completion_contract.md, item 5.
-/

namespace ConnesWeilRH
namespace Source
namespace C1QuantitativeConsumer

open MeasureTheory
open scoped Topology
open scoped ContDiff
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution.CompactLogTest
open C1CompactLogL2Export
open C1WindowMellinIndependence
open C1WindowTaperLift
open C1WindowTaperAssembly

/-! ### 1. The abstract (J1) consumer -/

/-- The digit-free core of contract 009 item 5 on route (A): a cost that fits
under a ceiling satisfying the record-1379 condition (J1),
`ceiling < δ / (2 · C_min)`, leaves the delivery margin
`δ / 2 - C_min · cost` strictly positive.  The proof is the two-step squeeze
`cost ≤ ceiling` and `C_min · ceiling < δ / 2`, the latter being (J1) read
after multiplying through by the positive `2 · C_min`.  `C_min > 0` is required:
at `C_min = 0` the ceiling `δ / (2 · C_min)` is `0` in `ℝ` and (J1) would be
vacuous for a nonnegative cost. -/
theorem margin_pos_of_cost_le_ceiling {δ Cmin cost ceiling : ℝ}
    (hC : 0 < Cmin) (hcost : cost ≤ ceiling)
    (hJ1 : ceiling < δ / (2 * Cmin)) :
    0 < δ / 2 - Cmin * cost := by
  have h2C : 0 < 2 * Cmin := mul_pos (by norm_num : (0 : ℝ) < 2) hC
  -- (J1) with the denominator cleared: `ceiling * (2 * Cmin) < δ`.  At this
  -- pin the positive-denominator form carries the `₀` suffix: a bare
  -- `lt_div_iff` is an Unknown identifier.
  have hmul : ceiling * (2 * Cmin) < δ := (lt_div_iff₀ h2C).mp hJ1
  have hcomm : ceiling * (2 * Cmin) = 2 * (Cmin * ceiling) := by ring
  rw [hcomm] at hmul
  have hkey : Cmin * ceiling < δ / 2 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm]
    exact hmul
  have hle : Cmin * cost ≤ Cmin * ceiling :=
    mul_le_mul_of_nonneg_left hcost hC.le
  linarith

/-! ### 2. The owner-level wrapper -/

/-- (J1) read on the genuine squared-L2 accessor: any `CompactLogTest` owner
whose `compactLogL2sq` fits under a (J1)-ceiling has a strictly positive N1c
local-mass margin.  This is the form the assembled owner of record 1386 is
fed into. -/
theorem margin_pos_of_owner_cost_fits {δ Cmin ceiling : ℝ} (hC : 0 < Cmin)
    (g : CompactLogTest) (hcost : compactLogL2sq g ≤ ceiling)
    (hJ1 : ceiling < δ / (2 * Cmin)) :
    0 < δ / 2 - Cmin * compactLogL2sq g :=
  margin_pos_of_cost_le_ceiling hC hcost hJ1

/-! ### 3. The record-1378 band-bridge consumption step -/

/-- The bridge consumer.  Record 1378 Lemma D delivers
`B_δ ≥ (δ/2)·|G(s_v)|² - C_min·‖g‖²`, and the record-1379 normalization
forces `|G(s_v)|² = 1`; together with a positive margin that gives positive
delivered band mass.  The bridge inequality is PAPER-lane analysis and is
therefore an explicit hypothesis: this leaf proves the consumption, not the
bridge. -/
theorem bandBridge_pos_of_margin_pos {Bδ δ Cmin Gsq cost : ℝ}
    (hbridge : (δ / 2) * Gsq - Cmin * cost ≤ Bδ) (hG : Gsq = 1)
    (hmargin : 0 < δ / 2 - Cmin * cost) : 0 < Bδ := by
  have hb : δ / 2 - Cmin * cost ≤ Bδ := by
    rw [hG, mul_one] at hbridge
    exact hbridge
  linarith

/-! ### 4. The F1/F2 recast hooks on the multiplicative value law -/

/-- The vanishing side of the healthy-data package, recast onto the assembled
owner: because record 1386 makes the node values MULTIPLY
(`laplaceAt g = laplaceAt u * y`), a zero target value kills the assembled
owner at that node with no hypothesis on the base value. -/
theorem laplaceAt_assembled_eq_zero_of_target_eq_zero {ι : Type*} (i : ι)
    (g u : CompactLogTest) (nodes : ι → ℂ) (y : ι → ℂ)
    (hval : laplaceAt g (nodes i) = laplaceAt u (nodes i) * y i)
    (hy : y i = 0) : laplaceAt g (nodes i) = 0 := by
  rw [hval, hy, mul_zero]

/-- The detection side (`detectsRho`), recast onto the assembled owner: a
nonvanishing base value times a nonvanishing target value keeps the assembled
owner nonvanishing at the node. -/
theorem laplaceAt_assembled_ne_zero_of_target_ne_zero {ι : Type*} (i : ι)
    (g u : CompactLogTest) (nodes : ι → ℂ) (y : ι → ℂ)
    (hval : laplaceAt g (nodes i) = laplaceAt u (nodes i) * y i)
    (hu : laplaceAt u (nodes i) ≠ 0) (hy : y i ≠ 0) :
    laplaceAt g (nodes i) ≠ 0 := by
  rw [hval]
  exact mul_ne_zero hu hy

/-! ### 5. The consumer deliverable on the record-1386 assembled owner -/

/-- Contract 009 item 5, shape layer: the SAME single owner `u.convolution f`
of record 1386 — summed support window `Ioo (c + a) (d + b)` and node values
`laplaceAt u (nodes i) * y i` — now carries a strictly positive N1c local-mass
margin, provided its factorized budget `(d - c) · ‖u‖₂² · ((1 + ε) · K_loc)`
fits under a ceiling (`hfit`, the construction side) and that ceiling obeys
(J1) (`hJ1`, the analysis side).  The budget expression is spelled exactly as
record 1386 emits it so the two premises chain by `le_trans` with no cast. -/
theorem exists_assembledOwner_margin_pos
    {δ Cmin ceiling : ℝ} (hC : 0 < Cmin)
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (nodes : ι → ℂ) (hne : Function.Injective nodes) (y : ι → ℂ)
    (u : CompactLogTest) (hu : Function.support u.test ⊆ Set.Ioo c d)
    {ε : ℝ} (hε : 0 < ε)
    (hfit : (d - c) * compactLogL2sq u *
        ((1 + ε) * (dotProduct (star (Matrix.mulVec
          ↑(windowExpGramMatrix_isUnit_of_injective hab nodes hne).unit⁻¹
          y)) y).re) ≤ ceiling)
    (hJ1 : ceiling < δ / (2 * Cmin)) :
    ∃ g : CompactLogTest,
      Function.support g.test ⊆ Set.Ioo (c + a) (d + b) ∧
        (∀ i : ι, laplaceAt g (nodes i) = laplaceAt u (nodes i) * y i) ∧
        0 < δ / 2 - Cmin * compactLogL2sq g := by
  obtain ⟨g, hgsupp, hgval, hgcost⟩ :=
    exists_assembledOwner_cost_le hab hcd nodes hne y u hu hε
  exact ⟨g, hgsupp, hgval,
    margin_pos_of_owner_cost_fits hC g (le_trans hgcost hfit) hJ1⟩

/-- The route-(A) endpoint at the shape layer: under the same two premises,
the assembled owner of record 1386 delivers strictly positive band mass
`0 < B_δ` through ANY record-1378-shaped bridge bound available on its summed
window class.  The bridge is supplied as a hypothesis quantified over the
window class, so no localization, Plancherel, or damping-split analysis enters
the formal lane here. -/
theorem exists_assembledOwner_bandBridge_pos
    {Bδ δ Cmin ceiling Gsq : ℝ} (hC : 0 < Cmin) (hG : Gsq = 1)
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (nodes : ι → ℂ) (hne : Function.Injective nodes) (y : ι → ℂ)
    (u : CompactLogTest) (hu : Function.support u.test ⊆ Set.Ioo c d)
    {ε : ℝ} (hε : 0 < ε)
    (hfit : (d - c) * compactLogL2sq u *
        ((1 + ε) * (dotProduct (star (Matrix.mulVec
          ↑(windowExpGramMatrix_isUnit_of_injective hab nodes hne).unit⁻¹
          y)) y).re) ≤ ceiling)
    (hJ1 : ceiling < δ / (2 * Cmin))
    (hbridge : ∀ g : CompactLogTest,
      Function.support g.test ⊆ Set.Ioo (c + a) (d + b) →
        (δ / 2) * Gsq - Cmin * compactLogL2sq g ≤ Bδ) :
    ∃ g : CompactLogTest,
      Function.support g.test ⊆ Set.Ioo (c + a) (d + b) ∧
        (∀ i : ι, laplaceAt g (nodes i) = laplaceAt u (nodes i) * y i) ∧
        0 < Bδ := by
  obtain ⟨g, hgsupp, hgval, hmargin⟩ :=
    exists_assembledOwner_margin_pos hC hab hcd nodes hne y u hu hε hfit hJ1
  exact ⟨g, hgsupp, hgval,
    bandBridge_pos_of_margin_pos (hbridge g hgsupp) hG hmargin⟩

end C1QuantitativeConsumer
end Source
end ConnesWeilRH
