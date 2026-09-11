# 1328 — G8 P1 quantitative column-energy alignment (HS adjoint invariance + two-channel ledger)

Date: 2026-09-11.
Status: VERIFIED (batch build `1541_g8_p1_quantitative_alignment_batch.log`).
Owner route: G8 P1 metric-to-radial transport, conditional on the single
named full-carrier column-energy premise.  Consumers unchanged: the same
healthy-`CompactLog` B5 detector-specific semi-local positivity chain.

## 1. Context

Record 1327 (`C1G8P1ColumnEnergyAlignment`) aligned the two P1 boundary
channels *summability-wise*: both channels eat the same composite
`antiCol ∘L newFrame† ∘L oldFrame`, and the metric-side basis energy is
summable whenever the full-carrier column energy
`∑_i ‖antiCol (newFrame† u_i)‖²` is summable.

1327's generic engine (`summable_comp_normSq_of_contractive_pull`) only
transfers *finiteness*.  For the P2 aggregate inequality the ledger needs
*constants*: an explicit bound of the metric boundary energy by a named
multiple of the column energy.  This record upgrades the alignment from
"summability-wise" to "quantitative".

## 2. Construction

File: `ConnesWeilRH/Dev/C1G8P1ColumnEnergyQuantitativeAlignment.lean`
(namespace `ConnesWeilRH.Source.C1G8P1ColumnEnergyQuantitativeAlignment`).

Six statements:

1. `realParseval` — Parseval's identity in real norm-square form along any
   `HilbertBasis` of a complex inner product space:
   `‖x‖² = ∑' i, ‖⟪b i, x⟫‖²`.  Routed through `tsum_inner_mul_inner`
   + `Complex.mul_conj` + `Complex.reCLM.map_tsum`.

2. `hsNormSq_adjoint_invariance` — the engine:
   `∑_j ‖T b_j‖² = ∑_i ‖T† u_i‖²` along *arbitrary* Hilbert bases of
   domain and codomain, assuming both outer series are summable (the two
   hypotheses `hsrc`, `hadj`).  Proof: one shared nonnegative coefficient
   matrix `‖⟪carrierBasis i, operator (sourceBasis j)⟫‖²`, two
   partial-sum comparisons via `Real.tsum_le_of_sum_le`, the finite/infinite
   exchange via `(Summable.tsum_finsetSum ·).symm` (pointwise column
   summability from Parseval-side `inner_products_summable`), row bounds via
   `Summable.sum_le_tsum` transferred by `Summable.of_nonneg_of_le`, and
   `le_antisymm`.

3. `comp_normSq_le_of_contractive_pull` — precomposition cost:
   ```text
   ∑_j ‖(column ∘L pull) b_j‖² ≤ ‖pull‖² · ∑_i ‖column u_i‖²
   ```
   Proof: invariance on both composites, pointwise
   `‖(column∘pull)† u_i‖ ≤ ‖pull‖ · ‖column† u_i‖` via
   `ContinuousLinearMap.le_opNorm` + `adjoint.norm_map`, then
   `Summable.tsum_le_tsum` + `le_of_eq tsum_mul_left`.

4. `metricBoundaryComposite_normSq_le_fullCarrierColumnEnergy` — the
   instantiated metric channel: with `pull := oldSuffixFrame` and
   `column := antiCol ∘L newFrame†`,
   `E_metric ≤ ‖oldFrame‖² · E_col`.

5. `...Contractive` — since `‖oldSuffixFrame‖ ≤ 1`
   (`norm_oldSuffixFrame_le_one`), `E_metric ≤ E_col`.

6. `p1BoundaryEnergyLedger_of_fullCarrierColumnEnergy` — the two-channel
   P1 ledger under the single named premise `hcolumn`:
   ```text
   ∑_j ‖radialSoninBoundaryCrossing p S (oldFrame b_j)‖²
     + ∑_j ‖(antiCol ∘L newFrame† ∘L oldFrame) b_j‖²
   ≤ (1 + (32 · ‖(coeff p : ℂ)⁻¹‖)²) · ‖oldFrame‖² · E_col
   ```
   The radial leg uses the 1325 pointwise bound
   `‖crossing (oldFrame x)‖ ≤ 32·‖q_p⁻¹‖·‖antiCol (newFrame† (oldFrame x))‖`
   squared and summed; the metric leg is statement 4; legs combined by
   `add_le_add` + `ring`.

## 3. Verification

- Batch build (round 6 final): `Build completed successfully (3490 jobs)`,
  `EXIT:0`, zero `error:` lines, zero `sorryAx`.
- Axiom audit: 14 `#print axioms` outputs in the log = 6 new statements +
  8 regression statements (`C1G8P1ColumnEnergyAlignmentAudit` replay);
  **all 14 are `[propext, Classical.choice, Quot.sound]`**.
- Mirror sync MD5-verified at every round
  (`/home/peter/rh/ConnesWeilRH/Dev/`).

Debug rounds (6 total):

| round | errors | root cause |
|---|---|---|
| 1 | 5 groups | NNReal bridge (`toNNReal` argument shape, congr direction) |
| 2 | — | switched strategy to all-ℝ (`realParseval` passed) |
| 3 | 9 | `Summable.tsum_finsetSum` direction (needs `.symm`), fragile `▸` casts, `Summable.of_nonneg_of_le` fed to a `≤` goal, `mul_le_of_le_one_right` vs `_left`, `tsum_mul_left` is argument-free |
| 4 | 1 | `linarith` fed unfolded atoms (`pull.adjoint (column.adjoint _)` vs the composite form in the goal) |
| 5 | 1 | `sq_le_sq'` first hypothesis is `-b ≤ a`, not `0 ≤ a`; replaced by `nlinarith` with explicit `norm_nonneg` atoms |
| 6 | 0 | green |

## 4. Boundary (non-claims)

- The full-carrier column-energy summability premise `hcolumn` is NOT
  proved here.  It remains the single named analytic input of P1
  (records 1324-1327 lineage).
- No vanishing, no sign, no cutoff-limit, and no RH-facing claim is
  asserted.  This record makes the conditional gate *quantitative*: with
  the premise, both P1 channels are bounded by one closed constant times
  one energy, which is exactly the shape the endpoint/P2 aggregate
  inequality will consume.
- Structural note carried into the probe preregistration: instantiating
  `C := loss† ∘ P_range(newFrame)` (since `newFrame ∘L newFrame†` is the
  range projection and `antiCol = loss† ∘L newFrame`), the premise reads
  `‖(I + U_{-log p}) ∘ P_S‖²_HS < ∞` up to the scalar
  `lossScale p = √q_p/(1+q_p)`; since `P_S` has infinite rank, this is
  equivalent to asymptotic `p`-antiperiodicity of the frame range — a
  sharp, falsifiable claim (see probe prereg, workflow C).
