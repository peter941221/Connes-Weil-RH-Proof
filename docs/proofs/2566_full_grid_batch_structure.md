# Record 2566 — Full-grid batch structure for the correction-second channel

Status update (records 2573-2574, 2026-10-04): the constant-per-cell
second-channel construction below is OVER BUDGET at the production grid
and must not be mass-generated under the old cost plan. Its full-grid
external totals are about 5.14e6 and 5.11e6 against the 666472.585392 pin.
Record 2574 proves a same-owner endpoint-chord replacement, with external
prices about 183747 and 157982. The replacement needs separate endpoint
and fourth-envelope tables; the old three-sum affine plan and the claim
that 2561 prices its analytic totals are superseded. The original draft
below is retained as history. See 2573_decomposed_correction_grid_failure.md
and 2574_same_owner_second_chord.md.

Verdict: DESIGN DRAFT, no certificate. This record fixes the architecture,
the cost model, and the lane decomposition for scaling the certified cell2700
pipeline (2563 plus, 2565 minus) to all 10240 cells at both endpoint signs,
discharging the D(c) side of the 2560 two-channel bridge. It changes no
accepted proof file and claims no RH content.

## Target and acceptance

The 2562 consumer decomposes

  stripSecondNorm sigma (externalPhysical2344 coefficients modulations)
    <= signedSecondCompositeUpper2562 + 2|sigma| * signedFirstCompositeUpper2562
       + sigma^2 * signedCompositeUpper2539,

each composite being `sum index in Finset.range cells` of a per-cell summand
built from signedCurvatureUpper2539, signedJetUpper2539 (orders 1 and 0) at
grid positions. The full-grid batch must produce, per sign s in {+1/2, -1/2}:

1. per-cell theorems S_cell(i) <= cellUpper(i) for all 10240 cells, in the
   exact summand shape the composites consume;
2. a total theorem `sum over cells <= T_s` with T_s closing against the
   externally priced 2561 numbers, T_-1/2 = 126381.74-class, T_+1/2 =
   101290.55-class, under the pin 41654536587/62500 = 666472.585392;
3. every audited theorem on the axiom trio, centers/errors explicit at the
   2338 boxes (membership premise untouched).

## The structural lever: the total factors through three global sums

The certified three-piece summand is affine in its three inputs:

  S_cell = h*C + 2|sigma|*h*(J1 + C*h/2) + sigma^2*(h/2*(N0l + N0r) + C*h^3/12)
         = K1*C + K2*J1 + K3*(N0l + N0r),

with K1 = h + |sigma|*h^2 + sigma^2*h^3/12, K2 = 2|sigma|*h, K3 = sigma^2*h/2.
At sigma = +/-1/2 the constants are sign-independent (|sigma| and sigma^2
coincide), so one constant lemma serves both signs and only the leaf tables
differ.

Consequences:

- The per-cell assembly must NOT close a per-cell rational (the 2565
  correctionThirdL1Sum_eq_2565 chunked closure costs ~43 s of kernel time
  per cell and is the wrong shape at 10240 scale). Per-cell theorems keep
  the L1 curvature charge as an open Finset.sum expression and stop at
  S_cell(i) <= affine form in table rationals.
- Three global chunked closures (curvature aggregate, midpoint-jet
  aggregate, endpoint aggregate), one per aggregate per sign, carry the
  exact numerical content. A 300k-term sum of leaf rationals has a
  roughly 50-digit numerator - the 2565 closure was 177 digits and closed
  in seconds, so three global closures are cheap.
- The final total theorem is K1*CurvTotal + K2*JetTotal + K3*EdgeTotal <= T_s
  with the three totals as chunked rationals from the external exact
  engine (the 2561 engine computes exact Fraction totals in 40 s per sign;
  its per-cell columns double as the acceptance table).

## Cost model (existing single readings; no new measurements)

| lane | instances per sign | measured anchor | projected kernel cost |
|------|--------------------|-----------------|------------------------|
| edge order-0 + order-3 leaves (shared exp) | ~320470 (640940 both signs, 2553 count) | 2554: replay ~30 s per 30-family node | ~89 h user CPU |
| midpoint order-1 jet + order-2 leaf | ~160250 (320500 both signs) | 2553: ~35 s wall per 28-30-family node | ~45 h user CPU |
| fourth envelope | ~307k cell-family pairs | 2559: exact Horner replay per instance | TBD by lane decision below |
| per-cell assembly | 10240 | 2565 assembly 43 s WITHOUT the global-sum restructuring; restructured target: seconds | TBD after 2a |

Sequential wall at 16 logical CPUs is estimated in the 90-110 h range if
every fourth envelope is an exact replay; the analytic-envelope decision
below can remove most of that lane. All figures are extrapolations from
single matched readings (2552/2553/2554/2559) and are planning inputs,
not guarantees - the 2552 record's page-cache incident is the cautionary
precedent.

## Lane decomposition

- 2a (gate probe, must run first): the 2553/2554 open decision - on one
  fixed node input, compare the current cbv exponential replay against the
  kernel-only `decide` strategy and against a shared-replay variant, same
  inputs, one heavy lease. Deliverable: a timing readback choosing the
  replay mechanism for mass generation. No new mathematics.
- 2b edge lane: per-edge (10241 positions x 30 families x 2 signs) order-0
  values and order-3 norm leaves as closed-rational tables with per-instance
  theorems, extending the 2558/2559 generator pattern; adjacent cells share
  edge data (2559 already does this). Exterior families carry exact-zero
  certificates (weightedFamily_outside_zero2543), already counted in the
  2553 activity census.
- 2c fourth-envelope lane: prefer the 2459 W-C analytic envelope pattern
  (bump/phase boxes, Lipschitz bounds in the near/far parameters) over
  per-instance Horner replays; the 28x/35x D(c) headroom absorbs analytic
  slack. Fall back to 2559-style exact replay only where the analytic bound
  fails acceptance. This lane is where the largest cost swing lives.
- 2d midpoint lane: extend the 2563/2565 order-1 generator to also emit the
  per-cell order-2 midpoint leaves (the 2558 midpoint-bounds output), one
  module per segment of cells rather than per cell, reusing the paired
  160-bit replay.
- 2e assembly and totals: per-cell affine assembly theorems (2565 pattern,
  minus the per-cell closure), sum_le_sum over Finset.range 10240, three
  global chunked closures per sign, total theorems against T_+/-1/2 and the
  pin. Segment structure: 64 segments of 160 cells, each segment generated,
  built and validated independently (the 2559 segment precedent), so a
  failed cell invalidates one segment, not the grid.
- 2f validator: extend the 2563/2565 independent-readback architecture to
  segment scope (per-segment SHA closure + axiom audit + exact arithmetic
  replay of every table value), with the 2561 engine as the cross-check for
  the totals.

## Decision points and gates

1. Gate: 2a's replay-mechanism readback decides the generation volume of
   2b-2d. If no mechanism beats cbv by a factor, the projected wall is the
   90-110 h figure and the segment count is raised to keep leases bounded.
   RESOLVED by record 2567: cbv is the only kernel mechanism closing the
   compactExp2547 equalities at this interface (decide and rfl fail 30/30);
   the 90-110 h projection stands.
2. Gate: 2c's analytic envelope is accepted only if the inflated total
   stays under the pin with the two-channel product still above ~10x
   headroom (currently ~28x/35x); otherwise exact replays on the offending
   bands.
3. The membership brick (2564 probe verdict GO) stays independent of this
   lane; the batch consumes centers/errors hypotheses exactly as 2563/2565
   did.

## Explicitly not claimed

No cell certificate is produced by this record. The cost figures are
projections from single readings. No membership claim, no full-grid
certificate, no two-channel product theorem, no RH claim.

Evidence: docs/proofs/2552_batch_replay_cost.md,
docs/proofs/2553_paired_production_nodes.md,
docs/proofs/2554_proof_phase_cost.md,
docs/proofs/2559_zero_touching_cells.md,
docs/proofs/2560_grid_budget_and_two_channel_bridge.md,
docs/proofs/2561_correction_second_budget.md,
docs/proofs/2563_correction_second_cell2700.md,
docs/proofs/2565_correction_second_cell2700_minus.md,
ConnesWeilRH/Dev/C1RouteACorrectionSecondStrip2562.lean.
