# Route A.005 — Selected-owner C3' producer gate

Status: ACTIVE CORE TARGET. This is the next main attack.

Target:

```text
archimedeanTerm(selectedOwner.square)
    + integral(actualAggregate)
    <= -epsilon
```

Required invariants:

```text
same selected detector
same finite visible-prime owner
same support and Mellin nodes
same signed aggregate cancellation
same parameter quantifiers
```

The panel-local L2 model in `../003_panel_local_l2_model/` is admissible here
only if its model-to-real transfer supplies an explicit bound for this actual
owner. It cannot replace the signed C3' margin with channelwise absolute
majorants or a fixed-prime surrogate.

First next probe:

```text
1. Freeze the selected owner and all quantifiers.
2. Split the signed C3' budget into producer terms and declared error terms.
3. Attach the 2058 L2 certificate only to the matching error term.
4. Price the remaining signed margin, not another generic L5 envelope.
5. Stop on a positive unconditional margin or a named no-go.
```

Acceptance criterion: an unconditional quantitative bound on the actual
selected detector, a reproducible counterexample/no-go, or a strictly smaller
producer obligation with the old premise proved rather than renamed.

Authoritative records:

- `docs/map/003_b1_b5_minimal_exit_route_selection.md`
- `docs/map/080_c3p_signed_certificate_owner.md`
- `docs/map/082_direct_semilocal_gate_assault.md`
- `docs/map/104_route_a_four_round_campaign.md`
## 2059 owner-alignment result

Record 2059 cross-reads the one-copy G8-H owner in records 2037 and 2058.
The owner label, support `9.504`, visible-prime book size `1647`, basis size
`17`, rank `17`, and nullity `0` all agree. The inherited reduced-evaluator
reading is `Q1600 = -3.406049871881275e12`, while the complete 2058 L2 charge
is `4.412215566637855e10`, or `0.0129541 x |Q1600|`.

Decision: `L2-BUDGET-BELOW-SAMPLED-NEGATIVE-MARGIN`.

This removes owner mismatch as the immediate blocker, but it does not enclose
the full xi line or transfer the stored/ideal object to the actual producer.
The next probe must build that signed C3' enclosure or produce a scoped no-go;
another generic L5 repricing is not the next core action.

Evidence: `docs/proofs/2059_route_a_c3p_owner_margin_audit.md` and
`results/2059_route_a_c3p_owner_margin.json`.
## 2062 tail survival result

The same-owner tail screen was run at `m = 400`, `1600`, and `6400`. The first
two readings hit the committed quadrature alias horizon; they are instrument
incidents, not mathematical tail readings. At `m = 6400`, the measured
absolute tail on `|xi| = 40..160` is `4.091205950971527e6`, only
`1.2011585575262929e-6 x |Q1600|` and below the `4.412215566637855e10` L2
charge. Decision: `TAIL-SURVIVES-MEASURED`.

The next core obligation is now specific: prove the same-owner tail bound for
`|xi| > 160`, with the evaluator trust horizon handled explicitly. Do not
extrapolate the m=6400 measurement to infinity.

Evidence: `docs/proofs/2062_route_a_c3p_tail_survival.md` and
`results/2062_route_a_c3p_tail_probe.json`.
## 2063/2064 high-order tail branch

The measured high-order branch is numerically promising: with `r <= 48` and
100x stress on measured `N_r`, the candidate tail on `160..1e6` is
`8.096106404656881e-283`. The direct proof port is not viable: termwise
absolute expansion gives a `1.267e26` inflation at `r=48`.

Decision: `TERMWISE_ABSOLUTE_MAJORANT_DEAD`. The remaining admissible tail
route is a validated sign-partition / root-isolation enclosure for
`int |phi^(r)|`; do not reuse the termwise absolute majorant.

Evidence: `docs/proofs/2063_high_order_tail_branch_audit.md`.
## 2065-2068 validated high-order tail route

The tail branch now has a strong Go candidate. Exact rational construction and
root isolation find 64 roots of `P_48` in `(-1,1)`. Root partition reproduces
measured `N_48` to `8.51e-7` relative. The interval upper skeleton is
`1.2466403887652727e81`, only `5.4356851e7` above measured `N_48`.

Charging that factor uniformly to the 2063 `lb^2 * cc^2` envelope still gives
a stress-scaled tail `7.067948292096522e-260`, or
`1.6019045727365396e-270 x L2 charge`.

Status: `HIGH-ORDER-TAIL-GO-CANDIDATE`. Before promotion to a proved tail,
repeat the interval variation enclosure for every active rung, certify endpoint
and root completeness, and close the `1e6..infinity` remainder.

Evidence: `docs/proofs/2065_2068_validated_tail_route.md`.
## 2069 fixed-r48 tail price

A fixed `r=48` bound is enough; no rung-selection envelope is needed. Using
the 2068 interval upper skeleton, the same-owner tail price on `160..1e6` is
`7.068567822135646e-260`, or `1.6020449851959417e-270 x L2 charge`.

Status: `FIXED-R48-TAIL-GO-CANDIDATE`. The remaining work is now a proof
conversion task: certify the 2068 variation upper, close root/endpoint
completeness, and bound `1e6..infinity` analytically.

Evidence: `docs/proofs/2069_fixed_r48_tail_price.md`.
## 2070 infinity-tail bound

The fixed-r48 envelope now extends past `1e6` by explicit dyadic bands. The
first band log-bound is `-2177.9202904243193`; each doubling reduces the bound
by about `126.845`, with maximum observed ratio `8.17e-56`. The infinity tail
is no longer the numerical obstacle.

Next target: certify the finite-window signed quadrature on `|xi| <= 40` for
the same owner and the negative `Q1600` object.

Evidence: `docs/proofs/2070_infinity_tail_bound.md`.

## 2071 finite-window signed decomposition

On `|xi| <= 40`, the same-owner signed aggregate remains stable under steps
`0.02`, `0.01`, and `0.005`, with total approximately
`-3.40604985178e12`. The sigma contribution and the visible-prime contribution
are each about `2.3e14`; the prime-channel absolute sum is about `1.23e15`, so
the negative result is genuinely cancellation-led rather than a channelwise
sign claim.

Status: `FINITE-WINDOW-SIGNED-CANDIDATE`. The next implementation must enclose
the aggregate signed integrand or its quadrature error. Independent absolute
bounds for the `1647` prime channels are rejected because they destroy the
observed margin.

Evidence: `docs/proofs/2071_finite_window_channel_decomposition.md` and
`results/2071_finite_window_channel_decomposition.json`.

## 2072 aggregate residual screen

Recombining sigma and all prime channels before applying the owner weight keeps
the signed cancellation, with aggregate readings near
`-3.40604985178e12` at steps `0.02`, `0.01`, and `0.005`. But the measured
finite-difference L1 derivative is `2.84e16` to `3.08e16`; the naive global
first-derivative trapezoid remainder would be about `1e14`, so it cannot certify
the negative margin.

Decision: `NAIVE-FIRST-DERIVATIVE-BOUND-DEAD`. The next mechanism is a
higher-order or panelized signed remainder, preferably Euler–Maclaurin on the
aggregate object. This is a scoped quadrature-bound no-go, not a Route A
closure.

Evidence: `docs/proofs/2072_finite_window_aggregate_residual.md` and
`results/2072_finite_window_aggregate_residual.json`.

## 2073 aggregate Euler-Maclaurin fourth-order probe

The aggregate signed integrand was tested with a fourth-order
Euler–Maclaurin remainder on `|xi| <= 40`. At step `0.005`, the measured
remainder proxy is `9.345328754829594e9`, only `0.2744%` of the signed total
magnitude `3.406049851781223e12` and below the `4.412215566637855e10` L2 charge.

Status: `EM-FOURTH-ORDER-GO-CANDIDATE`. The finite-difference derivative is
not yet an enclosure. The next required conversion is a panelwise outward
interval/jet bound for the aggregate fourth derivative, retaining the full
sigma-plus-prime cancellation.

Evidence: `docs/proofs/2073_finite_window_em_fourth_probe.md` and
`results/2073_finite_window_em_fourth_probe.json`.

## 2074 aggregate Euler-Maclaurin jet bound

The 2051 real-jet calculus was applied to the same owner weight while keeping
the sigma-plus-prime kernel aggregate. At panel width `0.002`, the fourth-order
remainder proxy is `1.6840448281341767e9`, or `0.03817x` the L2 charge and
`0.0004944x` the sampled negative margin.

Status: `EM-JET-BOUND-GO-CANDIDATE`. The remaining proof gap is localized to
outward enclosure of aggregate kernel center derivatives, their summation
rounding, and the sigma derivative majorants. The measurement is not yet an
unconditional producer theorem.

Evidence: `docs/proofs/2074_finite_window_em_jet_bound.md` and
`results/2074_finite_window_em_jet_bound.json`.

## 2075 aggregate Euler-Maclaurin forward bound

The 2074 jet calculation now includes analytic sigma derivative majorants and an
explicit IEEE summation allowance for the aggregate prime cosine kernel. At
panel width `0.002`, the forward remainder bound is
`1.6840374794504895e9`, or `0.03817x` the L2 charge and `0.0004944x` the
sampled negative margin. The summation allowance changes the previous price by
only about `7.4e3`.

Status: `EM-JET-FORWARD-BOUND-CANDIDATE`. The next binding work is not further
quadrature refinement; it is conversion from stored model coefficients to the
actual physical owner, specifically the `a_mat` idealisation, Gram rule, and
COVER obligations.

Evidence: `docs/proofs/2075_finite_window_em_forward_bound.md` and
`results/2075_finite_window_em_forward_bound.json`.

## 2076/2077 model-to-real transfer pricing

Independent high-precision reconstructions now price the two named matrix gaps.
Replacing stored `a_mat` by true Laplace values moves Q by `4.1949934e4`; the
Gram-only move is `2.3908832e4`; replacing both moves Q by `2.7311158e4`. Each
is below `1.3e-8` of the signed margin.

Status: `GRAM-AMATRIX-TRANSFER-GO-CANDIDATE`. These are high-precision
measurements, not yet outward interval certificates. The remaining route-level
blocker is COVER/uniformity over the hypothetical zero parameters, plus formal
promotion of the finite-window and matrix bounds.

Evidence: `docs/proofs/2076_amatrix_true_transfer.md`,
`docs/proofs/2077_gram_true_transfer.md`, and their result artifacts.

## 2078/2079 COVER owner-margin screening

The `m=400` screen was rejected as evidence because of the known alias horizon.
A follow-up `m=6400`, step `0.02` run at six registered height/scale cells
keeps every signed finite-window Q negative, including G8-H at
`-3.406049851783499e12`.

Status: `COVER-SAMPLED-NEGATIVE`, not uniform COVER. The next task is a
parameterized continuity/envelope certificate across the hypothetical-zero
coordinates; six negative samples do not close the quantifiers.

Evidence: `docs/proofs/2078_2079_cover_owner_margin_screen.md` and the two
result artifacts.

## 2081 numerical margin ledger

The current sampled G8-H negative margin is `3.406049851783499e12`. The priced
L2, finite-window EM, `a_mat`, Gram, and tail terms sum to
`4.580625900459516e10`, only `0.0134485x` of that margin. The remaining margin
is `3.360243592778904e12`.

This is a routing ledger, not a proof. The open items are now explicit:
uniform COVER, formal outward promotion of the finite-window and matrix bounds,
physical-owner/model-to-real transfer, and symbolic tail closure.

Evidence: `docs/proofs/2081_routea_margin_ledger.md` and
`results/2081_routea_margin_ledger.json`.

## 2082/2085 COVER delta-layer screen

At G8-H and scale `0.88`, m=6400 finite-window Q stays negative through delta
`0.30`: `-1.55e13`, `-3.41e12`, `-6.80e11`, and `-2.52e11` at delta
`0.05`, `0.10`, `0.20`, and `0.30`. The margin contracts sharply, so the
center-owner L2/EM price cannot be reused across delta layers.

Status: `COVER-DELTA-SAMPLED-NEGATIVE`, not uniform. The next coverage route is
delta-layered pricing plus a far-delta argument.

Evidence: `docs/proofs/2082_2085_cover_delta_margin.md` and the result artifacts.

## 2086-2092 scale-adaptive COVER screen

The sampled sign remains negative as delta grows, but the usable scale shifts:
scale `0.86` improves delta `0.50`, scale `0.84` improves delta `0.70`, and
scale `0.80` remains negative at delta `1.00`. The absolute margin nevertheless
collapses from `1.02e12` at `(0.50,0.86)` to `3.21e9` at `(1.00,0.80)`.

Status: `COVER-SCALE-ADAPTIVE-CANDIDATE` with
`FAR-DELTA-MARGIN-COLLAPSE`. Full COVER requires relative error pricing or a
separate far-delta analytic sign theorem; center absolute budgets cannot be
reused.

Evidence: `docs/proofs/2086_2092_cover_scale_adaptive_screen.md` and the listed
result artifacts.

## 2093 legal half-strip COVER candidate

The source-zero strip bounds `0 < Re(rho) < 1` restrict positive delta to
`0 < delta < 0.5`. At G8 and fixed scale `0.86`, m=6400 readings are negative
at delta `0.10`, `0.30`, and `0.50`, with values
`-1.6038e13`, `-1.2911e12`, and `-1.0172e12`.

Status: `COVER-LEGAL-HALF-STRIP-CANDIDATE`. The remaining quantifiers are
continuity in delta, uniformity in gamma, and formal owner/model transfer.

Evidence: `docs/proofs/2093_cover_legal_half_strip_screen.md`,
`results/2093_cover_scale086_legal_delta_m6400.json`, and
`ConnesWeilRH/Source/CC20YoshidaNearZeros.lean:43`.

## 2094 gamma-side COVER candidate

At legal delta `0.10` and fixed scale `0.86`, the four registered heights
`37.586`, `40.919`, `43.327`, and `48.005` all remain negative at m=6400,
with Q from `-1.60e13` to `-5.67e14`.

Status: `COVER-GAMMA-SCALE086-CANDIDATE`. The next object is a continuous
legal-half-strip enclosure over gamma and delta; isolated height scans are no
longer the useful lever.

Evidence: `docs/proofs/2094_cover_gamma_scale086_screen.md` and
`results/2094_cover_gamma_scale086_m6400.json`.

## 2095 fixed-scale legal half-strip grid

At fixed scale `0.86`, m=6400, and finite window `|xi| <= 40`, all 20 points
from four registered gamma heights and delta `0.10/0.20/0.30/0.40/0.49` are
negative. The weakest sampled value is `-5.1246e11` at gamma `37.586178` and
delta `0.49`.

Status: `COVER-LEGAL-HALFSTRIP-GRID-CANDIDATE`. This is still a numerical
screen, not a continuous COVER theorem, producer theorem, or RH proof. The
next core object is a cellwise outward continuity/enclosure certificate,
with cells split at owner/book changes and all transfer charges retained.

Evidence: `docs/proofs/2095_cover_legal_halfstrip_grid_screen.md` and
`results/2095_cover_legal_halfstrip_grid_m6400.json`.

## 2104 continuous-owner correction

Records 2095-2099 used the ten-height `GAMMAS_EXT` list. The actual Lean
closed-ball owner is not restricted to that list: at an interior gamma around
39.252 and delta 0.15, the first 30 numerical on-line zeros add 12 omitted
kill nodes (record 2100). The 17/18-node screens cannot support actual-owner
COVER, regardless of their sampled sign. Scale 0.86 on the 18-node interior
family also has four positive Q readings (record 2096), a scoped family no-go.

A compact-support shared-kill-width family survives the stronger numerical
known-prefix test: direct 30/33/36-node interpolation at scale 0.80 gives
12/12 negative finite-window Q readings, weakest `-1.675397327895099e12`,
with support 5.12 and 52 visible prime powers (2101-2103). This is a new
architecture CANDIDATE, not a producer theorem. It still needs the complete
abstract zero owner, parameter-uniform conditioning and signed margin, and
owner-matched outward full-line error charges. Do not reuse 2058/2081 prices
from the 17-node G8-H owner.

Evidence: `docs/proofs/2104_route_a_continuous_owner_correction.md`.

## 2105-2109 owner-matched budget

The changed compact family now has an owner-matched numerical ledger at the
weakest tested cell: EM forward `5.720420308066749e7`, a_mat transfer
`5.9268334716796875e4`, Gram H1 diagnostic `1.733805888696289e7`, and tail
`2.21e-138`. Total known charge is `7.460153030234718e7`, only
`4.4528e-5` of the sampled margin `1.675397327895099e12`.

This survives numerical pricing, but the owner remains a first-30 numerical
prefix rather than the complete abstract closed-ball zero set. Formal outward
promotion, parameter-uniform owner control, and the Lean certificate socket
remain open.

Evidence: `docs/proofs/2104_route_a_continuous_owner_correction.md`.

## 2110-2112 complete-owner stress direction

Shared kill widths fail under an added symmetric off-line orbit: the matrix
becomes singular or the pin residual explodes. A unique-width extension fixes
the first stress orbit; at m=6400 it gives support `6.08`, book `103`,
condition `8.83e5`, pin residual `5.12e-11`, and negative Q
`-6.175280807191016e13`. This is the current selector direction, not yet a
uniform owner result. More off-line orbit cardinalities must be tested and
priced with the same EM/tail/transfer chain.

Evidence: `docs/proofs/2104_route_a_continuous_owner_correction.md`.

## 2113-2116 compact cardinality ladder

The compact unique-width ladder `2.21 + 0.05*i` keeps the actual support and
prime book almost fixed while adding nodes. At m=6400, 30/34/38/42/46-node
stress owners (0--4 added symmetric off-line orbits) are all negative. The
worst condition is `7.57e7`, support `4.736`, book `40`, and the weakest
sampled Q is `-6.134e13`.

This is the current producer candidate, but not yet a Go: the abstract owner
cardinality and zero positions remain unbounded in the numerical artifact, and
formal outward/parameter-uniform pricing is still required.

## 2119 formal owner-cardinality bridge

The exact closed-ball owner is no longer an unbounded placeholder at the
counting-interface level. `ConnesWeilRH/Dev/C1RouteAOwnerCardinality.lean`
proves an unconditional Jensen cardinality bound from the existing dyadic xi
Growth estimate, and its paired audit is clean.

At the current `N=0`, `rho=0.945+39.25244858548658i` stress point, the
formal bound translates numerically to about `3002.56` source-owner nodes,
while the compact ladder has only reached 62 nodes. This is a 48.43x gap in
the formal upper bound, not a measured zero count and not a Route A global
no-go. The next admissible moves are a sharper zero-count/anchor estimate, an
owner-local construction whose cost does not scale one-for-one with the count,
or a signed mechanism avoiding interpolation of every abstract owner zero.

Evidence: `docs/proofs/2119_routea_formal_owner_cardinality_bound.md`,
`results/2119_routea_formal_owner_cardinality_bound.json`.

## 2120 nearby-anchor refinement

The owner-count theorem now accepts an arbitrary nonzero Jensen center. A
zero-free nearby center on `Re(c) >= 1` reduces the current formal upper-bound
translation from about `3002.56` to about `1370.38` nodes, but this remains
about `22.1x` above the 62-node compact stress family. The refinement is not a
Go and does not justify a 62-node actual-owner certificate.

Evidence: `docs/proofs/2120_routea_nearby_anchor_cardinality_screen.md` and
`results/2120_routea_nearby_anchor_cardinality_screen.json`.
