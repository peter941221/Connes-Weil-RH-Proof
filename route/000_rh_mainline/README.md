# 000 - RH mainline

This is the parent node for every admissible route in this repository.

```text
000 RH mainline
|
+-- 001 shared contracts
|
+-- 002 B5 CompactLog producer
|   |
|   +-- 001 Route A: signed physical kernel
|   |
|   +-- 002 Route B: four-point SPAN
|
+-- 003 Route C: trace-formula positivity candidate
|
+-- 004 A/B common-bottleneck audit
|
+-- 099 frozen or audit-only branches
|
+-- final consumer: SourceRH -> Mathlib RiemannHypothesis
```

The parent goal is:

```text
hypothetical off-line zero
    -> healthy selected CompactLog detector g with qw(g) < 0
    -> prove qw(g) >= 0 for that same owner
    -> SourceRH
    -> Mathlib RiemannHypothesis
```

The child directories are subroutes of this goal. They are not independent
RH proofs. A child route survives only if it preserves the same owner,
support, visible-prime set, detector, and quantifiers through the consumer.

The open layer shared by every route is COVER (uniformity over all hypothetical off-line zeros). Per-rho SIGN is empirically green through gamma_8 (records 1981/1994/1996), but this is not yet an analytic theorem. The first strategy desk for the
(delta, gamma, scale) window problem is
`docs/proofs/1998_cover_strategy_desk.md` (verified knot anatomy,
margin growth, five priced directions, decision rules fixed for the
next scans).

The width track has since been measured and its first direction closed by
that measurement: record 2016 scans the committed scale family over eight
heights (190 cells, 181 certified) and reports KNOT_COMPLEX - `C > 0` holds
on 4-7 disjoint runs of scale per height with maximal contiguous width 4, 4,
4, 4, 2, 1 from `gamma_1` to `gamma_6`; `D >= 0` on 43 of 190 cells, all of
them at `gamma_1..gamma_5`; and the `gamma_5` layer control disagrees
between the committed and EXT layers position by position (record 2012
section A2), so no cross-height width law is licensed.  Direction A (the
window-track theorem) is therefore excluded on this data, `WINDOW_PINCHING`
was not triggered, and directions C/E are not selected by the registered
rules.  The reading is one-resolution and the record says so: `C` is the
cancelled coordinate amplified by `|2 + f|` (record 2014 section 5), `f`
reaches `1.6e+06` at `gamma_2`, and the band edges are registered for a
re-read at `dxi = 0.002` before any routing decision rests on the comb.

The delta-floor half then closed the other coordinate: record 2017 reports
FLOOR_UNIFORM - floor = 0.02, the smallest registered delta, at all eight
heights and at the layer control (366 cells, 366/366 certified), with the
registered stage-B trigger firing at `gamma_6`, whose only host lives at scale
1.00 outside the five-point grid.  The host scale window is delta-stable while
the `C`-comb is not, and `n_primes` is a function of (layer, height, scale)
alone, so moving the witness toward the line costs nothing in the
visible-prime book.  Direction D (the Speiser split) stays down-graded, and
the quantifier is explicit in the record: the verdict is a statement about
`delta >= 0.02`, so it cannot distinguish "no wall" from "a wall below 0.02";
the finer delta grid and the `dxi = 0.002` band-edge re-read are the
registered follow-ups, now running as record 2019.  The record-2020 currency
desk then identified the visible book exactly (`np(s) = #{n prime power :
n <= exp(2 s m_pool)}`, 27/27 committed cells), measured the comb as a
near-white sequence along scale at the 0.01 grid (flip rates at the
independence reference, flat in the step), and priced the currencies that
survive: no 0.01-scale window structure, healthy measure `mu = 0.306`
(`H = 3.27`) at `delta = 0.10`, and pointwise-in-scale certification
book-exact and finite - the scale ladder is registered as C1 in record 2020
section 8.  With both halves measured, the COVER layer's analytic currency is
an open question with directions A and D excluded by measurement and C/E
unselected - see `docs/map/107_cover_layer_measured_state.md`.

Authority remains in `docs/map/`; this directory is the navigational topology.

Read the binding parent first:

1. `002_b5_compactlog/README.md`
2. `002_b5_compactlog/001_route_a_signed_kernel/README.md`
3. `002_b5_compactlog/002_route_b_fourpoint_span/README.md`
4. `../README.md`
