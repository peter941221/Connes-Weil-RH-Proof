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
The delta-floor half is record 2017.

Authority remains in `docs/map/`; this directory is the navigational topology.

Read the binding parent first:

1. `002_b5_compactlog/README.md`
2. `002_b5_compactlog/001_route_a_signed_kernel/README.md`
3. `002_b5_compactlog/002_route_b_fourpoint_span/README.md`
4. `../README.md`
