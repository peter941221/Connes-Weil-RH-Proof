# 2266 — Exact two-end Hall enumeration with certified middle brackets

Date: 2026-09-30

Consumer: 2261 left the coalitional Hall quantity
`t* = max_J 62 · Hall(J)/(|J| · row)` as greedy lower bounds only, and its
greedy peaks scatter across coalition sizes (`k* = 28 / 9 / 18 / 8`), so
neither a small-k nor a large-k sweep alone decides the curve. This record
upgrades the screen to exact enumeration at both ends of the curve, plus
certified ceilings and local-search lower bounds in the middle.

Verdict: **all four rows are now two-sided bracketed, one of them
exactly. The exact global maximum for `base_M0` is
`2.1475067585012337` at `k = 28`; the other three rows are bracketed to
relative width `<= 4.8e-4` — `corr_M0 [6.1624990602415091,
6.1654080613840732]` at `k = 8`, `base_D2 [2.6403870620083922,
2.64068660502853]` at `k = 17`, `corr_D2 [6.0894516916697183,
6.0917247299667272]` at `k = 7`. The best coalitions beat 2261's greedy
bounds by `5.6% / 10.8% / 12.5%` on the three open rows, so every
single-factor uniform budget still fails, by certified factors
`2.1475 / 6.1625 / 2.6404 / 6.0895` against the pigeonhole floor
`62/30 = 2.0667` — stronger than 2261 on every row that was open. The
count-free assembly (2257) remains the live route; the coalitional Hall
LP is now priced at both ends and bracketed in the middle.**

## Method

The exact problem `max_J 62 · Hall(J)/(|J| · row)` with
`Hall(J) = ∫ e^{σx} (|G| - Σ_{j∉J}|g_j|)^+` is a cardinality-constrained
max of a supermodular set function (densest-k-subgraph-like in general).
A direct MILP encoding is not available: the positive part is the support
function of the `2^N` sign patterns, so an epigraph with only lower-bound
rows is unbounded, and the disjunctive form needs one binary per grid
node (240001). The record instead computes, on the committed 2197/2258
grid at float64:

1. **Exact enumeration** (fork-parallel, chunked matmul) for every
   `k <= 6` and — by enumerating the excluded complements of size
   `<= 6` — every `k >= 24`; `k = 30` reproduces the row norm bitwise.
2. **Certified ceilings** for `7 <= k <= 23`, the four-way minimum of
   (a) trivial `row` (`ratio <= 62/k`), (b) mass
   `Σ_{j∈J} ∫ min(|G|, |g_j|)`, (c) cover
   `Σ_{j∈J} ∫_{|g_j| > d/k} |G|` with `d = S - |G| >= 0`, and
   (d) complement-m-smallest `∫ (|G| - L_m)^+` with `m = 30 - k` and
   `L_m(x)` the pointwise sum of the `m` smallest `|g_j(x)|` — every
   excluded complement of size `m` dominates `L_m` pointwise, so
   `Hall(J) <= ∫ (|G| - L_m)^+` for every `|J| = k`. Bound (d) is the
   decisive one (it encodes "no coalition of `m` families covers this
   node"): it moved the binding middle ratios from `62/k` down to
   `0.09 … 6.09`.
3. **Lower bounds** in the middle from the greedy curve (recomputed,
   anchored bitwise against `results/2261_hall_screen.json`) improved by
   a 1-swap hill climb at every `k` whose ceiling could beat the current
   floor.

## Results

```text
row        k*   exact / bracket                          width rel   vs 2261   vs floor
base_M0    28   2.1475067585012337 (EXACT)              0           1.0000    1.0391
corr_M0     8   [6.1624990602415091, 6.1654080613840732]  4.72e-04   1.1078    2.9819
base_D2    17   [2.6403870620083922, 2.64068660502853]    1.13e-04   1.0557    1.2776
corr_D2     7   [6.0894516916697183, 6.0917247299667272]  3.73e-04   1.1251    2.9465
```

Binding ceilings at the upper end: complement-m-smallest at every `k*`
(the other three bounds never bind in the middle). Witness coalitions:
`base_M0` `{0,1,2,3,5,6,7,8,…}` (28 of 30, exact); `corr_M0` `{0,1,11,
12,13,14,15,16,…}` (8); `base_D2` `{0,1,2,3,12,14,15,17,…}` (17);
`corr_D2` `{0,1,12,13,14,15,16}` (7).

Consistency anchors (all four rows): greedy recomputation vs 2261
`rel_max = 0.0` (bitwise); `k = 30` vs row norm `rel = 0.0`;
monotonicity inside both exact ranges; every ceiling `>=` the exact
value on covered `k`; `ub >= lb` on every middle `k`. Wall time 2001 s
(14 fork workers, one index table per subset size shared by fork).

## Interpretation

- The greedy scan systematically *underestimated* the middle of the
  curve on the three open rows: 1-swap improvements found coalitions
  `5.6% / 10.8% / 12.5%` better than the 2261 greedy peaks, all at
  smaller coalition sizes (`8 / 17 / 7` vs `9 / 18 / 8`). The 2261
  verdict ("every single-factor split fails by at least 2.07x") only
  strengthens: certified factors are now `2.1475 / 6.1625 / 2.6404 /
  6.0895` of the budget.
- Why the curves are so close to their ceilings: the binding constraint
  in the middle is precisely the complement-cardinality obstruction —
  with `m = 30 - k` families excluded, the node can be covered only where
  the excluded families' magnitudes fall below `|G|`. Bound (d)
  quantifies exactly that, and the climb nearly attains it (relative
  gaps `1e-4 … 5e-4`).
- `base_M0` is genuinely closed: its global maximum sits in the
  complement-exact range (`k = 28`), and every middle ceiling lies below
  `2.1475` (max middle ceiling `1.9219` at `k = 23`), so the enumeration
  suffices without any local search.
- The three open rows are *not* certified to be maxima at their `k*` —
  the bracket upper ends are certified ceilings, not attained values —
  but their relative widths are at the `1e-4` level, far below any
  budget decision margin needed downstream.

## Nonclaims

- float64 measurements on the committed 2197/2258 grid; the ceilings are
  valid upper bounds only up to binary64 slack;
- the middle-range lower bounds come from greedy/1-swap search (not
  exhaustive), hence the brackets stay open at `~1e-4` relative width on
  the three non-closed rows;
- `Hall(J)` is a necessary condition on feasible pointwise allocations;
  sufficiency is not used;
- single candidate construction (2234 build); the three 2103 stress
  candidates are not re-measured;
- no producer GO, no gate sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_hall_exact_2266.py`;
- artifact: `results/2266_hall_exact.json`
  (md5 `e6e544d17d43371bd2b71ddc71d0e51e`);
- machinery: `scripts/routea_weighted_zero_cancellation_split_2258.py`
  (`family_terms`, `trap_weights`), `scripts/routea_weighted_zero_direct_product_outward_2234.py`
  (construction);
- predecessor: `docs/proofs/2261_routea_weighted_zero_hall_screen.md`;
- register: `docs/proofs/2258_routea_weighted_zero_cancellation_split.md`.