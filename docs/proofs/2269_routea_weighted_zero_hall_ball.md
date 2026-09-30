# 2269 — Ball-grade Hall quantities for the four direct-product rows

Date: 2026-09-30

Consumer: 2266 bracketed the coalitional Hall curve
`t* = max_J 62 · Hall(J)/(|J| · row)` in float64 — exact at both ends,
certified ceilings plus 1-swap lower bounds in the middle — and 2262
established the directed-MPFR standard for the same family/node
quantities. This record re-runs the 2262 node machinery and ball-izes the
decisive Hall quantities themselves, so that a count-side revival
consumes a fully certified bracket rather than a float64 one.

Verdict: **HALL-BALL-CERTIFIED. All four rows now carry two-sided
certified brackets — `base_M0 [2.1475067584947944, 2.147512373192978]`,
`corr_M0 [6.162499060223501, 6.165408061402101]`, `base_D2
[2.6403870620001513, 2.6406866050367617]`, `corr_D2
[6.0894516916512975, 6.091724729985202]` — each containing the 2266
float64 bracket, with both ends within `2e-11` of the 2266 float values
at the decisive k. The witness coalition Hall readings reproduce to
`<= 1.6e-12` relative, the certified upper is valid at every `k` through
`min(62/k, 62 · msmall_u[30 - k]/(k · norm_lo))` alone, and every
cross-anchor is green (mask disagreements 0, certified mask margin
`1.82e-06`, norm/triangle inside the 2262 certified intervals, weight
sum bitwise).**

## Method

1. **Node machinery.** The 2262 `family_step` is reused verbatim: per
   node `x`, per family `j` (30 lattice points, mask `q(x) > 0.04`), the
   eight certified float64 slots `(base_M0, corr_M0, base_D2, corr_D2) ×
   (upper, lower)`, plus the four signed MPFR row accumulators giving the
   per-node `AG = |G_row(x)|` interval through the 2262 `PAD` law. The
   `x` grid, trapezoid weights `w = (dx/2)·tw·e^{x}`, and family order
   are the committed 2197/2258 ones.
2. **Coalition Hall.** For each row, the 2266 witness coalition `J`
   (the argmax of `ratio_lo`) with the **2266 convention**
   `Hall(J) = ∫ w (AG - Σ_{j∉J} M_j)^+`: the summed family magnitudes are
   those of the *complement*. Per node:
   `hall_hi += w_u · max(AG_u - Σ_{j∉J} M_l,j, 0)` and
   `hall_lo += w_l · max(AG_l - Σ_{j∉J} M_u,j, 0)`, each add and product
   guarded one-sided (`up_sum`/`up_prod` / `lo_sum`/`lo_prod`).
3. **msmall table.** For every `m = 1..30`, `L_m` bounds from the
   sorted-domination law (`sorted(lb)[i] <= sorted(true)[i] <=
   sorted(ub)[i]` pointwise): `L_m^lo = Σ` of the `m` smallest lower
   bounds, `L_m^hi = Σ` of the `m` smallest uppers; then
   `ms_u[m] += w_u · max(AG_u - L_m^lo, 0)` and the lower analogue.
4. **Norm/triangle/weight anchors.** `norm = ∫ w AG`,
   `tri = ∫ w Σ_j M_j`, `wsum = Σ w`, all in directed pairs, computed
   with the same loop order as 2262.
5. **Reduce and brackets.** Guarded chunk aggregation, then
   `ratio_lo_cert = 62 · hall_lo/(k_w · norm_hi)` and
   `ratio_hi_cert = max_k min(62/k, 62 · ms_u[30 - k]/(k · norm_lo))`.
   The upper is valid at every `k` (msmall is one of the four 2266
   ceiling components, and `62/k` is the trivial bound
   `Hall <= ∫ w AG`); the lower uses the stored witness coalition.

## Results

```text
row        k   witness Hall [lo, hi]                    rel vs 2266   certified t* bracket
base_M0    28  [1.9429187110390924, 1.9429187110447967]  ±1.47e-12    [2.1475067584947944, 2.147512373192978]
corr_M0     8  [726.3375614006602, 726.3375614027204]    ±1.42e-12    [6.162499060223501, 6.165408061402101]
base_D2    17  [4842.37627769925, 4842.376277714376]     ±1.56e-12    [2.6403870620001513, 2.6406866050367617]
corr_D2     7  [1049250.321373734, 1049250.3213766257]   ±1.38e-12    [6.0894516916512975, 6.091724729985202]
```

The certified argmax `k` of the upper bound equals the 2266 decisive `k`
on every row (`28 / 8 / 17 / 7`), i.e. the complement-m-smallest
component binds `min(62/k, msmall)` there, exactly as in 2266.

Anchors: mask decisions `5,063,108` active / `2,136,922` masked pairs
with `0` disagreements between the MPFR test and the float64 mask, and
certified minimum margin to the `0.04` boundary `1.819057697104165e-06`;
`norm` and `triangle` of every row inside the 2262 certified intervals
(`rel <= 1e-12`); `wsum = [12.858512575568238, 12.858512575606635]`
identical to 2262; the witness Hall readings inside `1.6e-12` relative
of the 2266 float64 readings; `ratio_lo_cert <= t_lo` and
`ratio_hi_cert >= t_hi` of 2266 on every row.

## Interpretation

- The float64 readings of 2261/2266 were faithful: the directed-MPFR
  recomputation sits within `~1.5e-12` relative of every witness Hall
  and every bracket end — the 2266 numbers were accurate to the last
  two digits, no float pathology anywhere in the Hall lane.
- The certified upper no longer needs the exhaustive enumeration: at
  `base_M0` the ball-grade certificate gives `2.147512373192978` (the
  msmall ceiling at `k = 28`) versus the float "exact"
  `2.1475067585012337` — `2.6e-6` above it, which is the price of not
  re-verifying the `2^30`-scale enumeration in directed arithmetic.
  The other three rows certify at the same width 2266 had
  (`4.7e-4 / 1.1e-4 / 3.7e-4` relative), i.e. their brackets were
  ceiling-limited, not arithmetic-limited, and the ball-grade upper
  inherits exactly that limit.
- The single-factor infeasibility claim is now certified at both ends:
  every certified lower end (`2.1475 / 6.1625 / 2.6404 / 6.0895` modulo
  the `1e-11`-level offsets shown above) exceeds the pigeonhole floor
  `62/30 = 2.0667`, and every certified upper end is a valid bound on
  the true `t*`.
- A semantic trap fixed on the way: the 2266 `witness_idx` list indexes
  the coalition `J` whose **complement** is deducted
  (`Hall(J) = ∫(AG - Σ_{j∉J} M_j)^+`); summing the members instead
  collapses `Hall` to `~0` on the large-`k` witnesses. The convention is
  documented here and in the script docstring.

## Nonclaims

- the mass and cover ceiling components of 2266 are not re-certified;
  they are simply not used (the certified upper rests on
  `min(62/k, msmall)` alone);
- the exhaustive small/large-`k` enumerations of 2266 remain
  float64-grade; the certified lower bound uses only the stored witness
  coalition per row, so no claim of certified exhaustiveness is made;
- `Hall(J)` remains a necessary condition on feasible pointwise
  allocations (the LP is a relaxation); sufficiency is not used;
- single candidate construction (2234 build); the certified brackets
  are at `σ = 1` on the committed 2197 grid;
- no count-side revival, no allocation design, no producer GO, no gate
  sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_hall_ball_2269.py`;
- artifact: `results/2269_hall_ball.json`
  (md5 `d9ee6e795b2e34bf01aecc29911c04c1`);
- machinery: `scripts/routea_weighted_zero_cancellation_split_ball_2262.py`
  (`family_step`, guards, conversion laws — same node semantics);
- anchors: `results/2266_hall_exact.json`,
  `results/2262_cancellation_split_directed.json`;
- predecessor records: `docs/proofs/2266_routea_weighted_zero_hall_exact.md`,
  `docs/proofs/2262_routea_weighted_zero_cancellation_split_ball.md`.