# 2261 — Coalitional Hall screen of the direct-product rows (count-side LP)

Date: 2026-09-30

Consumer: record 2258 registered the coalitional Hall LP as the open
allocation-design question for any count-side revival of the split. This
record computes its two decidable pieces on the committed 2197 grid:
single-factor optimal-cap lower bounds, and the disjoint-cover diagnostics
for natural partitions.

Verdict: **the single-factor lower bounds are `2.1475 / 5.5627 / 2.5011 /
5.4124` (rows `base_M0 / corr_M0 / base_D2 / corr_D2`, greedy coalitions
of size `28 / 9 / 18 / 8`), all above the exact pigeonhole `62/30 =
2.0667`: every single-factor split of every row fails the uniform budget
by at least `max(found, 62/30)`. The `parity` and `halves` partitions are
disjoint self-covers on both sides of all four rows (both Hall ratios
`<= 0.0067` of the budget), so the pointwise-universe product split is
degenerate there — the count-side feasibility question must be posed on
the fixed analytic per-node pieces. The coalitional Hall LP stays
registered as the design question; the count-free assembly (2257) remains
the live route.**

## Method

For a row with signed sum `G`, per-family magnitudes `|g_j|`, `S = Σ_j |g_j|`,
every feasible pointwise allocation `(a_j)` with `0 <= a_j(x) <= |g_j(x)|`
and `Σ_j a_j(x) >= |G(x)|` satisfies, for every coalition `J`,

```text
Σ_{j ∈ J} a_j  >=  Hall(J) = ∫ w (|G| - (S - A_J))^+ ,   A_J = Σ_{j ∈ J} |g_j|,
```

hence `max_j a_j >= max_J Hall(J)/|J|`. The greedy scan (each step adds the
family maximizing the Hall increment) gives a certified lower bound
`t*_lo = max_k 62 · Hall_k/(k · row)` on the best single-factor split
ratio over the uniform budget row/62; the `k = 30` term is exactly
`62/30`. Disjoint-cover diagnostics measure `Hall(part)` for natural
partitions: a partition with both sides near zero makes the two-sided
disjoint product split degenerate (zero diagonal charge).

Sampling: float64 numpy on the committed grid, the 2258 machinery
(`family_terms`, `trap_weights`). Screening artifact: no producer GO, no
gate sign change, no RH claim.

## Results

```text
row        t*_lo    k*    pigeonhole 62/30   nodes 3-way decision
base_M0    2.1475   28    2.0667             <= budget·2.1475
corr_M0    5.5627    9    2.0667             <= budget·5.5627
base_D2    2.5011   18    2.0667             <= budget·2.5011
corr_D2    5.4124    8    2.0667             <= budget·5.4124
```

Disjoint-cover ratios (Hall/budget; both sides `< 0.05` = self-cover):

```text
partition        base_M0        corr_M0        base_D2        corr_D2
parity        (0.00672, 0.0)  (0.0, 0.00161) (0.00408, 0.0) (2e-05, 0.00138)
halves        (0.0, 0.0413)   (0.0, 0.00363) (0.0, 0.01301) (0.0, 0.00316)
theta_sign    (8.38, 0.0241)  (62.0, 0.0)    (36.10, 0.008) (62.0, 0.0)
min_width     (0.0954, 0.0)   (0.1958, 0.0)  (0.0544, 0.0)  (0.1596, 0.0)
```

Self-cover pairs: `parity` and `halves` on all four rows. The `theta_sign`
split is emphatically not a self-cover: the `theta >= 0` shield side alone
carries Hall ratio `8.38 / 62.0 / 36.10 / 62.0` (for the corr rows the five
shield families' magnitude sums cover the integrand up to budget scale).

## Interpretation

- The single-factor cap lower bounds are *necessary* conditions (any
  found coalition is a certificate of the max-J lower bound); they are
  `>= 2.07` everywhere, i.e. any split holding one factor flat exceeds the
  budget by at least `2.07x` — consistent with, and slightly stronger
  than, the structural `62/30` of 2258.
- The disjoint self-cover of `parity`/`halves` shows the *pointwise
  universe alone* cannot decide feasibility: a free pointwise allocation
  can concentrate each factor on disjoint node sets with zero diagonal
  charge. The 2258 conclusion stands: feasibility must be posed on the
  fixed analytic per-node pieces (the canonical allocations), not on the
  free allocation polytope.
- The exact LP dual value (the true `max_J Hall(J)/|J|`, not just the
  greedy lower bound) is not claimed here; the greedy curve gives lower
  bounds only.

## Nonclaims

- greedy lower bounds, not the exact LP dual;
- the Hall family is necessary, not sufficient, for feasible allocations;
- float64 measurement on the committed grid;
- no producer GO, no gate sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_hall_screen_2261.py`;
- artifact: `results/2261_hall_screen.json`
  (md5 `82290392e225dad4e43a865a79fc031a`);
- machinery: `scripts/routea_weighted_zero_cancellation_split_2258.py`
  (`family_terms`, `trap_weights`), `scripts/routea_weighted_zero_direct_product_outward_2234.py`
  (construction);
- predecessor: `docs/proofs/2258_routea_weighted_zero_cancellation_split.md`.