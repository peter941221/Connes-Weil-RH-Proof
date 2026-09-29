# 2258 — Cancellation-aware split recon of the direct-product screen

Date: 2026-09-30

Consumer: the withdrawn count-side transfer (2253 falsified the triangle
per-node split at `owner/62`; the 2257 count-free assembly is the live
route). This record answers the structural question the triangle split
cannot: the 2234 sigma rows are CANCELLED strip-weighted L1 norms of the
signed family sums, so a split has canonical cancellation-aware forms —
the pointwise pro-rata allocation (telescopes exactly to the row) and the
coalitional Hall floors (mandatory mass of any subset of nodes).

Verdict: **SPLIT-STILL-FAILS-CANONICALLY. Reconstruction of the signed
sums against the committed MPFR anchors holds to `1.77e-15` relative on
all four rows; the cancellation factors are 19.25 / 64.55 / 10.30 / 61.12
(triangle/norm); the canonical pro-rata two-sided split fails at max
diagonal ratio `8.1166` (channel a) / `9.0918` (channel b), 3/30 nodes
over budget, while its total charge is only `0.1997` / `0.2241` of the
screen product — localization, not total. The mandatory floors are ~0 at
the singleton and top-3 coalition levels (`<= 0.00288` and `<= 8.7e-3` of
the single-node budget), so the failure is an allocation-design gap, not
mandatory integrand mass. Flat-factor and any per-factor-bounded splits
are structurally impossible (30 nodes < 62 budget slots; the all-node
Hall condition). The `owner/62` count-side transfer stays withdrawn.**

## Reconstruction (convention check)

The rows are the cancelled L1 norms `int e^x |sum_j c_j f_j''(x)| dx`
(base) and `int e^x |sum_j c_j f_j(x)| dx` (corr) at sigma = 1,
NX = 240001. Rebuilding the signed sums in float64 (2234 `smoke()` numpy
formulas; boundary region `qq <= 0.04` masked, there `exp(-K/qq)` is below
float64) reproduces the committed MPFR anchors:

```text
row        float64 reconstruction    2234_sigma_100 anchor   rel err
base_M0              2.0033357887456087     2.0033357887456122   8.6e-16
corr_M0             913.4469710803507      913.4469710803506     1.6e-16
base_D2            6688.576604759935      6688.576604759946      1.8e-15
corr_D2         1526140.687188009      1526140.6871880104        9.3e-16
```

## The four canonical splits (per row, budget = row/62)

```text
row        norm          canc   signed-sum  max pro-rata  max floor  max signed
base_M0       2.0033     19.25        1.370        21.81     0.00288      48.58
corr_M0     913.4470     64.55    1.99e-06         25.33     0.00121    1.04e-04
base_D2    6688.5766     10.30    4.10e-04         19.87     0.00282      0.0146
corr_D2 1526140.6872     61.12    1.19e-09         25.85     0.00101    6.23e-08
```

`canc` = triangle total / norm. `max pro-rata` / `max floor` = the worst
node's ratio over the uniform budget. `max signed` (informational) = the
worst node's `|int e^x g_j|` over budget: the corr rows' signed pieces
essentially vanish (intra-family x-oscillation at `e^{i theta x}`, sums
of `|I_j|` at 2e-6 and 1e-9 of the norm), so a hypothetical signed-form
transfer would face the base rows only.

## The two channels (diagonal product split `4*mult*share_b_j*share_c_j`)

```text
channel  rows               raw product            max diag  floor   over  product share
a        base_D2 x corr_M0      6109660.040456859     8.1166  7.8e-14  3/30        0.19972
b        corr_D2 x base_M0      3057372.2573045553    9.0918  2.4e-13  3/30        0.22406
```

The channel-b raw product equals the committed 2197 `B_upper`
`3057372.2573045553` bitwise (the binding screen channel). The diagonal
split is dominated by three nodes: node 0 `(a=1.60, theta=-39.25)` with
32.0–41.7% of each row, node 15 `(1.76, -40.92)` with 14.9–25.3%, node 14
`(1.76, -37.59)` with 12.6–24.4%; everything else is under 4% and 27
nodes sit far under budget.

## Structural facts

1. Flat-factor pigeonhole: any split holding one factor flat has
   `max_j >= row/30`, ratio over the budget `>= 62/30 = 2.0667 > 1`.
   The 2253 failure (triangle 207x) is this structural factor times
   triangle localization — no flat-format transfer can ever fit.
2. All-node Hall condition: `sum_j a_j >= int |G| = row` with 30 nodes
   and `a_j <= row/62` each gives `row <= 30*row/62 = 0.4839*row`,
   contradiction: per-factor-bounded splits are impossible.
3. Free two-sided allocation is degenerate: concentrating the two factors
   on disjoint node sets makes all diagonal products vanish, so
   feasibility is not a free-allocation question; the binding objects are
   the floors and the canonical allocations.
4. Pro-rata dominance: for every coalition `J`, the Hall mass
   `int (|G| - (S - A_J))^+ <= int A_J |G|/S` pointwise, so the pro-rata
   allocation of `J` dominates every valid split's mandatory mass of `J`.
   The measured Hall masses sit at the bottom of this sandwich:
   singletons `<= 0.00288` budget units, top-3 coalition `<= 8.7e-3`
   (corr_D2; the other three rows `<= 2.2e-40`).
5. Sandwich: `Hall (≈0) <= feasible allocations <= pro-rata (8-9x over
   budget)`. The canonical split fails; whether ANY floor-respecting
   allocation fits is an allocation-design LP (the coalitional Hall
   system), registered open, and even then realizability by the
   producer's fixed shell pieces would have to be shown.

## Nonclaims

Float64 measurement on the committed grid (anchors bound the convention
error); the floors are valid pointwise-allocation lower bounds, but the
producer's fixed shell pieces may impose structure not modeled; the
ledger ratios use the diagonal (same-family) pairing — cross-node pairings
are not available to the analytic decomposition. No producer GO, no gate
sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_cancellation_split_2258.py`;
- artifact: `results/2258_cancellation_split.json`
  (md5 `030f15f64f7edf513114092ab4624aca`);
- machinery: `scripts/routea_weighted_zero_direct_product_outward_2234.py`
  (`build_construction`, grid), anchors `results/2234_sigma_100.json`;
- predecessor: `scripts/routea_weighted_zero_pernode_charge_2253.py`.