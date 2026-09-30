# 2270 — Exact middle-k enumeration for the two open Hall rows (reserve)

Date: 2026-09-30

Consumer: 2266 closed the two ends of the coalitional Hall curve exactly
(`k <= 6` and, via excluded complements, `k >= 24`) and bracketed the
middle with certified ceilings plus 1-swap lower bounds; the two open
rows are decided in the middle — `corr_M0` at `k = 8` (bracket width
`4.72e-04` relative) and `corr_D2` at `k = 7` (`3.73e-04`). This reserve
driver enumerates those two `k` exhaustively on the committed float64
machinery, converting the registered climb lower bounds into exact
maxima.

Verdict: **MIDDLE-EXACT-CONFIRMED. Both exact maxima land within
`1.4e-15` relative of the 2266 climb lower ends and the exact argmax
witnesses are *identical* to the 2266 climb witnesses —
`corr_M0 k = 8`: hall `726.3375614016927`, ratio `6.1624990602415135`
vs lower end `6.1624990602415091`; `corr_D2 k = 7`: hall
`1049250.3213751798`, ratio `6.089451691669726` vs lower end
`6.0894516916697183`. The 2266 1-swap climbs were globally exact at the
deciding `k` on both rows; the remaining bracket width of the 2266
middle brackets is entirely ceiling slack, not enumeration slack. The
certified upper ends are unchanged (`6.1654080613840732` /
`6.0917247299667272`) and remain the valid bounds.**

## Method

1. The 2266 machinery is reused byte-for-byte: `row_arrays` (per-family
   magnitudes `M`, signed sum modulus `AG`, total `S` on the committed
   2197/2258 grid), `c58.trap_weights`, the one-hot chunked matmul
   `_chunk_task` with the complement convention
   (`Hall(J) = ∫ w (c + Σ_{j∈J} M_j)^+`, `c = AG - S`), 14 fork
   workers.
2. The only change is the index table: one full
   `itertools.combinations(range(30), k)` table per job
   (`5,850,925` rows for `k = 8`, `2,035,800` for `k = 7`), shared by
   fork exactly as in the 2266 fix — no `islice` generation skipping.
3. `exhaustive(k, "in")` then returns the exact float64 maximum over
   all `C(30, k)` subsets together with the argmax witness.

## Results

```text
row        k   exact hall              exact ratio           2266 [lo, hi]                    lo rel gap   wall
corr_M0    8   726.3375614016927      6.1624990602415135    [6.1624990602415091, 6.1654080613840732]  7.1e-16  2472.6 s
corr_D2    7   1049250.3213751798     6.0894516916697260    [6.0894516916697183, 6.0917247299667272]  1.3e-15   878.1 s
```

Witness sets (exact argmax): `corr_M0` `{0, 1, 11, 12, 13, 14, 15, 16}`,
`corr_D2` `{0, 1, 12, 13, 14, 15, 16}` — identical to the 2266
`witness_idx` on both rows; both pair the two small-`a` mirror families
`0/1` with a contiguous block `11–16` (respectively `12–16`).

## Interpretation

- The 2266 climb was not merely a local optimum at the deciding `k`: the
  global float64 maximum was already in hand, and the exact enumeration
  moves the lower end of the row bracket by at most `4.4e-15` absolute
  in ratio units. The 2266 bracket width (`4.72e-04` / `3.73e-04`
  relative) is therefore the ceiling's width, and only a sharper
  certified ceiling (or a directed-MPFR exhaustive run at the deciding
  `k`) can narrow it further.
- The infeasibility margins against the pigeonhole floor `62/30` are
  unchanged and now exact at the lower end: `2.1475067585012337` /
  `6.1624990602415135` / `2.6403870620083922` / `6.089451691669726`;
  the certified-grade statement of the same facts is 2269's.
- Cost calibrated: `k = 8` at `41.2 min`, `k = 7` at `14.6 min`, total
  `55.8 min` wall on the repo venv — this is the measured price of one
  exact middle `k` row, recorded so a future count-side revival can
  budget the remaining `k`'s if ever needed.

## Nonclaims

- float64 enumeration on the committed 2197/2258 grid: the maxima are
  exact in the enumeration sense, the arithmetic is float64;
- the certified upper ends are the 2266 ceilings, untouched; no ceiling
  improvement is claimed;
- the remaining middle `k`'s (`9..16` on `corr_M0`-side rows, `8..23`
  generally) stay at 2266 ceilings plus climb lower bounds;
- certified-grade brackets of the same quantities are 2269 (directed
  MPFR); no count-side revival, no allocation design, no producer GO,
  no gate sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_hall_middle_exact_2270.py`;
- artifact: `results/2270_middle_exact.json`
  (md5 `2d5019dd0453138282c558bcc5c91245`);
- machinery: `scripts/routea_weighted_zero_hall_exact_2266.py`
  (`row_arrays`, `_chunk_task`, `exhaustive`);
- anchors: `results/2266_hall_exact.json` (climb witnesses and
  brackets, compared row-by-row);
- predecessor records: `docs/proofs/2266_routea_weighted_zero_hall_exact.md`,
  `docs/proofs/2269_routea_weighted_zero_hall_ball.md`.