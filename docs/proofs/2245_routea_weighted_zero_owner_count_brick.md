# 2245 — Explicit owner zero-count brick on the screened windows

Date: 2026-09-30

Consumer: the 2119 complete-owner transfer, decision item (1): "a
substantially sharper explicit zero-count bound on this owner window".

Verdict: **landed** (count side). At the stress point the formal Jensen /
dyadic-growth cardinality bound `3002.5554464806` is replaced by an explicit
window count: `<= 26` unconditionally, `= 21` under the Platt-Trudgian
import; the 2119 coarse transfer product drops from
`48.428313652912905 x tail/margin` to `<= 0.41935483870967744 x
tail/margin` (unconditional) or `= 0.3387096774193548 x tail/margin`
(imported).

## The window and the identity

A closed-ball owner zero `z` with `|z - rho| <= R` has `|Im z - gamma| <= R`,
so its height lies in `[T-, T+]` with `T+ = gamma + R` and `T- = gamma - R`
(here negative; the conjugate window is `|T-|`). Since
`Z(t) = exp(i theta(t)) zeta(1/2 + i t)` is real, the unwrapped
critical-line phase `Phi` of `zeta` satisfies the exact identity

```text
N(T) = (theta(T) + Phi(T)) / pi      (classical: N = 1 + theta/pi + S, S = Phi/pi - 1)
```

so the owner count is bounded by `N(T+) + N(|T-|)` with each window bounded
through `|S(T)|`. The script verifies the identity numerically at every
candidate (Hardy-Z sign-change scan versus accumulated phase; residual
`0.0 / 0.0 / 2.5e-60`).

## Imported bounds

- `|S(T)| <= 0.111 log T + 0.275 log log T + 2.450` for `T >= e`
  (T. S. Trudgian, "An improved upper bound for the argument of the Riemann
  zeta-function on the critical line II", J. Number Theory 134 (2014),
  Theorem 1; arXiv:1208.5846, statement read from the paper). The 2012
  variant `0.17 log T + 1.998` (same paper's comparison table) is computed
  alongside; both give the same floored counts here.
- D. Platt, T. Trudgian, "The Riemann hypothesis is true up to 3*10^12",
  Bull. LMS 53 (2021) 792-797: every zero with `0 < Im <= 3*10^12` is on
  the critical line with certified counts; the enumerated critical-line
  count then equals the exact owner count.

## Numbers at the three 2103 stress candidates

```text
gamma          39.25244858548658  42.12289614653125  45.66611208104108
R              43.266623803890596 46.13610571435686  49.67829700851605
T+             82.51907238937719  88.2590018608881   95.34440908955713
|T-|           4.014175218404013  4.013209567825612  4.012184927474969
theta(T+)/pi   20.56205790295165  22.945612850453898 25.969480899363067
N_up(T+) 2014  24.910158557424733 27.305336713036194 30.342475574268278
N_up(|T-|)     2.6463342025374934 2.6463291699780167 2.646323842072918
owner <=       26                 29                 32
zeros in ball  21                 24                 27
ratio uncond   0.4193548387096774 0.4677419354838709 0.5161290322580645
ratio imported 0.3387096774193548 0.3870967741935484 0.4354838709677419
```

Readings against the 2243 standing `tail/margin = 0.006850392090059914`
(the 62-node screen charge; the count ratio multiplies the screen charge
in the linear transfer reading):

```text
reading uncond 0.0028727450700251254  0.003204215655028024   0.003535686240030923
reading import 0.0023202940950202934  0.0026517646800231923  0.0029832352650260917
```

At the stress point the improvement over the 2119 formal count bound is
`115.48290178771539x` (unconditional floor) and `142.9788307847905x`
(imported exact). The last enumerated heights and the first beyond the
window confirm the counts: `79.33737502024937 / 87.42527461312523 /
94.65134404051989` and `82.91038085408603 / 88.80911120763446 /
95.87063422824531`.

## Kill-list audit (instrument finding)

`fourpoint_owner_completion_1980.GAMMAS[3] = 27.67032193035704`, labelled
`gamma_4` from record 1980 onward, is **not a zeta zero**:
`|zeta(1/2 + 27.67032193035704 i)| = 2.845101349` at 50 dps, the Hardy-Z
scan finds no sign change there, and the exact identity gives
`N(82.51907238937719) = 21` to `1e-15`. The true `gamma_4` is
`30.424876125859513210` (already the 5th entry of the same list). The 1994
kill list is therefore 9 true zero pins plus one non-zero pinned ordinate.
Impact: the 2103 construction and the 2109 ledger price the actual
construction (unchanged); node totals `30 / 33 / 36` decompose as
`21 / 24 / 27` true in-ball zeros plus 9 non-zero nodes (3 targets, 2
conjugate orbit pins, 3 real-axis pins, 1 non-zero kill pin); no Lean
statement is affected (the formal owner stays abstract). This count brick
enumerates true zeros only.

## What this closes and what it does not

Closed: the count side of the 2119 transfer decision item at the three
screened candidates, at both the unconditional and the imported reading;
the 2241 "count-refinement lever" is priced (`115x`-`143x`).

Not closed / nonclaims:

- the Trudgian `S(T)` bound, the Riemann-von Mangoldt identity input and the
  Platt-Trudgian import are cited external theorems, not Lean-formalized
  facts; Lean registration is a separate obligation;
- the count brick bounds the owner cardinality; the per-node uniformity
  half of the transfer (charge of nodes outside the screen) remains open,
  so the product reading is still a reading;
- no producer GO, no gate sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_owner_count_brick_2245.py`;
- artifact: `results/2245_owner_count_brick.json`;
- inputs: `results/2103_full_known_prefix_direct_owner_grid_m6400.json`
  (candidates and supports), `results/2243_panel_cem_reprice.json`
  (standing `tail/margin`), `r80.ball_radius`, `r94.G7/G8` candidates.