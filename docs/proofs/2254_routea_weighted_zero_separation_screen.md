# 2254 — Certified separation and local uniform-in-ρ disks at all three registered configurations

Date: 2026-09-30

Consumer: the 2157 near-pin derivative floor input (via the 2247 separation
input, certified at candidate 1 by 2251), upgraded from one candidate to the
full registered configuration screen.

Verdict: **each of the three 2103 stress configurations is certified —
Hardy-Z brackets for every pin, per-target separation lower bounds, and a
local disk in ρ on which the node set is unchanged and every target-to-pin
separation degrades by at most `2 eps_rho`; a literal continuum
uniform-in-ρ statement is obstructed at ball-edge ordinate crossings and is
not claimed.**

## The screen and its numbers

```text
gamma                       39.25244858548658   42.12289614653125   45.66611208104108
critical-line zeros                     21                  24                  27
construction nodes                      30                  33                  36
in-ball added zeros                     12                  15                  18
min target-pin sep (certified    1.7246687029005738  1.283770840521257   2.380992966914272
  lower, two-ulp outward)
eps_rho (0.95 * min)           0.18587152073670574 0.2613019397045188  0.2499569408768854
first ordinate above window    82.91038085408603   88.80911120763446   95.87063422824531
  (index)                              22                  25                  28
local separation  s_min-2eps   1.3529256614271623  0.7611669611122195  1.881079085160502
local floor 2157 (min over     0.0003688351374802202 0.00038388813750691464 0.00020275988007744964
  targets)
```

Brackets: 72 total, max width `5.293955920339377e-25`, min endpoint margin
`2.9109288740357516e-26`, min pairwise bracket gap `1.4401493697908734`
(candidates 1–2).

Targets at every candidate are `(0.055, gamma)`, `(0.945, gamma)`,
`(1.445, gamma)` — the `0.945 = 0.5 + 0.445` stress point and its mirror and
outer companions. All three nearest pins are critical-line zeros.

## The two ingredients of the disk

The construction depends on ρ only through the node set (the ball
`|z - rho| <= R(rho)` selects which zeta ordinates are appended). A disk
`|rho' - rho| <= eps_rho` therefore keeps the node set fixed if no ordinate
can enter or leave the ball, which is controlled by two scans:

```text
eps_window   (first ordinate above the window edge gamma + R) / 2
             distance from the closed-ball edge to the next ordinate above
eps_ball     (first ordinate outside the ball) / 2
             distance from the ball boundary to the first ordinate beyond R
eps_rho      0.95 * min(eps_window, eps_ball)
```

On that disk each node moves by at most `eps_rho`, so every certified
separation degrades by at most `2 eps_rho` (triangle inequality), and the
2157 floor is re-evaluated at `floor_2157(sep_j - 2 eps, support,
s_j + 2 eps)`.

Instrument note (correction made during assembly): the first run recorded
the floor at the smallest-separation target; the floor is decreasing in
`s_real` and the `Re = 1.445` target has the largest `s_real`, so the true
worst floor is ~4x smaller than that first reading. The artifact now takes
the min over all three targets (and stores the full per-target table).

Candidate 1's `eps_rho = 0.18587152073670574` is consistent with the 2251
value `0.18587152073670352` (absolute difference `2.2e-15`, a
rounding-order effect in the `0.95` scaling).

## The covering statement

The union of the three disks covers the registered configuration screen:
within each disk the node set is unchanged, every target-to-pin separation
is `>= s_min - 2 eps_rho`, and the 2157 floor is at least the registered
per-candidate local floor. The floor is worst at candidate 3
(`0.00020275988007744964`), the separation is worst at candidate 2
(`1.283770840521257`).

## The continuum obstruction

A literal statement "for every ρ in the band" is obstructed, and the
obstruction is measured rather than assumed:

```text
pair    window edge sweep                  ordinates crossed (indices 22-27)         in-ball added
1 -> 2  82.51907238937717 -> 88.2590018608881   82.91038085408603 (22)  12 -> 15 (+3 = the three
                                                84.73549298051705 (23)          crossed ordinates)
                                                87.42527461312523 (24)
2 -> 3  88.2590018608881  -> 95.34440908955713   88.80911120763446 (25)  15 -> 18 (+3)
                                                92.49189927055848 (26)
                                                94.65134404051989 (27)
```

The closed-ball edge `gamma + R(rho)` sweeps across zeta ordinates as gamma
varies (it sits below the next ordinate at candidate 1 and above it at
candidate 2), the in-ball node set changes between candidates, and
`eps_rho` degenerates to zero at each crossing. The correct uniform object
is therefore the discrete registered configuration screen, certified member
by member here; a continuum claim would need a fresh node-set
re-derivation at each crossing.

## Registered caveat

At candidate 2, `target_target_margin = min_target_distance - 2 eps_rho =
-0.02260387940903763` is negative: the crude displacement bound does not
preserve target-to-target separation inside the disk when `2 eps_rho`
(0.523) exceeds the lattice spacing of the targets (0.5). This does not
affect the 2157 floor, which uses target-to-pin separations only, but no
future consumer should read target-target isolation off this disk.

## What this closes and what it does not

Closed: the "certified zero isolation per configuration" obligation
screen-wide, with explicit local disks.

Not closed: Lean formalization of these numeric certificates; any continuum
uniform-in-ρ statement; the 2157 floor lemma itself beyond what 2247/2157
already carry; no producer GO, no gate sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_separation_certified_2254.py`;
- artifact: `results/2254_separation_certified_three_candidates.json`
  (md5 `7fc74254d9341cee894c55dad2c86cf4`);
- machinery: `scripts/routea_weighted_zero_separation_input_2247.py`;
- predecessor: `scripts/routea_weighted_zero_separation_certified_2251.py`;
- anchor: `results/2103_full_known_prefix_direct_owner_grid_m6400.json`.