# 1401 — Rung-3 low-height outcome: VALID first invocation, 0/41, A(g) now measured NEGATIVE at the actual zeta-zero heights including the first zero; the taper is STRUCTURALLY tiny on the (J1)-feasible region, which is why 82/82 negatives are one mechanism, not 82 data points

Date: 2026-09-14. Outcome record of
[1400](1400_rung3_lowheight_joint_witness_prereg.md). Instrument and
model byte-shared with the certified 1398 v3 chain by import. First
rig of this line to run VALID on invocation 1 — the F12 pre-run
conditioning audit did its job. RH not claimed.

## 1. Verdict (up front)

BAD as campaign news, GOOD as instrumentation, and NEW as structure:

* `DONE gates=G0:PASS,GI:PASS,GS:PASS,GT:PASS,GF:PASS,GD:PASS,GR:PASS,GQ:PASS`
  (all 8, first invocation, 368 s wall, no VOID, no BADCELL).
* `VERDICT jointWitness=NONE cells=POS:0,NEG:41,TIE:0,BAD:0`.
* **The archimedean functional has now been evaluated on owners built at
  the three ACTUAL zeta-zero heights (14.134725, 21.022040, 25.010858)
  — including the first zero — and it is decisively negative at every
  one: A = -36.0..-23.8, -9.2, -5.9 respectively, margins 1.0e5-1.5e5
  tie-band widths.**
* Kill scope honored VERBATIM (1398 s6 via 1400 s4): 0/41 kills NOTHING.
  Together with 1399 this retires the remaining "we never looked at low
  heights" excuse: within the 4-node route-alpha family and the
  instrument-visible (J1)-head of the grid, rung 3 is uniformly,
  mechanistically negative.
* NEW STRUCTURAL FINDING (section 4): the negativity is not a tuning
  accident — the locked construction makes the taper correction
  O(1e-10) small on every geometry where (J1) passes. The two rungs are
  inversely coupled through alpha. This converts 82 cell-negatives into
  one model-level statement.

## 2. Gate table (1400 inv1 = the only invocation)

| gate | measured (tier-1 = (0.1732, 0.08, 0.01, 0.01, rr=0.99, im=14.134725)) | class | verdict |
|---|---|---|---|
| G0 | max Rf+Ru = 0.2532 <= log2/2 | exact | PASS |
| GI | 1393 artifact recompute, every PASS row + samples | 1e-9 | PASS |
| GS | mp solve residuals | 1e-30 | PASS |
| GT | S-symmetry / J-pairing / J(0) | 1.2e-60 / 6.8e-17 / 1.0e-15 | PASS |
| GF | F(0) = +25.29300, \|Im\| = 4.1e-17, npw-24 recompute | ~1e-10 obs | PASS |
| GD | \|lap(g,rho)+1\| = 1.27e-9 (best of all tiers: 3.5e-9 max) | 1e-6 | PASS |
| GR | npw 32/64/96 + Richardson A_R all agree to 7+ digits | 1e-5 | PASS |
| GQ | A(2g) = 4A: -143.1883 vs 4x(-35.797066918) | 1e-9 | PASS |

F12 validation: the pre-run prediction was relative noise <= 2.4e-7;
the observed convergence spread is ~1e-10 — predicted-achievable,
locked-unchanged-from-1398, achieved 3+ orders better. The visibility
filter (1e-11 alpha floor) was neither too loose (no GR/GF near-misses)
nor over-restrictive (820 of 1200 visible).

## 3. Stratified census (41 tested; 380 excluded cells disclosed as UNTESTED in 1400_rig_visibility.tsv, never counted as negatives)

| height im | cells | A range | A/S | \|lap+1\| max |
|---|---|---|---|---|
| 14.134725 (FIRST ZERO) | 21 | -36.041 .. -23.819 | -0.152 | 3.5e-09 |
| 21.02204 | 10 | -9.219 .. -9.167 | -0.165 | 1.7e-09 |
| 25.010858 | 10 | -5.935 .. -5.899 | -0.167 | 1.1e-09 |

Within-stratum spread: |A| decreases with height (14.13 -> 21.02 ->
25.01 gives 36 -> 9.2 -> 5.9 at the heads) while |A/S| barely moves:
the scale is carried by F(0), the SIGN is not scale-tunable.

## 4. The mechanism finding: visibility is not sensitivity (law F14)

1399 found eps/epsp dead at tier-1 because delta ~ 7e-33 fell below
float64. 1400 ran the low-height head where delta = 1.5e-14..1.5e-13
IS representable — and eps STILL does not move A at printed precision
(all four eps-combos of each geometry agree to 7 digits). The deeper
law: the taper correction to g is O(delta/R) RELATIVE even when
representable; at the (J1)-feasible head delta/R ~ 1e-13, so the taper
correction to A is ~1e-10 relative — invisible, and structurally so:

```text
delta = eps * alpha / (4(1+eps) TB^2)     [Lift.lean:700, locked model]
delta/R ~ 1e-2  would require  alpha ~ 0.04 * 4(1+eps) TB^2 R / (eps R)
                               ~ 1e2..1e3  >>  lambda_max(G) ~ 2R ~ 0.1
IMPOSSIBLE for any window R in the grid.
```

Consequence (MODEL-level, honest scope): on the 4-node route-alpha
construction the (1+eps) taper can NEVER be an A(g)-shape lever at any
(J1)-feasible geometry — the budget inequality that delivers rung 2
forces the taper to be a ~1e-10 perturbation, and A is then the functional
of the UNTAPERED solved-exponential convolution, whose sign is fixed by
the node set and the heights. All 82 negatives (41 high + 41 low, 1399 +
1401) are ONE statement of this mechanism. Rung 3 will not be won by
searching more of this grid; it requires a DIFFERENT shape class
(route beta's orbit/7-node family, where the interpolation condition
does not force the same spectral content) or a proof-level idea.

## 5. Boundary and register

No Lean was written in this wave. Artifacts committed:
`1400_rung3_lowheight_joint_witness_prereg.md`, `scripts/run_1400_rig.py`,
`docs/proofs/1400_rig_{run.log,results.json,cells.tsv.gz,visibility.tsv}`
(sha256 in the log; *.log gitignore convention as in 1399: the VALID log
stays in the working tree, its sentinels quoted verbatim here and every
number reproduced in results.json). harch/hJ1 UNDISCHARGED; rung 4
formal-conditional; rung 5 = THE wall (B0b machine-checked iff
SourceRH). RH not claimed, in either direction, by anything in this
record.
