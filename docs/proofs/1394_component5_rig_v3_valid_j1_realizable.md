# 1394 — 1393 rig run: VALID (G0–G5 all PASS) — (J1) is MODEL-realizable on route alpha; the digits are recorded

Date: 2026-09-13. Verdict up front: **GOOD**. Under the continuation prereg
[1393](1393_component5_route_A_prereg_v3_instrument_fix.md) the rig executed
clean: all five verdict-capable gates PASS, and the verdict is that **(J1)
`ceiling < delta / (2 * C_min)` holds on a large, structured region of the
locked grid** — 45,915 of 96,000 cells PASS with margin ratio >= 1/2, at EVERY
locked `d` including the largest (`d = 0.45`). This is 009 section 5 item 3's
executable obligation discharged: the rig-confirmed (MODEL, law 65) digits
exist and are committed with their artifacts.

Scope lock inherited from 1393 section 0, restated because it is the whole
meaning of this record: a PASS cell here is budget arithmetic on the
route-alpha register. It does NOT discharge `hfit` or `hJ1` on the formal lane
(they remain input hypotheses of the record-1391 leaf), does NOT evaluate the
archimedean gate, does NOT certify RH. A FAIL cell kills only its own window,
family, bridge route, and parameter range (1393 section 6).

## 1. Run ledger (both invocations, per the 1225 precedent)

```text
invocation 1  VOIDED — implementation bug, no model content ever produced
invocation 2  VALID  — the run this record adjudicates
```

Invocation 1 sentinel: `DONE gates=G0:PASS,G1:FAIL,G2:PASS,G3:FAIL,G4:PASS,
G5:PASS` with every `K_loc = 0.0`. Root cause (minimal reproduction): the
script built the value vector as `mp.matrix(4, 1, pattern)`, but mpmath's
THIRD POSITIONAL ARGUMENT IS A CALLABLE, not entries — the matrix was
silently zero-filled, so `z* G^-1 z` was identically zero, all cells were
spuriously PASS, and **G3's positivity check caught it** (96,200 violations).
The instrument failed exactly the way 1393 section 3 G3 was written to catch
a dropped zero-frequency branch; same detector, different bug.

Hygiene note, stated plainly: invocation 1's artifacts were overwritten by
invocation 2 because they shared the prereg'd output paths (the `.inv1`
rename was skipped). No information loss beyond that — the invocation-1
sentinel and the all-zero telemetry are quoted above from the run itself,
and an invalid instrument produced no verdict to preserve. Law 42 is
untouched: the fix is a transcription repair of the LOCKED 1393 formulas
(a crashed/zero-filled evaluation is not a different model), so invocation 2
ran the identical prereg, unchanged, before any v3 digit was adjudicated.

Invocation 2 artifacts (repository paths; sha256):

```text
docs/proofs/1393_component5_rig_run.log          c8778f002b5b3eec78566ab0646ea4d3
  630c381ab17e2e72d359116442fa59c5
docs/proofs/1393_component5_rig_results.json     da304c1f441a49f180d88d754b658d6d
  22435c8f5033152946a04251a8f22f0d
docs/proofs/1393_component5_rig_cells.tsv.gz     8548d87a9ede4b7725137bafb56b3267
  8f975de3521beaf10692ab8163c66c2e        (96,000 rows + header)
```

Literal final line of the run log (prereg 1393 section 4 sentinel form):

```text
DONE gates=G0:PASS,G1:PASS,G2:PASS,G3:PASS,G4:PASS,G5:PASS
```

## 2. Gate telemetry (1393 section 3)

+------+-------+--------------------------------------------------------------+
| gate | result| detail                                                     |
+------+-------+--------------------------------------------------------------+
| G0   | PASS  | max Rf+Ru = 0.3464 <= log2/2 = 0.3465736; max d*Rg = 0.15588 |
| G1   | PASS  | (a) ratio strictly lower under x10 K_loc_f: -0.85391687 ->   |
|      |       | -17.5391687; (b) shortfall identity 1.85391687 ->            |
|      |       | 18.5391687 exactly x10; (c) band rank non-increasing         |
|      |       | (FAIL -> FAIL). The band-universal redesign: a reference     |
|      |       | that is itself FAIL-band no longer makes the control         |
|      |       | unsatisfiable — this is the gate whose 1390 form was void.   |
| G2   | PASS  | strict on all pure-formula sweeps (C_min in Rg and delta;    |
|      |       | ratio in C_min and ceiling)                                  |
| G3   | PASS  | 0 violations at 200-bit: min K_loc = 2.831 over the 200      |
|      |       | tables, solve residuals <= 1e-30 class (measured ~1e-58),    |
|      |       | |Im K| ~ 1e-60 class, 0 tie cells. The float64 spurious      |
|      |       | imaginary ~294 of v2 is gone                                 |
| G4   | PASS  | small-d limits within 3e-4 and 1.5e-4 relative (lock: 1%);   |
|      |       | C_D attains C_min at every corner                            |
| G5   | PASS  | 0 cells with d*Rg > 0.53 (max 0.15588): near-line regime     |
|      |       | covers the whole grid, as 1390 section 2 asserted            |
| G6   | REPORT| informational only, 100 (Ru, rho) rows, no verdict weight    |
+------+-------+--------------------------------------------------------------+

Fidelity check against the void v2 run (instrument-vs-instrument, not model):
reference-cell `ceiling = 12317.084792` (200-bit) against 12317.1 (float64),
ratio `-0.85391687` against `-0.85391696` — the corrected mp pipeline
reproduces the precision-safe part of v2 and removes the R = 0.02 artifacts.

## 3. The verdict: (J1) holds on a structured region of the locked grid

Band counts over all 96,000 cells (1393 section 1.7 bands: PASS ratio >= 1/2):

```text
PASS       45,915   (47.8%)
MARGINAL    6,283   ( 6.5%)
FAIL       43,802   (45.6%)
ties            0
```

Structure 1 — the PASS region spans every locked `d` (each `d` slice has
12,000 cells), i.e. nothing here is a "small-d only" artifact of the grid:

```text
d        PASS  MARG   FAIL     best ratio in slice
0.005    6780   674   4546      0.999998
0.01     6744   655   4601      0.999996
0.02     6636   697   4667      0.99999
0.05     6355   645   5000      0.999943
0.1      5905   725   5370      0.999777
0.2      5155   900   5945      0.999107
0.3      4565   947   6488      0.997985
0.45     3775  1040   7185      0.995442
```

Frontier (per `(d, Rg)`, largest PASS `delta`, 112 entries): at EVERY locked
`d`, 10–11 of 14 radius-sum entries reach `delta* = 1.0`, the TOP of the
locked `delta` grid — the PASS region is not hugging a knife edge in
`delta`.

Structure 2 — the dominant FAIL driver is LOW OSCILLATION, not the budget
scale generally. Per node-height (24,000 cells each):

```text
Im rho      PASS/24000   best ratio at
14.134725    4,460       0.999773   (Rf=0.1732, Ru=0.02)
21.022040    8,678       0.999957   (Rf=0.1732, Ru=0.02)
25.010858   10,652       0.999974   (Rf=0.1732, Ru=0.02)
1054.0      22,125       0.999998   (Rf=0.02,   Ru=0.02)
```

At the reference `(d, delta, Rf, Ru, eps, epsp) = (0.05, 0.1, 0.08, 0.08,
0.01, 0.01)` this shows as: ALL five `Re rho` variants of the FIRST ZERO
(`Im = 14.134725`) are FAIL at ratio ~= -0.85, while `Im = 21.02` -> PASS
0.798, `Im = 25.01` -> PASS 0.919, `Im = 1054` -> PASS 0.997. The prereg'd
reference geometry chose the hardest height — which is why 1390's band-DROP
G1 was unsatisfiable — but the grid as a whole is NOT reference-dominated.

Mechanism reading (MODEL, offered as diagnosis not theorem): `K_loc_f ~
||y||^2 * (1 + |Im rho|^2 stuff)` grows like `|Im rho|^2 / Rf`-type power as
the taper window shrinks around an oscillatory target, so the escape route
for a low-height node is the LARGE taper radius; the best low-height cell
indeed sits at the largest admissible `Rf = 0.1732` combined with the
smallest `Ru = 0.02` (the `2*Ru` width factor is linear there, while the
`K_loc_f` gain from a wide taper beats it).

## 4. Concrete (J1) witness and the falsification content

Best cell, fully specified for reuse (all parameters on locked grids):

```text
d = 0.005   delta = 0.01   Rf = 0.02   Ru = 0.02
eps = eps' = 0.01   rho = 0.99 + 1054.0 I
K_loc_f = 25.23943122   K_loc_u = 83.82445464   ceiling = 86.32827029
C_min = 1.173397341e-10 (= C_D)
ratio = 0.9999979741  ->  PASS with margin ~ 2.03 ppm short of 1
```

And the low-height witness the mechanism reading predicts (same
`d, delta, eps`, radii swapped to the taper-heavy corner): ratio 0.999773
PASS at `Rf = 0.1732, Ru = 0.02` with `rho` on the first-zero height. So
route alpha's budget arithmetic is consistent with (J1) at EVERY node height
in the locked grid — there is NO height at which (J1) is unattainable on
this grid, and the FAIL cells are interior to the parameter box, not the
whole register. That is the negative-control content of this run: had the
locked formulas made `C_min * ceiling >= delta/2` at ALL 96,000 cells,
route alpha's N2beta budget would have been falsifiable at MODEL level
(scoped per 1393 section 6). It is not.

What this does NOT say: the FAIL region (43,802 cells + 6,283 MARGINAL) is
real telemetry — careless window choices (large `Ru`, small `Rf`, big `d *
delta`) DO blow the budget, and the 1391 Lean leaf is silent about which
cell is eventually wired, so the digit table constrains future wiring
choices rather than funding them.

## 5. Register state after this record

```text
009 section 4 block:
  component 5-discharge R1 leaf + wiring                FORMAL DONE (1391)
  component 5-discharge rig digits (hJ1), prereg 1390
    -> v2 VOID (1392) -> v3 prereg (1393) -> VALID RUN   RIG DONE (MODEL)
  Archimedean gate 0 < archimedeanTerm                  OPEN (inherited,
                                                        not an N2beta duty)
```

009 section 5 items 1–4: CLOSED as far as this contract's executable
obligations go (items 1, 2, 4 formal; item 3 now backed by a valid,
committed, gate-green MODEL run). What remains under this contract is
section 5 item 5, the inherited archimedean gate, which 1389 section 6
established is pre-existing open science from records 1080/1081 — not a
wiring task — and which no rig in this family evaluates. RH NOT claimed
anywhere in this record.
