# 1392 — 1390 rig run: COMPLETE, SENTINEL DONE, GATES G1+G3 FAIL — run VOID (instrument, not route)

Date: 2026-09-13. Status: **VOIDED RUN — NO EVIDENTIARY STATUS** for any
verdict inside it (law 65 would make even a green run MODEL; a void run is not
even that). Record 1391 unblocked the run; the run happened; the prereg's own
sentinel adjudicated it. RH not claimed; the archimedean gate untouched.

## 1. Run facts

Script `scripts/run_1390_rig.py` (numpy float64) executed through
`scripts/run_resource_aware_task.sh --class normal` under
`/usr/bin/python3.12`, stdout captured to
`docs/proofs/1390_component5_rig_run.log` (sha256
`09b72f19a678b08a0a0297d6fc34ac5a248269b75dbb8665ff219b674e6573c5`), summary to
`docs/proofs/1390_component5_rig_results.json` (sha256
`00b632c989aff8fa5cc63f47f79e741d7b971058cdd83bed9ad650dc72884f81`), full
96,000-cell table to `docs/proofs/1390_component5_rig_cells.tsv.gz` (sha256
`a6fc36fec8fae00b99674407f0d02ccf79a2b516d60fef12fd90e0aff5f005a1`).

Literal final line of the run log (prereg §4 sentinel form):

```text
DONE gates=G0:PASS,G1:FAIL,G2:PASS,G3:FAIL,G4:PASS,G5:PASS
```

Per prereg §3, a failed gate VOIDS THE RUN, not the route. Two failed ⇒ the
run is void. Nothing in §1–§2, §6, §7 of 1390 is in question; the two
failures are located in the run-VALIDITY controls and in the numerical
precision class, analyzed separately below — they demand a new prereg
(1393 = v3) under the record-1373 protocol, NOT an edit of 1390.

## 2. Gate-by-gate telemetry (instrument diagnostics, NOT model evidence)

+------+--------+----------------------------------------------------------+
| gate | verdict| diagnosis                                                |
+------+--------+----------------------------------------------------------+
| G0   | PASS   | self-check confirmed: max Rf+Ru = 0.3464 <= log2/2,      |
|      |        | max d*Rg = 0.15588; all 25 radius cells admissible       |
+------+--------+----------------------------------------------------------+
| G1   | FAIL   | PREREG DEFECT. Reference cell (locked in 1390 s2)        |
|      |        | computes to ratio = -0.8539169552, band = FAIL (ceiling |
|      |        | 12317.1 vs delta/(2 C_min) = 6643.8 at C_min =          |
|      |        | 7.52579e-06). The control demands the BAND DROP under   |
|      |        | x10 K_loc_f inflation; at a saturated FAIL-band          |
|      |        | reference, ratio -0.854 -> -17.539 keeps band FAIL, and |
|      |        | NO faithful implementation of the locked formulas can    |
|      |        | make a band event occur: unsatisfiable-by-construction. |
|      |        | The prereg pre-assumed the reference would sit in        |
|      |        | PASS/MARGINAL. This is an instrument-spec defect.        |
+------+--------+----------------------------------------------------------+
| G2   | PASS   | pure formula calculus on the locked closed forms green:  |
|      |        | C_min strictly increasing in Rg, d, delta on sweeps;     |
|      |        | ratio strictly decreasing in C_min and in ceiling.       |
+------+--------+----------------------------------------------------------+
| G3   | FAIL   | IMPLEMENTATION-CLASS DEFECT (43 violations, all confined |
|      |        | to the R = 0.02 radius at oscillatory rho): cond(G) up   |
|      |        | to 1.174e13, float64 solve residual up to 1.26e-6 and    |
|      |        | spurious imaginary part up to ~294 on a quantity the     |
|      |        | model guarantees is REAL and strictly positive (Gram is  |
|      |        | positive definite at distinct nodes — record 1384        |
|      |        | theorem). So the MODEL passes G3 exactly; float64        |
|      |        | fidelity does not. The prereg fixed formulas, not a      |
|      |        | precision class; an honest instrument must state one.    |
|      |        | Non-0.02 radii resolve cleanly in float64 (cond max      |
|      |        | within those radii was under threshold), so the G1       |
|      |        | reference diagnosis (Rf = Ru = 0.08) is precision-safe.  |
+------+--------+----------------------------------------------------------+
| G4   | PASS   | C_min = min(C_C, C_D) consistent; 1378 small-d limits    |
|      |        | hold within 1% at d = 1e-3 on the reference geometry and |
|      |        | C_D < C_C (attainment) over all radius/delta corners.    |
+------+--------+----------------------------------------------------------+
| G5   | PASS   | zero cells exceed d*Rg = 0.53; regime claim of 1390 s2   |
|      |        | verified mechanically (max 0.15588).                     |
+------+--------+----------------------------------------------------------+

## 3. What the void means and what discipline follows

1. NO verdict status: the 45915 PASS / 6283 MARGINAL / 43802 FAIL counts, the
   best/worst cells, the frontier and seam tables are VOID telemetry. None may
   be cited as evidence about route alpha, and none enters 009's ledger.
2. Operator leak (stated explicitly, 1225 ABORTED-UNINFORMATIVE precedent):
   running v2 taught the operator that the 1390 reference geometry is
   deeply-FAIL-band and that tiny-radius oscillatory Grams are ill-conditioned.
   The defense is the same as it has always been: the MODEL side of the
   prereg — formulas (1390 s1), grids (s2), band thresholds (s1.7), kill scope
   (s6) — is re-locked VERBATIM by 1393 and was not touched by this leak; only
   the two instrument sections (G1 control form, G3 precision class) are
   revised, and their revision is justified solely by the two proofs above
   (unsatisfiability; model-exactness vs float64), which are statements about
   instruments, not about which cells PASS.
3. 1393 = v3 preregistration: same model, same grids, same bands, same
   sentinel; G1 replaced by a band-universal negative control (x10 inflation
   must strictly decrease ratio, multiply the shortfall 1 - ratio by exactly
   10 within 1e-9, and never RAISE the band rank); G3 given a locked
   precision class (mpmath >= 50 dps for K_loc and for the final J1
   comparison; exact zero-frequency branch; residual/imag thresholds stated
   numerically in the prereg itself). No grid, band, formula or threshold
   otherwise moves.

## 4. Register state after this record

```text
009 §5 item 3 (rig-confirmed digits discharging hJ1)   OPEN — v2 run VOID,
                                                       v3 prereg committed
everything else per record 1391                        unchanged
```
