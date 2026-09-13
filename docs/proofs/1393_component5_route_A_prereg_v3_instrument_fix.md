# 1393 — Preregistration v3: N2beta component 5 discharge rig (route A, route-alpha register, MODEL evidence)

Date: 2026-09-13. Law 42: committed BEFORE any v3 digit. Law 65: every number
a future run produces under this prereg is MODEL.

**Lineage.** This file continues [1390](1390_component5_route_A_prereg_v2.md)
(supersedes [1388](1388_component5_route_A_prereg.md)). The first 1390 run
executed on 2026-09-13 after its run precondition was met (record
[1391](1391_r1_route_alpha_owner_leaf_green.md)) and came back
**VOID** on two gates, diagnosed in
[1392](1392_rig_run_void_G1G3_pregate_defects.md). Both failures are
run-VALIDITY controls, not model content:

1. **G1 unsatisfiable-by-construction**: the locked reference geometry is
   deeply FAIL-band (telemetry: ratio -0.8539), and a band-DROP negative
   control can never fire at a saturated reference under ANY faithful
   implementation of the locked formulas. Fix: band-universal control (§3 G1).
2. **G3 precision class unstated**: at R = 0.02 oscillatory corners
   float64 Gram cond reaches 1.174e13 and the model-guaranteed-real K_loc
   leaks ~294 of spurious imaginary part. The MODEL passes G3 exactly
   (positive definite Gram at distinct nodes, record 1384); float64 fidelity
   is the failure. Fix: locked precision class (§3 G3).

**The model side is re-locked VERBATIM below and is untouched**: same
closed forms (§1), same grids (§2), same verdict bands, same kill scope,
same sentinel. Operator-leak disclosure, as in 1392 §3.2 and the 1225
ABORTED-UNINFORMATIVE precedent: the void v2 run told the operator the
reference band and the ill-conditioning locus — both instrument facts. No
verdict structure of the actual grid (which cells PASS) is treated as known,
and nothing in §1/§2/§1.7/§6 moved.

Route: **(A)**, per 009 section 5 and 1387. Register: **route alpha**
(minimal interpolation, ROOT-pinned), per 1389 section 3. Run precondition
(1390 §5 = 1391): **MET** as of record 1391.

## 0. What this rig decides, and what it does not

```text
DECIDES      (J1):  ceiling < delta / (2 * C_min)
             for the record-1386 factorized ceiling on the route-alpha
             4-node register.  Verdict bands PASS / MARGINAL / FAIL.

DOES NOT     the archimedean gate  0 < archimedeanTerm g.convolutionSquare
             (1389 section 6; records 1080/1081).  Never evaluated here.
DOES NOT     discharge hfit or hJ1 on the formal lane; certify RH; verify the
             visible-anchor escape from the [1371] floor; or kill route beta.
```

## 1. Locked model — VERBATIM from 1390 §1, re-locked, nothing changed

### 1.1 Nodes and value pattern

```text
nodes(rho) = healthyDetectorNodeSet rho = {0, 1/2, 1, rho}          (4 nodes)
u (xi factor,   window (-Ru, Ru)): v = (1, 1, 1, 1)
f (taper factor, window (-Rf, Rf)): y = (0, 0, 0, -1)
laplaceAt g z = laplaceAt u z * laplaceAt f z  ==>  v*y = healthyDetectorNodeTarget
```

Distinctness funded in source (`sourceNontrivialZero` trio + `rho.re <> 1/2`);
the grids keep `Re rho >= 0.55`, `Im rho > 0` by construction.

### 1.2 Hard support constraint

```text
Rg = Ru + Rf  <=  log(2) / 2
```

Violations are INADMISSIBLE (G0 instrument property), not FAIL.

### 1.3 Gram closed forms (machine-checked, record 1383)

```text
G(R)_ij = (exp((s_i + conj s_j) R) - exp((s_i + conj s_j)(-R))) / (s_i + conj s_j)
G(R)_ij = 2 R                                   when  s_i + conj s_j == 0
```

over the ordered list `(0, 1/2, 1, rho)`. The branch IS hit (`G_00 = 2R`);
dividing without the branch is INVALID-INSTRUMENT.

### 1.4 Local-mass quantities (record 1379 Lemma E; lower-bound status 1384)

```text
K_loc_f = y* G(Rf)^(-1) y        K_loc_u = v* G(Ru)^(-1) v
```

Real and strictly positive at distinct nodes (1382/1383/1384).

### 1.5 Ceiling, record-1386 factorized form (RHS, as the formal chain emits)

```text
ceiling = (2 * Ru) * ((1 + eps') * K_loc_u) * ((1 + eps) * K_loc_f)
```

### 1.6 Couplings (record 1378, symmetric window (-Rg, Rg))

```text
C_C = 8 pi sinh(d Rg)^2 + 2 delta^3 Rg^3 exp(2 d Rg)
C_D = 2 Rg delta (exp(d Rg) - 1)^2 + (4/3) delta^3 Rg^3
C_min = min(C_C, C_D)
small-d limits:  C_C -> 8 pi d^2 Rg^2 + 2 delta^3 Rg^3,
                 C_D = (4/3) delta^3 Rg^3 + O(d^2),   C_min = C_D at small d
```

### 1.7 The (J1) test, bands — UNCHANGED

```text
(J1)     ceiling < delta / (2 * C_min)
margin   = delta / 2 - C_min * ceiling
ratio    = 1 - 2 * C_min * ceiling / delta
PASS  ratio >= 1/2 ;  MARGINAL 0 < ratio < 1/2 ;  FAIL  ratio <= 0
```

## 2. Locked grids — VERBATIM from 1390 §2, nothing changed

```text
d       in {0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.45}
delta   in {0.01, 0.03, 0.1, 0.3, 0.6, 1.0}
Rf      in {0.02, 0.05, 0.08, 0.12, 0.1732}
Ru      in {0.02, 0.05, 0.08, 0.12, 0.1732}
eps, eps' in {0.01, 0.1}   (independently)
Re rho  in {0.55, 0.6, 0.75, 0.9, 0.99}
Im rho  in {14.134725, 21.022040, 25.010858, 1054.0}
reference cell: d = 0.05, delta = 0.1, Rf = Ru = 0.08,
                eps = eps' = 0.01, rho = 0.75 + 14.134725 I
```

Largest radius `log(2)/4` truncated DOWN => max `Rf+Ru = 0.3464 < log2/2`;
all 25 radius cells admissible by construction; `d*Rg <= 0.15588 < 0.53` on
the whole grid (near-line regime covers everything). Every `rho` is a
HYPOTHETICAL off-line zero.

## 3. Gates — G0/G2/G4/G5/G6 verbatim from 1390 §3; G1 and G3 REVISED

- **G0 ADMISSIBILITY** (unchanged): `Rf + Ru <= log(2)/2` and `d * Rg <=
  0.15588` at every cell; violations: INVALID-INSTRUMENT.
- **G1 NEGATIVE CONTROL, band-universal** (REVISED; a violation invalidates
  the RUN): at the reference cell, recompute with `K_loc_f -> 10 * K_loc_f`.
  Lock the identity implied by the §1.5/§1.7 formulas — the shortfall
  `s = 1 - ratio = 2 C_min ceiling / delta` is LINEAR in `K_loc_f`, so any
  faithful implementation must produce exactly `s' = 10 s`:
  (a) `ratio' < ratio` strictly;
  (b) `|s' - 10 s| <= 1e-9 * max(1, s)`;
  (c) band rank never increases (`PASS->PASS`, `MARGINAL->{MARGINAL,FAIL}`,
      `FAIL->FAIL` allowed).
  Rationale (pre-committed): this is the same wiring-bug detector 1390
  intended (a mis-wired `K_loc_f -> ceiling -> ratio` chain breaks (b) or
  (c) at any reference band), but it is SATISFIABLE-BY-CONSTRUCTION for
  every reference geometry, so it can never be dead like 1390's
  band-DROP requirement was. The v2 void proved the drop-form unsatisfiable
  at this reference; (b)/(c) are strictly weaker on band content and
  strictly stronger on formula fidelity.
- **G2 MONOTONICITY** (unchanged, pure formula calculus): at fixed `d`,
  `C_min` strictly increasing in `Rg` and in `delta`; at fixed `ceiling > 0`
  `ratio` strictly decreasing in `C_min`, and at fixed `C_min` strictly
  decreasing in `ceiling`. Violation: INVALID-INSTRUMENT. (Checked on dense
  sweeps of the locked closed forms, same construction as 1392 §2.)
- **G3 POSITIVITY + PRECISION CLASS** (REVISED): the instrument runs in
  `mpmath` at 200-bit working precision (~60 decimal digits). At EVERY
  (R, rho, pattern) of the tables, and every per-cell comparison:
  * `K_loc` via the EXACT §1.3 branch formula and an exact 4x4 solve;
    solve residual `|G x - y|_inf / max(|y|_inf, tiny) <= 1e-30`;
  * `|Im K_loc| <= 1e-30` (the model guarantees a real value);
  * `K_loc > 0` strictly (min over the 200 tables reported);
  * `ceiling > 0`, `C_min > 0`, and the final band comparison of
    `ratio` against `1/2` and `0` evaluated in that mp context (exact
    rationals). A cell within `1e-30` of a band edge is REPORTED as a tie
    (listed, band by the stated >=/>/<= rules) — with prob 0 expected, but
    the rule is total so the run cannot stall on it.
  Any violation: INVALID-INSTRUMENT (a degenerate node collision or dropped
  zero-frequency branch surfaces here — the v2 failure was a float64
  artifact, which this class removes).
- **G4 COUPLING SANITY** (unchanged): `C_min <= C_C`, `C_min <= C_D`, and
  the §1.6 small-`d` limits within 1% at `d = 1e-3` on the reference geometry
  plus the universal attainment branch `C_D < C_C` over all radius/delta
  corners (identical construction to 1392 §2 G4). Violation:
  INVALID-INSTRUMENT.
- **G5 REGIME ASSERTION** (unchanged): zero cells with `d * Rg > 0.53`.
  Violation: INVALID-INSTRUMENT.
- **G6 WINDOW BALANCE** (unchanged; informational, NO verdict weight): per
  `(Ru, rho)` at the reference `(d, delta, eps, eps')`, report the `Rf`
  minimizing `C_min * ceiling`; assert nothing (1389 flags the
  `Rf = Ru`-heuristic unreliable at `|Im rho| ~ 14`).

## 4. Outputs — verbatim from 1390 §4

Per-cell table `d, delta, Rf, Ru, Rg, K_loc_f, K_loc_u, ceiling, C_C, C_D,
C_min, ratio, band`; frontier table per `(d, Rg)` of largest PASS `delta`;
seam table per `(delta, Rg)` of largest FAIL `d`; G6 balance table; all six
gates plus the literal final line

```text
DONE gates=G0:PASS,G1:PASS,G2:PASS,G3:PASS,G4:PASS,G5:PASS
```

(or with FAIL entries naming the voided gate). Acceptance is log-based; exit
codes prove nothing (A2x).

## 5. Run precondition — MET (record 1391)

## 6. Kill scope — verbatim from 1390 §6 (nothing added, nothing removed)

A FAIL cell kills ONLY that support window, the route-alpha 4-node family,
that bridge route, and that parameter range. A PASS cell certifies nothing
beyond MODEL budget arithmetic: not RH, not the visible-anchor escape, not
`hfit`/`hJ1` in Lean, not the archimedean gate, not the healthy-data wiring.

## 7. Environment and protocol

WSL2 ext4 mirror; `/usr/bin/python3.12` with numpy 2.5.3 and mpmath 1.4.1
(the precision class of §3 G3); script
`scripts/run_1393_rig.py` executed through
`scripts/run_resource_aware_task.sh --class normal`; stdout to
`docs/proofs/1393_component5_rig_run.log`, summary JSON to
`docs/proofs/1393_component5_rig_results.json`, per-cell table to
`docs/proofs/1393_component5_rig_cells.tsv.gz`, sha256 of all three recorded
in the outcome record. No shell variables inside `wsl.exe` one-liners (the
SILENT FAKE-EMPTY law); literal paths. Law 42: after this commit, no grid,
formula, band, gate or threshold may move — a further model or instrument
change costs a NEW prereg.
