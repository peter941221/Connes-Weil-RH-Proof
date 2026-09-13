# 1390 — Preregistration v2: N2beta component 5 discharge rig (route A, route-alpha register, MODEL evidence)

Date: 2026-09-13. Law 42: committed BEFORE any digit. Law 65: every number a
future run produces under this prereg is MODEL.

**This file supersedes [1388](1388_component5_route_A_prereg.md)**, which is now
marked SUPERSEDED and must not be run. Reason, with source evidence, in
[1389](1389_component5_recon_route_alpha_collapse.md): 1388 locked the orbit
package's 7-node family whereas the route-alpha register uses 4 nodes, and 1388
locked a radius grid of which **19 of 25 cells violate** route alpha's hard
support constraint `Ru + Rf <= log(2)/2`. Per the record-1373 protocol a model
revision requires a NEW record and a NEW prereg rather than an edit, so the
grids below are re-locked from scratch.

Instrument class: VERDICT-capable inside a locked scope. (J1) is a
theorem-shaped inequality whose inputs are explicit closed forms, so a FAIL has
real kill-power, scoped exactly as
[009](../map/009_n2beta_core_bone_completion_contract.md) section 3 permits and
no wider (section 6).

Route: **(A)**, per 009 section 5 and
[1387](1387_component5_shape_consumer.md). Register: **route alpha**
(minimal interpolation, ROOT-pinned), per 1389 section 3.

## 0. What this rig decides, and what it does not

```text
DECIDES      (J1):  ceiling < delta / (2 * C_min)
             for the record-1386 factorized ceiling on the route-alpha
             4-node register.  Verdict bands PASS / MARGINAL / FAIL.

DOES NOT     the archimedean gate  0 < archimedeanTerm g.convolutionSquare
             (1389 section 6).  That gate is a SIGN, not a magnitude; it is a
             pre-existing open item from records 1080/1081 and this rig never
             evaluates it.  A PASS here produces NO healthy detector data.

DOES NOT     discharge hfit or hJ1 on the formal lane; certify RH; verify the
             visible-anchor escape from the [1371] floor; or kill route beta.
```

## 1. Locked model (a future script must implement EXACTLY these formulas)

### 1.1 Node family and value pattern (route-alpha register)

Not free parameters. Locked to
`C1HealthyYoshidaMinimalInterpolation.lean:27-35`:

```text
nodes(rho) = healthyDetectorNodeSet rho = {0, 1/2, 1, rho}     (4 nodes)
```

The value pattern is SPLIT across the two convolution factors so that the
record-1387 multiplicative hook reproduces `healthyDetectorNodeTarget` exactly.
With `g = u.convolution f` and `laplaceAt g z = laplaceAt u z * laplaceAt f z`:

```text
u (xi-side factor, window (-Ru, Ru)) realizes   v = (1,  1,  1,  1)
f (taper  factor, window (-Rf, Rf)) realizes   y = (0,  0,  0, -1)
                                          ==>  v*y = (0, 0, 0, -1)
```

which is `healthyDetectorNodeTarget rho` node-by-node
(`if z.1 = rho then -1 else 0`), hence `HealthyMinimalLaplaceRealizes rho g`
with the normalization `laplaceAt g rho = -1`.

Rationale for the split, pre-committed: `u` is the factor whose L2 norm is
traded against its window width by the record-1386 L1 step, so it carries the
simple all-ones pattern; the concentrated target sits on `f`, whose cost enters
the ceiling only through `(1 + eps) * K_loc_f`.

Distinctness: `rho` is required distinct from `0`, `1/2`, `1`. Funded in source
by `source_nontrivial_zero_ne_zero`, `_ne_half`, `_ne_one` from
`sourceNontrivialZero rho` and `rho.re ≠ 1/2`; the grids in section 2 satisfy
both by construction (`Re rho >= 0.55`, `Im rho > 0`).

### 1.2 Hard support constraint

From `convolutionSquare_support_logTwo_of_rootSupport_logTwoHalf`
(`C1HealthyDetectorPinning.lean:42-47`) and the record-1386 summed window:

```text
Rg = Ru + Rf  <=  log(2) / 2
```

Any cell violating this is INADMISSIBLE and is rejected by gate G0, not
reported as a FAIL. Admissibility is a property of the instrument, not of the
route.

### 1.3 Gram matrices (closed forms machine-checked, record 1383)

```text
G(R)_ij = (exp((s_i + conj s_j) * R) - exp((s_i + conj s_j) * (-R))) / (s_i + conj s_j)
                                                     if s_i + conj s_j != 0
G(R)_ij = 2 * R                                      if s_i + conj s_j == 0
```

over the ordered 4-node list `(0, 1/2, 1, rho)`. Note the zero-frequency branch
is actually hit: `s_0 + conj s_0 = 0 + 0 = 0`, so `G_00 = 2R` exactly. An
implementation that divides by `s_i + conj s_j` without the branch is
INVALID-INSTRUMENT.

### 1.4 Local-mass quantities (record 1379 Lemma E; lower-bound status record 1384)

```text
K_loc_f = y* G(Rf)^(-1) y        (taper factor, concentrated target)
K_loc_u = v* G(Ru)^(-1) v        (xi-side factor, all-ones pattern)
```

Both are real and nonnegative by the record-1382/1383 quadratic-form law, and
strictly positive here because `y != 0`, `v != 0`, and the nodes are distinct
(record 1384 invertibility). Gate G3 checks this numerically.

### 1.5 Ceiling, in the factorized form record 1386 emits

```text
||f||_2^2 <= (1 + eps)  * K_loc_f        [record 1385, FORMAL]
||u||_2^2 <= (1 + eps') * K_loc_u        [R1 commitment, 1388 section 0]
ceiling    = (2 * Ru) * ||u||_2^2 * (1 + eps) * K_loc_f
           <= (2 * Ru) * (1 + eps') * K_loc_u * (1 + eps) * K_loc_f
```

`2 * Ru` is the record-1386 width factor `d - c` of the xi-side window, from the
`L1 <= sqrt(width) * L2` trade at the constant one. The script must use the
right-hand side, since that is the expression the formal chain actually emits.

### 1.6 Couplings (record 1378 sections 2-3, exact symmetric-window forms on `(-Rg, Rg)`)

```text
C_C = 8 * pi * sinh(d * Rg)^2 + 2 * delta^3 * Rg^3 * exp(2 * d * Rg)
C_D = 2 * Rg * delta * (exp(d * Rg) - 1)^2 + (4 / 3) * delta^3 * Rg^3
C_min = min(C_C, C_D)
```

Cross-check lock (small-`d` limits against record 1378's stated asymptotics):
`C_C -> 8 * pi * d^2 * Rg^2 + 2 * delta^3 * Rg^3` and `C_D -> 0` like `d^2`, so
`C_min` is attained by `C_D` at small `d`. Any implementation disagreeing with
these limits is INVALID-INSTRUMENT.

### 1.7 The (J1) test and the delivered margin

Record 1379 section 3; record 1387 `margin_pos_of_cost_le_ceiling`:

```text
(J1)     ceiling < delta / (2 * C_min)
margin   = delta / 2 - C_min * ceiling
ratio    = margin / (delta / 2) = 1 - 2 * C_min * ceiling / delta
```

Verdict bands (LOCKED, unchanged from 1388): **PASS** if `ratio >= 1/2`;
**MARGINAL** if `0 < ratio < 1/2`; **FAIL** if `ratio <= 0`. Rationale,
pre-committed: PASS means the coupling eats less than half the forced signal
`(delta/2) * 1`, the weakest band that still leaves the bridge quantitatively
meaningful rather than merely positive.

Interpretation lock: a PASS is a MODEL statement about budget arithmetic on the
route-alpha register. It does not verify the visible-anchor escape from the
[1371] floor (a construction property, not a digit), does not discharge `hfit`
or `hJ1` in Lean, does not produce `HealthyYoshidaDetectorData`, and carries no
RH inference in either direction.

## 2. Locked grids

```text
d       in {0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.45}
delta   in {0.01, 0.03, 0.1, 0.3, 0.6, 1.0}
Rf      in {0.02, 0.05, 0.08, 0.12, 0.1732}
Ru      in {0.02, 0.05, 0.08, 0.12, 0.1732}
eps, eps' in {0.01, 0.1}   (independently)
Re rho  in {0.55, 0.6, 0.75, 0.9, 0.99}
Im rho  in {14.134725, 21.022040, 25.010858, 1054.0}
```

Radius-grid derivation (locked, so the choice is auditable rather than
convenient): the largest radius is `log(2)/4 = 0.173286...`, truncated DOWN to
`0.1732` so that the worst cell satisfies

```text
Rf + Ru = 2 * 0.1732 = 0.3464  <  log(2)/2 = 0.346574...
```

Hence **all 25 radius cells are admissible by construction** and G0 is a
self-check on the implementation, not a filter on the grid. The smallest radius
`0.02` gives a worst-case ratio `Rg/min(Rf,Ru) = 9.65`, so the grid spans nearly
a decade of window imbalance.

The three low `Im rho` values are the classical low zeros used as reference
geometry; `1054.0` is a high-height control. Every `rho` is a HYPOTHETICAL
off-line zero: no claim about actual zeta zeros is made or needed.

Reference cell (for controls): `d = 0.05`, `delta = 0.1`, `Rf = Ru = 0.08`,
`eps = eps' = 0.01`, `rho = 0.75 + 14.134725 * I`. Admissible: `Rg = 0.16`.

Regime note (replaces 1388's OUT-OF-REGIME flag): since `d <= 0.45` and
`Rg <= 0.3464`, every cell satisfies `d * Rg <= 0.15588 < 0.53`, so the
near-line regime of record 1378's map covers the **entire** grid. There are no
out-of-regime cells to discount. This is asserted by gate G5.

## 3. Gates (instrument validity; a failed gate VOIDS the run, not the route)

- **G0 ADMISSIBILITY**: `Rf + Ru <= log(2)/2` at every cell, and `d * Rg <=
  0.15588` is never exceeded. Any violation: INVALID-INSTRUMENT.
- **G1 NEGATIVE CONTROL** (inflated local mass): recompute the reference cell
  with `K_loc_f` multiplied by 10. The band must DROP (PASS -> MARGINAL/FAIL or
  MARGINAL -> FAIL). If not: INVALID-INSTRUMENT.
- **G2 MONOTONICITY** (pure formula calculus, no heuristic): at fixed `d`,
  `C_min` is strictly increasing in `Rg` and strictly increasing in `delta`;
  and at fixed `ceiling > 0`, `ratio` is strictly decreasing in `C_min`, and at
  fixed `C_min`, strictly decreasing in `ceiling`. Any violation:
  INVALID-INSTRUMENT.
- **G3 POSITIVITY**: `K_loc_f > 0`, `K_loc_u > 0`, `ceiling > 0`, `C_min > 0`,
  and `G(Rf)`, `G(Ru)` both invertible at every cell. A degenerate node
  collision or a silently dropped zero-frequency branch surfaces here. Any
  violation: INVALID-INSTRUMENT.
- **G4 COUPLING SANITY**: `C_min <= C_C` and `C_min <= C_D` at every cell, and
  the section-1.6 small-`d` limits hold to within 1% at `d = 1e-3`. Any
  violation: INVALID-INSTRUMENT.
- **G5 REGIME ASSERTION**: zero cells carry `d * Rg > 0.53`. Any such cell:
  INVALID-INSTRUMENT (it would mean the grid of section 2 was not implemented).
- **G6 WINDOW BALANCE (informational, NO verdict weight)**: report, per
  `(Ru, d, delta, eps, eps', rho)`, the `Rf` minimizing `C_min * ceiling`.
  Record 1389 section 5 predicts a minimum near `Rf = Ru` from the
  low-frequency heuristic `K_loc ~ ||pattern||^2 / (2R)`; that heuristic is
  explicitly flagged there as unreliable at `|Im rho| ~ 14`, so this gate
  reports the empirical location and asserts nothing.

## 4. Outputs

- Per-cell table: `d, delta, Rf, Ru, Rg, K_loc_f, K_loc_u, ceiling, C_C, C_D,
  C_min, ratio, band`.
- Frontier table: per `(d, Rg)`, the LARGEST `delta` achieving PASS, or NONE.
- Seam table: per `(delta, Rg)`, the LARGEST `d` with FAIL, or NONE.
- Balance table (G6): per `(Ru, rho)`, the minimizing `Rf` at the reference
  `(d, delta, eps, eps')`.
- All six gates plus a DONE sentinel at log end. Acceptance is log-based: the
  verdict parser requires the literal final line
  `DONE gates=G0:PASS,G1:PASS,G2:PASS,G3:PASS,G4:PASS,G5:PASS`
  (or with FAIL entries naming the voided gate). Exit codes prove nothing
  (A2x rule).

## 5. Run precondition (NOT satisfied at commit time)

This prereg gates a run; it does not authorize one. A run may start only after
the R1 leaf exists and is green — a `CompactLogTest` owner `g = u.convolution f`
with `u`, `f` built by the record-1385 taper wrapper on the section-1.1
patterns, carrying items (a)-(d) of 1389 section 7:

```text
(a) the two node/value realizations               (record 1385 wrapper)
(b) laplaceAt g = (0, 0, 0, -1)                   (record 1387 value hooks)
(c) support g.test subset Icc (-(Ru+Rf)) (Ru+Rf), with Ru+Rf <= log(2)/2
(d) compactLogL2sq g <= ceiling                   (record 1386 assembly)
```

Until then the formulas above have no funded `||u||_2^2` and any digit would be
decoration. Note that item (f) of 1389 section 7 — the archimedean gate — is
**not** a precondition for running this rig, because the rig does not evaluate
it; it is a precondition for the healthy-data wiring of 009 section 5 item 4,
and it remains open independently of every verdict below.

## 6. Kill scope (LOCKED, per 009 section 3)

A FAIL cell kills ONLY: that support window, the route-alpha 4-node family,
that bridge route (C or D, whichever attained `C_min`), and that parameter
range. It does NOT kill B5, healthy `CompactLog`, the record-1385/1386
producers, route beta's orbit register, the archimedean gate, or any larger
detector class — none of those is quantified over here.

A PASS cell does NOT: certify RH; verify the visible-anchor escape from the
[1371] floor; discharge `hfit` or `hJ1` on the formal lane; close the
archimedean gate; or substitute for the healthy-data wiring of 009 section 5
item 4.

## 7. Environment and protocol

WSL2 mirror (ext4). Sync the script from the Windows repo, run it through
`scripts/run_resource_aware_task.sh` with absolute interpreter paths, capture
stdout to `docs/proofs/1390_component5_rig_run.log` and results to
`docs/proofs/1390_component5_rig_results.json`. No shell variables inside
`wsl.exe` one-liners; spell the literal path in every command of a compound
(the SILENT FAKE-EMPTY law). Read the log back and require the DONE line before
writing the outcome record. No post-hoc rescoping of grids, bands, formulas, or
verdict thresholds (law 42); any model revision requires a NEW record and a NEW
prereg.
