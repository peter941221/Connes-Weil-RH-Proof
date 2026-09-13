# 1388 — Preregistration: N2beta component 5 discharge rig (route A, MODEL evidence)

Date: 2026-09-13. Law 42: this file is committed BEFORE any digit. Law 65:
every number a future run produces under this prereg is MODEL. Instrument
class: VERDICT-capable inside a locked scope — unlike the record-1373 mapping
rig, (J1) is a theorem-shaped inequality whose inputs are explicit closed
forms, so a FAIL has real kill-power. That kill-power is scoped exactly as
[009](../map/009_n2beta_core_bone_completion_contract.md) section 3 permits and
no wider (section 5 below).

Route: **(A)**, per the ruling recorded in 009 section 5 and
[1387](1387_component5_shape_consumer.md) — visible-anchor family with an
explicit norm budget, so the [1371] invisible-anchor floor does not bind, (J2)
drops, and (J1) alone decides.

## 0. The named gap this prereg commits to closing first

The record-1387 shape layer leaves two premises open: `hfit` (the construction
fits under a ceiling) and `hJ1` (the ceiling obeys (J1)). A source readback
shows `hfit` has an **unfunded input**.

The xi-side owner `u` in the record-1386 assembly is produced by the correction
engine, whose only quantitative output is a vertical decay bound
(`CC20YoshidaConvolution.lean:323-333`):

```lean
theorem exists_residualWindow_correction_with_quadratic_decay
    (nodes : Finset ℂ) {lower upper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → ℂ) :
    ∃ correction : CompactLogTest, ∃ C : ℝ,
      Function.support correction.test ⊆ Set.Ioo lower upper ∧
      (∀ z : FiniteMellinNode nodes, laplaceAt correction z.1 = y z) ∧
      0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖laplaceAt correction ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C
```

That is a pointwise bound in the Laplace coordinate, not an L2 bound on
`correction.test`. Corroborating sweep: the accessor `compactLogL2sq` occurs in
98 places across 13 files, **all** of them the record-1381..1387 N2beta leaves;
it occurs nowhere in the orbit package (`CC20YoshidaFullProduct`,
`CC20YoshidaConvolution`, `C1SelectedSquareHeightTail`,
`C1HealthyYoshidaDetector`). So no existing orbit-package owner carries an L2
bound. This is the record-1380 section 1 gap restated at component-5 level.

Two resolutions were considered:

```text
R1  Make u ITSELF a record-1385 taper owner for the orbit's node/value data.
    Then compactLogL2sq u <= (1 + eps') * K_loc_orbit is machine-checked by
    the same wrapper that funds f, and (FIT) closes with ZERO new analysis:
    ceiling <= (q - p) * (1 + eps') * K_loc_orbit * (1 + eps) * K_loc.

R2  Add an L2 producer to the correction engine, e.g. by Plancherel from the
    vertical decay bound.  Rejected: the decay bound controls
    |laplaceAt| only like t^(-2) at INFINITY and says nothing near t = 0,
    so the Plancherel integral is not bounded by it.  A low-frequency bound
    would be new analysis of exactly the kind this ladder avoids.
```

**Commitment: R1.** Consequence for the value structure: with `u` a taper owner
realizing the orbit pattern, the assembled owner `g = u.convolution f` has
`laplaceAt g (nodes i) = laplaceAt u (nodes i) * y i`, so kill nodes get
`0 * y i = 0` (vanishing) and target nodes get `1 * y i = y i` (values), which
is exactly the pair of record-1387 hooks. Open wiring risk, stated honestly:
`u` must additionally land in `C1.healthyCC20TestSpace` and preserve the F3
positivity field, and the register kill set `cc20TripleFiniteVanishingSet` is
FIXED, so the node family must contain it rather than be chosen freely.

## 1. Locked model (a future script must implement EXACTLY these formulas)

Fixed inputs per cell: `d` (= `Re s_v`, the vertical point's real part),
`delta` (band half-width), `Rf` (Gram/taper window radius), `Ru` (xi-side
window radius), `eps`, `eps'`, and `rho` (the hypothetical off-line zero).

Design lock (makes every coupling explicit): both factor windows are SYMMETRIC,
`f` on `(-Rf, Rf)` and `u` on `(-Ru, Ru)`, so the assembled owner lives on the
symmetric summed window `(-Rg, Rg)` with

```text
Rg = Ru + Rf
```

Node family and value pattern are NOT free parameters. They are locked to the
register's own definitions (`CC20YoshidaFullProduct.lean:52-61`):

```text
nodes(rho) = sourceFunctionalEquationOrbit rho = {rho, 1 - conj rho, conj rho, 1 - rho}
y(rho)     = negativeSourceOrbitValue rho:
               rho            |-> 1
               1 - conj rho   |-> -1
               every other    |-> 0
```

a `Finset` records orbit collisions honestly, so a real orbit degenerates
rather than being assigned incompatible values.

Gram matrix (closed forms are machine-checked, record 1383):

```text
G_ij = (exp((s_i + conj s_j) * b) - exp((s_i + conj s_j) * a)) / (s_i + conj s_j)
                                                     if s_i + conj s_j != 0
G_ij = b - a                                         if s_i + conj s_j == 0
```

evaluated at `a = -Rf`, `b = Rf` for the taper factor and at `a = -Ru`,
`b = Ru` for the xi-side factor.

Local-mass quantities (record 1379 Lemma E):

```text
K_loc        = y* G(Rf)^(-1) y          (taper factor, N1c value pattern)
K_loc_orbit  = v* G(Ru)^(-1) v          (xi-side factor, register orbit pattern v)
```

Ceiling and norm budget, in the factorized form record 1386 emits:

```text
||f||_2^2 <= (1 + eps)  * K_loc                       [record 1385, FORMAL]
||u||_2^2 <= (1 + eps') * K_loc_orbit                 [R1 commitment]
ceiling     = (2 * Ru) * ||u||_2^2 * (1 + eps) * K_loc
            <= (2 * Ru) * (1 + eps') * K_loc_orbit * (1 + eps) * K_loc
```

(`2 * Ru` is the record-1386 width factor `q - p` of the xi-side window, from
the `L1 <= sqrt(width) * L2` trade at the constant one.)

Couplings, exact symmetric-window forms of record 1378 sections 2-3 on
`(-Rg, Rg)`:

```text
C_C = 8 * pi * sinh(d * Rg)^2 + 2 * delta^3 * Rg^3 * exp(2 * d * Rg)
C_D = 2 * Rg * delta * (exp(d * Rg) - 1)^2 + (4 / 3) * delta^3 * Rg^3
C_min = min(C_C, C_D)
```

Cross-check lock (small-`d` limits against record 1378's stated asymptotics):
`C_C -> 8 * pi * d^2 * Rg^2 + 2 * delta^3 * Rg^3` and `C_D -> 0` like `d^2`,
so `C_min` is attained by `C_D` at small `d`. Any implementation disagreeing
with these limits is INVALID-INSTRUMENT.

The (J1) test and the delivered margin (record 1379 section 3, record 1387
`margin_pos_of_cost_le_ceiling`):

```text
(J1)     ceiling < delta / (2 * C_min)
margin   = delta / 2 - C_min * ceiling
ratio    = margin / (delta / 2) = 1 - 2 * C_min * ceiling / delta
```

Verdict bands (LOCKED): **PASS** if `ratio >= 1/2`; **MARGINAL** if
`0 < ratio < 1/2`; **FAIL** if `ratio <= 0`. Rationale, pre-committed: PASS
means the coupling eats less than half the forced signal `(delta/2) * 1`, which
is the weakest band that still leaves the bridge quantitatively meaningful
rather than merely positive.

Interpretation lock: a PASS is a MODEL statement about the budget arithmetic.
It does NOT verify the visible-anchor escape from the [1371] floor (that is a
construction property, not a digit), does NOT discharge `hfit` or `hJ1` in Lean,
and carries no RH inference in either direction.

## 2. Locked grids and bands

- `d` in {0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.45}
- `delta` in {0.01, 0.03, 0.1, 0.3, 0.6, 1.0}
- `Rf` in {0.05, 0.1, 0.25, 0.5, 1.0}
- `Ru` in {0.05, 0.1, 0.25, 0.5, 1.0}
- `eps`, `eps'` in {0.01, 0.1} (both factors, independently)
- `Re rho` in {0.55, 0.6, 0.75, 0.9, 0.99} with `Im rho` in
  {14.134725, 21.022040, 25.010858, 1054.0} (the first three are the classical
  low zeros used as reference geometry; the fourth is a high-height control).
  Every `rho` is treated as a HYPOTHETICAL off-line zero: no claim about actual
  zeta zeros is made or needed.

Reference cell (for controls): `d = 0.05`, `delta = 0.1`, `Rf = Ru = 0.25`,
`eps = eps' = 0.01`, `rho = 0.75 + 14.134725 * I`.

Regime guard (LOCKED, from record 1378's map): cells with `d * Rg > 0.53`
are reported but flagged OUT-OF-REGIME; they carry no verdict weight, because
the near-line band is where the bridge was shown informative.

## 3. Gates (instrument validity; a failed gate VOIDS the run, not the route)

- **G1 NEGATIVE CONTROL** (inflated local mass): recompute the reference cell
  with `K_loc` multiplied by 10. The band must DROP (PASS -> MARGINAL/FAIL or
  MARGINAL -> FAIL). If not: INVALID-INSTRUMENT.
- **G2 RADIUS MONOTONICITY**: at fixed `(d, delta, eps, eps', rho)`, `ratio` is
  strictly decreasing in `Rg`. Checked over the full `Rf x Ru` grid. Any
  violation: INVALID-INSTRUMENT.
- **G3 COUPLING SANITY**: `C_min <= C_C` and `C_min <= C_D` at every cell, and
  the small-`d` limits of section 1 hold to within 1% at `d = 1e-3`. Any
  violation: INVALID-INSTRUMENT.
- **G4 (informational, no verdict weight)**: report the fraction of cells where
  `C_C < C_D`, and the fraction of PASS cells that are OUT-OF-REGIME.

## 4. Outputs

- Per-cell table: `d, delta, Rf, Ru, Rg, K_loc, K_loc_orbit, ceiling, C_C,
  C_D, C_min, ratio, band, regime flag`.
- Frontier table: per `(d, Rg)`, the LARGEST `delta` achieving PASS, or NONE.
- Seam table: per `(delta, Rg)`, the LARGEST `d` with FAIL, or NONE.
- All four gates plus a DONE sentinel at log end. Acceptance is log-based: the
  verdict parser requires the literal final line
  `DONE gates=G1:PASS,G2:PASS,G3:PASS` (or with FAIL entries naming the voided
  gate). Exit codes prove nothing (A2x rule).

## 5. Kill scope (LOCKED, per 009 section 3)

A FAIL cell kills ONLY: that support window, that node family, that bridge
route (C or D, whichever attained `C_min`), and that parameter range. It does
NOT kill B5, healthy `CompactLog`, the record-1385/1386 producers, or any
larger detector class — none of those is quantified over here.

A PASS cell does NOT: certify RH; verify the visible-anchor escape from the
[1371] floor; discharge `hfit` or `hJ1` on the formal lane; or substitute for
the healthy-data wiring of 009 section 5 item 4.

## 6. Environment and protocol

WSL2 mirror (ext4). Sync the script from the Windows repo, run it through
`scripts/run_resource_aware_task.sh` with absolute interpreter paths, capture
stdout to `docs/proofs/1388_component5_rig_run.log` and results to
`docs/proofs/1388_component5_rig_results.json`. No shell variables inside
`wsl.exe` one-liners; spell the literal path in every command of a compound.
Read the log back and require the DONE line before writing the outcome record.
No post-hoc rescoping of grids, bands, formulas, or verdict thresholds
(law 42); any model revision requires a NEW record and a NEW prereg.

## 7. Run precondition (NOT satisfied at commit time)

This prereg gates a run; it does not authorize one. A run may only start after
the R1 leaf exists and is green: a `CompactLogTest` owner built by the
record-1385 taper wrapper on the register's orbit node/value pattern, carrying
`compactLogL2sq u <= (1 + eps') * K_loc_orbit`, together with the
`C1.healthyCC20TestSpace` membership evidence. Until then the formulas above
have no funded `||u||_2^2` and any digit would be decoration.
