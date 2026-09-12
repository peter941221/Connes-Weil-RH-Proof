# 1376 - N0' closure archive and the N1 vertical-bridge recon

Date: 2026-09-13. Consumes [1375](1375_two_sided_tail_height_form_design.md)
(N0' formal campaign, A→E3+F), [1372](1372_phase_diagram_total_variant_attack.md)
§3 S5 / §6 (N1 definition), [008](../map/008_l2_hbridge_bone_attack_plan.md) §9.
Evidence class: READBACK for the N0' closure (all statements committed and
machine-checked); PAPER recon with one load-bearing new observation for N1.
No numerical claims. RH NOT claimed.

## 1. N0' closure: the formal state (archive)

The N0' ledger row is now FORMAL-DONE. Commits 9b69df9 + 9372492 + 15d073f +
4b6a59d + 59800f8; leaf `ConnesWeilRH.Dev.C1SelectedSquareHeightTail`
(+ paired Audit), 13 theorems, all `[propext, Classical.choice, Quot.sound]`,
zero sorryAx, byte-identity verified at every step (build logs
1375_height_tail_budget_try15 / 1375_orbit_package_try2 /
1375_unconditional_try4, each `Build completed successfully (3634 jobs)`).

The end-to-end entry point is

```
exists_smallSupport_healthyDetectorData_unconditional   (1375 s12, F3)
  premises : (rho, hoff, hright, routeNodes, windows)   — nothing else
  conclusion : ∃ N, dyadicShellIndex |rho.1.im| < N + 1 ∧
               ∃ n g, HealthyYoshidaDetectorData rho.1 g ∧
                 support g.test ⊆ Ioo ((n+1)*baseLower + lower)
                                      ((n+1)*baseUpper + upper)
```

Mechanism summary: the height-form two-sided tail removed the
`2*|rho.im| ≤ |z.im|` pin (N0'); E2 discharged the budget leaf under a
decay hypothesis on the base constant; F1/F2 restated the wrapper on RAW
node data (the correction engine's inputs are n-free, killing the apparent
constants-before-n circularity); F3 chose `N` AFTER the constructed `C_b`
was on the ground (`N := shell + k`, `k < 2^k ≤ 2^(4(N+1))`), collapsing
the decay hypothesis into a pure existence statement. The B5 exit's
premise producer — for every off-line source zero, a healthy detector with
`(n+1)`-window support and strictly negative spectral square — is now a
hypothesis-free theorem up to the B5 consumer side itself.

Honesty ledger (unchanged, binding): no rate on `N` or `n` is proved; the
constructed constants may force astronomically large windows (the
MODEL-digits lane, law 65); no negativity number beyond the strict sign;
RH NOT claimed.

## 2. N1 recon: what the vertical bridge actually is

1372 S5 states the task in MODEL form: prove for the spline family
`G = baseHat^(n+1) · corrHat` any fixed-`rho_b > 0` version of

```
|G(i t0)| ≥ e^{-d (1 + rho_b (n+1) R)} |G(d + i t0)|          (MODEL)
```

with `d = Re rho − 1/2`, `R = n + 2`. Recon verdicts:

### 2a. The pointwise form is dead; the mass form is the deliverable

S5's own text says the GAIN needs LINE MASS near `t0` on the `sigma = 0`
line (to be compared against the local zero density `eta(t0)`), not a point
value. Pointwise lower bridges on oscillatory splines are FALSE in general:
`G(d + i t)` is the Fourier transform of the DAMPED profile `g(x) e^{dx}`,
and no pointwise inequality relates Fourier values of `g` and `g e^{d·}` at
a prescribed frequency — the damping reweights the phase, not just the
modulus. Any N1 candidate of the literal MODEL shape would need a
construction-specific pinning of `baseHat(it0)`, which the interpolation
nodes do not supply (they pin values at the 4 healthy targets and kills at
zeros, all in the strip's low region).

So the deliverable theorem has the MASS shape, matching S5's consumption:

```
∫_{t0−δ}^{t0+δ} |G(i t)|² dt  ≥  |G(d + i t0)|² / B(d, δ, R) − (coupling)
```

with every constant explicit.

### 2b. Load-bearing recon result: the global bridge is linear in R

Cauchy–Schwarz in the x-coordinate gives, for EVERY member of the family
(`g` supported in `(−R, R)`, no other structure used), with the register's
Laplace convention `G(z) = ∫ g(x) e^{z x} dx`
(C20YoshidaConvolution.lean:55, character `e^{+sx}`):

```
|G(d + i t0)|² ≤ ‖g‖²_{L²} · ∫_{−R}^{R} e^{2 d x} dx = ‖g‖² · sinh(2 d R) / d
∫_ℝ |G(i t)|² dt = 2π ‖g‖²                                    (Plancherel)
⟹  |G(d + i t0)|² ≤ C_bridge(d, R) · ∫_ℝ |G(i t)|² dt,
   C_bridge(d, R) := sinh(2 d R) / (2 π d)
```

Consistency check: `C_bridge → R/π` as `d → 0`, exactly the PW_R
evaluation constant that S4 uses on the line — the two ends of the chain
agree at `d = 0`. The d-penalty is `sinh(2 d R)/(2 π d)`, LINEAR in R at
fixed small d (growing like e^{2dR}/(2πd) for large argument). Compare the
MODEL penalty at `rho_b = 1`: `e^{2 d (1 + (n+1) R)}`, QUADRATIC in R
through the `(n+1) R` factor:

| n | R | C_bridge(d, R) at d = 0.1 | MODEL penalty (rho_b=1, d = 0.1) |
|---|---|---|---|
| 1 | 3 | sinh(0.6)/(0.2π) ≈ 1.08 | e^{2·0.1·7} = e^{1.4} ≈ 4.06 |
| 4 | 6 | sinh(1.2)/(0.2π) ≈ 2.40 | e^{2·0.1·31} ≈ 493 |
| 8 | 10 | sinh(2.0)/(0.2π) ≈ 5.77 | e^{2·0.1·91} ≈ e^{18.2} ≈ 8e7 |

The bridge coefficient question ("does ANY fixed positive rho_b hold?") is
resolved in the strongest useful sense: the mass-form global bridge holds
with an explicit constant, for every family member, with no subharmonic
machinery and no construction input beyond the support width — and its
R-dependence beats the MODEL's quadratic `(n+1) R` form by orders of
magnitude at large `n`.

### 2c. The honest cost: localization couples to ‖g‖²

The gain leg needs the mass LOCALIZED near `t0` (bandwise density
comparison). Global mass does not localize for free: the off-band mass of
`G(i·)` is `‖g‖²` minus the band projection, and the construction pins
VALUES at nodes, not the norm. This is exactly where the 1371 finding
bites — the killed prefix puts the anchor in the invisible complement with
the sharp floor `‖g‖² ≥ 4/B_R(d)` — and 008 §8.5's binding constraint that
N1/N2 must be designed together. The local deliverable therefore has the
shape

```
local mass ≥ |G(d+i t0)|² / B(d, δ, R) − K_loc · (off-band coupling) · ‖g‖²
```

and the N1 paper must DERIVE the joint inequality, not assume the coupling
away. Falsifier to respect: if the coupling term always dominates, the
bridge is real only in cells where the constructed norm is controlled —
that condition becomes an explicit hypothesis of the closure theorem (a
legitimate conditional, same standing as any other constant war input).

### 2d. Attack surface list (the N1 plan)

1. N1a (paper, classical): global bridge lemma with the exact constant
   `C_bridge(d, R) = sinh(2dR)/(2πd)` — Cauchy–Schwarz + Plancherel +
   support width, with the `d → 0` limit `R/π` as the sanity anchor.
2. N1b (paper): local band bridge — kernel of the band projection
   `W_{t0,δ}` (Fejér/sinc form), exact `K_loc` reuse from N2, explicit
   off-band coupling constant; the δ-optimization against the RvM density
   band.
3. N1c (paper): the joint N1×1371-floor inequality — state and prove the
   strongest (local mass, ‖g‖²) pair compatible with the killed prefix
   under the off-line-zero assumption; this is the 008 §8.5 "designed
   together" clause made into a lemma.
4. N1d (formal leaf, after N1a): the global bridge is a small formal
   candidate — C-S, Plancherel (`MeasureTheory` internals permitting) and
   support-width bound on the existing spline family; conditional on the
   register's L² bookkeeping being exposed (the family is currently
   value-based, so the norm interface may need a small export).
5. N1e (rig): recompute the L* table with the recon penalty `e^{2dR}`;
   update 1373's locked bands per its own amendment protocol (prereg the
   amendment BEFORE digits).

### 2e. What this record does NOT claim

No bridge theorem is proved here; §2b is a two-line classical estimate,
recorded as a RECON VERDICT with its derivation, not as a formal or
paper-final result. No closure region changes. The 1373 scoreboard is not
amended by this record. RH NOT claimed.

## 3. Status board after this record

| Row | State |
|---|---|
| N0' two-sided tail + package | FORMAL DONE (F3 unconditional) |
| N1 vertical bridge | recon DONE; N1a–N1e plan above; paper beat next |
| N2 K_loc constant | unchanged (feeds N1b multiplicatively) |
| N3 density adapter | unchanged |
| N4 low-height certificate | unchanged |
| Stop word | gate Lean certificate (1358) |
