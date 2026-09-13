# 1386 — Component 4: Young/convolution final-owner budget and the assembly

Date: 2026-09-13.

Status: FORMAL. This closes N2beta component 4 of the 009 contract (same-owner
assembly budget). It does not prove the quantitative F1/F2 recast or any N1c
margin (component 5), a global decay rate, an orbit instantiation, or RH.

## What component 4 had to deliver

Contract 009 item 4 requires that the Young bound control the FINAL assembled
`CompactLogTest`, not an unrelated auxiliary interpolant. Concretely: the
taper owner `f` of record 1385 (values `y`, cost `(1 + ε) · K_loc`) must be
composable with the xi-side correction owner `u` — through the repo's
`CompactLogTest.convolution` — so that the product is ONE owner carrying the
multiplied values, living in the summed window, with a budget chain that
reaches `K_loc` end to end.

## Formal owner and theorem anatomy

One leaf, paired with one audit.

`ConnesWeilRH/Dev/C1WindowTaperAssembly.lean` (9 public declarations):

- `compactLogL1`: the L1 accessor `f ↦ ∫ x, ‖f.test x‖` on the same-owner
  class, plus the nonnegativity facts
  `compactLogL2sq_nonneg` / `compactLogL1_nonneg`.
- `integral_weighted_cauchySchwarz`: the full-measure weighted discriminant
  Cauchy–Schwarz `(∫ W b)² ≤ (∫ W)(∫ W b²)` for a nonnegative weight `W`
  and arbitrary `b`. The proof mirrors the record-1381 window argument with
  `∫ x in a..b` replaced by full integrals: expanding
  `∫ W (b + s)² ≥ 0` through `integral_add` / `integral_smul` gives a
  quadratic in `s`; the leading-coefficient case `∫ W = 0` makes the
  quadratic affine-nonnegative so the cross term vanishes; the positive
  case is read at the vertex `s = -(∫ W b)/(∫ W)`. Note the honest
  hypothesis set: `b ≥ 0` is NOT needed and is not assumed.
- `young_kernel_sq_le`: the kernel Young inequality
  `∫ x, ‖∫ t, F t * G (x - t)‖² ≤ (∫ ‖F‖)² * ∫ ‖G‖²` for continuous
  compactly supported `F G : ℝ → ℂ`, in raw pointwise form. Structure:
  1. pointwise at `x`: triangle bound `‖∫ F · G(x−·)‖ ≤ ∫ ‖F‖‖G(x−·)‖`
     followed by the weighted Cauchy–Schwarz at the weight `t ↦ ‖F t‖`;
  2. the line bound: `integral_mono` against the majorant
     `x ↦ (∫ ‖F‖) · ∫ t, ‖F t‖ ‖G (x - t)‖²`; the inner integral is the
     REAL convolution of `‖F‖` against `‖G‖²`, so continuity comes from
     `HasCompactSupport.contDiff_convolution_right` at `n = 0`, compact
     support from `HasCompactSupport.convolution`, integrability from
     `Continuous.integrable_of_hasCompactSupport`;
  3. boundedness of `‖G‖`: read at the supremum `⨆ i, ‖G i‖` through
     `Continuous.bddAbove_range_of_hasCompactSupport` applied to the
     REAL-valued `x ↦ ‖G x‖`, so no `tsupport` window extraction enters
     the chain (the 1381 lesson);
  4. the Fubini swap `∫ x ∫ t = (∫ ‖F‖)(∫ ‖G‖²)` is Mathlib's
     `integral_convolution` — the packaged product-measure argument.
- `compactLogL1_sq_le_of_window`: `(∫ ‖u‖)² ≤ (d − c) · ∫ ‖u‖²` for a test
  supported in `Ioc c d` — the record-1381 window Cauchy–Schwarz evaluated
  at `v = 1`, intervalized through
  `intervalIntegral.integral_eq_integral_of_support_subset`.
- `compactLogL2sq_convolution_le`: the same-owner budget law
  `compactLogL2sq (f.convolution g) ≤ compactLogL1 f ^ 2 * compactLogL2sq g`
  (the owner's test-field unfolding is definitional, so the transfer is a
  `rfl` step).
- `compactLogL2sq_convolution_le_of_window`: the windowed law, trading the
  L1 factor for width via the previous two.
- `exists_assembledOwner_cost_le`: the assembly deliverable. For any window
  `Ioo c d`, any `u` supported in it, distinct nodes `nodes : ι → ℂ`,
  target values `y`, and `ε > 0`, there is ONE owner `g = u.convolution f`
  with `f` the record-1385 taper owner, satisfying
  1. `support g.test ⊆ Ioo (c + a) (d + b)` (`convolution_support_subset_add_Ioo`),
  2. `laplaceAt g (nodes i) = laplaceAt u (nodes i) * y i`
     (`laplaceAt_convolution` plus the 1385 value lemma),
  3. `compactLogL2sq g ≤ (d − c) * compactLogL2sq u * ((1 + ε) * K_loc)`
     for the record-1379 `K_loc = y* G⁻¹ y` (windowed Young law + the 1385
     wrapper cost, glued by `mul_le_mul_of_nonneg_left` with the explicit
     nonnegativity of `(d − c) · compactLogL2sq u`).

## Why the proof shape is right (first principles)

The contract's "same-owner" clause is what forces convolution: the only
operation that composes two supported tests into one owner while
MULTIPLYING their `laplaceAt` values is the repo's `CompactLogTest`
convolution (values) plus the support-addition law (window). Once
multiplicativity of values is given, the whole budget question becomes the
L1→L2 Young inequality — and the classical
`‖F ⋆ G‖₂ ≤ ‖F‖₁‖G‖₂` proof needs nothing beyond: pointwise weighted
Cauchy–Schwarz (proved from scratch, no `Lp`/`MemLp` API per the 1381 rule),
one packaged Fubini (`integral_convolution`), and the fact that the
continuous-compact-support class is closed under convolution
(`contDiff_convolution_right` / `HasCompactSupport.convolution`). The
endpoint is not the textbook constant: the budget keeps the FACTORIZED form
`(d − c) · compactLogL2sq u · ((1 + ε) · K_loc)` so component 5 can
multiply the xi-side factor against the 1379 joint-feasibility digits
without ever re-deriving them. The `L¹ ≤ √width · L²` trade is the only
place the window enters, and it is exactly the 1381 brick at `v = 1`.

## Evidence

Focused WSL runner logs: `009_taperassembly_probe1.log` through
`009_taperassembly_probe6.log` and the acceptance
`009_taperassembly_accept.log` (repository build-log naming; kept in the
Linux-side verification environment). Error trajectory: 21 → 5 → 4 → 1 →
0 across the probe iterations (probe 1/2 shared the same run: the leaf's
first pass reported 21). Recon name probes `009_reconprobe6..8.log`
settled the v4.30 API facts (see the AGENTS 7b ledger).

Acceptance build (both targets named explicitly, law of 1384):
`lake build ConnesWeilRH.Dev.C1WindowTaperAssembly
ConnesWeilRH.Dev.C1WindowTaperAssemblyAudit` — EXIT=0,
`Build completed successfully (3552 jobs)`, zero `error:` lines, zero
`sorryAx`, no Dev-file warnings (only the three accepted lake
"has local changes" environment notes), and all 9 audit prints exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Boundary and next consumer

FORMAL lane only: no rate claim, no numeric margin, no orbit instantiation,
no RH-adjacent conclusion. The leaf is the budget COMPOSER: it hands
component 5 (quantitative F1/F2 recast) a theorem that already presents the
factorized `(d − c) · compactLogL2sq u · (1 + ε) · K_loc` budget at the
N1c joint-feasibility interface of 1379 — `(J1) x* > 2 C_min / δ` becomes
checkable once one assembles a healthy detector whose `K_loc` and norm
factors are supplied by the 1375/1385 producers and composed here.
Map sync: 009 §4 component-4 flip, docs/map/README item 18.
