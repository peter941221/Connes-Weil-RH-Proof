# 2728 — the exact seed mass `l1Mass smoothSeed = 3` (brick 1 of the row-B pins campaign)

Verdict: BRICK GREEN.  `ConnesWeilRH.Source.C1ExplicitSmoothSeed.l1Mass_smoothSeed_eq_three
: l1Mass smoothSeed = 3`.  This is the load-bearing `h1` premise
(`l1Mass smoothSeed <= l1u` at `l1u = 3`) of the record-2725 envelope
brick `norm_cardinalSum_poweredSeed_le_endpoint_env`; the committed
`smoothSeed_l1Mass_le_four` was too weak for the lane (2725 measured
`l1u = 4` failing the wired pins 10.57x / 7.44x).

## 1. The mathematics (why the value is exactly 3)

`smoothSeedRaw x = T (x + 2) * T (2 - x)` with `T = Real.smoothTransition`
(the flat transition: `T u = 0` for `u <= 0`, `T u = 1` for `u >= 1`, and
`T (1 - u) = 1 - T u` by the glue symmetry `g u / (g u + g (1-u))`).
Support decomposition of `int_R`:

```text
x <= -2, x >= 2 : seed = 0
x in [-2,-1]    : T (2-x) = 1  -> seed = T (x+2)   -> int = int_0^1 T
x in [-1, 1]    : seed = 1                          -> int = 2
x in [ 1, 2]    : T (x+2) = 1  -> seed = T (2-x)   -> int = int_0^1 T
```

and `int_0^1 T = 1/2` from `u -> 1 - u` (the substitution fixes the
interval and turns `T` into `1 - T`, so the integral equals `1 - itself`).
Total: `1/2 + 2 + 1/2 = 3`.

## 2. The Lean brick (`ConnesWeilRH/Dev/C1SmoothSeedMassThree2728.lean`)

Eight declarations, paired audit `C1SmoothSeedMassThree2728Audit.lean`
(8 focused `#print axioms`):

```text
smoothTransition_add_one_sub : T x + T (1 - x) = 1
smoothTransition_one_sub     : T (1 - x) = 1 - T x
integral_smoothTransition_zero_one : int_0^1 T = 1/2
norm_smoothSeed_test_eq      : ||smoothSeed.test x|| = smoothSeedRaw x
smoothSeedRaw_eq_zero_of_notMem_Icc
integral_smoothSeedRaw_eq_three : int_R smoothSeedRaw = 3
l1Mass_smoothSeed_eq_three   : l1Mass smoothSeed = 3
smoothSeed_l1Mass_le_three   : l1Mass smoothSeed <= 3   (the h1 shape)
```

Proof route: pointwise norm -> nonneg real cast (`RCLike.norm_ofReal`);
`int_R = int` over `Icc (-2) 2` via `Set.indicator` + `integral_indicator`;
`Icc -> Ioc -> interval` via `integral_Icc_eq_integral_Ioc` +
`intervalIntegral.integral_of_le`; three-piece split via
`integral_add_adjacent_intervals`; each piece by
`intervalIntegral.integral_congr` + the flat-transition case splits; the
two edge pieces by the shift/reflection substitutions
(`integral_comp_add_right` at `d = 2`, `integral_comp_sub_left` at
`d = 2`).

Acceptance (Linux-native workspace, resource runner, `LEAN_NUM_THREADS=1`):
footer `Build completed successfully (3501 jobs)`, zero `error:` lines,
zero `uses sorry`, 8 axiom records all exactly
`[propext, Classical.choice, Quot.sound]`, both oleans present, zero
entry-path warnings (`build-logs/2728_mass_audit_build.log`).

## 3. Instrument lessons (build iterations)

- `#check` placed BEFORE the `open` lines produces false
  "Unknown identifier" reports (name resolution context) — checks belong
  after the opens.
- v4.30 names: `RCLike.norm_ofReal` is the generic `||(r : K)|| = |r|`
  (there is no `Complex.norm_ofReal`); `div_add_div_same` survives only
  for `ℝ≥0∞`, the field lemma is `add_div` (use `rw [← add_div]`);
  `intervalIntegral.integral_of_le` lands on `Set.Ioc`, not `Icc`.
- `rw [lemma]` is syntactic: a cast-spelling mismatch
  (`RCLike` algebraMap vs the `ℂ` coercion) defeats it; `simpa only
  [...] using` closes by definitional equality.
- A `calc` step with `rw [h]` must not be replaced by a bare
  `rw [h1, h2, h3]` chain on a goal with TWO occurrences of the rewritten
  term (both sides get rewritten, the goal stays open).

## 4. Premise accounting

`wired_hypotheses_removed = 0` at the wiring level (the wired pins remain
named hypotheses), but the record-2725 envelope instantiation now has its
`h1` premise PROVED at `l1u = 3`: the pins campaign's seed-derivative residual is
`{D_4 pin}` only; finite-cell envelope certification, domain coverage and
the infinite-frequency bound are still required to discharge the pins (record 2727), plus the 2722D-pattern carrier re-seed and
the rho-quantified duties.  No producer GO, no SourceRH, no RH claim.

Evidence:
- `ConnesWeilRH/Dev/C1SmoothSeedMassThree2728.lean`,
  `ConnesWeilRH/Dev/C1SmoothSeedMassThree2728Audit.lean`,
- `build-logs/2728_mass_audit_build.log` (green 3501 jobs, 0 error,
  0 sorry, 8/8 standard trio),
- `docs/proofs/2725_powered_seed_envelope.md`,
  `docs/proofs/2727_rung_collapse.md`.

Correction (2729): the exact mass theorem is unchanged. The D_4-only
seed-derivative residual quoted above is withdrawn for global pins;
the correction envelope requires a rung >=6 or a different tail proof.
