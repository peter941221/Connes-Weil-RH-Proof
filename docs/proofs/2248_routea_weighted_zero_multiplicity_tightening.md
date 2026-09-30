# 2248 — Lean multiplicity-constant tightening: absorption 192 -> 72

Date: 2026-09-30

Normalization correction in record 2274: the absorption proof 192 -> 72
remains valid, but the quoted multiplicity decimals below use the
standard xi-at-two value pi/6. They are conservative proxies, not exact
evaluations of the project's doubled-xi constant. Lean proves project
xi(2) = pi/3 and the current constant <= 128.65. The historical numeric
tables remain unchanged; record 2274 supplies the formal comparison.

Consumer: `spectralMultiplicityConstant` feeds the Lean high-shell tail
`4 * mult * B_upper` of the weighted-zero-measure C3' producer gate
(records 2240, 2243).

Verdict: **landed in Lean, full library builds**. The flat rung constant
`192 * 3^n` of the dyadic absorption was three times its exact supremum;
it is now `72`, the multiplicity proxy drops
`301.83032993648527 -> 128.70692502980964` (`2.3450978248962033x`), and
the high-shell tail reprices `11477128602.720102 -> 4894093747.764274`
(`tail/margin 0.006850392090059914 -> 0.0029211540846331738`).

## The sharp lemma

`ConnesWeilRH/Dev/C1SpectralSummability.lean`:

```lean
theorem two_mul_add_four_add_rlogr_le_three_pow (n : Nat) :
    2 * ((n : Real) + 4) + ((n : Real) + 4) * (2 : Real) ^ (n + 4) <=
      72 * (3 : Real) ^ n
```

`72` is the exact supremum of the ratio (attained at `n = 0`:
`2*4 + 4*16 = 72`); the geometric term alone is tight at `64` on the same
rung, and the linear term `2 (n+4)` is absorbed with the same
three-per-step factor. The old reading `192 = 3 * 64` charged the linear
term a second full `64`; the sharp lemma is the direct induction with
`LHS(n+1) <= 3 * LHS(n)`.

## Constant chain (all four sites moved 192 -> 72)

```text
norm_completedRiemannXi_le_exp_of_halfplane_dyadic     192 -> 72
norm_completedRiemannXi_le_exp_on_dyadic_jensen_sphere 192 -> 72
spectralMultiplicityConstant  (definition)             192 -> 72
finiteHeightMultiplicity_dyadic_le (G and ledger)      192 -> 72
```

Everything else is untouched: the sharp `R log R` exponent
`xiDyadicRLogRGrowthExponent`, the Jensen bridge, the `3 < 4` geometric
summability ratio, and every abstract consumer of the constant (which only
uses it as a bound in `<=` statements). A `rg` audit shows the remaining
mentioned `192` is the docstring pointer to the old reading.

## Numeric proxy and reprice

```text
xiGrowthFixedConstant   15.565812619574155
1 + |log (pi/6)|        1.6470295833786548
mult(c=192)             301.83032993648527   (bitwise the 2243 artifact)
mult(c=72)              128.70692502980964
mult gain               2.3450978248962033

B_upper                 9506275.102584327
tail (4 * mult * B_up)  11477128602.720102 -> 4894093747.764274
tail/margin             0.006850392090059914 -> 0.0029211540846331738

combined with 2245 (count ratio x tail/margin):
  2119 old/old           0.3317529367828551
  unconditional, 72      0.00122500010000746
  imported, 72           0.000989423157698333
```

## Lean evidence

- module + probe build log:
  `build-logs/routea_multiplicity_tightening_2248_build_20260930.log`
  (`Build completed successfully (3532 jobs)`, exit 0);
- full library build log:
  `build-logs/routea_multiplicity_tightening_2248_fullbuild_20260930.log`
  (`Build completed successfully (4148 jobs)`, exit 0);
- paired axiom audit in the probe log: every audited theorem depends only
  on `[propext, Classical.choice, Quot.sound]`.

## What this closes and what it does not

Closed: the optional Lean-side tightening of the `192/log 2` slack
registered in 2240/2241; the constant is now rung-tight in its shape.

Not closed: the constant shape `G + 1 + c * 3^n` still charges the
multiplicity growth; further gains would need a different bound shape, not
a sharper rung constant. No producer GO, no gate sign change, no RH claim.

## Provenance

- Lean: `ConnesWeilRH/Dev/C1SpectralSummability.lean` (lemma + four sites);
- script: `scripts/routea_weighted_zero_multiplicity_tightening_2248.py`;
- artifact: `results/2248_multiplicity_tightening.json`;
- inputs: `results/2243_panel_cem_reprice.json`,
  `results/2245_owner_count_brick.json`.
