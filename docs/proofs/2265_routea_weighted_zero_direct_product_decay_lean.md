# 2265 — Lean brick: the direct-product decay estimate (producer lemma)

Date: 2026-09-30

Consumer: 2260 pinned the producer side of the count-free assembly to one
Lean lemma — the direct-product decay estimate giving the chain constant
as the min-product of factor `L¹` strip norms over `(2π)²`, tied to the
2257 count-free consumer. This record lands that lemma as a formal brick.

Verdict: **landed**. The producer-side inequality and its chain-shaped
corollary are machine-checked with the permitted axioms; the numeric
envelope enters only as an explicit hypothesis (`hB`), whose screen-grade
value is the 2264 audit's subject.

## The module

`ConnesWeilRH/Dev/C1RouteADirectProductDecay.lean` defines the two strip
functionals and proves nine declarations:

```text
stripNorm        σ f = ∫ e^{σx} ‖f x‖
stripSecondNorm  σ f = ∫ e^{σx} ‖f'' x‖

stripNorm_nonneg, stripSecondNorm_nonneg
laplaceAt_eq_integral          laplaceAt f s = ∫ e^{sx} f x
sq_mul_exp_integral_eq         s² ∫ e^{sx} f = ∫ e^{sx} f''    (two IBPs)
norm_exp_integral_le_stripNorm      ‖∫ e^{(σ+it)x} f‖ ≤ M_f(σ)
t_sq_mul_norm_exp_integral_le       t² ‖∫ e^{(σ+it)x} f‖ ≤ D2_f(σ)
test_t_sq_mul_norm_le_stripSecond   same, instantiated at CompactLogTest
laplaceAt_convolution_quadratic_bound
    ‖t/2π‖² ‖L(b⋆c)(σ+it)‖ ≤ min(D2_b·M_c, D2_c·M_b)(σ) / (2π)²
laplaceAt_convolution_spectral_bound_of_strip
    (∀ σ ∈ [-1/2, 1/2], min(D2_b·M_c, D2_c·M_b)(σ) ≤ B) ->
    ∀ ρ : sourceNontrivialZeroSet,
      ‖ρ.im/2π‖² ‖L(b⋆c)(centeredXiCoordinate ρ)‖ ≤ B / (2π)²
```

The quadratic bound is the two-channel estimate: one integration by parts
per factor turns `s²` into the second-derivative face on one factor, and
the trivial face on the other; the `min` picks the better channel. The
corollary is the producer-shaped interface to
`exists_spectral_laplaceAt_quadratic_bound`
(`ConnesWeilRH/Dev/C1SpectralWeil.lean:275`): it evaluates at
`centeredXiCoordinate ρ = (ρ.re - 1/2) + i·ρ.im` with the Laplacian real
part shipped in via `sourceNontrivialZero_zero_lt_re` /
`_re_lt_one` giving `σ ∈ [-1/2, 1/2]`.

Implementation notes (for a future reviser): the derivative chain runs on
`CompactLogTest` smoothness (`ContDiff ℕ∞ω` order bookkeeping, `by decide`
for the order inequalities); compact support of `f'`, `f''` comes from
`HasCompactSupport.deriv`; the two integrations by parts use
`integral_mul_deriv_eq_deriv_mul_of_integrable` with the four integrability
side conditions discharged by
`Continuous.integrable_of_hasCompactSupport`; the `(2π)²` normalization is
pulled out with `Real.norm_eq_abs` + `div_le_div_iff_of_pos_right`.

## Verification

```text
module + probe build        Build completed successfully (3518 jobs)
axiom audit                 all nine declarations:
                            [propext, Classical.choice, Quot.sound]
                            (no sorryAx)
```

Paired audit probe:
`ConnesWeilRH/Dev/C1RouteADirectProductDecayProbe.lean` (`#print axioms`
for all nine declarations), run via `lake env lean` in WSL; full log in
`build-logs/routea_direct_product_decay_20260930.log` (786 lines).

## What this closes and what it does not

Closed: the producer-side *shape*. The 2260 single producer gap is now a
theorem: from a strip-norm envelope `B` on `[-1/2, 1/2]` for the two
product channels, every source nontrivial zero satisfies the exact
chain-shaped quadratic bound with constant `B/(2π)²`. The earlier
convention mismatch (screen tabulated `[0, 1]`, chain evaluates
`(-1/2, 1/2)`) is resolved at the interface level: the hypothesis is
stated on precisely the strip the chain uses.

Not closed: the numeric hypothesis `hB` itself. At screen grade the frozen
`bUpper2243 = 9506275.102584327` dominates the centered strip with margin
3.3071× (2264), but the certified envelope on `[-1/2, 1]` (2234-style
panel / coefficient / Lipschitz re-run) is not yet computed, so the
consumer tie is screen-grade only. The count-free consumer assembly (2257)
is a separate, already-landed brick; this module supplies its producer
side. No producer GO, no gate sign change, no RH claim.

## Nonclaims

- the numeric envelope on the negative half is not certified here (2264);
- `CompactLogTest` is the test-function class of the committed chain;
  nothing is claimed beyond it;
- no claim about the 2103 stress candidates or other constructions.

## Provenance

- module: `ConnesWeilRH/Dev/C1RouteADirectProductDecay.lean`;
- probe: `ConnesWeilRH/Dev/C1RouteADirectProductDecayProbe.lean`;
- build log: `build-logs/routea_direct_product_decay_20260930.log`;
- chain interface: `ConnesWeilRH/Dev/C1SpectralWeil.lean:275`
  (`exists_spectral_laplaceAt_quadratic_bound`, `centeredXiCoordinate`);
- product law: `CC20YoshidaConvolution.laplaceAt_convolution`
  (`ConnesWeilRH/Source/CC20YoshidaConvolution.lean:431`);
- predecessor: `docs/proofs/2260_routea_weighted_zero_producer_assembly_recon.md`;
- companion audit: `docs/proofs/2264_routea_weighted_zero_sigma_range_audit.md`.