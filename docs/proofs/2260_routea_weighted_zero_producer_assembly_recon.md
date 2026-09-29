# 2260 — Producer-side assembly recon: the count-free bound chain and its single remaining Lean lemma

Date: 2026-09-30

Consumer: the open producer-side item after the 2257 count-free consumer
landing ("assembly of the producer gate") and the 2197 / 2243 direct-product
screens. This record is docs-only: it traces the Lean high-shell chain to
its exact analytic content, verifies that the screen lane computes the same
constant of that chain, and names the one lemma that remains formal.

Verdict: **the producer-side count-free assembly is one Lean lemma short,
and the numeric tie is already certified. The fully proved chain
`exists_weightedZeroMeasure_highShell_tsum_bound`
(`ConnesWeilRH/Dev/C1RouteAWeightedZeroMeasure.lean:219`) gives
`∃B ≥ 0, Σ'_n Σ'_{ρ ∈ shell(n+1)} wZM ≤ 4 · multConst · B` with
`B = (2π)^2 · C` from the abstract compactness constant of
`exists_spectral_laplaceAt_dyadic_tail_bound`
(`ConnesWeilRH/Dev/C1SpectralWeil.lean:385`). The 2197 header formula
`C ≤ min(‖base''‖₁ ‖corr‖₁, ‖corr''‖₁ ‖base‖₁)/(2π)^2` computes exactly
that `C`: `(2π)^2 · 77444.14398633591 = 3057372.2573045553` bitwise equals
the 2197 `B_upper`, and `(2π)^2 · 240796.76135588222 = 9506275.102584315`
against the frozen 2243 `B_upper = 9506275.102584327` (relative difference
`1.175630914820416e-15`, the frozen value rounded up). Hence the producer side reduces
to formalizing the direct-product decay estimate for the concrete
factorization; count-freeness then follows because the factor norms are
zero-set-independent.**

## The chain, leaf to root

```text
C1SpectralWeil.lean
  248  exists_uniform_centered_laplaceAt_vertical_quartic_decay
         (compact-strip uniformity of laplaceAt F)
  275  exists_spectral_laplaceAt_quadratic_bound
         ∃C ≥ 0, ∀rho, ‖Im(rho)/(2π)‖² · ‖laplaceAt F (centeredXiCoordinate rho)‖ ≤ C
  385  exists_spectral_laplaceAt_dyadic_tail_bound
         shell |Im| ≥ 2^(n+1) gives ‖laplaceAt‖ ≤ B / (2^n)² with B = (2π)² C
C1RouteAWeightedZeroMeasure.lean
  117  exists_spectralHeightShell_weightedZeroMeasure_bound
         shell sum ≤ shellMultiplicity(n+1) · B/(2^n)²
  158  exists_geometric_spectralHeightShell_weightedZeroMeasure_bound
         geometric ratio 3/4
  219  exists_weightedZeroMeasure_highShell_tsum_bound
         ∃B ≥ 0, tsum ≤ 4 · spectralMultiplicityConstant · B
```

The constant `C` of line 275 is produced by compactness: a uniform bound
on the compact strip, not a computable constant. The screen lane supplies
the computable surrogate: for `F = base * correction` in Laplace space the
convolution estimate is

```text
C ≤ min(‖base''‖₁ ‖correction‖₁, ‖correction''‖₁ ‖base‖₁) / (2π)²,
```

a direct product of L¹ norms of the two factors, each independent of the
zero set. The numeric tie to the frozen constants:

```text
lane          C_upper                 (2π)² C_upper          frozen B_upper
2197 screen   77444.14398633591       3057372.2573045553     3057372.2573045553  (bitwise)
2243 screen   240796.76135588222      9506275.102584315      9506275.102584327   (rel 1.26e-15)
```

## What remains

One Lean lemma: the direct-product decay estimate for the concrete
factorization — that the `C` of `exists_spectral_laplaceAt_quadratic_bound`
can be taken as the min-product of the factor L¹ norms divided by `(2π)²`,
plus the arithmetic tie `(2π)² · C ≤ B_upper` consumed at the frozen
constants. The 2257 consumer (count-free, 10 theorems axiom-clean, exact
product `6.32e-6` below the rounded-up frozen tail) already consumes the
`B_upper` side; the producer-side obligation is exactly the lemma above.

Count-freeness: `‖base''‖₁`, `‖correction‖₁` and their mirror pair are
‖·‖₁ norms of fixed functions of the construction, with no node or zero
count in them; the multiplicity entering line 219 is the certified
multiplicity constant, not an enumerator.

## Nonclaims

- the direct-product decay lemma is **not yet formalized** (this record
  names it; the screen lane's `C_upper` is a computed upper bound with its
  own certification status in the 2197/2234/2249 line);
- the min-product formula is the screen's header identity, verified
  numerically at the two frozen constants, not a Lean theorem;
- no producer GO, no gate sign change, no RH claim.

## Provenance

- Lean: `ConnesWeilRH/Dev/C1RouteAWeightedZeroMeasure.lean` (lines 117,
  158, 219), `ConnesWeilRH/Dev/C1SpectralWeil.lean` (lines 248, 275, 385);
- screens: `scripts/routea_weighted_zero_direct_product_mass_screen_2197.py`
  (constants `C_upper = 77444.14398633591`, `B_upper = 3057372.2573045553`),
  `scripts/routea_weighted_zero_direct_product_outward_2234.py`
  (`SCREEN_2197`, `bUpper2243 = 9506275.102584327`);
- consumer: the 2257 section of `docs/map/104_route_a_four_round_campaign.md`
  (count-free Lean assembly, ten axiom-clean theorems);
- numeric identity re-verified in this session: `(2*math.pi)**2 *
  77444.14398633591 == 3057372.2573045553` (bitwise);
  `(2*math.pi)**2 * 240796.76135588222 == 9506275.102584315`.