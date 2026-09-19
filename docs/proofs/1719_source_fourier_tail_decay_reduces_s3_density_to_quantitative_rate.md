# 1719 — Existing Hardy tail decay reduces the S3 density bone to a rate estimate

Date: 2026-09-20

## New formal evidence

The repository already proves the qualitative source-Fourier tail statement

```text
sourceFourierSupportProjection unitSoninScale
  (T_(-n) u) -> 0 in norm.
```

The proof is exact: Hardy--Titchmarsh reverses translation, the positive
half-line projection becomes the tail of the Hardy-transformed vector, and
the L2 tail tends to zero.  The source-Sonin projection then inherits the
bound because it factors through the source-Fourier projection and is a
contraction.  The formal declarations are
`sourceFourierSupportProjection_unit_globalLogTranslation_neg_tendsto_zero`
and
`sourceSoninProjection_selectedSourceTranslationOrbit_norm_tendsto_zero`.

## Consequence for S3

This rules out another false shortcut: qualitative orbit decay alone does not
give the uniform annular trace bound.  The missing source-Sonin density lemma
can now be split into a quantitative tail-rate statement for the fixed compact
root vector (or its Plancherel multiplier), strong enough to make the weighted
translation orbit square-summable/integrable.

The required upgrade is schematically

```text
sum_n ||P_Sonin T_(-n) k_g||^2 < infinity
```

or its continuous weighted analogue.  Once this is proved with the actual
root multiplier, the existing Tonelli and annular-trace consumers apply.

## Status

The qualitative decay is FORMAL; the quantitative rate is OPEN.  This is a
newly narrowed analytic target, not a numerical conclusion and not an RH
claim.
