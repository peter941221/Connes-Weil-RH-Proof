# 1033 - Translation-invariant Lane R penalty screen

Date: 2026-08-19.

Probe: `docs/proofs/1033_lane_r_translation_invariant_penalty_screen.py`.

## Verdict

A translation-compatible replacement survives the finite sine-basis screen:

```text
P_21(g) <= |L(g,0)|^2
           + |L(g,-1/2)L(g,1/2)|
           + |L(g,-1)L(g,1)|.
```

The paired terms are invariant under root translation because their exponential
characters cancel.  They also vanish on the existing Lane R constraints: a
zero at `+1/2` or `+1` is enough to kill the corresponding product.

This is a candidate certificate only.  The continuous inequality and its
restriction to the full compactly supported owner remain open.

## Method

The probe uses the same L2-orthonormal sine basis and exact analytic resolvent
action as 1032.  For each vector it evaluates the absolute-value penalty
directly.  The search combines:

- the four sign-sector eigenvector candidates;
- deterministic random unit directions;
- BFGS refinement of the best candidates.

The unrestricted sign-sector eigenvalues are reported as diagnostics only: a
sector eigenvector must satisfy its own product-sign constraints before it is
an admissible direction.  The final `sampled_max` is the largest value found
for `P_21 - penalty`.

## Representative boundary results

At `radius = 0.3464`, so `2*radius = 0.6928 < log(2)`, the result was stable
under centers `-4,-1,0,1,4` and quadrature sizes `600`, `900`, `1200`, and
`1800`.

```text
+--------+----+-----------------+----------------+
| radius | K  | sampled_max     | prefix_min    |
+--------+----+-----------------+----------------+
| 0.3464 |  8 |       -0.09395609|      -1.45298358|
| 0.3464 | 16 |       -0.07899948|      -1.75193841|
| 0.3464 | 24 |       -0.07296857|      -1.82982445|
| 0.3464 | 32 |       -0.06970150|      -1.85962401|
| 0.3464 | 48 |       -0.06624775|      -1.88175178|
+--------+----+-----------------+----------------+
```

At smaller radii the sampled maximum is more negative:

```text
+--------+----+-----------------+
| radius | K  | sampled_max     |
+--------+----+-----------------+
| 0.2000 | 48 |       -0.44964297|
| 0.3000 | 48 |       -0.20201414|
| 0.3450 | 48 |       -0.07006794|
| 0.3464 | 48 |       -0.06624775|
+--------+----+-----------------+
```

The equal values across translated centers are the expected invariance check,
not independent evidence of a continuous theorem.

## Lean owner

`Dev/C1XiCenterTwoGammaConstrainedPrefix.lean` now exposes:

```text
laneRTranslationInvariantLaplacePenalty
laneRConstrainedPrefixTranslationInvariantPenaltyCertificate
laneRConstrainedPrefixTranslationInvariantPenaltyCertificate_implies_target
laneRTranslationInvariantLaplaceProduct_translate
laneRTranslationInvariantLaplacePenalty_translate
```

The last two theorems are axiom-clean translation/readback interfaces.  They
prove the algebraic invariance and the logical reduction only; no numerical
eigenvalue is imported into Lean, and no Lane R, global spectral positivity, or
RH theorem is claimed.

## Reproduction

```text
python docs/proofs/1033_lane_r_translation_invariant_penalty_screen.py \
  --length 21 --quadrature 900 --random-directions 2500 \
  --radii 0.20 0.30 0.345 0.3464 \
  --centers -4 -1 0 1 4 --basis-sizes 8 16 24 32 48
```
