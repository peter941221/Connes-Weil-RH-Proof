# 2343 - Endpoint strip bridge in Lean

Date: 2026-10-01.

Status: LOGICAL-BRIDGE-CERTIFIED / NUMERICAL-ENDPOINTS-EXTERNAL.

Record 2342 supplies four external endpoint norm bounds for the repaired
ideal source. Record 2343 proves the missing logical reduction in Lean:
endpoint bounds at sigma = -1/2 and sigma = 1/2 imply the corresponding
weighted norm bound at every sigma in the centered interval. It then combines
four endpoint constants into the existing `FrozenStripHypothesis` consumer.

This is a bridge theorem, not an import of the 2342 numerical artifact. The
four endpoint inequalities remain explicit hypotheses. No coefficient
certificate is imported, no owner handoff occurs, and no producer GO or RH
claim is made.

## Mathematical bridge

For a nonnegative continuous weight g with compact support, convexity of the
real exponential gives, for sigma in [-1/2,1/2],

  exp(sigma x) <= (1/2-sigma) exp(-x/2)
                 + (sigma+1/2) exp(x/2).

After multiplying by g and integrating, the middle weighted integral is at
most the convex combination of the two endpoint integrals. If both endpoint
integrals are at most U, the middle integral is at most U.

A `stripNorm` is this integral with g(x)=norm(F(x)). A `stripSecondNorm`
uses g(x)=norm((F'') (x)). The proof uses nonnegativity and compact support;
it does not differentiate a complex modulus and does not use a zero-count
premise.

The existing producer consumer then applies the theorem to both functions and
both derivative channels, multiplies the nonnegative bounds, and uses the
frozen arithmetic inequality

  min(9044.9434472 * 231.2642026141,
      666472.585392 * 2.7790943782)
    <= 9506275.102584327.

The constants are deliberately rounded upward from the 2342 endpoint
intervals. A separate exact-rational external check confirms that every 2342
endpoint upper is below its corresponding constant.

## Lean evidence

New modules:

- `ConnesWeilRH/Dev/C1RouteAEndpointStrip.lean`
- `ConnesWeilRH/Dev/C1RouteAEndpointStripAudit.lean`

Main theorems:

- `expWeightedIntegral_le_of_endpoint_bounds`
- `stripNorm_le_of_endpoint_bounds`
- `stripSecondNorm_le_of_endpoint_bounds`
- `endpoint_min_product_le_frozen`
- `frozenStripHypothesis_of_compact_endpoint_bounds`
- `frozenStripHypothesis_of_owner_endpoint_bounds`

Focused build:

```text
Build completed successfully (3707 jobs).
All six audited leaves depend only on:
[propext, Classical.choice, Quot.sound]
```

The source and WSL mirror are byte-identical. The build log is
`build-logs/2343_endpoint_strip_build.log`.

## Scope boundary

The final owner theorem still takes four endpoint norm inequalities as
hypotheses. Supplying those hypotheses from 2342 requires an analytic identity
between the external evaluator's repaired source and the Lean
`correctedPhysical` function, plus a formalized or imported proof that the
Arb node and panel chain encloses the exact integrals. The bridge does not
silently turn a JSON number into a Lean theorem.

The selected detector's marked negative value, source-zero conditions,
complete composed-support prime book, signed full-kernel charge, and live
consumer handoff remain separate obligations.

## Next steps

1. Formalize the endpoint norm bounds for `correctedPhysical` or create a
   narrowly scoped certificate-import interface whose assumptions state the
   exact function, coefficients, radii, and endpoint inequalities.

2. Prove the external evaluator's function is definitionally the same source
   as `correctedPhysical`; matching coefficient hashes alone is insufficient.

3. Feed the same-owner endpoint bounds into
   `frozenStripHypothesis_of_owner_endpoint_bounds`, then continue with the
   signed composed-support kernel budget.
