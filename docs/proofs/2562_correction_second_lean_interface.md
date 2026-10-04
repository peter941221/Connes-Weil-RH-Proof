# Record 2562 — Correction-second channel decomposed onto the certified weighted aggregate in Lean

Verdict: GREEN as an analytic interface. The Lean theorem
`externalPhysical2344_stripSecond_le_decomposed2562` bounds the correction
channel `stripSecondNorm sigma c` for every sigma, coefficient set, and
modulation set through three already-certified per-family composite bounds of
record 2539, charged on the same 10240-cell production grid over
[-r, r] with r = stripRadius2303. The axiom audit reports exactly
[propext, Classical.choice, Quot.sound] for all six audited theorems. This is
not a numeric certificate: the family centers and per-family errors remain
explicit hypotheses, so no number from record 2561 is yet machine-checked.

## What the theorem says

For every real sigma, coefficients centers errors modulations with
`forall index, |coefficients index - centers index| <= errors index`:

  stripSecondNorm sigma (externalPhysical2344 coefficients modulations)
    <= signedSecondCompositeUpper2562 ... (-r) (2r/10240) 10240
     + 2|sigma| * signedFirstCompositeUpper2562 ... (-r) (2r/10240) 10240
     + sigma^2 * signedCompositeUpper2539 ... (-r) (2r/10240) 10240

This is the Lean-side landing pad for the externally priced D(c) channel of
record 2561 (126381.736940 at sigma = -1/2, 101290.552277 at sigma = +1/2
against pin 666472.585392): once the per-family centers/errors are certified
against the 2338 boxes, the same certificate program as the N(b) channel
feeds all three composites and the two-channel budget
N(b) * D(c) <= 9506275.1026 becomes fully machine-checked on this side.

## Decomposition chain

Pointwise identity, then three-piece charging:

  exp(sigma*x) * f''(x) = W''(x) - (2 sigma) W'(x) + sigma^2 W(x)
                        <= |W''(x)| + 2|sigma| |W'(x)| + sigma^2 |W(x)|

where W = weightedFunction2348 sigma f is the already-certified weighted
aggregate and f = externalPhysical2344 coefficients modulations. Each piece
is charged on the identical production grid through the 2539 machinery:

| piece        | pointwise bound source                  | grid composite                          |
|--------------|-----------------------------------------|-----------------------------------------|
| second jet   | per-cell midpoint + curvature (2539)    | signedSecondCompositeUpper2562 (new)    |
| first jet    | same shape one level up (new, below)    | signedFirstCompositeUpper2562 (new)     |
| function     | existing tight 2539 composite           | signedCompositeUpper2539 (2539)         |

## Theorem inventory

- `externalPhysical2344_contDiff_two2562`: ContDiff R 2 of the physical
  function, obtained by setting sigma = 0 in the certified order-<= infinity
  statement and lowering with of_le.
- `weightedFunction2348_exp_second_jet_combo2562`: the pointwise identity
  above, from the certified first and second derivative formulas of
  weightedFunction2348 plus ring.
- `externalPhysical2344_secondDeriv_zero_at_or_beyond_pin2562`: f'' vanishes
  identically at |x| >= r. Strict exterior via the open-set
  {r < |z|} around each point and nested deriv_eq transfers; the boundary
  points |x| = r are reached by continuity of f'' plus one-sided
  Tendsto on nhdsWithin filters and tendsto_nhds_unique.
- `externalPhysical2344_stripSecond_eq_interval2562`: the channel norm equals
  the interval integral of exp(sigma*x)|f''| over [-r, r] (support clip,
  2539 clone).
- `weightedPhysical2539_secondDeriv_integrand_le2562`: the pointwise
  domination of the physical integrand by the three weighted-aggregate jets,
  proved as a norm triangle chain on the identity.
- `weightedPhysical2539_first_le_signed_midpoint2562` (new): first-jet analog
  of the 2539 second-jet midpoint bound: on any cell,
  |W'(x)| <= |W'(midpoint)| + curvature * width/2, via
  Convex.norm_image_sub_le_of_norm_deriv_le with the certified curvature
  ceiling as the derivative bound and the certified center-error bound at the
  midpoint.
- `signedSecondCompositeUpper2562` / `signedFirstCompositeUpper2562` (new
  defs): per-cell sums step * curvature(cell) and
  step * (jet(midpoint) + curvature(cell) * step/2) over the 10240 cells.
- `weightedPhysical2539_second_integral_le_composite2562` /
  `weightedPhysical2539_first_integral_le_composite2562`: grid composites by
  sum_integral_adjacent_intervals + per-cell integral_mono_on.
- `externalPhysical2344_stripSecond_le_decomposed2562`: support clip, mono_on
  split into the three pieces, integral_add / integral_const_mul to pull out
  the 2|sigma| and sigma^2 factors, then the three grid composites.

No numerical node table is imported anywhere in the module; the same explicit
centers/errors hypotheses that the N(b) certificate program already consumes
carry through unchanged.

## Verification

- Module build: ConnesWeilRH.Dev.C1RouteACorrectionSecondStrip2562, 0 errors,
  no module-scoped warnings (log 2562_correction_strip_try9.log; build
  completed successfully, 3723 jobs).
- Axiom audit (2562_audit.log): #print axioms on the main theorem and the
  five interface theorems, all six report exactly
  [propext, Classical.choice, Quot.sound].
- Integration: root ConnesWeilRH target rebuild, 0 errors (log
  2562_correction_strip_integration.log, 4148 jobs).

## Remaining obligations

- The three composites are still formulas over the explicit centers/errors;
  certifying the 2338 correction coefficient boxes into them (first target:
  cell2700 on the correction channel) is the next brick and is where the
  record 2561 numbers become Lean-checked.
- Coefficient membership of the actual interpolation coefficients in the 2338
  boxes remains open.
- The two-channel product theorem still takes both endpoint inputs as
  explicit hypotheses. Nothing here supports an RH claim.

Evidence: ConnesWeilRH/Dev/C1RouteACorrectionSecondStrip2562.lean,
ConnesWeilRH/Dev/C1RouteACorrectionSecondStrip2562Audit.lean,
build-logs/2562_correction_strip_try9.log,
build-logs/2562_correction_strip_audit.log,
build-logs/2562_correction_strip_integration.log.
