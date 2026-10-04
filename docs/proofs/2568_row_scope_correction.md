# Record 2568 — Row-scope correction: the correction channel consumes correction rows

Verdict: SCOPE CORRECTION, direction preserved. The committed cell2700
correction-second certificates (2563, 2565) and the 2558 signed aggregates
were instantiated at the record-2338 `ideal_base_coefficient` rows, while the
channel they feed - the correction side of the 2560 two-channel reduction -
is the function built from the `ideal_correction_coefficient` rows. The two
row sets are different coefficient vectors (right-hand sides 1 versus the
captured target y_i, per the 2338 record), their midpoints are about
5.7e17 apart in L2 at the worst family, so no membership premise can bridge
them. The architecture (2562 decomposition, 2566 batch structure) and every
position-keyed table are unaffected; the coefficient pair of the aggregate
layers is what changes.

## The finding, from source

- The 2560 consumer hypothesis for the correction side is
  `stripSecondNorm endpoint (externalPhysical2344 correctionCoefficients
  modulations) <= correctionSecondUpper2343` - the correction-coefficient
  function (C1RouteATwoChannelStrip2560.lean).
- The 2561 external pricing of this channel loads
  `row['ideal_correction_coefficient']` (price_correction_second_2561.py,
  load_families).
- The 2563/2565 generators load `row["ideal_base_coefficient"]`
  (generate_firstjet_midpoint_2563.py, generate_firstjet_midpoint_minus_2565.py),
  and the Lean aggregates they close are stated over
  `baseCoefficientCenter2540`, the midpoints of the record-2338 BASE
  rectangles (C1RouteABaseCoefficientBoxes2540.lean: "Exact record-2338 base
  coefficient rectangles").
- The 2338 record defines the two row sets by their right-hand sides
  ("1 for base and the prescribed captured target y_i for correction");
  exact rational measurement of the midpoints gives worst-family squared L2
  distance 3.2345739501270363e+35, i.e. distance about 5.7e17 - seventeen
  orders of magnitude above any membership radius in play.

Consequences for committed work:

1. 2563/2565 are valid certificates for the three-piece 2562 summand of the
   function built from coefficients within 1e-30 of the BASE midpoints. They
   do not, and cannot, feed the 2560 correction hypothesis: the claimed
   pipeline identity with the 2561 budget rows does not hold.
2. The 2564 membership probe's "correction channel needs a new center/error
   pair" was real but understated: the pair is not a wider ball around the
   same centers, it is a different center vector (the correction midpoints)
   with error 1e-28 (probe slack 1.56x over the worst correction half-L1
   6.418e-29).
3. The salvage surface is large. The per-family replay tables (exp inputs,
   centers, factors, rounded jets, per-family ThirdCell leaves, endpoint and
   midpoint value leaves) are position-keyed and coefficient-independent;
   the 90-110 h kernel projection of the 2566 batch structure is unchanged.
   What regenerates is the aggregate layer: the signed sums, charges, and
   the resulting uppers - generator parameter changes, not architecture.

## Ordered disposition

1. (This record) the finding and the ordered disposition, on record before
   any further generation.
2. Reprice the single-cell sigma = -1/2 certificate at the correction pair
   (correction midpoints, 1e-28) in exact external arithmetic; done as record
   2569: the cell2700 bound moves from 5.07e-6 to 3.32e-2. The 2561 grid
   average is about 12 per cell, but the correction mass concentrates near
   the origin, so cell2700 (|x| about 3.1) sits far below that average.
3. Regenerate the cell2700 correction-second modules (first-jet aggregate,
   2558-style aggregates, assembly) at the correction pair; re-audit and
   revalidate; supersede the row choice of 2563/2565 for the correction
   consumer while leaving the committed records untouched.
4. Only then mass-generate: the 2566 lanes proceed with the correction pair
   from the first table on.
5. The membership brick imports the 60 correction-row representatives
   (2^-200 truncations of the correction midpoints; probe smallest k 95)
   against correctionError = 1e-28, and the base-channel membership at the
   committed 1e-30 pair remains as the 2564 probe found it (29.8x slack).

## Explicitly not claimed

No regenerated certificate exists yet in this record. The committed 2563 and
2565 modules stay as accepted artifacts of their stated (base-pair) scope.
No RH claim; the two-channel product theorem keeps both endpoint inputs as
hypotheses.

Evidence: ConnesWeilRH/Dev/C1RouteATwoChannelStrip2560.lean,
scripts/price_correction_second_2561.py,
scripts/generate_firstjet_midpoint_2563.py,
scripts/generate_firstjet_midpoint_minus_2565.py,
ConnesWeilRH/Dev/C1RouteABaseCoefficientBoxes2540.lean,
results/2338_exact_interpolation_repair.json,
results/2564_membership_margin_probe.json,
docs/proofs/2566_full_grid_batch_structure.md.
