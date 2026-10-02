# Record 2491: directed MPFR family-hybrid price

The 2489 high-precision price was independently replayed with the directed
MPFR bump enclosure used by record 2478. On the production 640-cell grid
(40 coarse cells, subdivision 16), each safe family cell takes the valid
minimum of the directed interval-family upper and the same-family L1 upper;
unsafe cells retain the L1 upper.

For both `sigma = -1/2` and `sigma = +1/2`, the directed price is:

- baseline remainder: `635.5759930912202`;
- hybrid remainder: `433.0933619523697`;
- hybrid/baseline: `0.6814186921157209`.

The baseline agrees with the 2489 evaluator to about `2e-12`, while the
independent directed path gives a further reduction to about 68.14% of the
baseline. This is a reproducible pricing control only. The artifact is not a
Lean literal import, producer certificate, producer GO, or RH proof. The next
obligation is directed rational binding/import of the family upper data.
