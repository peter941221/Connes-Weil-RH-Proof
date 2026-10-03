# Record 2517 — production exponential remainder price

The 2516 production remainder was priced on the same exact-owner 640-cell
grid as the corrected 2495 replay, using directed MPFR.  The 2495 L1 control
reproduces `635.575993091222` for both sigma signs.  The 2516 rule uses the
2508 floor/Taylor upper on cells `196..443` and the L1 fallback elsewhere, and
reads `414.57518775159883`, or `0.6522826416637425` of baseline, for both
sigma signs.

The artifact also stores the 640 per-cell upper values, their binary64 hex
encodings, and one-ulp `nextUp` encodings.  The largest safe-cell value is
`667249.4571825103` at index `317`; the outside-safe cells retain the L1
fallback.  The totals above are unchanged by this decomposition.  These
fields are audit scaffolding for a future table certificate, not Lean inputs.

This is routing evidence only: the result is not imported into Lean, does not
certify the analytic enclosure or the final producer margin, and makes no RH
claim.

Evidence: `scripts/routea_owner_production_exp_remainder_2517.py` and
`results/2517_owner_production_exp_remainder.json`.
