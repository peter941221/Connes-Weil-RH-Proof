# Record 2495: exact-input directed-MPFR replay

The 2491 evaluator was re-run after removing two non-certified conversions:
owner radius/modulation values are now formed from their exact rational
payloads and `exp(-30)` is evaluated by directed MPFR rather than enclosed
from `math.exp` with neighboring binary64 values. The 640-cell replay gives,
for both sigma signs:

- baseline: `635.575993091222`
- hybrid: `433.0933155503201`
- hybrid/baseline: `0.6814186191078487`

The old 2491 hybrid was `433.0933619523697`; the difference is about
`4.64e-5`. Therefore the 2492 rational table is not silently promoted to the
corrected evaluator. It must be regenerated before it can be used as a table
payload for the 2494 bridge. This remains external pricing evidence, not a
Lean enclosure certificate or producer/RH result.

Evidence: `scripts/routea_owner_family_hybrid_mpfr_exact_2495.py` and
`results/2495_owner_family_hybrid_mpfr_exact.json`.
