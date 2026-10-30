# Record 3203: concrete owner parameter readback

The repository already contains concrete Lean owner data:

- `record2680CorrectionCoefficient` in `C1RouteARepairedOwnerCorrectionM02680.lean`
- `capturedModulations2584` in `C1RouteACorrectionCaptureParameters2584.lean`

This audit compares those exact rational lifts with the 2275 captured family
hex values and the 2338 `ideal_correction_coefficient` boxes.

Result:

```text
modulations:       30 / 30 exact matches
owner coefficients: 0 / 30 inside the 2338 ideal boxes
```

The mismatch is systematic binary64 rounding / representation drift, not a
missing parser. For example, family 0's real owner value is about
`154748600460917856`, while the ideal box is centered near
`154748600460917860.858...` with width below `1e-28`. The old 3187 evaluator
uses the ideal-box center and radius, so it does not enclose the concrete
`record2680CorrectionCoefficient` owner.

This closes one ambiguity and creates the actual numerical task: reprice the
Taylor-6 enclosure with the exact owner binary64 coefficients, or construct a
new explicitly widened coefficient box that contains those owner values. The
old JSONL cannot be promoted by an identity theorem alone.

Evidence:

- `scripts/audit_routea_concrete_owner_parameter_readback_3203.py`
- `results/3203_routea_concrete_owner_parameter_readback.json`
- `ConnesWeilRH/Dev/C1RouteARepairedOwnerCorrectionM02680.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean`

No producer certificate, `SourceRH`, or RH claim follows.