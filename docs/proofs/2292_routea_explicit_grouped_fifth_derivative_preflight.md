# 2292 — Fifth-derivative instrument erratum

Date: 2026-09-30.

Status: the previous method no-go and subdivision freeze are WITHDRAWN.
The recorded astronomical prices were instrument errors. Record 2293 is the
current result.

The old implementation evaluated exterior families as growing exponentials
instead of zero, mixed `R` and `R^2` in derivative formulas, used a component
maximum instead of the complex modulus, and omitted panel length from its
integrated-error proxy. The old prices therefore do not support a mathematical
no-go. Independent pointwise differentiation exposed these defects.

The repaired 2292 engine now skips exterior families, reports endpoint-crossing
cells, uses the corrected grouped derivative formulas, and forms the complex
modulus after summation. Its selftest passes 7 tests. It remains an interior
instrument only; endpoint handling and the centred variation method are in
record 2293.

Evidence: `scripts/routea_interval_fifth_derivative_preflight_2292.py`,
`scripts/routea_interval_fifth_derivative_selftest_2292.py`, and
`results/2292_interval_fifth_derivative_preflight.json`.

No hgap supplier, producer GO, or RH claim follows.