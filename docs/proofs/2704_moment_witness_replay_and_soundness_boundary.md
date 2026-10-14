# Record 2704: moment witness replay and soundness boundary

Date: 2026-10-14.

Status: REPLAY GREEN; ANALYTIC SOUNDNESS STILL OPEN.

The committed record-2351 Fraction checker was rerun from the current `main`
tree. It returned `EXACT_NEUMANN_AND_BOX_PASS` with
`eta = 5.873158307277732e-38`; the two coefficient-box maximum ratios were
`0.9999999438559326` and `0.999999941431241`. The 17 adversarial tests in
`scripts/routea_moment_matrix_exact_selftest_2351.py` also passed.

The 900 rectangle entries in
`ConnesWeilRH/Dev/C1RouteACorrectionAnalyticIntervals2597.lean` were parsed
and compared against `results/2351_moment_matrix_witness.json`. All 900
real/imaginary endpoint quadruples matched exactly, and the Lean source
contains the witness SHA256. This confirms data identity between the external
witness and the Lean payload.

This does not prove analytic interval soundness. The 2597 theorem still takes
the 900 containment statements as an explicit premise, and 2351's rational
Neumann/box calculation assumes the exported rectangles contain the actual
analytic integrals. The diagonal 30-entry assembly is available; the current
off-diagonal manifest closes 51 of 870 positions, leaving 819 explicit
membership premises.

The next proof target remains a directed interval-integrator theorem for the
actual `ownerMomentMatrix2351` entries. Do not treat this replay or the exact
endpoint comparison as a Producer GO, `SourceRH`, or RH result.

Evidence:

- `scripts/routea_moment_matrix_exact_check_2351.py`
- `scripts/routea_moment_matrix_exact_selftest_2351.py`
- `results/2351_moment_matrix_exact_check.json`
- `ConnesWeilRH/Dev/C1RouteACorrectionAnalyticIntervals2597.lean`
- `docs/proofs/2597_analytic_matrix_interval_interface.md`
