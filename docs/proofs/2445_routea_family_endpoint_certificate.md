# 2445 - Route A family endpoint rectangle preflight

Date: 2026-10-02.

The current same-owner capture was evaluated with the audited 256-bit MPFR
directed primitives from record 2286. The run covers 30 stored family rows,
both coefficient vectors, and 9 fixed positions:

9 positions x 2 vectors x 30 family terms = 540 term rectangles

Each interior term records directed rectangles for q, the bump exp(-30/q),
the real and imaginary phase, and the final complex family term. Outside-support
terms are recorded as the exact zero rectangle.

Evidence:

- scripts/routea_family_endpoint_certificate_2445.py
- scripts/routea_family_endpoint_certificate_selftest_2445.py
- results/2445_routea_family_endpoint_certificate.json

The initial independent replay exposed two implementation defects before any
certificate interpretation: subtraction used same-direction endpoints, and the
real bump factor was accidentally represented as a complex value with a
nonzero imaginary component. Both defects were fixed in the producer, the
artifact was regenerated, and the final WSL2 run completed with 540/540 terms
contained and 4 selftests passing.

The artifact binds the 2275 owner capture. The independent replay is in
scripts/routea_family_endpoint_independent_replay_2445.py and its result is in
results/2445_routea_family_endpoint_independent_replay.json.

This is a point-box preflight, not the final numerical certificate. It does not
prove continuum transfer, quadrature error, a strip norm, Lean numeric import,
the signed selected-detector budget, producer GO, or RH.

The result is still a finite point-box control. The next numerical step is to
extend the same independently checked construction to the actual evaluator
box and quadrature obligations, then package those facts for Lean.

Record 2449 supersedes the original replay's decimal-string position
convention and incomplete backend-source manifest. The current regenerated
artifacts use exact stored binary64 positions, bind the reused 2286 source,
and pass 540/540 containment checks plus 10 selftests. Support branches now
use exact stored-input fractions and unresolved positive-q intervals are
rejected. See `docs/proofs/2449_routea_family_exact_input_replay.md` for the
boundary fixture, failure controls and remaining formal obligations.
