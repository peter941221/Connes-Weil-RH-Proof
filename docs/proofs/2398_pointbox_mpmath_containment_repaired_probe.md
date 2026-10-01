# 2398 — repaired point-box containment probe

Date: 2026-10-02.

The 2397 control exposed a cancellation-scale containment escape. The repair
has three scoped changes in the 2242 evaluator: directed bounds for the
precomputed k=2 constants, an upward-rounded second angle endpoint, and one
binary64 `nextafter` step outward after the directed MPFR-to-binary64
conversion.

The repaired revision was checked against an independent 90-digit mpmath
evaluation on 1001 grid points and four channels: 4004/4004 values were
contained, with zero failures. The probe is not source-hash compatible with
the 2385 full-grid artifact, so that artifact is stale for this evaluator
revision and must be regenerated before any full-grid claim. This is sampled
containment evidence only; it is not a full-domain enclosure, Lean numeric
import, producer certificate, or RH claim.

Evidence:
`scripts/routea_weighted_zero_zero_count_certificate_2242.py`,
`scripts/routea_pointbox_mpmath_containment_control_2397.py`, and
`results/2398_pointbox_mpmath_containment_repaired_probe.json`.
