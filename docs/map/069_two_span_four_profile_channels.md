# 069 — Two-span four-channel profile expansion

Status: formal channel expansion; channel sign/aggregate estimate remains open
(2026-09-21).

The finite prime-profile term of the same two-span owner with coefficients
`[1,-lam]` is now expanded at every prime-power index into the four actual
pair channels: AA, AB, BA, and BB, with the expected coefficients
`1`, `-lam`, `-lam`, and `lam^2`. The forward and reverse cross channels stay
separate; no symmetry or sign is assumed.

Evidence: `signedProfileTerm_twoSpan_eq_four_pair_profiles` in
`C1P2SpanProfileMatrix.lean`, its paired Audit, and
`shortest_route_20260921_four_profile_v15.log`.

This is a formal same-owner decomposition on the active healthy-`CompactLog`
B5 route. The remaining producer obligation is a signed estimate for these
four channels on the actual OrbitG8 owner.
