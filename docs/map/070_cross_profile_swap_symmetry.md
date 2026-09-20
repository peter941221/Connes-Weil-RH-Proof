# 070 — Directed cross profile swap symmetry

Status: formal arithmetic/profile symmetry; Archimedean cross equality and
the signed gate estimate remain open (2026-09-21).

For any two CompactLog tests, exchanging the inputs of the pair convolution
turns the pair test into the reflected complex conjugate. Consequently the
real part of its bilateral profile is unchanged. The finite visible-prime
AB and BA channels therefore have identical coefficients at every prime-power
node and can be merged in the arithmetic profile only.

Evidence: `bilateralProfile_pairTest_swap_re` in
`C1P2SpanProfileMatrix.lean`, paired Audit, and
`shortest_route_20260921_swap_profile_v20.log`.

The result does not assert equality of the full Archimedean cross gates and
does not provide a sign or RH conclusion.
