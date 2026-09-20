# 072 — Full ICgate cross swap symmetry

Status: formal complete pair-gate symmetry; signed C3 estimate remains open
(2026-09-21).

The directed pair convolution swap is now transported through every layer of
the same owner: complex finite-prime term (by conjugation), visible
prime-power index set, real finite-prime sum, and the Archimedean term. The
result is the exact full-gate identity
`ICgate (f* * g) = ICgate (g* * f)`.

Evidence: `finitePrimeTermComplex_pairTest_swap`,
`globalPrimeIndexSet_pairTest_swap`, `finitePrimeSum_pairTest_swap`, and
`ICgate_pairTest_swap` in `C1P2SpanProfileMatrix.lean`, paired Audit, and
`shortest_route_20260921_full_gate_swap_v26.log`.

This is a formal owner symmetry, not a positivity or RH theorem. The next
active target is the one remaining cross-gate signed estimate in the two-span
C3 producer.
