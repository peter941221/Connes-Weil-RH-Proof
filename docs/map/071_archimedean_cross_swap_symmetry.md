# 071 — Archimedean cross swap symmetry

Status: formal Archimedean symmetry; finite-index-set transport to a full
`ICgate` equality remains open (2026-09-21).

The reflection-conjugation identity for the two directed pair convolutions now
propagates through the direct Archimedean numerator, denominator, restricted
integral, and real readout. Thus the Archimedean terms of `f* * g` and
`g* * f` are exactly equal.

Together with record 1762, this merges the two directed cross channels in the
Archimedean and real bilateral-profile observables. The remaining small
interface is transport of the complex nonzero support index set used by
`finitePrimeSum`, followed by the signed estimate; no sign or RH conclusion
is asserted.

Evidence: `archimedeanTerm_pairTest_swap` in
`C1P2SpanProfileMatrix.lean`, paired Audit, and
`shortest_route_20260921_arch_swap_v24.log`.
