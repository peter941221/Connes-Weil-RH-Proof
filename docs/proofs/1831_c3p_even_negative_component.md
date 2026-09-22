# 1831 — C3' even negative companion

Date: 2026-09-22

## Result

`C1P2EvenNegativeDiagonalCertificate.lean` proves
`exists_even_negative_diagonal_of_offLineZero`. Given a hypothetical
off-line source zero and a narrow residual window satisfying the explicit
Archimedean budget, finite interpolation projected to the even part gives
the zero, half, and one nodal equations, positive square mass, and a strict
negative complete `ICgate`.

The construction complements the odd negative component from records 1813
and 1825. It is exact and formal; the audit reports only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## Boundary

This closes the two artificial parity-component signs needed by the generic
two-span consumer. It does not identify either component with the selected
healthy orbit detector, prove a support/visible-prime transfer, or establish
the actual detector-specific semi-local `qw >= 0`. It therefore does not
close C3' or RH.

## Verification

Build log: `/home/peter/rh/build-logs/1831_even_negative_final.log`.
