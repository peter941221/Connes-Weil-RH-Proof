# G8 P1 — complement cross-channel trace owner

Date: 2026-09-10

The P0 complement channel is now given a concrete finite-cutoff
`BasisHilbertSchmidtPairData` owner.  Its left leg is the actual complement
`D_n`, and its right leg is `G J C_n`; Lean proves the exact trace-product
identity

`traceProduct = D_n† G J C_n`.

The pair is trace-class on the same named source basis.  Its swapped pair is
the existing same-owner adjoint channel, so the two mixed complement terms can
be handled by the established trace ledger without changing owners or using
an ambient cyclicity shortcut.

Evidence: owning and Audit targets of
`ConnesWeilRH.Dev.C1G8AdjointShearGram` build successfully in
`build-logs/1270_g8_p1_cross_channel.log` (3922 jobs, standard axioms only,
zero `error:`/`sorryAx`).

This is a formal P1 trace-legality brick.  It does not identify a finite-prime
sum, prove the complement trace vanishes, or imply `qw >= 0`.
