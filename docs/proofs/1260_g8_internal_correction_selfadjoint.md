# G8 internal correction is self-adjoint

Date: 2026-09-10

The internal forward correction from record 1259 is

\[
K_{\mathrm{fwd}}=F^\dagger W_gM+M^\dagger W_gF+F^\dagger W_gF,
\]

with `F` the actual forward coframe, `M` the finite Euler metric coframe, and
`W_g` the selected detector operator.  The detector is self-adjoint.  Lean
therefore proves that the two mixed terms are adjoints of one another and that
the forward Gram term is self-adjoint, hence `K_fwd` itself is self-adjoint.

Formal declaration: `g8InternalForwardCorrection_isSelfAdjoint` in
`ConnesWeilRH.Dev.C1G8AdjointShearGram`.

Evidence: `1260_g8_selfadjoint_main.log` and
`1260_g8_selfadjoint_audit.log`; both builds completed successfully, with zero
`error:` and zero `sorryAx` lines.  The focused audit reports exactly
`[propext, Classical.choice, Quot.sound]`.

This is an operator-domain prerequisite for a real finite-cutoff trace
readback.  It does not identify that trace with the finite visible-prime
ledger, prove a cutoff limit, establish `0 ≤ qw g`, or claim RH.
