# 1485 — R3 diagonal trace-limit energy constraint

**Consumer:** the same-owner G8 trace ledger on the healthy `CompactLog`
B5 detector and its finite visible-prime family.

**Evidence:** formal Lean proof in
[`C1G8R3DiagonalRootEnergyLimitConstraint.lean`](../../ConnesWeilRH/Dev/C1G8R3DiagonalRootEnergyLimitConstraint.lean),
paired audit in
[`C1G8R3DiagonalRootEnergyLimitConstraintAudit.lean`](../../ConnesWeilRH/Dev/C1G8R3DiagonalRootEnergyLimitConstraintAudit.lean).
Focused build log: `1504_g8_diagonal_energy_constraint_try4.log`;
3962 jobs, zero `error:` lines, zero `sorryAx`, and three standard-axiom
audit terminators. The follow-up conditional limit theorem was checked in
`1505_g8_diagonal_limit_conditional_try4.log` (3962 jobs, zero `error:`
lines, zero `sorryAx`, four standard-axiom audit terminators).

The actual-cutoff selected detector-root columns converge pointwise to the
uncut same-owner columns by the strong source-compression limit. At every
finite cutoff, the diagonal trace is the sum of the squared column norms.
Combining these facts with finite-partial-sum lower bounds proves:

> If the real parts of the actual-cutoff diagonal traces converge to a finite
> real number, then the uncut same-owner detector-root columns are
> square-summable on the same source basis.

The converse is formal too: if the uncut same-owner root columns are
square-summable on that basis, the literal actual-cutoff diagonal trace
converges to the ordinary trace of the uncut root-energy operator. This
conditional limit uses the fixed-HS-pair strong-sandwich theorem and the
actual G8 source-compressed physical cutoff; it does not prove the required
square-sum estimate.

Together these results make the finite diagonal limit equivalent to
square-summability of the uncut same-owner root columns on the named basis.
The required estimate remains open. Consequently the two diagonal channel
limits, the total four-channel readback, the signed-remainder identity, the
endpoint/P2 signs, and the `qw` identification remain open. No route authority
or RH status changes.
