# 1485 — R3 diagonal trace-limit energy constraint

**Consumer:** the same-owner G8 trace ledger on the healthy `CompactLog`
B5 detector and its finite visible-prime family.

**Evidence:** formal Lean proof in
[`C1G8R3DiagonalRootEnergyLimitConstraint.lean`](../../ConnesWeilRH/Dev/C1G8R3DiagonalRootEnergyLimitConstraint.lean),
paired audit in
[`C1G8R3DiagonalRootEnergyLimitConstraintAudit.lean`](../../ConnesWeilRH/Dev/C1G8R3DiagonalRootEnergyLimitConstraintAudit.lean).
Focused build log: `1504_g8_diagonal_energy_constraint_try4.log`;
3962 jobs, zero `error:` lines, zero `sorryAx`, and three standard-axiom
audit terminators.

The actual-cutoff selected detector-root columns converge pointwise to the
uncut same-owner columns by the strong source-compression limit. At every
finite cutoff, the diagonal trace is the sum of the squared column norms.
Combining these facts with finite-partial-sum lower bounds proves:

> If the real parts of the actual-cutoff diagonal traces converge to a finite
> real number, then the uncut same-owner detector-root columns are
> square-summable on the same source basis.

This is a necessary condition only. It proves neither the finite trace limit
nor the required square-sum estimate. Consequently the two diagonal channel
limits, the total four-channel readback, the signed-remainder identity, the
endpoint/P2 signs, and the `qw` identification remain open. No route authority
or RH status changes.
