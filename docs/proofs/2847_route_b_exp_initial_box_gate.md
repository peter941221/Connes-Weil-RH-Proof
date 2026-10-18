# 2847 Route B exponential initial-box gate

The Lean phase bridge is available on cell 4096. The existing analytic Lean
initial bound for the exponential stage is the broad box `[0,1]`. Replaying
order 4 with that sound initial box was measured against the Python tight
transition boxes, and all five transition slots fail target containment.

This is a pricing gate: it does not reject the recurrence. It shows that the
generic `[0,1]` initial proof cannot be consumed by the current tight charge
ledger. The next admissible move is a Lean-proved tighter exponential bound on
the registered phase interval, or an explicit re-pricing of the wider replay.
The Python tight exp endpoint cannot be used as a proof premise by itself.
