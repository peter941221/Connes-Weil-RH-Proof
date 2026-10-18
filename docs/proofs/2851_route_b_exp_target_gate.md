# 2851 Route B exponential target gate

The tight `[1/32,1/4]` initial box is Lean-proved, but replaying from that box
does not fit the existing Python exp-stage targets: all eight order-0 through
order-7 slots fail target containment. The target artifact was generated from
a tighter Python initial interval and cannot be consumed unchanged.

This is a pricing/interface failure, not a recurrence failure. The next move
is to recompute the downstream exp targets with the proved initial box, or
prove a tighter initial box and re-run the containment gate.
