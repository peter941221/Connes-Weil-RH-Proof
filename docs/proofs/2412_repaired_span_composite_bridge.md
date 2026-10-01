# 2412 — repaired span-witness composite bridge

The 2411 artifact now contains the 39 ordered directed span witnesses.  This
ledger re-reads the composite charge using the sum of those witnesses, rather
than silently substituting the parent-reduction total.  It retains the old
parent reading beside the new span-sum reading so the accumulation convention
is auditable.

This is still an interface ledger: pointwise mathematical-term dominance,
Lean numeric import, and the producer gate remain false.  The symbolic
trapezoid theorem and the concrete span partition are the formal consumers;
the next missing certificate is the proof that each stored directed witness
dominates the corresponding mathematical span quantity.
