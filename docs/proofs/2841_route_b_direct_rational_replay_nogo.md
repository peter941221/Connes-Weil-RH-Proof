# 2841 Route B direct rational-box replay no-go

The concrete replay probe used the exact rationalized endpoint boxes exported
by record 2840 for cell 4096/order 4. It fed the phase boxes and the Python
initial exponential box into the existing Lean `RationalBox2744` exponential,
reciprocal, and product recurrences.

The final replay box did not fit inside the exported Python transition box.
This is a scoped no-go for the direct independent-box replay, not a failure of
the derivative recurrence. The mechanism is dependency loss: each stage box
forgets that its slots came from the same interval and the same previous
expressions, so repeated multiplication and reciprocal operations widen the
box. The tight Python box therefore cannot be recovered by independently
replaying its rounded stage endpoints.

The probe was removed after recording the failed containment goal. The next
admissible move is to preserve correlation (for example, replay exact stored
operands with a structured jet object) or to inflate the target boxes with a
proved dependency-loss allowance. Directly weakening the final charge without
pricing that inflation is not valid.

Nonclaims: no statement about the soundness of the Lean recurrence, the
Python-to-Lean semantic bridge, ledger domination, SourceRH, or RH.
