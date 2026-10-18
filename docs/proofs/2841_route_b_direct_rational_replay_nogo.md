# 2841 Route B direct rational-box replay probe withdrawn

This record is withdrawn. The original Lean probe accidentally fed the
exported Python denominator boxes into the reciprocal replay instead of the
denominator boxes computed by that replay. Its failed containment goal was
therefore an owner mismatch, not a mathematical no-go.

The concrete replay probe used the exact rationalized endpoint boxes exported
by record 2840 for cell 4096/order 4. It fed the phase boxes and the Python
initial exponential box into the existing Lean `RationalBox2744` exponential,
reciprocal, and product recurrences.

The corrected replay must compute `den_replay` from `exp_replay`, then feed
`den_replay` to the reciprocal recurrence. Record 2842 performs that corrected
arithmetic measurement and shows the target transition box contains the replay
box for every order-4 slot.
The corrected Lean theorem is `routeB_replay_transition_contained2841`.

Nonclaims: no statement about the soundness of the Lean recurrence, the
Python-to-Lean semantic bridge, ledger domination, SourceRH, or RH.
