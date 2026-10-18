# 2835 Route B jet semantic anchor

This record anchors the Python evaluator formula to the Lean transition
semantics: the phase is `1/(1-x) - 1/x`, and the transition is
`exp(phase)/(1+exp(phase))` on the interior.

It does not yet prove equality of the Python interval arithmetic evaluator and
the Lean interval enclosure.
