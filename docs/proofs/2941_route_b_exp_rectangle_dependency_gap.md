# 2941 Route B exponential rectangle dependency gap

The subcell stage artifact stores an `a = 2t/(1-t^2)` rectangle and an
`exp(2a)` rectangle.  Replaying `exp` on the independently extracted `a`
rectangle produces a wider interval than the stored target rectangle.  The
stored target is therefore not justified by a plain rectangular containment
chain; it relies on correlation retained inside the original interval
evaluation.

Decision: do not consume the stored `a` rectangle as an independent box for
the exponential stage.  The next formal design must either preserve the
dependency (a Taylor/affine form) or widen and re-price the exponential
rectangle.  This is an interval-method gap, not a Route-B mathematical
failure and not a Producer GO.

