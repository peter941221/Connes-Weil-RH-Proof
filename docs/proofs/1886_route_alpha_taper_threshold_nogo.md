# 1886 - Route-alpha taper threshold no-go

Date: 2026-09-23.

Status: Formally verified in Lean; rules out the current real-part strict
budget on intervals of length at most one.

The theorem
`routeAlpha_realPart_gap_budget_impossible_of_interval_length_le_one`
combines the previous records on the same route-alpha owner:

```text
alpha <= b - a                         (zero-node Gram upper ceiling)
1 <= card(index)
1 <= ||healthyDetectorNodeTarget rho||
1 <= windowTaperRealPartBound
2 * card(index) * ||target|| * bound < alpha   (strict budget)
```

The hypotheses imply `alpha > 2`, while `b - a <= 1` and the Gram ceiling
imply `alpha <= 1`, yielding a contradiction.

This is a scoped NO-GO for the current route-alpha real-part taper consumer on
narrow intervals.  It does not refute the detector-specific B5 route, does
not prove RH, and does not rule out a different owner or a different signed
phase/physical-kernel producer.  The next live producer target is therefore
the C3' same-owner signed budget rather than this scalar taper threshold.

Verification: WSL focused build `route-alpha-threshold-nogo-1886d.log`;
successful footer for 3686 jobs, zero `error:` lines, zero `sorryAx`, and the
paired Audit declaration uses only `[propext, Classical.choice, Quot.sound]`.
