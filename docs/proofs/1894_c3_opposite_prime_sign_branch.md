# 1894 - C3' opposite-prime-sign determinant branch

Date: 2026-09-23.

Status: Formally verified in Lean; this is a conditional same-owner B5
consumer, not a positivity theorem and not an RH proof.

The carrier phase owner now has the following sign branch:

```text
P_u = carrierSquarePrimePhaseSum gamma u <= 0
0 <= P_v = carrierSquarePrimePhaseSum gamma v
-----------------------------------------------
carrierPrimeDeterminantPhase gamma u v <= 0
```

The proof is direct from `P_u * P_v <= 0` and the nonnegative square of the
directed pair phase sum.  It preserves the actual visible-prime owners and
does not replace them with an absolute majorant or a frozen prime set.

There is now a fully compatible sign branch.  If the two Archimedean
diagonal phase terms satisfy `A_u <= 0 <= A_v`, the two prime diagonal phase
sums satisfy `P_u <= 0 <= P_v`, and the directed Archimedean/prime product is
nonnegative, then:

```text
A_u * A_v - A_pair^2 <= 0
A_u * P_v + A_v * P_u - 2 * A_pair * P_pair <= 0
P_u * P_v - P_pair^2 <= 0
```

Thus the complete two-span determinant budget is nonpositive with no separate
Archimedean or mixed-margin premise.  With the existing positive-BB
hypothesis, the optimal two-span gate q-form is therefore nonpositive and
can feed the existing `orbitWindowSemiLocalGate` consumer.

The remaining analytic obligation is now explicit: establish these
detector-specific sign conditions for the selected carrier, especially the
opposite signs and the directed pair product.  No sign is inferred from the
formal branch alone.

Verification: WSL focused build
`c3-sign-branch-1894c.log`; successful footer for 3788 jobs, zero `error:`
lines, zero `sorryAx`, and the paired Audit declarations use only
`[propext, Classical.choice, Quot.sound]`.
