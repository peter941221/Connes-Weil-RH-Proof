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

The mixed determinant has a separate compatible sign branch when both
Archimedean diagonal phase terms are nonpositive, both prime diagonal phase
sums are nonnegative, and the directed Archimedean/prime product is
nonnegative.  Under an independent nonpositive Archimedean determinant and
the opposite-prime-sign condition, the complete two-span determinant budget
is nonpositive.  With the existing positive-BB hypothesis, the optimal
two-span gate q-form is therefore nonpositive and can feed the existing
`orbitWindowSemiLocalGate` consumer.

The remaining analytic obligations are explicit: establish the required
detector-specific sign conditions and the Archimedean determinant bound for
the selected carrier.  No sign is inferred from the formal branch alone.

Verification: WSL focused build
`c3-sign-branch-1894c.log`; successful footer for 3788 jobs, zero `error:`
lines, zero `sorryAx`, and the paired Audit declarations use only
`[propext, Classical.choice, Quot.sound]`.
