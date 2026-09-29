# 2155 — Minimal-height off-line zero does not close the healthy owner

Date: 2026-09-29.

Status: EXACT SCOPED NO-GO for a proposed owner truncation. No RH claim.

## Consumer and proposed premise removal

The consumer is the selected healthy `CompactLog` detector's same-owner
semi-local sign, followed by `SourceRH`. The exact correction owner is
`healthyKillSet rho N routeNodes` in
`ConnesWeilRH/Dev/C1ExplicitHealthyCorrectionBudget.lean`:

```
sourceNontrivialZerosInClosedBallFinset rho R_N ∪ routeNodes,
R_N = 2^(N+1) + 2 + dist(2,rho),  N >= 0.
```

The sketched shortcut chooses an off-line zero `rho=beta+i gamma` of least
positive ordinate and proposes to treat every other zero in that ball as
a critical-line zero. That would replace the complete zero owner by a
line-only residual and perhaps avoid exact pinning of all nodes.

## Exact obstruction

For `gamma>0`,

```
R_N = 2^(N+1) + 2 + sqrt((2-beta)^2 + gamma^2)
    >= gamma + 2^(N+1) + 2 > gamma.
```

Thus the closed ball centred at `rho` extends above ordinate
`gamma+R_N >= 2 gamma + 2^(N+1)+2`. For every `0<delta<R_N`, the point
`rho+i delta` is in the ball and has ordinate strictly above `gamma`.
The minimal-height assumption constrains off-line zeros *below* `gamma`;
it says nothing about such a point. In an abstract source-zero model,
adjoining a second off-line zero at `rho+i delta` preserves minimality and
places that new zero inside the exact owner. This is a logical
countermodel to the proposed inference, not a claim that zeta has such a
zero. The same argument applies at every `N>=0` and becomes worse as `N`
grows.

## Decision

`MINIMAL-HEIGHT-OWNER-TRUNCATION-NO-GO`: minimal ordinate alone cannot
replace the complete closed-ball owner by the first off-line orbit plus
critical-line zeros. Reopen only with an additional theorem controlling
the above-`gamma` portion of the exact ball, or a different spectral
prefix/tail geometry whose owner ends at the minimal ordinate. No
quantifier, owner, or route ruling changes. Evidence level: exact algebra
read against the committed Lean definition; no new Lean theorem or build.

The record-2050 mechanism intake fired `TRUNC` and `STAB` on the words
"truncation" and "pinning." The TRUNC exhibit (record 2044) reinforces
the requirement to retain the complete owner; this record proves that
dropping its upper part is unjustified. The STAB exhibit concerns a
different parameter-stability issue and adds no hypothesis here. These
fires are triage, not independent no-go evidence.
