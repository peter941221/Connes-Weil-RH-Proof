# 1198 - Route 1 visible-profile residual identity

Date: 2026-09-06.

Status: formal identity brick.  RH is not claimed.

Consumer: the healthy `CompactLog` B5 aggregate owner
`P2BilateralProfileRangeWitness`.

For two triple-vanishing owners `g` and `W`, assume their bilateral profiles
agree on the union of their visible-prime log points.  The formal theorem
`p2AggregateValue_sub_eq_archimedean_sub_of_visibleProfileMatch` proves

```text
p2AggregateValue g - p2AggregateValue W
  = archimedeanTerm g.convolutionSquare
      - archimedeanTerm W.convolutionSquare.
```

The proof factors through the exact defect identity and the existing
visible-point profile matching theorem, which cancels the entire finite-prime
contribution.

## Consequence

This is the first precise detector-specific residual target for route 1.  A
reference owner can only help if the pinned detector satisfies a genuine
visible-profile matching or signed residual relation.  Mellin-node
interpolation alone does not provide that relation.  The theorem supplies no
sign and does not identify a reference owner; it is an exact cancellation
interface only.

Evidence: `ConnesWeilRH/Dev/C1P2BilateralProfile.lean` and its paired audit.
Focused build `p2-visible-residual-3.log` completed successfully with standard
axioms only and zero `sorryAx`.
