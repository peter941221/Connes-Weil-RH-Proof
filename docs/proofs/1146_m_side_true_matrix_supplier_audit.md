# Record 1146: M-side true-matrix supplier audit

Date: 2026-09-06.

Consumer: the healthy-`CompactLog`, B5-shaped q28 `hcert` consumer, namely
the concrete class-window branch that feeds the detector-specific semi-local
route. This record audits its missing input; it does not claim P2 or RH.

## Finding

The q28 Hbox/T-box chain still has an analytic true-data premise. In
`C1HboxRationalData`, `Hbox` is defined with two independent data matrices
`G_true` and `M_true`; the rational matrices `Q28.G` and `Q28.M` are committed
reference data and are not definitionally identified with either true matrix.
The q28 adapter
`q28_hbox_of_baseMomentBounds` therefore requires the separate premise

```lean
∀ i j, MLo_q28 i j ≤ M_true i j ∧ M_true i j ≤ MHi_q28 i j
```

and merely transports it into `Hbox`.

The exact source locations are:

- `C1HboxRationalData.lean`: `Hbox` quantifies over `M_true`, while `Q28.M`
  is only a concrete rational matrix.
- `C1Q28ClassGramIntervalTransfer.lean`: the two moment bounds produce the
  `G` enclosure; the theorem's `hM` argument remains an independent input.
- `C1ClassGramOwner.lean`: `hbox_of_classGramBounds` packages an already
  supplied `hM`; it does not prove it.
- `C1TboxPullthrough.lean`: `tbox_true_q28` consumes `Hbox` and does not
  construct `M_true`.

Conversely, the landed G2 certificate only proves the two concrete base
moment intervals. Its public consumer is the G-side theorem
`q28_baseMoment_bounds_of_concrete_certificate`; no declaration in that
certificate supplies the M-side interval or an equality
`gateMatrix w = Q28.M`.

## Status classification

This is a FORMAL interface audit, not a numerical conclusion. The M-side
true-table supplier remains OPEN. The existing central-moment envelope
theorems can be reused for the G-side moment owner, but they do not discharge
the independent `M_true` field. The external compact-window preprint also
cannot fill this slot without the convention, owner, and support bridges
listed in map record 004.

## Consequence for the route

G2 is now LANDED and removes the mechanical certificate blocker. It does not
turn the conditional Hbox chain into a window certificate. The next honest
M-side brick must construct the actual gate matrix for the selected owner and
prove its entrywise enclosure, or replace the entire ROOT-local certificate
with a proved theorem whose hypotheses apply to that same owner. A literal
reuse of `Q28.M` as `M_true` would be an unproved identification and is
rejected.

RH is not claimed.
