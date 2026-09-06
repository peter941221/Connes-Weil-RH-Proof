# Record 1147 - Line-B same-owner P2 bridge contract

Date: 2026-09-06.

Status: FORMAL interface brick. It proves no new analytic sign and does not
claim RH. Consumer: the healthy `CompactLog`, B5-shaped detector-specific
route.

## Landed contract

`ConnesWeilRH/Dev/C1BombieriP2Bridge.lean` defines
`BombieriP2BridgeData g`. Its fields contain the finite Bombieri eigen-relation,
the reciprocal identity, a nonzero coefficient vector, and the explicit
same-owner equality

```text
qw(g) = lam * bombieriWMass(gamma,z).
```

The equality is producer data, not a stored positivity conclusion. The
existing Bombieri theorem `lambda_mass_eq_nonneg` then gives a nonnegative
real for the right-hand side, so
`qw_nonneg_of_bombieriP2BridgeData` proves `0 <= qw(g)`.

The theorem
`sourceRH_of_right_bombieriP2BridgeData` quantifies this contract over every
right-oriented off-line zero, packages the healthy detector on the same `g`,
and feeds the result to the already-formal `SourceRH` contradiction consumer.

## Remaining Line-B obligation

No current declaration constructs `BombieriP2BridgeData` for the orbit
detector. In particular, the repository still lacks the Bombieri-to-
`CompactLog`/`qw` owner equality and the finite eigensystem data for each
zero. The bridge therefore narrows Line B to a concrete producer target but
does not close P2.

## Verification

The owning and audit modules build with the resource-aware runner:
`Build completed successfully (3660 jobs)`, zero `error:` lines. All four
audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` occurs.
