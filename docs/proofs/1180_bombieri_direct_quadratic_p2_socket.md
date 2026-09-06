# 1180 — Direct finite-quadratic P2 socket

Date: 2026-09-06

## Result

`BombieriQuadraticP2BridgeData g` packages finite data together with the
explicit same-owner equality

```text
qw g = Re (star w ⬝ᵥ (H(Γ;t) *ᵥ w)).
```

Records 1178–1179 prove the right-hand side is nonnegative for `t > 0`, so the
new consumers `qw_nonneg_of_bombieriQuadraticP2BridgeData` and
`sourceRH_of_right_bombieriQuadraticP2BridgeData` are fully formal.  The same
contract is also wired into the P2 bilateral-profile aggregate and exit.

## Boundary

The equality field is a producer obligation, not a stored conclusion.  No
detector-specific construction of this data, no new support estimate, and no
RH conclusion is claimed.

## Evidence

The focused P2 bridge/exit build completed in 3778 jobs with no `error:` lines
or `sorryAx`; audits use only `[propext, Classical.choice, Quot.sound]`.
