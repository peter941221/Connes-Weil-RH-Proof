# 1207 - Route 1 spectral tail repayment obligation

Date: 2026-09-06.

Status: formal necessary condition for the direct producer. RH is not claimed.

The exact same-owner split is

```text
qw(g) = finite spectral prefix + high-shell spectral tail.
```

If orbit interpolation controls the selected finite prefix by
`prefix ≤ -xiMultiplicity(rho)` and the desired direct P2 sign supplies
`qw(g) ≥ 0`, then necessarily

```text
xiMultiplicity(rho) ≤ high-shell-tail(g).
```

This is now a formal theorem on the same `CompactLog` owner. It identifies the
next signed analytic target for the Bombieri/trace route: the tail cannot merely
be small or bounded in norm; it must carry a positive lower bound large enough
to repay the negative orbit anchor. No numerical claim or RH conclusion is
made.

Evidence: `spectralTail_re_ge_xiMultiplicity_of_qw_nonneg_and_prefix_anchor`
in `C1BombieriP2Bridge`, audited by its paired audit module. Focused acceptance
build: `p2-spectral-tail-repayment.log`, footer `Build completed successfully
(3665 jobs)`, zero `error:` lines, standard three axioms, and no `sorryAx`.
