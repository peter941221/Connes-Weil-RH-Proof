# 1208 - Route 1 aggregate Bombieri socket

Date: 2026-09-06.

Status: formal producer interface. RH is not claimed.

The aggregate version keeps the same-owner identity

```text
qw(g) = finite quadratic term + signed high-shell tail
```

and asks directly for the signed lower bound `tail >= -finite quadratic
term`.  The finite Hermitian term is nonnegative by the existing Bombieri
matrix theorem, so this lower bound closes `qw(g) >= 0` without pretending
that the finite prefix itself is nonnegative.  This is the correct socket for
the orbit-controlled case: the negative finite prefix is allowed, but its
repayment by the tail is explicit.

Evidence: `BombieriQuadraticAggregateP2BridgeData` and
`qw_nonneg_of_bombieriQuadraticAggregateP2BridgeData` in
`C1BombieriP2Bridge`, audited by its paired audit module.  The producer field
is an analytic signed-tail obligation, not a stored conclusion. Focused
acceptance build: `p2-aggregate-socket.log`, footer `Build completed
successfully (3665 jobs)`, zero `error:` lines, standard three axioms, and no
`sorryAx`.

The socket is now wired through the healthy-detector wrapper and the pinned
same-detector `SourceRH` consumer in `C1P2BilateralProfileExit`; the latter
still requires the aggregate producer for every hypothetical right-hand zero.
The integration build `p2-aggregate-exit-integration.log` also completed
successfully (3779 jobs), with the same axiom and `sorryAx` audit.
The repayment-corollary rebuild `p2-aggregate-repayment-corollary.log`
completed successfully (3779 jobs) with the same audit.

The paired formal consequence
`spectralTail_re_ge_xiMultiplicity_of_bombieriQuadraticAggregateP2BridgeData`
connects the socket to the orbit obstruction: once the selected finite prefix
is at most `-xiMultiplicity(rho)`, every successful aggregate producer must
repay at least that amount in its same-owner tail.
