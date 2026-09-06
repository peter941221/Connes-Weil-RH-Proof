# 1209 - Route 1 aggregate versus fourth-order tail no-go

Date: 2026-09-06.

Status: formal no-go for a proposed producer combination. RH is not claimed.

The orbit-controlled prefix can be at most
`-xiMultiplicity(rho)`.  The existing fourth-order Yoshida estimate makes
the corresponding high-shell norm tail smaller than that multiplicity.  The
exact shell split therefore gives `qw(g) < 0`.  Consequently it cannot be
combined with `BombieriQuadraticAggregateP2BridgeData`, whose signed-tail
socket gives `qw(g) >= 0`.

This does not reject the aggregate architecture.  It rejects only the
combination of that architecture with the current absolute-value fourth-order
tail estimate at the same orbit cutoff.  The remaining target must be a
genuine signed trace/tail lower bound, or a different aggregate decomposition.

Evidence: `not_bombieriQuadraticAggregateP2BridgeData_of_fourthOrderTail_and_prefix`
in `C1BombieriP2Bridge`, with its paired axiom audit. Focused acceptance
build: `p2-aggregate-fourth-order-nogo.log`, footer `Build completed
successfully (3665 jobs)`, zero `error:` lines, standard three axioms, and no
`sorryAx`.
The downstream Exit regression `p2-aggregate-fourth-order-regression.log`
also completed successfully (3779 jobs) and re-audited the pinned aggregate
`SourceRH` consumer.
