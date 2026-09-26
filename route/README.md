# Route topology

This directory is a navigation layer for proof routes. It does not replace the
authoritative records in `docs/map/`, and it does not promote a candidate to a
producer theorem.

Authority order:

```text
route/README.md
    |
    +-- navigation and current status only
    |
    v
docs/map/README.md
    |
    +-- binding route decisions and active obligations
    |
    v
Lean source + paired audits + proof records
```

Current topology:

```text
001_binding_b5_compactlog/
    Healthy CompactLog B5-shaped mainline
    Status: binding producer route; detector-specific positivity OPEN

002_route_a_signed_kernel/
    Same-owner signed physical-kernel / C3' campaign
    Status: active, current selector has a scoped final-sign no-go

003_route_b_fourpoint_span/
    Same-owner four-point SPAN / determinant + joint-tail campaign
    Status: project candidate; fast survival screen required

004_shared_contracts/
    SourceRH consumer, owner rules, quantifier rules, audit gates
    Status: shared infrastructure, not a producer by itself

099_frozen_or_audit_only/
    Normalized ROOT socket, retired shortcuts, and disconnected branches
    Status: do not start new producer work here
```

The single RH core obligation is:

```text
hypothetical off-line zero
    -> selected healthy CompactLog detector g with qw(g) < 0
    -> prove qw(g) >= 0 for that same owner
    -> SourceRH
    -> Mathlib RiemannHypothesis
```

A route is not considered alive merely because it has Lean interfaces or a
numerical candidate. It must preserve the same owner, support, visible-prime
set, detector, and quantifiers through the final consumer.

Read next:

1. `001_binding_b5_compactlog/README.md`
2. `003_route_b_fourpoint_span/README.md`
3. `004_shared_contracts/README.md`
4. `docs/map/README.md` for binding decisions