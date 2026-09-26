# 004 — Shared route contracts

These documents and interfaces are shared by all admissible routes.

Core contracts:

- `docs/map/README.md`: binding dependency graph and route authority
- `docs/map/003_b1_b5_minimal_exit_route_selection.md`: healthy CompactLog B5
  owner and minimal exit
- `docs/map/090_finite_index_pinning_and_frozen_prime_domain.md`: finite owner
  and prime-domain discipline
- `docs/map/106_centered_signed_moments_joint_tail_execution.md`: same-owner
  determinant/tail quantifiers for Route B
- `RH_MAINLINE_FREEZE.md`: frozen namespaces and mainline checks

Invariant:

```text
same owner -> same support -> same visible-prime set
           -> same detector -> same consumer
```

A conditional certificate, coordinate transport, generic tail lemma, or
interface-only theorem is infrastructure unless it removes a named premise of
`qw(g) >= 0` for the selected owner.