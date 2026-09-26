# 000 - RH mainline

This is the parent node for every admissible route in this repository.

```text
000 RH mainline
|
+-- 001 shared contracts
|
+-- 002 B5 CompactLog producer
|   |
|   +-- 001 Route A: signed physical kernel
|   |
|   +-- 002 Route B: four-point SPAN
|
+-- 003 Route C: trace-formula positivity candidate
|
+-- 004 A/B common-bottleneck audit
|
+-- 099 frozen or audit-only branches
|
+-- final consumer: SourceRH -> Mathlib RiemannHypothesis
```

The parent goal is:

```text
hypothetical off-line zero
    -> healthy selected CompactLog detector g with qw(g) < 0
    -> prove qw(g) >= 0 for that same owner
    -> SourceRH
    -> Mathlib RiemannHypothesis
```

The child directories are subroutes of this goal. They are not independent
RH proofs. A child route survives only if it preserves the same owner,
support, visible-prime set, detector, and quantifiers through the consumer.

Authority remains in `docs/map/`; this directory is the navigational topology.

Read the binding parent first:

1. `002_b5_compactlog/README.md`
2. `002_b5_compactlog/001_route_a_signed_kernel/README.md`
3. `002_b5_compactlog/002_route_b_fourpoint_span/README.md`
4. `../README.md`
