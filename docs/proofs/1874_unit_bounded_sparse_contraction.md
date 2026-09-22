# 1874 - Unit-bounded sparse contraction consumer

Date: 2026-09-23.

Status: Formally verified in Lean; conditional strict-contraction consumer.

The new theorem `strict_base_contraction_of_sparse_unitBounded_correction`
connects the unit-bounded source owner to the existing strict base
contraction theorem.  Every selected source basis test has zero-order
Schwartz seminorm at most `1`, while the sparse support has cardinality at
most `nodes.card`.  Therefore the remaining finite hypothesis is reduced to
the single scalar inequality

```text
2 * nodes.card * coeffBound < budget
```

with `budget <= 1/2`.  No coefficient bound is invented: the theorem keeps
the actual per-coefficient bound as an explicit premise.

Verification: WSL focused build `unit-bounded-contraction-1874a.log`;
successful footer for 3663 jobs, zero `error:` lines, zero `sorryAx`, and the
paired Audit declaration uses only `[propext, Classical.choice, Quot.sound]`.

This closes the selected basis-seminorm side of the base contraction gate.
The actual sparse coefficient estimate, detector-specific signed semi-local
positivity, and RH remain open.
