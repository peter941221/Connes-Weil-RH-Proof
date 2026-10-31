Record 3251: staged phase-power enclosure API

Status: verified structural bridge; no new numerical sign claim.

The Route A phase evaluator represents a 512th power by nine repeated
squarings. Expanding the 26th-order Taylor rectangle and all nine products in
one `norm_num` call causes simplifier-step exhaustion. That is a
proof-engineering failure, not evidence for or against the mathematical sign.

The new module separates each layer into two objects:

```text
phase Taylor rectangle
        |
        v
mechanical square rectangle = inner
        |
        |  local endpoint inequalities
        v
checked coarse rectangle   = outer
```

`complexRectPowSq_staged_mem3251` proves the repeated-squaring induction for
an arbitrary sequence of boxes. The caller supplies the local enclosure proof
for each layer, while the theorem supplies only the algebraic induction and
the exponent bookkeeping.

`complexRectPowSq_staged_step_of_subset3251` adapts a family-specific endpoint
lemma: once an outer box contains the mechanical product rectangle, it also
contains the actual squared complex value.

The companion audit prints the axioms for all three exported theorems. The
required WSL2 Lean 4.30.0 audit result is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

This record does not prove `reHi < 0`, the finite aggregate, the full-line
tail, `producer_go`, `SourceRH`, or the Riemann Hypothesis.
