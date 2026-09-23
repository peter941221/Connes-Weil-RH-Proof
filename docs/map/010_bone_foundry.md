# 010 — Bone foundry: deriving obligations from the obstruction ledger

Status: reusable analysis method; subordinate to [003] and [006].

The foundry turns a failed proof idea into the smallest owner-correct theorem
that could actually remove the obstruction.

## Procedure

1. Name the live consumer and expand its missing premise.
2. Identify the first mathematical, rather than bookkeeping, obstruction.
3. Hold owner, support, finite prime set, and quantifiers fixed.
4. Generate candidate lemmas that imply the missing premise.
5. Attack the cheapest necessary consequence first.
6. If it fails, record a scoped no-go; if it survives, prove the smallest
   quantitative brick and wire it into the consumer.

The output must be a theorem-shaped obligation, not a topic such as “study
prolate operators” or “improve decay”.

## Required bone card

```text
consumer:
committed owner:
missing statement:
candidate lemma:
explicit constants / quantifiers:
cheap falsifier:
success rewiring:
stop rule:
```

## Lessons from the original foundry run

The historical scale-covariant bridge was screened dead because its scaling,
support, and sign requirements could not coexist on the committed owner. The
useful residue was the minimal wall:

```text
selected detector already gives qw(g) < 0
the only missing contradiction input is same-detector qw(g) >= 0
```

That residue is now the canonical graph in this directory's README. Future
foundry runs must end closer to that line.

## Acceptance and rejection

Accept a bone only when it removes a named premise on the actual owner with a
checked margin. Reject it when a theorem, exact counterexample, or invariant
contradicts a required hypothesis. “Difficult”, “no library theorem found”,
or “numerically inconclusive” is not a no-go.

Conditional exits, coordinate isomorphisms, and new data structures are not
bones unless their introduction simultaneously proves a previously open
field. This is the operational meaning of the core-progress gate.
