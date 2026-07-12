# Compact Bad-Space Evaluation-Span Lean Admission

Date: 2026-07-12

Status: accepted into Lean as a lower abstract consumer. This does not prove
the concrete CC20 evaluation-span containment or RH.

## Result

The compact remainder theorem already produced a finite-dimensional control
space on whose orthogonal complement `K-threshold*Id` is nonpositive. The new
consumer proves that any larger evaluation space inherits that sign on its
vanishing subspace:

```text
controlSpace <= evaluationSpace
  -> evaluationSpace^perp <= controlSpace^perp
  -> Re <x,(K-threshold*Id)x> <= 0.
```

Lean declarations:

```text
mem_controlSpace_orthogonal_of_le_evaluationSpace
exists_finiteDimensional_remainder_nonpositive_on_evaluationSpace
```

Source module:

```text
ConnesWeilRH/Source/CC20Concrete/CompactBadSpace.lean
```

Import-facing audit:

```text
ConnesWeilRH/Dev/CompactBadSpaceEvaluationAudit.lean
```

## Why the API is lower

The theorem consumes only:

```text
an inner-product space,
a compact continuous linear operator,
a positive threshold,
and a submodule containment.
```

It does not assume Weil positivity, source RH, detector coverage, a stored
remainder sign, or a finite-prime trace read-off. The conclusion is obtained
from the existing compactness theorem and order reversal of orthogonal
complements.

The remaining concrete producer is explicit:

```text
CC20 controlSpace <= span{evaluation kernels at 0,1/2,1}.
```

That containment must be proved from the concrete remainder operator. It is
not stored in the new API.

## Verification

The Windows source snapshot was copied one way to an isolated WSL2 ext4
verification directory because the persistent mirror contained unrelated
dirty changes.

Smallest owning build:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CC20Concrete.CompactBadSpace
```

Result: passed.

Import-facing build:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.CompactBadSpaceEvaluationAudit
```

Result: passed. Both declarations print only:

```text
propext
Classical.choice
Quot.sound
```

The full printed theorem type contains no project root, RH premise, or hidden
typeclass provider.

## Route judgment

```text
abstract compact bad-space consumer: accepted in Lean
same-object vanishing-space transport: accepted in Lean
concrete evaluation-span containment: open mathematical producer
active RH root removed: no
RH: unproved
```
