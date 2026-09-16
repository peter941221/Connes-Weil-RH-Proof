# 1530 — Independent outer-pair Hilbert–Schmidt split is blocked

Date: 2026-09-17

The consumer in record 1529 is formally correct, but its premise is too
strong for the root-completed leakage leg that occurs in the actual R3
assembly.  The existing theorem
`sourceRootCompletedRightCommutatorLeftLeg_not_hilbertSchmidt` proves, from a
nonzero Laplace value and a separated orthonormal translation orbit, that the
unit-scale operator

```text
C E (I - Q) E
```

has no summable squared outputs on any Hilbert basis.  The companion theorem
`sourceRootCompletedBandRoot_not_hilbertSchmidt` proves the same obstruction
for the full band-root operator: the already Hilbert–Schmidt range leg tends to
zero on that orbit, while the leakage leg stays uniformly bounded below.

Therefore the raw radial-leakage premise in record 1529 cannot be promoted to
an unconditional estimate for the actual root-completed branch.  This does
not invalidate the algebraic identities or the consumer; it rejects the
strategy of estimating the outer pair in isolation.  The surviving route must
keep the signed outer/remainder/common-right cancellation intact, or introduce
a new compactifying factor before the leakage is read back.  WO-B remains
OPEN, with the independent outer-pair estimate explicitly marked NO-GO under
the present root ordering.

Formal evidence: `ConnesWeilRH.Dev.C1G8R3HilbertSchmidtOrthonormalObstruction`.
