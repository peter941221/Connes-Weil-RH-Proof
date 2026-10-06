# Record 2592: entrywise defect-bound interface

Date: 2026-10-05

Status: LEAN-ENTRYWISE-DEFECT-BOUND-INTERFACE-PASS.

This is the correct shape for importing the 2338 numerical certificate. The
complex defect matrix remains an analytic object `D`. A separate `NNReal`
matrix supplies nonnegative upper bounds `B[i,j]` with

    ||D[i,j]|| <= B[i,j]
    sum_j B[i,j] < 1.

The Lean theorem converts these facts into an operator-norm defect below one,
then proves that the captured owner realizes all 30 interpolation targets.
The upper-bound matrix is never substituted for the complex defect matrix.

```text
analytic complex defect D
          |
          | entrywise modulus bounds
          v
nonnegative NNReal bounds B
          |
          | every row sum < 1
          v
operator norm of D < 1
          |
          v
captured owner realizes targets
```

## Evidence

- `ConnesWeilRH/Dev/C1RouteACorrectionOperatorNorm2590.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionEntrywiseDefect2592.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionEntrywiseDefect2592Audit.lean`
- `results/2592_entrywise_defect_validation.json`

The clean Linux-side build and axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`.

## Boundary

The numerical 2338 payload is not imported yet. In particular, Lean still lacks
proofs that the 900 analytic matrix intervals enclose the actual integrals, that
the candidate inverse and analytic matrix produce the declared complex defect,
and that the exported row bounds are valid. Membership, owner transfer,
producer GO, and RH remain open.

The next target is a generated rational `NNReal` bound payload plus the
actual-operator equality/enclosure theorem.