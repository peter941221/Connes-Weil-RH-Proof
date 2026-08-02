# Proof 742: Gate Physical Leakage Trace Reduction

## Result

The result is structurally good but does not close Gate 3U.  Proof 742 removes
the already controlled first jet from the ordinary Gate trace and proves that
one complete physical leakage trace is the exact remaining uniform target.

Let

```text
J   = sourceInclusion,
B   = sourceBandProjection,
A_S = normalizedFiniteEulerInverse,
F_S = B A_S J,
W   = detectorOperator,
P_S = sourcePhysicalCoframeLeakage.
```

Lean first proves the operator identities

```text
Forward_S
  = J^dagger W F_S + F_S^dagger W J
  = sourceActualBandFiniteEulerSoninResponse_S,

Leakage_S
  = J^dagger W P_S
  = -sourceBandGramResponse_S.
```

Both operators have legal diagonal traces for every fixed finite prime-power
family.  The complete Gate owner therefore satisfies the exact ordinary-trace
identity

```text
Tr(Gate_S) = Tr(Forward_S) + Tr(Leakage_S).
```

This is the first direct alignment between Proof 733's forward/leakage
diagonal and the family-independent first-jet support estimate from Proofs
483--487.

## Uniform Reduction

Write

```text
H_lambda = sum_i ||sourceProlateHilbertSchmidtFactor(lambda,e_i)||^2,
P(g)     = (c-a)^2 seminorm_(0,0)(g)^2.
```

The existing first-jet theorem gives, for every finite family `S`,

```text
||Tr(Forward_S)|| <= (12 + 4 H_lambda) P(g).
```

Proof 742 consequently proves

```text
||Tr(Gate_S)||
  <= (12 + 4 H_lambda) P(g) + ||Tr(Leakage_S)||.
```

More strongly, with the owner, support interval, and Hilbert bases fixed,
Lean proves the existence-level equivalence

```text
(exists C, forall S, ||Tr(Gate_S)|| <= C)
  <->
(exists C, forall S, ||Tr(Leakage_S)|| <= C).
```

The reverse implication uses the displayed first-jet bound.  The forward
implication subtracts the same uniformly bounded first jet.  Thus no
family-dependent lower Euler factor is introduced in either direction.

## Structure

```text
complete Gate owner
        |
        +-- forward conjugate pair
        |       |
        |       +--> actual first jet
        |              |
        |              +--> uniform support bound already proved
        |
        +-- complete physical leakage
                |
                +--> -sourceBandGramResponse
                |
                +--> only remaining uniform ordinary-trace target
```

The active ordinary-trace bottom is now one signed scalar:

```text
Tr(J^dagger W sourcePhysicalCoframeLeakage_S).
```

Its outer, second-support, and prolate components must remain recombined until
compact-root support has been used.

## Guard

Proof 742 is an ordinary-trace reduction, not an ordered-prefix estimate.
In particular:

```text
- do not apply the first-jet ordinary-trace bound to every finite prefix;
- do not infer a uniform prefix bound from trace-class summability;
- do not split the physical leakage into three separately bounded branches;
- do not reuse the inverse-lower-factor endpoint bound as a uniform S bound.
```

Proof 741's full-kernel prefix remains a valid sufficient route to the Gate
trace, but Proof 742 shows that the stronger `sup_(S,N)` premise is not the
only possible route.  A direct uniform bound for the complete leakage trace
would now suffice.

That bound is not proved.  Gate 3U, the finite-S sign, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.

## Verification

The Windows source of truth was synchronized to the Ubuntu-24.04 WSL2 ext4
mirror.  The focused Proof 742 source and audit passed with `3386/3386` jobs,
the `CCM25Concrete` aggregate with `4010/4010`, and the full repository with
`4091/4091`.

All eight audited Proof 742 theorems use exactly
`[propext, Classical.choice, Quot.sound]`.  Static checks found no `sorry`,
`admit`, user axiom, heartbeat increase, recursion-limit increase, unsafe
declaration, new linter warning, or line over 100 characters in the new source
and audit.
