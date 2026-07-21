# Proof 450: Signed finite bounds produce endpoint trace legality

## Result

Proof 448 treated endpoint trace legality and the uniform finite signed
diagonal bound as two separate premises.  Proof 449 showed that the endpoint
is self-adjoint.  Together these facts imply that the second premise already
produces the first one.

For real diagonal coefficients `a_i`, assume

```text
for every finite J, abs(sum_(i in J) a_i) <= C.
```

Filter `J` into the indices where `a_i >= 0` and `a_i < 0`.  Applying the
same bound to both filtered subsets gives

```text
sum_(i in J) abs(a_i) <= 2 C.
```

Mathlib's `summable_of_sum_le` then proves absolute summability.  Because the
endpoint is self-adjoint, every complex diagonal coefficient equals its real
part, so this is exactly the project's same-carrier
`PositiveTrace.IsTraceClassAlong` predicate.

Proof 447 identifies each finite endpoint sum with the negative of the finite
moving-flow integral.  Therefore Lean now proves

```text
uniform finite signed integral bound
  -> endpoint IsTraceClassAlong
  -> full complex ordinary-trace norm bound.
```

The canonical theorem has no independent trace-legality premise.  Its only
remaining analytic input is the uniform finite signed bound

```text
2 * (owner.supportRadius + log 3)
  * (1 + owner.supportRadius + log 3).
```

## Boundary

`IsTraceClassAlong` in this project records absolute summability of one named
Hilbert-basis diagonal.  Proof 450 does not claim a basis-independent Schatten
`S1` theorem.  It also does not prove the remaining finite signed bound,
Gate 3U, the finite-S sign, Burnol's identity, or RH.
