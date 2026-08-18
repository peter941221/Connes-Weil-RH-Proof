# 1030 - Lane R constrained Gamma_R prefix owner

Date: 2026-08-19.

## Verdict

The finite Gamma_R prefix selected by the numerical budget screen is now a
named Lean owner.  It is attached to the exact shifted profile tail from the
same summed-kernel owner, and its real-valued readback is explicit.

This closes an ownership and convergence interface.  It does not prove the
uniform `N = 21` constrained-prefix inequality, universal Lane R, or RH.

## Lean owner

`Dev/C1XiCenterTwoGammaConstrainedPrefix.lean` defines:

```text
laneRPrefixLength = 21
gammaRArchProfilePrefix F N
  = sum over n in range N of gammaRArchProfileIntegral F n
gammaRArchFinitePrefixValue F N
  = constant(F) + Re(gammaRArchProfilePrefix F N)
laneRFinitePrefixQuadraticValue g
  = gammaRArchFinitePrefixValue (g.convolutionSquare) 21
```

The exact same-owner identity is

```text
archimedeanTerm F
  = gammaRArchFinitePrefixValue F N
  + Re(gammaRArchProfileTail F N)
```

The finite sum is also read back through real profile integrals, so the
object used by a future sign proof is a real quadratic value rather than an
unidentified complex remainder.

## Constraint interface

`laneRTripleVanishing` is the healthy three-node condition at `0`, `1/2`, and
`1`.  `laneRPrimeFreeSquare` is the actual support condition in
`(-log 2, log 2)`, and `laneRConstrainedPrimeFree` combines the two.

The D3 root proves the triple-vanishing interface exactly, and its existing
support transport proves the prime-free interface under an explicit base
support hypothesis.  On this owner, the existing same-owner readback gives

```text
qw g = -archimedeanTerm (g.convolutionSquare)
```

without dropping or reassigning the prime terms.

## What is actually closed

Because `gammaRArchProfileTail F N -> 0`, a strictly negative complete
`archimedeanTerm F` implies that some test-dependent finite prefix is strictly
negative.  The theorem
`exists_gammaRArchFinitePrefixValue_lt_zero_of_archimedeanTerm_neg` proves
that statement constructively from the exact decomposition.

It does not imply that the witnessing length is `21`, nor that one length
works uniformly over the constrained test space.  The remaining producer is
therefore the fixed-length statement named by
`laneRConstrainedPrefixSignTarget` (or a coupled quadratic tail estimate that
avoids this absolute-prefix budget).

## Verification

WSL2 ext4 verification used the repository's shared Lean lock:

```text
Build commands:
lake build ConnesWeilRH.Dev.C1XiCenterTwoGammaConstrainedPrefix
lake build ConnesWeilRH.Dev.C1XiCenterTwoGammaConstrainedPrefixProbe
```

The owner and import-facing probe completed at 3607 and 3608 jobs.  Every
audited declaration reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, project axiom, numerical-to-Lean transfer, universal
Lane R theorem, or RH conclusion in this batch.
