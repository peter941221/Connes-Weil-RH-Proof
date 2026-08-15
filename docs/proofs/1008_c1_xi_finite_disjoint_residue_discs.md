# 1008 Finite Disjoint Xi Residue Discs And Factor Owners

Date: 2026-08-13

## Result

The finite local-residue geometry for the Gate 2 xi contour now closes
axiom-clean at two strengths. For every finite family
`S : Finset sourceNontrivialZeroSet`, the historical theorem

```text
exists_finite_pairwiseDisjoint_xiResidueClosedBalls
```

constructs radii `R` such that:

```text
rho in S -> 0 < R rho
the closed balls closedBall rho R rho are pairwise disjoint
integral over C(rho, R rho) xiContourKernel
  = -2*pi*i*spectralTerm F rho
```

The height-truncated corollary
`exists_finiteHeight_pairwiseDisjoint_xiResidueClosedBalls` supplies the same
data for `finiteHeightZeros T`.

The stronger current theorem is

```text
exists_finite_pairwiseDisjoint_xiFiniteFactorCircleData
```

It retains, for each disc, one outer finite-factor cofactor, its analytic and
nonzero certificate, closed-disc containment in the factorization ball, and
explicit exclusion of every other point of that outer divisor support. The
finite-family T2 argument proves only pairwise disjointness; it does not stand
in for this ambient-support exclusion.

## Construction

```text
source-zero subtype family S
        |
        v
complex-coordinate image Z
        |
        +-- finite T2 separation --> pairwise-disjoint open U(rho)
        |
        +-- local cofactor --> safe residue radius Rmax(rho)
        |
        v
R(rho) = min(Rmax(rho)/2, eps(rho)/2)
        |
        +-- closedBall(rho, R) subset ball(rho, eps) subset U(rho)
        +-- R(rho) <= Rmax(rho)
        v
disjoint closed residue discs with exact local residues
and retained outer finite-factor owners
```

The coordinate image is essential.  `sourceNontrivialZeroSet` is a subtype
that retains the source spectral owner and analytic multiplicity, whereas
Hausdorff separation applies to the underlying complex coordinates.  The
proof uses `Subtype.ext` only after coordinate equality is obtained, so no
distinct-zero assumption is smuggled in.

## Evidence

The verification command was:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Dev.C1XiFiniteResidueProbe
```

It completed successfully with `3524` jobs. Focused `#print axioms` for both
historical declarations reported only:

```text
[propext, Classical.choice, Quot.sound]
```

The topology source used by the proof is mathlib
`Topology/Separation/Hausdorff.lean`, theorem `Set.Finite.t2_separation`.
The closed-ball shrink is mathlib
`Topology/MetricSpace/Pseudo/Defs.lean`, theorem `closedBall_subset_ball`.

The strengthened factor-owned construction was verified by:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.C1XiFiniteFactorCircleProbe

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.C1XiFiniteFactorResidueProbe
```

Those isolated ext4 builds completed `3528` and `3529` jobs. The focused
audits for every new declaration reported only `[propext, Classical.choice,
Quot.sound]`.

## Boundary

This closes geometry and local residue ownership, not the finite
punctured-rectangle Cauchy theorem. The next common-contour layer must use one
outer finite-factor owner and exclude its entire divisor support from the
boundary; a generic principal-circle theorem now reads that boundary as the
finite sum over all enclosed support points. It still needs a support-to-source
reindexing theorem before it can be called a finite spectral partial sum.

Mathlib's
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`
requires continuity on the whole closed rectangle, while
`xiContourKernel` has poles at the xi zeros.  The next layer must either
prove a finite-puncture boundary theorem or remove all finite principal parts
before invoking the existing rectangle theorem.

This remains consistent with Burnol's contour architecture:

```text
Jean-Francois Burnol, The Explicit Formula in Simple Terms,
https://arxiv.org/pdf/math/9810169, pp. 3-4.
```

No explicit-formula equality and no RH claim is made here.
