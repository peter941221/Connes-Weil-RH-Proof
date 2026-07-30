# Proof 579: raw local Douglas bridge

## Result

This batch closes the local transfer step for bone 1.  It does not prove the
raw physical domination premise itself.

For the source Sonin carrier, the exact cofactor identities are:

```text
localRawDefect
  = (-rawIntertwiningDefect) * reverseTransition

localRawDefect^dagger
  = -(reverseTransition^dagger * rawPhysicalFourTermRow)
```

The reverse transition is contractive.  Therefore an assumed packed physical
Douglas estimate

```text
||rawPhysicalFourTermRow x||^2
  <= bound^2 * ||leftCoDefect x||^2
```

transfers to the local raw defect with the same `bound`.

## Signed gap

The local raw defect is already split by the existing Julia decomposition:

```text
localRawDefect = polarJuliaContribution + nonpolarLocalizationGap
```

The polar contribution has the factorization

```text
polarJuliaContribution
  = leftCoDefect * polarJuliaRightFactor
```

and the right factor is bounded by the detector norm.  Since `leftCoDefect` is
self-adjoint, subtracting the polar slot gives the complete signed estimate:

```text
||nonpolarLocalizationGap^dagger x||
  <= (||detector|| + bound) * ||leftCoDefect x||
```

The flow is:

```text
 +------------------------------+
 | raw physical Douglas premise |
 | bound on physical four-term  |
 +--------------+---------------+
                |
                v
 +------------------------------+
 | local raw defect              |
 | same bound via reverse        |
 | transition contraction       |
 +--------------+---------------+
                |
                v
 +------------------------------+
 | subtract polar Julia slot    |
 | cost <= ||detector||         |
 +--------------+---------------+
                |
                v
 +------------------------------+
 | signed nonpolar gap           |
 | bound <= ||detector||+bound  |
 +------------------------------+
```

## Lean owners

The source module is:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawLocalDouglasBridge.lean
```

The focused audit is:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawLocalDouglasBridgeAudit.lean
```

The main declarations are:

```text
suffixActualBandLocalRawDefect_eq_neg_rawIntertwiningDefect_comp_reverse
suffixActualBandLocalRawDefect_adjoint_eq_neg_reverse_adjoint_comp_rawPhysicalRow
suffixActualBandLocalRawDefect_adjoint_normSq_le_of_rawDomination
suffixActualBandLocalNonpolarLocalizationGap_douglas_of_rawDomination
SuffixRawAmbientBoundaryUniformDominationData.toNonpolarGapDouglas
```

The final handoff consumes the existing
`SuffixRawAmbientBoundaryUniformDominationData` and produces the matching
uniform local nonpolar Douglas data with the additive detector norm cost.

## Boundary

The source-level contract
`SuffixRawAmbientBoundaryDomination` remains an explicit premise.  This batch
does not construct its bounded physical readout, prove a uniform old-carrier
lower bound, or establish Gate 3U.  The finite-S sign, the negative owner,
Burnol's identity, and RH remain open.

No transition skew is cancelled, and no residual norm estimate is promoted to
Douglas domination.  The bridge only composes a genuinely supplied readout
with the exact cofactor identities and then performs the signed polar
subtraction.

## Verification

Verification ran in the Ubuntu-24.04 WSL2 ext4 mirror after synchronizing from
the Windows source of truth:

```text
focused source build: 3344 jobs, PASS
focused audit + CCM25Concrete aggregate: 3847 jobs, PASS
full repository build: 3927 jobs, PASS
git diff --check: PASS
```

The focused audit reports exactly
`[propext, Classical.choice, Quot.sound]` for all five declarations.  The new
source and audit contain no `sorry`, `admit`, or user axiom declaration.
