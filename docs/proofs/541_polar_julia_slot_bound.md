# Proof 541: polar Julia slot bound

Result: good.  This closes the quantitative part of the already-localized
polar Julia slot.  It does not prove the non-polar gap estimate, Gate 3U, the
finite-S sign, Burnol's identity, or RH.

## What it is

Proof 501 had already proved that the local polar contribution factors through
the actual adjacent Julia left co-defect:

    polarJuliaContribution
      = leftCoDefect * polarRightFactor.

Proof 541 proves the missing uniform bound on that known right factor:

    ||polarRightFactor|| <= ||detector||.

The proof uses only three contractions:

    boundary co-defect factor <= 1
    new suffix frame          <= 1
    reverse Schur transition  <= 1

so the only remaining norm is the selected detector norm.

## Why it matters

The local raw defect has the exact decomposition:

    local raw
      = polar Julia contribution
        + non-polar localization gap.

Since the polar term is now both factored and uniformly bounded, the remaining
local Gate 3U producer is exactly the non-polar gap factorization through the
same adjacent left co-defect.

Lean packages this as a two-way reduction:

    uniform local raw co-defect factors
      <-> uniform non-polar gap co-defect factors.

The conversion in either direction adds only the fixed detector norm.  This is
not an isometric equivalence, but it is a finite uniform reduction.

## Boundary

This proof does not estimate the non-polar gap.  That gap still contains the
first-jet contribution and the route/polar ordering residual, kept together.
Splitting those two terms before the final estimate would discard the
cancellation needed by Gate 3U.

## Verification

Verified in the Ubuntu-24.04 WSL2 ext4 mirror:

    +------------------------------------------+-------+--------+
    | target                                   | jobs  | result |
    +------------------------------------------+-------+--------+
    | focused source target                    |  3325 | PASS   |
    | focused axiom audit                      |  3326 | PASS   |
    | CCM25Concrete aggregate                  |  3811 | PASS   |
    | full repository                          |  3892 | PASS   |
    +------------------------------------------+-------+--------+

The focused audit checks these six declarations:

    suffixActualBandLocalPolarJuliaRightFactor_norm_le_detector
    SuffixLocalNonpolarGapCoDefectFactorData.toLocalRawFactor
    SuffixLocalRawCoDefectFactorData.toNonpolarGapFactor
    SuffixLocalNonpolarGapCoDefectUniformFactorData.toLocalRawUniform
    SuffixLocalRawCoDefectUniformFactorData.toNonpolarGapUniform
    exists_uniformLocalRawFactor_iff_exists_uniformNonpolarGapFactor

All six audited declarations use exactly:

    [propext, Classical.choice, Quot.sound]

The Proof 541 source and audit contain no `sorry`, `admit`, or user
`axiom`/`constant` declaration, and have no line longer than 100 characters.
The WSL localhost-proxy notice is external to the Lean build.
