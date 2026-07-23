# Proof 516: terminal survivor and physical boundary readout contract

## Result

Proof 516 isolates the next nonempty-family producer without identifying
different carriers or projections.

The terminal column has the exact shape:

    survivor(S) * fixedPhysicalSourceInput

and its physical target is:

    sourceRight * sourceInclusion * survivor(S) * fixedPhysicalSourceInput

The correct Douglas premise is therefore the pointwise domination:

    ||sourceRight * sourceInclusion * survivor(S) * fixedInput x||
        <= ||survivor(S) * fixedInput x||.

Under that premise, Lean constructs a norm-one terminal readout. The old
fixed right Douglas factor alone cannot be substituted here because the
survivor and the fixed Gram input need not commute.

The raw boundary target is recorded before estimates as:

    physicalBoundaryTarget
      = rightLeg * endpoint
          - rightLeg * inclusion * survivor

PhysicalBoundaryDaggerReadoutContract requires a readout of the genuine
rectangular boundary-dagger column into this target, together with its norm
bound. exists_completed_readout then combines the terminal and boundary
equations through the existing WithLp 2 history, provided the joint readout
norm is supplied.

This is a source contract and exact assembly theorem. It does not prove the
terminal domination, the raw boundary readout, the joint norm, Gate 3U, the
finite-S sign, Burnol's identity, or RH.

## Lean owner

    ConnesWeilRH/Source/CCM25Concrete/
      CCM24FiniteSCompletedPhysicalTerminalReadout.lean
    ConnesWeilRH/Dev/
      CCM24FiniteSCompletedPhysicalTerminalReadoutAudit.lean

The module keeps the raw boundary-dagger column separate from the metric
suffixEulerBoundaryOutputMaps. The audited declarations use only
[propext, Classical.choice, Quot.sound].

## Verification

Ubuntu 24.04 WSL2, ext4 mirror:

    focused source: PASS
    focused axiom audit: PASS, 3312 jobs
    CCM25Concrete aggregate: PASS, 3791 jobs
    full repository: PASS, 3872 jobs

The source and audit contain no sorry, admit, or user axiom declaration. The
WSL localhost-proxy notice is external.
