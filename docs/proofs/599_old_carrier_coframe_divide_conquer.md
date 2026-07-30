# Proof 599: old-carrier coframe divide and conquer

## Result

The new module
`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer.lean`
packages the remaining old-carrier coframe row as a conditional
divide-and-conquer handoff.

Its row contract is explicit:

```text
row = readout * oldCarrierAnalysis
||readout|| <= bound
0 <= bound
```

The package accepts three such contracts for the same old-carrier analysis:

```text
orientation row
residual row
known bounded row
```

It then proves the exact algebraic decomposition

```text
signed telescope = hard row + known row
hard row = orientation row + residual row
```

The readouts are added before any physical-coordinate projection.  Therefore
the hard and known pieces remain one old-carrier readout, with norm bound
`orientationBound + residualBound + knownBound`.  Composing this readout with
the contractive left and right ambient-boundary embeddings gives two rows with
the same bound.  The existing two-channel factor owner then yields old-carrier
domination with bound

```text
2 * (orientationBound + residualBound + knownBound).
```

The uniform adapter finally hands this domination to the existing non-polar
Douglas/Gate 3U interface, adding the detector norm as required by that
interface.

## Boundary

This is a conditional composition layer, not the missing source theorem.  It
does not construct any of the three input readouts.  In particular, the
elementary bounds for the known forward leg do not factor the signed
orientation row or the survivor residual row through the same old-carrier
analysis.  A separate operator-norm or Hilbert-Schmidt estimate cannot be
substituted for the readout factorization.

Consequently Bone 1 remains open at the family-uniform producer of the
orientation, residual, and known readout contracts.  The module does not prove
Gate 3U, the finite-S sign, Burnol's identity, or RH.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquerAudit.lean
```

## Verification

The focused source build in the Ubuntu-24.04 WSL2 ext4 mirror completed with
`3357` jobs.  The import-facing audit completed and printed exactly

```text
[propext, Classical.choice, Quot.sound]
```

for all seven audited declarations.  No `sorry`, `admit`, or user axiom was
added.

The owner-level build boundary was repaired without changing its three public
declarations: the old file contained a large commented proof history and an
unused `ResponseBounds` import.  The retained owner now imports the orientation
ledger, reuses its exact signed-telescope split, and keeps the same names and
types.

The repaired owner build passed with `3347` jobs.  The aggregate build passed
with `3864` jobs, and the full repository build passed with `3945` jobs.  The
focused divide-and-conquer source build passed with `3357` jobs.  Both focused
audits passed, and all audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The WSL localhost-proxy notice and existing linter warnings are environmental
or pre-existing.  No `sorry`, `admit`, or user axiom was added.
