# Proof 514: Completed physical component readout

Date: 2026-07-23

## Result

Proof 514 adds the exact component-level algebra needed to assemble a
completed physical-history readout.  It does not construct the source-specific
components, their norm bound, Gate 3U, the finite-S sign, Burnol's identity,
or an unconditional RH proof.

The completed carrier is

```text
source input
    |
    v
(terminal Julia survivor, raw boundary-dagger column)
    |                         |
    v                         v
terminalReadout          boundaryReadout
    \_________________________/
              |
              v
       terminalColumn + boundaryColumn
```

## Lean owner

Source:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedPhysicalHistory.lean
```

Audit:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedPhysicalHistoryAudit.lean
```

The new declarations are:

```text
completedRectangularBoundaryReadoutOfComponents
completedRectangularBoundaryReadoutOfComponents_apply
completedRectangularBoundaryReadoutOfComponents_comp_column_eq_add
```

The last theorem proves, for actual rectangular Schur steps,

```text
terminalReadout * survivor * sourceInput = terminalColumn
boundaryReadout * boundaryDaggerColumn * sourceInput = boundaryColumn
---------------------------------------------------------------------
combinedReadout * completedHistory * sourceInput
    = terminalColumn + boundaryColumn.
```

The proof keeps the `WithLp 2` product carrier explicit.  It therefore does
not identify the metric `suffixEulerBoundaryOutputMaps` with the physical raw
`rectangularBoundaryDaggerColumn`, and it does not infer either component
identity from Julia contraction.

## Verification

The following Ubuntu 24.04 WSL2 checks passed under the repository Lake lock:

```text
lake env lean ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedPhysicalHistory.lean
lake build ConnesWeilRH.Dev.CCM24FiniteSCompletedPhysicalHistoryAudit
lake build ConnesWeilRH.Source.CCM25Concrete
lake build
```

The focused audit reports the existing axiom-clean set
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, `admit`, or user axiom
was added.  Existing repository linter warnings and the WSL localhost-proxy
notice are unchanged.

## Boundary

The active producer still must supply the two source-specific component
readbacks and prove the norm of their combined `WithLp` readout is at most
one.  Until that producer exists, the completed physical-history consumer is
conditional and Gate 3U remains open.
