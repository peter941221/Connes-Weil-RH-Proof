# 3078 — Route A canonical owner and finite-grid budget

Date: 2026-10-20

Status: `CANONICAL-OWNER-AND-LEDGER-ARITHMETIC-PROVED; CONTINUUM-ASSEMBLY-AND-TAIL-OPEN`.

## Canonical owner

The fixed owner is now constructed directly from the captured coefficients and
modulations:

```text
base       = correctedPhysicalCompactLogTest record2678BaseCoefficient
               capturedModulations2584
correction = correctedPhysicalCompactLogTest record2680CorrectionCoefficient
               capturedModulations2584
source     = halfDensityShift (base.convolution correction)
owner      = selectedOwner base correction 0
```

Record 3076 proves the two packaged factors equal their respective
`externalPhysical2344` functions, gives the support transfer for the shifted
source, and identifies the canonical owner's source and convolution square.
The coefficient casts and modulation order are fixed by the imported 2678,
2680, and 2584 definitions, rather than by an arbitrary residual-family
choice.

This is the canonical owner for the captured item-5 repaired coefficient
pair. It is not a theorem identifying every `selectedOwner base correction n`
or the binding healthy selected detector with that fixed pair.

## Cell versus full-grid charge correction

The first implementation incorrectly treated `record2686RepairedOwnerTotal2800`
as the full finite-window charge. Its integration endpoint is
`record2675CellRight = 0.0015999999999998238`, so it is the single central
cell certificate (cell 4096), not the full support. This is corrected in the
current modules:

```text
record 2800 / record 2686: central cell only
record 2685: exact sum of all 8192 stored cell prices
```

Record 2685 proves the exact rational sum of all cell bit-pattern prices and
proves that the sum is below `knownError2109`. The total is approximately
`6.70596e6`; it remains a numerical ledger until all cell rectangles are
proved to contain the continuous canonical channels.

## Implemented interfaces

- `C1RouteACanonicalOwner3076.lean` defines the fixed base, correction,
  half-density-shifted source, and n=0 owner; exact physical-function,
  support, and owner identity lemmas are compiled.
- `C1RouteACanonicalFiniteCharge3077.lean` names the full record-2685 grid
  charge and proves its budget comparison. Its channel certificate requires,
  for each of 8192 cells and each of the four channels, rectangle containment,
  norm and weight bounds, integrability, and a cell price. It composes those
  obligations with the existing partition integral theorem and the exact
  record-2685 total. The outer assembly separately requires a full-support
  residual inequality and an explicit tail budget before it can conclude
  `chargeRest <= knownError2109`.
- `C1RouteASelectedOwnerChargeBridge3073.lean` now consumes that fixed
  canonical assembly. It no longer accepts a `Classical.choose` residual
  family or a free `chargeRest <= record2686...` premise. Its certificate
  structure still takes the full-support residual assembly and tail budget as
  explicit hypotheses; it does not construct either proof.

## Remaining mathematical obligations

The full-grid continuum theorem still needs all 8192 cell rectangles for each
of the four channels, matching the canonical coefficient owner and modulation
vector. The new theorem composes these cell obligations but does not produce
them. Record 2685 proves exact sum arithmetic; record 2684's numerical screen
is not a Lean continuum enclosure. The signed full-support residual also needs
an explicit tail theorem and an owner-specific assembly into `chargeRest`.
The 3073 producer adapter is conditional on those obligations and therefore is
not a producer closure result.

These item-5 repaired-owner obligations do not by themselves establish the
binding selected-detector physical-kernel/C3' budget. Records 3051 and 3052
remain controlling for that distinction. No Producer GO, `SourceRH`, or RH
conclusion follows from record 3078.

## Verification

Linux-native Lean 4.30 builds passed for the canonical owner, finite-grid
budget interface, selected-owner charge bridge, and its producer adapter. The
3077 audit reports `[propext, Classical.choice, Quot.sound]` for the finite
budget, four-channel partition, charge bridge, and producer adapter. These
axiom results verify the Lean derivations under their stated hypotheses; they
do not discharge the cell-containment, full-support assembly, or tail inputs.
