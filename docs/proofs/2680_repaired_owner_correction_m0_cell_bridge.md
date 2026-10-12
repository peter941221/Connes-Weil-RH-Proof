# Record 2680: repaired-owner correction-M0 cell bridge

Status: Lean bridge GREEN for cell 4096 and the correction-M0 channel; this is
not an RH proof.

The module `C1RouteARepairedOwnerCorrectionM02680.lean` decodes the 30
repaired binary64 correction coefficients from their stored IEEE-754 bit
patterns.  It reuses the already proved whole-cell phi/cosine/sine enclosures
from record 2677 and the record-2676 correction-M0 family rectangles.  For
each family it proves the point-owner product rectangle is contained in the
exported dyadic family rectangle, then applies the existing aggregate
consumer to prove `record2680CorrectionM0CellContained`.

The independent record-2676 numerical screen was rerun after restoring its
Linux MPFR input and returned `CELL4096_CONTAINMENT_SCREEN_PASS`.  All four
channels remain inside their exported rectangles.  The closest correction-M0
margin is the upper imaginary coordinate at approximately 4.0716 binary64
ulps; the base-M0 margins remain those recorded in 2676.

The Linux-native Lean/Mathlib v4.30 build used an explicit `.olean` output.
The audit reports exactly `[propext, Classical.choice, Quot.sound]` for the
cell consumer and representative family leaves, with no `sorryAx`.

This closes only one additional channel in one cell.  The base-D2 and
correction-D2 owner bridges, the remaining 8191 cells, `chargeRest`, the
signed xi tail, Producer GO, `SourceRH`, and RH remain open.
