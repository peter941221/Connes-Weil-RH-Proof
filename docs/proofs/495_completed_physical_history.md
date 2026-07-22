# Proof 495: Completed physical Schur history

Date: 2026-07-22

## Result

The result is a necessary correction, not Gate 3U.

Proof 494 used only the rectangular boundary-defect history as the proposed
source of the complete physical column.  That history has no coordinate when
the visible-prime list is empty:

```text
rectangularBoundaryDaggerColumn([]) = 0.
```

The complete physical column still contains its fixed base channel.  A
defect-only readout therefore cannot be the general producer.  Proof 495 adds
the terminal Julia survivor and uses the completed history

```text
                 +--------------------+
source input --->| terminal survivor  |---+
                 +--------------------+   |
                 +--------------------+   +--> contractive readout
                 | boundary defects   |---+      |
                 +--------------------+          v
                                         M (V_S + C_S)
```

For an empty list this column is exactly

```text
(source input, 0),
```

not zero.

## Energy identity

Let `steps` be the actual rectangular Schur steps.  The existing Julia
Pythagorean telescope states

```text
juliaDefectEnergy(steps, x)
  + norm(juliaSurvivor(steps, x))^2
  = norm(x)^2.
```

The rectangular boundary column is pointwise dominated by the Julia defect
column.  Hence Lean proves

```text
norm(completedRectangularBoundaryColumn(steps, x))^2
  <= norm(x)^2.
```

After a Hilbert--Schmidt source input and a norm-at-most-one readout are
inserted, summing over the source Hilbert basis gives

```text
energy(readout * completedHistory * sourceInput)
  <= energy(sourceInput).
```

## Gate-facing consequence

The source module reconnects this corrected history to Proof 492's exact
physical column.  If the source-specific equality

```text
M (V_S + C_S)
  = readout * completedHistory * sourceInput
```

is proved with

```text
norm(readout) <= 1,
energy(sourceInput) <= fixedPhysicalEnergyMajorant,
```

then the already proved same-object trace consumer gives

```text
norm(trace(raw completed response))
  <= 2 * fixedPhysicalEnergyMajorant.
```

The displayed equality and the source-input energy bound are not constructed
by Proof 495.  They are the remaining source-specific producer.  In
particular, Proof 495 does not close Gate 3U, prove the finite-S sign, prove
negative-owner integration, prove Burnol's identity, or prove RH.

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

The central declarations are:

```text
rectangularBoundaryDaggerColumn_nil_eq_zero
completedRectangularBoundaryColumn_nil_apply
completedRectangularBoundaryColumn_normSq_le
completedRectangularBoundaryReadout_tsum_normSq_le
sourceActualBandCombinedPhysicalRightEnergy_le_of_completedActualSchurReadout
lowerFactorGaugedActualBandCompletedRelativeResponse_trace_norm_le_of_completedHistory
```

## Boundary

```text
defect-only readout for the full column:       rejected;
terminal survivor in the producer carrier:    mandatory;
completed-history contraction:                Lean proved;
source-specific completed readout identity:   open;
Gate 3U / finite-S sign / Burnol / RH:         open / open / open / open.
```
