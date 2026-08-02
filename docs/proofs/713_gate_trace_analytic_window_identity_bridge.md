# Proof 713: Gate Trace Handoff from Analytic Windows, Identity Input

## What is established

Proof 713 feeds the Proof 712 completed endpoint readout into the Proof 697
Gate-facing trace-norm handoff.

The bridge is deliberately identity-input:

~~~text
Proof 712:
  rightLeg o endpoint
    = readout o completedRectangularBoundaryColumn

Proof 697:
  rightLeg o endpoint
    = readout o completedRectangularBoundaryColumn o sourceInput
~~~

Therefore the direct composition uses sourceInput = id.

## Declaration

~~~text
lowerFactorGauged_trace_norm_le_of_analytic_window_originalMultiplier_idInput
~~~

Under translated analytic representatives, original-root Fourier
almost-everywhere nonvanishing, the completed physical boundary readout
contract, the terminal survivor identity, and the explicit identity-input
energy majorant, the theorem proves:

~~~text
norm ordinaryTraceAlong sourceBasis
  lowerFactorGaugedActualBandCompletedRelativeResponse
  <= 2 * fixedPhysicalEnergyMajorant.
~~~

## Boundary

This is not Gate 3U.  It exposes the exact obstruction left by the current
handoff: after dense-range cancellation removes fixedPhysicalSourceInput,
the existing Gate-facing energy consumer only composes directly with identity
input.  The required identity-input energy summability/majorant is explicit
and is not proved here.

The next producer must either supply the identity-input energy bound on the
actual source carrier, or produce a Gate-facing consumer whose energy ledger
matches the dense-range endpoint readout without reverting to identity input.

## Verification

Pending WSL2 verification after synchronization.
