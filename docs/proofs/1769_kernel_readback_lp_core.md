# Proof record 1769: canonical Lp readback on the Schwartz core

Date: 2026-09-21

Status: FORMAL, no sign claim.

## Result

`sourceKernelReadback_ae_toLp_core` combines the existing Schwartz convolution
readback with the new `MemLp.toLp` representative bridge.  On the dense
Schwartz core, the Plancherel-defined root convolution is therefore equal
almost everywhere to the honest kernel row written using the canonical L2
representative.

## Route role

This is the exact input shape for a future `DenseRange.induction` or continuity
argument.  It does not identify the row integral with the Plancherel operator
for arbitrary L2 inputs; that extension remains the next analytic obligation.

## Provenance

Original project composition of records 1734, 1767, and 1768.  No numerical
input, new axiom, or positivity conclusion is used.
