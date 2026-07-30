# Proof 566: Joint Residual Douglas/Readout Contract

## Result

Proof 565 aligned the family endpoint with the literal suffix endpoint. Proof
566 keeps the two endpoint residuals in one signed ledger:

```text
alignment residual + physical/Schur endpoint residual
  = transport residual.
```

At the raw-row level, the existing exact identity is repackaged as

```text
actual raw row
  = named Schur raw row + whole coframe-residual row.
```

The new component-row package supplies four rows:

```text
named Schur ambient row       + named Schur boundary row
coframe residual ambient row  + coframe residual boundary row
```

If both signed rows factor through the corresponding physical analysis
coordinates with uniform bounds, their sum produces one uniform raw readout.
The existing raw-readout equivalence then produces the family-uniform
physical domination contract used by Gate 3U.

## What This Closes

This closes the interface composition for the three requested layers:

1. endpoint residuals are combined without setting either residual to zero;
2. a uniform component-row producer is an explicit Douglas/readout contract;
3. the combined readout is connected to the existing uniform physical
   domination owner.

The source theorem remains conditional on the component rows and their
uniform bounds. The module does not claim that CCM24 or the current source
objects produce those rows.

## What Remains Open

The actual analytic producer is still missing. In particular, no theorem here
proves the family-uniform estimate

```text
||gap(p,S)† x||² <= C² ||leftCoDefect(p,S) x||².
```

Approximate kernels, the finite-S sign, Burnol's identity, and RH remain open.
The residual is kept as one signed object; do not estimate its ambient,
boundary, coherence, and alignment pieces independently unless a new source
theorem justifies that split.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSJointResidualDouglasReadout.lean
ConnesWeilRH/Dev/
  CCM24FiniteSJointResidualDouglasReadoutAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```
