# Proof 568: Actual Schur Transition Orientation

## Result

The raw row and the packed physical analysis use different transition
orientations.  The exact identity is

```text
EulerTransition† - actualSchurTransition†
  = (EulerTransition - actualSchurTransition†)†
    + (actualSchurTransition - actualSchurTransition†)
```

Using Proof 567's transport identity, this becomes

```text
row-level gap
  = (oldFrame† * (EulerTransport - actualSchurTransport†) * newFrame)†
    + actualSchurTransition skew.
```

The second term is a genuine skew-adjoint transition residual.  It is not
proved zero, self-adjoint, or bounded by the packed ambient boundary analysis.

## What This Closes

This prevents the physical transport Douglas estimate from being silently
applied to the adjoint transition appearing in the raw row.  Any future
producer must either control the skew term inside the same signed row or prove
a source-specific cancellation with it.

Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurTransitionOrientation.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurTransitionOrientationAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```
