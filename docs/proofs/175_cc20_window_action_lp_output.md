# Proof 175: finite-window action output on the common global carrier

## Result

Accepted finite-window output construction, but not an RH proof.

For every `lambda > 1` and continuous input `u`, the continuous finite-window
action is first shown to belong to

```text
Lp C 2 (volume.restrict (cc20LogWindow lambda)).
```

The proof uses compact-window continuity, a compact-image norm bound, and
`MemLp.of_bound`.  Mathlib's indicator/restriction equivalence then constructs

```text
cc20GlobalLogWindowRegularActionToLp lambda hlambda u
  : Lp C 2 volume,
```

whose representative is the log-window indicator times the continuous finite
window action.  The construction is finite-window and input-specific; it does
not assert a whole-line bounded operator or an `L1` kernel.

## Verification

The aggregate WSL2 build and import-facing audit pass with only
`propext`, `Classical.choice`, and `Quot.sound`.  No `sorryAx`, RH premise, or
stored operator-bound conclusion is present.

## Boundary

The remaining work is to prove linearity and a uniform operator bound in the
input, identify this output with the existing parameterized Haar-L2 operator
on continuous inputs, and establish compatibility under increasing windows.
The oscillatory whole-line Fourier multiplier, diagonal `-2 Dirac_0` identity,
same-test trace read-off, and RH remain open.
