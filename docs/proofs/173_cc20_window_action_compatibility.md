# Proof 173: finite-window log action compatibility

## Result

Accepted continuous-input compatibility, but not an RH proof.

For `1 < lambda <= mu`, if a continuous log input is supported in the smaller
window, the global log-kernel action over the larger window equals the action
over the smaller window:

```text
support(u) subset [-log lambda, log lambda]
  -> A_mu(t,u) = A_lambda(t,u).
```

## Proof shape

`GlobalLogKernel.lean` proves
`cc20GlobalLogWindowRegularAction_eq_of_support_subset`.  It splits the large
interval into:

```text
[-log mu, log mu]
  = [-log mu, -log lambda]
    + [-log lambda, log lambda]
    + [log lambda, log mu].
```

The two exterior interval integrals vanish almost everywhere because the input
support is inside the small log window.  Endpoint exceptions are handled with
the Lebesgue a.e. exclusion of singletons; no pointwise false endpoint claim is
used.  Mathlib's adjacent-interval integral identities then leave exactly the
small-window action.

This is the continuous-input action-level counterpart of the projection law
`P_lambda P_mu = P_lambda`.

## Verification and boundary

The aggregate WSL2 build and import-facing audit pass with only
`propext`, `Classical.choice`, and `Quot.sound`.  No `sorryAx`, RH premise, or
stored action compatibility is present.

The theorem does not yet extend the action to a global bounded `L2` operator,
prove uniform norms, identify the finite-window Hilbert--Schmidt operators as
global compressions on all L2 inputs, or close the diagonal and trace gates.
RH remains unproved.
