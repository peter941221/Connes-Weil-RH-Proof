# Proof 172: log-window projection exhaustion for source tests

## Result

Accepted common-domain infrastructure, but not an RH proof.

Every positive compact source test is now shown to enter one finite logarithmic
window on the common carrier `Lp C 2 volume`.  Its global log pullback is fixed
by the corresponding window projection.

## Lean statements

`GlobalLogHaar.lean` proves:

```text
exists_cc20LogWindow_containing_logPullback
cc20LogWindowProjection_eq_self_of_support_subset
exists_cc20LogWindowProjection_fix_logPullbackLp
cc20LogWindow_subset_of_le
cc20LogWindowProjection_comp_of_le
```

The first theorem transports the already-proved positive multiplicative-window
containment through `rho=exp(t)`, including the endpoint logarithm identities.
The second theorem proves that an `Lp C 2 volume` representative whose support
is inside a log window is fixed by the `L-infinity` indicator projection.  The
third theorem applies this to the actual `cc20LogPullbackLp` using its
almost-everywhere representative theorem; it does not identify arbitrary Lp
representatives pointwise.

The resulting dependency is:

```text
positive compact source test
        -> finite multiplicative window
        -> finite log window
        -> common global L2 projection fixed-point.
```

For `1 < lambda <= mu`, Lean also proves

```text
P_lambda P_mu = P_lambda.
```

The cutoffs therefore form a monotone projection family on the common carrier,
not merely a collection of independently typed windows.

## Verification

The aggregate WSL2 build and import-facing audit pass using the retained Lake
cache.  Focused declarations use only:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorryAx`, RH premise, Weil-positivity premise, or stored support
conclusion.

## Boundary

This proves test exhaustion only.  It does not prove compatibility of the
finite-window regular-kernel operators with the global projection, uniform
operator bounds, a global Fourier multiplier, the diagonal `-2 Dirac_0` split,
or the same-test CC20 trace read-off. RH remains unproved.
