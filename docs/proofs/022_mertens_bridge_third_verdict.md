# Plan 022 Mertens-Bridge Third Verdict

Date: 2026-07-11

Verdict: **the fixed direction remains active, but the separated energy proof
is rejected.** The double-Mobius divisor collapse exposes a centered Mertens
bridge. Bounding that bridge at square-root scale independently would import
the same cancellation strength the route is meant to prove.

## 1. Exact Bridge

With `theta(d)=-mu(d)/d` for `d<=8` and `Q=theta*mu`, define

```text
P_Q(x)=sum_(k<=x) Q(k),
M(x)=sum_(k<=x) mu(k).
```

Finite convolution gives

```text
P_Q(x)=sum_(d=1)^8 theta(d)M(floor(x/d)).
```

Since `theta(1)=-1`,

```text
M(x)=-P_Q(x)+sum_(d=2)^8 theta(d)M(floor(x/d)).
```

The square-root recursion coefficient is

```text
sum_(d=2)^8 |theta(d)|/sqrt(d) < 0.758.
```

Therefore a uniform pointwise `O(sqrt x)` bound for `P_Q` recursively supplies
the same scale for `M`. Such a theorem is not accepted as a lower auxiliary
estimate.

## 2. Why The Coupled Ratio Survives

For `N<n<2N`, the selected sequence is exactly

```text
h_N(n)=N*S_N-(P_Q(n)-P_Q(N)).
```

Thus its energy and its correlation with the optimal residual contain the same
centered partial-sum bridge. The numerical mechanism need not require that
bridge to be absolutely small; it requires a nonvanishing angle:

```text
|<r_N,h_N>|^2
  / (||r_N||^2*||h_N||^2) >= c/log N.
```

The fixed direction passes this test through `N=16384` as rejection evidence.
A scan of every `16<=N<=512` found no sign change and a minimum normalized
value about `0.1029`.

## 3. Rejected And Active Statements

```text
rejected:
  prove ||h_N||=O(1) from a standalone square-root P_Q estimate
  prove pointwise positivity of r_N*h_N
  discard the far tail
  replace r_N by a smooth scaling profile

active:
  prove the coupled residual--Mertens-bridge angle directly from the same
  finite optimality equations and the exact convolution identity
```

This is still a deep theorem and may ultimately be RH-equivalent. The route is
kept active because the second vector is fixed and explicit, the denominator
contains no Schur inverse, and repeated numerical rejection tests have not
found a collapse. It is not yet a guaranteed RH route.
