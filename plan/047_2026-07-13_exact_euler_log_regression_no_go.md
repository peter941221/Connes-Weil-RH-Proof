# 047 Exact Euler-Log Regression No-Go

Date: 2026-07-13

Status: rejected by translation-invariance of the requested graph; no Lean
owner authorized.

## Candidate

After Plan 046 fails, prescribe the exact one-prime regression map instead of
deriving it from an inverse-log metric:

```text
Q H R(R H R)^(-1)
  = Q sum_(m>=1) p^(-m/2) U_p^(-m)/m R,
```

with `H` positive and translation invariant so that the test convolution can
cycle through it.

## Rejection

On each `log(p)` translation fiber, the right side is the Hankel graph with

```text
d_n=p^(-(n+1)/2)/(n+1)>0.
```

If such `H` existed, its graph would be invariant under the unilateral shift.
Applying that shift to `e_0+D e_0` requires simultaneously the coefficients

```text
d_(s+1)
```

and

```text
d_(s+1)+d_0 d_s,
```

which is impossible. See proof 207.

## Remaining reopen shape

Only a genuine two-cutoff Sonin identity or a common-domain unbounded relative
form remains outside this no-go. Neither may reuse the false local regression
identity.
