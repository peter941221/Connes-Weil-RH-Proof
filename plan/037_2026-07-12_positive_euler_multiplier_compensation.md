# 037 Positive Euler Multiplier Compensation

Date: 2026-07-12

Status: exact one-prime positive operator found; global direct-multiplier route
rejected by unavoidable divergent scalar compensation.

## Exact Positive Operator

For `a=p^(-1/2)` and unitary `U_p`, set

```text
L_p(a)=2 log(1+a)I-log((I-aU_p)^*(I-aU_p)).
```

Its radial derivative is

```text
M_p(a)=a d/da L_p(a)
  = 2a/(1+a) I
    + sum_(m>=1) a^m(U_p^m+U_p^(-m)).
```

On a scalar phase `z=exp(i theta)`,

```text
M_p(theta)
  = 2a(1-a)(1+cos theta)
      /((1+a)(1-2a cos theta+a^2))
  >= 0.
```

Thus the nonconstant Fourier coefficients are exactly the final prime-power
Weil coefficients after multiplication by `log p`.

## Minimal Compensation

The unshifted prime symbol has minimum

```text
min_theta 2 log(p) sum_(m>=1) a^m cos(m theta)
  = -2 log(p) a/(1+a),
```

attained at `theta=pi`.  Therefore the scalar term in `M_p` is the smallest
possible scalar shift making that multiplier positive.

For finitely many distinct primes, the numbers `log p` are rationally
independent.  Kronecker approximation lets the phases `t log p` approach `pi`
simultaneously, so the minimum compensations add:

```text
C_S >= sum_(p in S_f) 2 log(p)/(sqrt(p)+1).
```

This grows without bound with `S`.  It cannot be absorbed by CC20's fixed
archimedean essential coefficient `-2 Id`.

## Verdict

```text
one-prime positive Euler multiplier: exact
prime-power coefficients: exact
minimal scalar compensation: exact
finite-prime compensations: additive by phase density
cofinal finite-S compensation: divergent
direct positive-multiplier route: rejected
```

This does not reject a non-translation-invariant boundary construction that
cancels the scalar before positivity.  Such cancellation is precisely the
remaining Plan 036 requirement. See proof 115.

