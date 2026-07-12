# 033 Log-Poisson Positive Owner Screen

Date: 2026-07-12

Status: positive spectral function passes; positive-trace Weil read-off
shortcut rejected by proof 111.

## Candidate

For `U_p` unitary and `a=p^(-1/2)`, define

```text
L_p = 2 log(1+a) I
      - log((I-aU_p)^*(I-aU_p)).
```

The spectrum of `(I-aU_p)^*(I-aU_p)` lies in
`[(1-a)^2,(1+a)^2]`, so `L_p >= 0`.  Functional calculus gives

```text
L_p = 2 log(1+a) I
      + sum_(m>=1) a^m/m (U_p^m + U_p^(-m)).
```

This fixes the endpoint metric projection's missing `1/m` coefficient.

## Cheap Positive-Trace Test

The only obvious positive boundary object is a square-root block

```text
A_p(h) = Q L_p^(1/2) P C_h.
```

Its trace is positive, but its kernel is the continuous Hankel kernel of
`L_p^(1/2) C_h`.  The resulting trace is an integral of

```text
|(L_p^(1/2) * h)(t)|^2
```

over the crossing region.  It is quadratic in the square-root kernel, not the
linear discrete evaluation

```text
sum_(m>=1) a^m/m * m log(p)
  [F_h(m log p)+F_h(-m log p)].
```

Taking `L_p` linearly instead preserves the desired Fourier coefficients but
does not give a positive boundary trace; the identity term also has infinite
bulk trace before a nonpositive subtraction.

## Verdict

```text
L_p positive: pass
L_p Fourier/Weil coefficient: pass
positive square-root boundary trace: wrong nonlinear read-off
linear L_p boundary read-off: not positive and bulk-divergent
Plan 033 shortcut: rejected
```

Reopening requires a different source-backed positive factorization whose trace
is linear in the logarithmic Euler operator.  Do not use `L_p` or its square
root as a new route owner without that same-object theorem.

