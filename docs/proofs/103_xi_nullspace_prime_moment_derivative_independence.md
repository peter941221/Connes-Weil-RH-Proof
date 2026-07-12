# 103 Xi-Nullspace Prime-Moment Derivative Independence

Date: 2026-07-12

## Derivative

On the critical line write `H_0` for the quotient detector and

```text
v_A = Xi * R * A,
R(s)=s(s-1/2)(s-1).
```

The autocorrelation moment at shift `a` is the Fourier coefficient of
`|H|^2`. Its first variation is

```text
dC_a(v_A)
  = FourierCoefficient_a(2 Re(conj(H_0) v_A)).
```

## Independence argument

Suppose a finite linear combination of the rows `dC_(a_j)` vanishes for every
controlled `A`. Testing both `A` and `iA` recovers the complex pairing and gives

```text
conj(H_0(t)) * Xi(t) * R(t) *
  sum_j c_j exp(i a_j t) = 0
```

almost everywhere on the critical line. The analytic prefactor is not
identically zero and has only a discrete zero set. Hence the finite exponential
polynomial vanishes on an interval. Distinct shifts `a_j` force every
coefficient `c_j` to vanish.

Therefore the finite prime-moment derivative rows are independent, provided
the allowed `A` family is dense enough to separate the displayed multiplier.
Compact smooth physical corrections, with unrestricted finite support, give
the intended separating family.

## Verdict

```text
finite first-variation row independence: passes structurally
local finite-moment submersion: plausible
nonlinear target reachability from H_0: open
uniform support/type bounds as moments grow: open
```

The next cheap gate is not matrix rank. It is whether a controlled path in the
Xi-nullspace can reach the required prime moments without leaving the common
form domain or blowing up the cutoff constants.

