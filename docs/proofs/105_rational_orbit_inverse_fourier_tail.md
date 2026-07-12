# 105 Rational Orbit Inverse-Fourier Tail

Date: 2026-07-12

## Proper rational form

Choose the finite orbit interpolation polynomial `S` with degree strictly less
than the orbit divisor polynomial `P_rho` (Hermite interpolation when
multiplicities occur). In centered coordinate `u=s-1/2`, the critical-line
restriction

```text
B(t) = S(1/2+it) / P_rho(1/2+it)
```

is a proper rational function. Its poles are the centered removed orbit, none
on the real `t` axis under the off-line hypothesis.

## Partial fractions

After partial fractions, every term has the form

```text
c_(j,k) / (it-u_j)^k.
```

The inverse Fourier transform is supported on one half-line according to the
sign of `Re(u_j)` and is a constant multiple of

```text
x^(k-1) * exp(-|Re(u_j)|*|x|).
```

Let

```text
delta = min_j |Re(u_j)| > 0.
```

Then the full inverse transform `b` and every derivative away from the origin
satisfy

```text
|b^(m)(x)| <= C_m (1+|x|)^M exp(-delta |x|).
```

## Smooth truncation

Take a smooth cutoff equal to one on `[-T,T]`. The tail error is supported where
`|x|>=T`; all derivatives of that error are bounded by a polynomial in `T`
times `exp(-delta T)`. Its Fourier transform is an entire exponential-type
approximant `A_T` to `-B` with the weighted error required after multiplication
by the rapidly decaying critical-line Xi factor.

## Verdict

```text
proper rational decomposition: passes
explicit exponential physical tail: passes
smooth compact truncation: passes structurally
formal constants/multiplicity bookkeeping: open
```

The next gate is multiplication by `Xi*R` and continuity of the full Weil form,
not existence of a Paley--Wiener approximant.

