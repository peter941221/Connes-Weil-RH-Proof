# 116 Log-Factor Cross Trace Has An Extra Boundary Term

Date: 2026-07-12

## Candidate Identity

The nonnegative symbol

```text
n_p(theta)=log(|1-a exp(i theta)|^2/(1-a)^2)
```

has Fourier coefficients `-a^m/m` for `m != 0`.  It is tempting to factor
`N_p=B_p^*B_p` and identify

```text
Tr((Q B_p P C_h)^*(Q B_p P C_h))
```

with the finite-prime Weil atom.

## Why The Identification Fails

Algebraically,

```text
P B_p^* Q B_p P
  = P B_p^*B_p P - P B_p^*P B_p P.
```

The first term contains the desired linear symbol; the second term is a
nonzero half-line boundary correction.  It cannot be dropped while preserving
positivity.

Take `h` nonzero and compactly supported in an interval of width less than
`log(p)/2`.  The square `h^**h` has no support at `+/- log(p)`, so the Weil
prime atom is exactly zero.  Nevertheless, any nonconstant analytic factor
`B_p` has a nonzero translation coefficient; `Q B_p P C_h` crosses the half-line
on a positive-measure strip, making its Hilbert--Schmidt norm strictly positive.

This is a same-object counterexample to the proposed read-off, independent of
numerical truncation or a choice of finite section.

## Verdict

```text
positive factorization: valid
linear prime read-off from cross norm: rejected
extra boundary correction: unavoidable
RH: unproved
```

