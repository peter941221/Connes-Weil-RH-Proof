# 038 Log-Factor Cross Read-Off Rejection

Date: 2026-07-12

Status: positive local factor survives; half-space cross read-off is rejected
by an exact support test.

## Candidate

For `a=p^(-1/2)` and translation `U_p`, define

```text
N_p = log((I-aU_p)^*(I-aU_p)) - 2 log(1-a)I >= 0.
```

Its Fourier coefficients are

```text
(N_p)_m = -a^m/m,  m != 0,
```

so a formal crossing trace would have the exact `-W_p` coefficient.

Factor `N_p=B_p^*B_p` and use the positive cross block

```text
A_p(h)=Q B_p P C_h.
```

## Exact Death Test

The positive trace is

```text
||A_p(h)||_HS^2
  = Tr(C_h^* P B_p^* Q B_p P C_h).
```

This contains the projection/boundary operator `B_p^* Q B_p`, not the linear
convolution operator `N_p=B_p^*B_p`.  The two differ by

```text
B_p^* P B_p,
```

which is an additional nonzero boundary term.

Choose a nonzero compact smooth `h` whose support width is strictly smaller
than `log(p)/2`.  Then the convolution square has support below `log(p)`, so
the exact finite-prime Weil atom is zero:

```text
W_p(h^**h)=0.
```

But `B_p` has a nonzero positive translation coefficient, and that translation
maps a nonzero strip of `P` across `Q`; hence

```text
||Q B_p P C_h||_HS^2 > 0.
```

Therefore the positive cross trace cannot equal `-W_p` for the same test.

## Verdict

```text
N_p positive and correct Fourier coefficients: pass
outer factor exists formally: pass
positive cross trace = linear Weil atom: false
extra boundary term: nonzero on a prime-invisible test
Plan 038 shortcut: rejected
```

Subtracting the extra term would restore the linear read-off but would remove
the positive-trace guarantee. A viable Plan 036 owner still needs a new
non-translation boundary identity controlling this term.

