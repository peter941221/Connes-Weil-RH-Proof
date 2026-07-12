# 111 Log-Poisson Positive Trace Read-Off Death

Date: 2026-07-12

## Candidate Algebra

Let `U` be unitary and `0<a<1`.  Functional calculus gives the positive
operator

```text
L = 2 log(1+a) I - log((I-aU)^*(I-aU)) >= 0,
```

with expansion

```text
L = 2 log(1+a) I + sum_(m>=1) a^m/m (U^m+U^(-m)).
```

The coefficient is exactly the one needed before a crossing of length
`m log(p)` supplies `m log(p)`.

## Positivity Versus Linear Read-Off

To obtain a positive trace from a half-line boundary, one must factor `L`:

```text
A = Q L^(1/2) P C_h,
Tr(A* A) >= 0.
```

In the log coordinate, `L^(1/2)` is a translation-invariant convolution
operator with kernel `b`, while `C_h` has kernel `h`.  The Hilbert--Schmidt
trace is therefore a crossing integral of the form

```text
integral_0^infinity t * |(b*h)(t)|^2 dt,
```

up to the reflected orientation.  This is a quadratic continuous convolution
energy.  It is not the linear sum of point evaluations of `h**h` at the
discrete shifts `m log(p)`.

If instead one inserts `L` linearly, the Fourier coefficients do have the
desired `a^m/m` values, but the identity component has infinite half-line bulk
trace and the crossing difference is not a positive quadratic form.  Removing
that bulk by hand recreates the missing sign theorem.

Thus the candidate cannot simultaneously provide the two required properties:

```text
positive same-object trace
and
linear Weil prime-power read-off.
```

## Verdict

```text
positive log-Poisson operator: valid spectral object
exact prime-power coefficient: valid algebraic identity
positive trace with same linear read-off: not obtained
Plan 033: rejected as a lower owner
RH: unproved
```

