# 115 Positive Euler Multiplier Compensation No-Go

Date: 2026-07-12

## One Prime

Let `0<a<1`, `U` be unitary, and

```text
L(a)=2 log(1+a)I-log((I-aU)^*(I-aU)).
```

Functional calculus gives

```text
L(a)=2 log(1+a)I+sum_(m>=1) a^m/m (U^m+U^(-m)).
```

Taking the radial derivative produces

```text
M(a)=a L'(a)
  =2a/(1+a)I+sum_(m>=1)a^m(U^m+U^(-m)).
```

For `U=exp(i theta)`, direct simplification gives

```text
M(a,theta)
  = 2a(1-a)(1+cos theta)
      /((1+a)(1-2a cos theta+a^2)) >= 0.
```

The scalar shift is sharp.  The nonconstant symbol is

```text
2 sum_(m>=1)a^m cos(m theta)
  =2 Re(a exp(i theta)/(1-a exp(i theta))),
```

whose minimum is `-2a/(1+a)` at `theta=pi`.

## Several Primes

After multiplying by `log p`, the desired finite-prime symbol is

```text
V_S(t)=2 sum_(p in S_f) log(p)
  sum_(m>=1)p^(-m/2) cos(m t log(p)).
```

Distinct prime logarithms are rationally independent: an integer relation
would exponentiate to a multiplicative relation among distinct primes.
Kronecker approximation therefore makes all phases `t log(p)` simultaneously
arbitrarily close to `pi`.  It follows that

```text
inf_t V_S(t)
  = -sum_(p in S_f) 2 log(p)/(sqrt(p)+1).
```

Any scalar shift making `V_S(D)` positive must be at least the opposite of this
infimum.  The lower bound diverges over increasing prime sets.  In particular,
it cannot be merged into a fixed `-2 Id` archimedean remainder uniformly in the
support cutoff.

## Consequence

The radial log-Euler derivative solves the coefficient problem but exposes the
same unavoidable diagonal cost seen in the Lindblad screens, now with the
optimal scalar.  Positivity must arise from a boundary/projection identity
that cancels this scalar before taking the positive trace; direct Fourier
multiplier positivity cannot close Plan 036.

```text
exact positive one-prime owner: retained as diagnostic
direct cofinal finite-S owner: rejected
non-translation-invariant cancellation: still open
RH: unproved
```

