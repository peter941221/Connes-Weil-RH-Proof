# 106 Rational Cancellation Prime-Density Threshold

Date: 2026-07-12

## Competing exponential rates

Let

```text
delta = |Re(rho)-1/2|.
```

The nearest pole of `S/P_rho` limits the Paley--Wiener approximation rate to
order `exp(-delta T)` when the physical correction has radius `T`. The
autocorrelation/prime-square error is therefore at best of order

```text
exp(-2 delta T)
```

under a norm-square estimate.

A physical square supported to log radius comparable with `T` sees prime powers
up to `n <= exp(T)` (up to fixed normalization factors). Their absolute Weil
weights satisfy the standard scale

```text
sum_(n <= exp(T)) Lambda(n)/sqrt(n) = O(exp(T/2)).
```

Consequently the direct absolute estimate is

```text
prime error <= C exp((1/2 - 2 delta) T).
```

It decays only when `delta > 1/4`. An RH counterexample may lie arbitrarily
close to the critical line, so no such lower bound on `delta` is available.

## Consequence

Critical-line norm smallness alone does not control the growing finite-prime
sum uniformly for every possible off-line zero. The same support parameter that
improves rational approximation exposes exponentially more prime weight.

## Verdict

```text
Plan 031 Paley-Wiener cancellation: survives for line terms
absolute finite-prime control: rejected for delta <= 1/4
uniform RH route: rejected without structured prime cancellation
```

Reopening requires a prime-sum estimate exploiting oscillation or an exact
same-object cancellation. A crude count, termwise bound, or stronger Sobolev
norm does not change the exponential threshold imposed by the nearest pole.

