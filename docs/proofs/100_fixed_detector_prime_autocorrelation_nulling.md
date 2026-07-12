# 100 Fixed-Detector Prime Autocorrelation Nulling

Date: 2026-07-12

## New idea

Do not prove that finite-prime translation blocks are compact. For one compact
detector `g`, kill every visible prime-power atom directly on its convolution
square

```text
F = g* * g.
```

In logarithmic coordinates the prime term reads values of `F` at translations
`± log(n)`. Compact support makes the visible set finite. The target conditions
are therefore

```text
F(log n) = 0
F(-log n) = 0
```

for finitely many prime powers `n`.

## Finite-dimensional realization shape

Take compact smooth bumps `b_j` with generic translations and write

```text
g = sum_j c_j b_j.
```

Orbit values, triple Mellin zeros, and M4 bad-space orthogonality are linear in
`c`. Each prime autocorrelation condition is a Hermitian quadratic equation

```text
c* A_n c = 0.
```

If the finite system has a nonzero solution preserving the negative orbit
pairing, the full QW loses all finite-prime contributions. Triple vanishing
kills the pole directions, leaving the archimedean M4 inequality on the same
square.

## Rejection-first gates

1. The matrices `A_n` may be positive definite on the linear constraint
   kernel, making `c* A_n c = 0` force `c=0`.
2. Nulling all visible shifts may destroy the negative orbit value pattern.
3. Increasing support for the Xi cutoff increases the number of visible prime
   shifts; the number of bump degrees of freedom must grow faster without
   recreating the old radius/count cycle.
4. The prime read-off must be exactly the autocorrelation value on the same
   square, not a separately normalized proxy.

## Status

```text
operator noncompactness: bypassed at one-test level if nulling succeeds
finite algebraic system: explicit but untested
uniform/growing-cutoff solvability: open and likely death gate
Lean owner: forbidden
```

