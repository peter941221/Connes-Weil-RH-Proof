# Plan 022 Fixed-Convolution Second Verdict

Date: 2026-07-11

Verdict: **the fixed convolution subroute survives and is now primary.** It is
not proved. The second round rejects three tempting shortcuts, identifies a
fixed double-Mobius direction inside the surviving frame, and verifies it
through `N=16384` as a rejection test.

## 1. Rejected Shortcuts

The first-block correlation cannot be treated as the whole main term. Frame
energy beyond `2N` is comparable to energy on `(N,2N]`, and the two correlation
pieces can oppose one another, as at `N=1024`.

The exact intersection

```text
span(gamma_(N+1),...,gamma_(3N)) intersect V_N^perp
```

also fails. Although its dimension is about `N`, its normalized target capture
drops from about `0.299` at `N=16` to `0.00050` at `N=512`.

Finally, the proposed general Bessel inequality for all moment-zero dyadic
coefficients is false numerically. Its generalized largest eigenvalue grows
from about `1.66` at `N=32` to `209.8` at `N=4096`, approximately linearly in
`N`. Any energy proof must use the selected arithmetic coefficients.

## 2. Fixed Direction Recovered From The Frame

The normalized eight-correlation vector is consistently aligned with

```text
(-mu(1)/1,...,-mu(8)/8).
```

Adjacent-scale direction cosines range from about `0.90` to `0.98`. This yields
the fixed coefficient

```text
Q(k) = -sum_(d|k, d<=8) mu(d)*mu(k/d)/d.
```

No per-scale coefficient is fitted. With the old anchor

```text
h_N = sum_(N<k<=2N) Q(k)gamma_k
      - N*(sum_(N<k<=2N) Q(k)/k)*gamma_N,
```

the sequence vanishes for `n<N`, while `<r_N,h_N>` equals the correlation with
the pure new block because `r_N` is orthogonal to `gamma_N`.

The key exact identity is

```text
1 * Q = theta,
theta(d)=-mu(d)/d for d<=8 and 0 otherwise.
```

Thus the global divisor sum of `Q` has fixed finite support. The remaining
terms come only from truncating `Q` to `(N,2N]` and adding the old anchor.

## 3. Rejection Evidence

The fixed normalized certificate stays between about `0.121` and `0.332` in
the double-precision runs through `N=4096`. At the largest high-cutoff run:

```text
N=4096
cutoff=250000
fixed capture * log(N) = 0.12133757135219235
||h_N||^2              = 0.17480467064364164
normal residual        = 7.819018000929052e-12
first-(N-1) leakage    = 1.3877787807814457e-17
```

Calibrated float32 rejection runs give approximately `0.1572` at `N=8192` and
`0.2544` at `N=16384`. These are not theorem-grade values; they only show that
the fixed formula does not collapse on the next two unseen scales.

## 4. Current Bottom

The route now needs two unconditional estimates on the same fixed object:

```text
||h_N||^2 <= C,
|<r_N,h_N>|^2 >= (c/log N)*||r_N||^2.
```

The energy proof must exploit the finite divisor collapse. The correlation
proof must not expand `r_N` through `G_N^-1`. Plan 022 remains worth research
because the object is fixed, scale-stable, initially localized, and has a new
finite convolution identity; it is not yet a guaranteed RH route.

## 5. Correlation Stress Tests

A scan of every integer `N` from `16` through `512` found no correlation sign
change. The lowest normalized certificate was approximately `0.1029` at
`N=100`. This rejects the concern that positivity occurs only on the sampled
dyadic subsequence.

The correlation is not pointwise positive. Across dyadic scales through
`N=4096`, negative pointwise products account for roughly 25--43 percent of the
positive product mass. The first block `(N,2N]` contributes positively at every
tested scale, while the tail beyond `2N` is smaller but becomes negative at
`N=1024`. The intended proof shape is therefore a positive first-block divisor
main term with a strict global tail error, not a pointwise sign theorem.

The normalized residual itself has no stable smooth block profile. Adjacent
dyadic profile correlations are often negative. The stable structure belongs
to the arithmetic convolution direction, not to a continuous limiting shape
of `r_N`.

## 6. Further Rejection Guards

Two broader geometric attempts fail:

```text
general moment-zero Bessel bound:
  generalized top eigenvalue grows approximately linearly in N

pure-new exact old-orthogonal window (N,3N]:
  normalized target capture falls to about 0.00050 by N=512
```

The eight explicit target correlations are also not dominated by the direct
`<gamma,b_d>` term; the old projection contribution is often two to three
times larger. A successful proof must use the residual orthogonality equations
structurally, but may not simply expand them through the old inverse Gram
matrix.
