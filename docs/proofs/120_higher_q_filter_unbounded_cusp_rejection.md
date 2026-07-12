# 120 Higher-Q Filter Unbounded Cusp Rejection

Date: 2026-07-12

## CC20 Mechanism

CC20 writes in log coordinates

```text
delta(exp(|x|)) = c0 + |x| + O(x^2)
```

and applies `Q_+=-partial_x^2+1/4`.  The derivative jump of `|x|` gives
`-2 delta_0`; the remaining kernel is square-integrable on every bounded
support interval.  This is Theorem `thmqkey1` in
`weil-compo.tex:765-808`, with the motivation at `186-196`.

## Higher Filter

Let `P(D)=Q(D)R(D)` with `deg R=r>0`.  Distributional differentiation gives
terms of order at least `r` at the origin.  Pairing these terms with
`xi*xi^*` is equivalent, after Fourier transform, to a polynomially weighted
root norm:

```text
integral |t|^r |xiHat(t)|^2 dt.
```

The associated operator is unbounded on the CC20 root Hilbert space.  It cannot
be represented as a bounded scalar multiple of the identity plus a compact
operator, and finite-dimensional bad-space removal does not control its high
frequency Weyl sequences.

For `r=0`, multiplying Q by a scalar multiplies the whole source square,
including finite-prime atoms, so the ratio to the prime compensation is
unchanged.

## Verdict

```text
higher-Q relative scalar amplification: impossible
higher-Q bounded compact remainder: false
Q as the unique usable minimal filter: retained
RH: unproved
```

