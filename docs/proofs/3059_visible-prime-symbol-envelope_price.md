# Pricing the visible-prime symbol envelope (record 3059)

Date: 2026-10-19.

Status: exact elementary upper bound from the geometry's support cutoff. It
does not estimate the actual signed prime symbol sharply and is not a no-go
for the selected-owner sign inequality.

## Geometry-linked cutoff

For one `OrbitG8Geometry`, write

```text
L = orbitIndex + 2,
X = exp(2*L).
```

In Lean, `globalPrimeIndexSet` stores prime powers `q` with a nonzero
prime-power term, and the geometry gives `q < X`. For this price, choose `S`
to be the exact set of prime bases that occur in those visible powers. If
`q=p^k` is visible, then `p <= q < X`, so every `p` in this canonical `S`
satisfies `p<X`. This estimate does not apply to an arbitrary superset `S`
that contains irrelevant primes. The symbol envelope of records 1738 and
3058 is

```text
C_S = 2*sum_(p in S) log(p)/(sqrt(p)-1).
```

For every integer `p >= 2`,

```text
sqrt(p)-1 >= sqrt(p)/4,
```

because `1-1/sqrt(p) >= 1-1/sqrt(2) > 1/4`. Thus

```text
C_S <= 8*sum_(p in S) log(p)/sqrt(p)
    <= 8*sum_(2<=k<X) log(k)/sqrt(k).
```

Let `N = ceil(X)`. Since `log(k) <= log(X)` for integers `k<X`, and
`sum_(k=1..N) 1/sqrt(k) <= 2*sqrt(N)`,

```text
C_S <= 16*log(X)*sqrt(N)
    <= 16*(2*L)*sqrt(X+1)
    <= 32*sqrt(2)*L*exp(L).
```

The last inequality uses `X>=1`, hence `X+1<=2X`. A slightly looser but
simpler bound is `C_S <= 48*L*exp(L)`, since `sqrt(2)<3/2`.

## Consequence for the absolute-tail allowance

Substitution into record 3058 gives the explicit geometry-level estimate

```text
E_tail(T*) <= (16*epsilon^2)/(3*pi*T*^3)
  * (K + 8 + 48*L*exp(L) + log(2) + log(T*) + 1/3).
```

This bound is exponentially increasing in the support half-width `L` before
the factors `epsilon^2/T*^3` are accounted for. The construction does connect
some of these parameters: `tailStart` is chosen from `T` and the zero height;
the correction and its quadratic decay constant `C` are then chosen using a
radius depending on `tailStart` and `rho`; finally `orbitIndex` is chosen so
that

```text
(6*pi)^2 * (1/2)^(orbitIndex+1) * C < 1.
```

The pinned construction chooses the minimal such index. However, the
finite-interpolation theorem provides no quantitative upper bound for
`C` in terms of that radius. The displayed condition therefore gives no
usable upper bound for `orbitIndex`, and the current source chain does not
show that `epsilon^2*L*exp(L)/T*^3` is small. In the pinned construction,
`epsilon=1`; the geometry interface also permits other parameter choices,
which would need their own price.

## Verdict

The 3058 reduction remains a valid same-owner decomposition, but its current
uniform envelope does not price the allowance at a useful scale. This only
rejects promotion based on the coarse support cutoff plus the termwise bound
`C_S`; it does not show the actual `C_S` is large, nor that a sharper signed
prime estimate or a relation among `orbitIndex`, `tailStart`, `epsilon`, and
the zero height cannot make the allowance small.

Before spending effort on a core-margin proof for 3058, first establish one
of those sharper same-owner controls. Without it, `Q_core(T*) >= E_tail(T*)`
may impose an exponentially large error budget.

Evidence:

- `ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean` supplies the support-derived
  prime cutoff and the separate tail parameters.
- `ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean` also shows the construction
  order: `tailStart`, then radius-dependent correction and `C`, then the
  minimal `orbitIndex`.
- `ConnesWeilRH/Source/CC20YoshidaConvolution.lean` supplies the quadratic
  correction constant and the displayed sufficient orbit-index condition.
- `docs/proofs/3058_joint_symbol_absolute_tail_reduction.md` supplies the
  absolute-tail allowance being priced.
