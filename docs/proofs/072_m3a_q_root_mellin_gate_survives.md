# 072 M3A Q-Root Mellin Gate

Date: 2026-07-12

Result: the logarithmic Q-root also survives the finite Mellin-node rejection
gate. The only zero of its Laplace multiplier is a node whose required value
is already zero.

## Repository Convention

`CC20YoshidaConvolution.lean` defines

```text
laplaceAt(f,s) = integral_x exp(s*x) f(x).
```

For a compactly supported smooth `xi`, integration by parts has no boundary
term and gives

```text
laplaceAt(d xi,s) = -s laplaceAt(xi,s).
```

For `L=d+1/2`, therefore,

```text
laplaceAt(L xi,s) = (1/2-s) laplaceAt(xi,s).
```

This agrees with the source normalization
`Q=-(rho d/drho)^2+1/4` recorded in
`docs/audits/cc20-post-q-remainder-term-map.md:46`; logarithmic coordinates
send `rho d/drho` to `d/dx`.

## Route Nodes

`CC20YoshidaCriterion.lean` sets the desired values to

```text
s=0     -> 0
s=1/2   -> 0
s=1     -> 0
s=rho   -> 1.
```

The Q-root multiplier is

```text
s=0     ->  1/2
s=1/2   ->  0
s=1     -> -1/2.
```

Thus all three required vanishings are preserved. The multiplier vanishes at
`s=1/2`, but the required value there is already zero.

At the detector node, choose the pre-root interpolation value

```text
laplaceAt(xi,rho) = (1/2-rho)^-1.
```

The route assumes `rho.re != 1/2` in the off-line contradiction. Hence
`rho != 1/2`, so this value is defined and `laplaceAt(L xi,rho)=1`.
The repository's finite-window Mellin surjectivity theorem realizes arbitrary
values on any finite set of distinct nodes, so this rescaled assignment creates
no new finite interpolation obstruction.

## Decision

```text
Q normalization/sign: matched
triple Mellin vanishing: preserved
off-line detector normalization: preserved after nonzero rescaling
finite-node rejection: failed to kill the candidate
M3A: pending
```

The remaining first hard gate is not finite interpolation. It is the proved
compact-domain identity connecting the same `xi`, `L xi`, its convolution
square, and the source `K_I` kernel action.
