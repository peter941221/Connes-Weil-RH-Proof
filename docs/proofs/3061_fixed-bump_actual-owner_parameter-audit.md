# Actual-owner parameters for the fixed-bump price (record 3061)

Date: 2026-10-19.

Status: source-backed parameter reduction. It does not numerically price the
fixed-bump bound or the record-3058 tail allowance.

## Exact owner and its radius

For the pinned healthy construction, put

```text
k = tailStart,
d = dist(2,rho),
R = 2^(k+1) + 2 + d,
Z = sourceNontrivialZerosInClosedBall(rho,R) union healthyUnscaledTargetNodes(rho),
N = card(Z).
```

The construction in `C1G8R0OrbitGeometry` uses exactly this radius for the
correction nodes (with no extra route nodes). The target set has at most eight
members: the four functional-equation orbit nodes and the four additional
healthy nodes, with collisions removed by `Finset` union. Interpreting the
cardinalities below as real numbers (the Lean count theorem is stated after
this cast) gives

```text
N <= card(sourceNontrivialZerosInClosedBall(rho,R)) + 8.
```

The existing Jensen/xi-counting bridge gives the following explicit
parameterized count. If an integer `j` satisfies

```text
2*(R + d) + 7 <= 2^(j+4),
```

then

```text
card(sourceNontrivialZerosInClosedBall(rho,R))
  <= (xiDyadicRLogRGrowthExponent(j) - log(norm(completedRiemannXi(2)))) / log(2).
```

The zero-count estimate is an existing Lean theorem, not a new asymptotic
claim. Its growth exponent is the repository's unconditional dyadic xi bound.
The displayed scale condition can always be met by taking a sufficiently
large `j`, but the resulting bound may be weak.

All source-zero nodes in the ball obey `|Im(s)| <= |Im(rho)|+R` and
`|s| <= |rho|+R`. The healthy target nodes add only the orbit and fixed
detector points, so the uniform coarse bounds

```text
H = max_(s in Z) |Im(s)| <= |Im(rho)| + R,
S = max(1,max_(s in Z)|s|) <= |rho| + R + 2
```

are valid. Thus the parameters `N`, `H`, and `S` in record 3060 can all be
bounded from the construction radius and a stated xi-growth rung.

## The remaining separation parameter

For each fixed hypothetical `rho` and finite radius, discreteness of the zeta
zero set proves that the finite distinct node set has

```text
delta = min_(s != t in Z) |s-t| > 0.
```

That is only pointwise positivity. Neither the finite-set/discrete-zero
theorems nor the Jensen count above give a positive lower bound for `delta`
in terms of `k`, `R`, `N`, or `H`. The known quantitative inputs constrain
how many zeros lie in a region, not how close two of them may be. A uniform
bound for distinct zeta-zero gaps would be an additional analytic theorem;
the present source interface does not contain one.

The fixed-bump cost includes

```text
(pi/(2*h*delta))^(N*(N-1)/2),
h = min(1/N, pi/(2*max(H,1))).
```

Therefore bounding `N`, `H`, and `S` does not produce a numerical bound on
`C_bump`: as `delta` decreases, this factor grows without bound. This is the
precise reason record 3060 remains a parameterized construction and cannot yet
price the actual owner or the 3058 allowance.

## Route consequence

There are two live ways to advance the price:

1. Prove a quantitative separation bound for the exact finite source-zero
   owner, including possible near-collisions with the fixed target nodes.
2. Replace the Vandermonde inverse estimate by an actual-owner interpolation
   bound whose cost uses aggregate node information and does not require a
   minimum-gap lower bound.

The existing `C1ExplicitHealthyCorrectionBudget` is already an actual-owner
construction. Its L1 bound contains products of node differences and a seed
derivative ladder, so it has not removed the gap yet; additionally, its
current consumer does not bound the quadratic strip constant. A next attempt
on that construction must price both features, not infer `C` from the L1
estimate alone.

Evidence:

- `ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean` defines the correction radius
  and finite owner used by the healthy construction.
- `ConnesWeilRH/Dev/C1RouteAOwnerCardinality.lean` proves the actual closed-ball
  cardinality estimate from the dyadic xi-growth rung.
- `ConnesWeilRH/Source/CC20YoshidaNearZeros.lean` proves finiteness and
  discreteness of the source-zero set, but no quantitative minimum gap.
- `ConnesWeilRH/Dev/C1ExplicitHealthyCorrectionBudget.lean` gives the
  actual-owner L1 budget and exposes its node-product denominators.
- `docs/proofs/3060_fixed_bump_interpolation_price.md` supplies the conditional
  Vandermonde cost that needs `delta`.
