# 2157 — Near-pin derivative-cost floor for the Route-A correction

Date: 2026-09-29.

Status: EXACT PAPER NO-GO for a separation-free, support-only uniform
derivative-cost bound. It is not a no-go for the actual selected owner or RH.

## Owner and consumer

The owner is the correction in `SelectedPhysicalDerivativeCorrection` on the
actual `CompactLog` support interval `(lower, upper)`, when its finite node
set includes a target `t` and a zero pin `z`. The intended consumer is the
same-owner C3' grouped physical-kernel margin of map 104, through the
derivative seminorm field of that selector. The current assumptions are
compact support, `Laplace(f,t)=1`, and `Laplace(f,z)=0`. The premise being
tested is a uniform derivative-cost bound from support width and target
values alone, with no lower bound on `|z-t|`. Failure means the necessary
cost diverges as a pin approaches the target.

## Exact bound

Write `a=lower`, `b=upper`, `L=b-a>0`,
`X=max(|a|,|b|)>0`, `delta=|z-t|>0`, and
`S=max(|Re t|,|Re z|)`. Let `M=sup_x |f'(x)|`; the selector's stored
`derivativeCost` is at least `M`. Its support condition gives
`f(a)=f(b)=0`. The fundamental theorem of calculus from each endpoint
gives

```
|f(x)| <= M * min(x-a,b-x)        (a <= x <= b),
integral_a^b |f(x)| dx <= (L^2/4) M.
```

For either sign convention in the Laplace exponent, its derivative along
the line segment from `t` to `z` obeys

```
|Laplace'(f,w)|
  <= integral_a^b |x| exp(|Re w| |x|) |f(x)| dx
  <= X exp(X S) (L^2/4) M.
```

The segment identity for the holomorphic Laplace transform then yields

```
1 = |Laplace(f,t)-Laplace(f,z)|
  <= delta * X exp(X S) (L^2/4) M,
derivativeCost >= M >= 4 exp(-X S)/(delta X L^2).
```

For support `[-R,R]`, this simplifies to
`derivativeCost >= exp(-R S)/(delta R^3)`.

## Scope and decision

The finite-node interpolation API permits distinct `z` arbitrarily close
to `t`; for fixed support and bounded real parts, the displayed lower
bound diverges as `delta -> 0`. Therefore support plus interpolation
targets cannot provide a **separation-independent uniform derivative
budget** for the Route-A correction. The finite actual source-zero set has
positive separation for each fixed `rho`, so this does not exclude an
owner-dependent estimate. Its uniform producer would need an explicit
separation bound, a cost estimate that uses the full node geometry, or a
signed argument that avoids charging the derivative seminorm. The exact
C3' sign and complete-owner transfer remain open; no producer Go follows.

## Exact selected-node geometry

`healthyKillSet rho N routeNodes` contains `rho` itself because the closed
ball is centered at `rho`. The actual interpolation owner is the union of
that kill set and `healthyUnscaledTargetNodes rho`, and
`healthyCorrectionValue` gives **target values priority** on overlaps.
Thus the correction takes value `1` at `rho`; the formal
`explicitHealthyCorrection_kills` theorem explicitly requires the killed
node to lie outside the target set. The near-pin bound applies to another
source zero `z` in the ball only when `z` is not one of those targets.

The detector target `t=rho+1/2` has a distinct automatic separation: for
`rho.re>1/2` and every source nontrivial zero `z` with `z.re<1`,

```
|t-z| >= t.re-z.re > rho.re-1/2 > 0.
```

This protects that detector target from a colliding source-zero pin, but
it does **not** control the distance from the orbit target `rho` to another
source zero. Therefore an estimate using only the off-line gap
`rho.re-1/2` cannot pay every target-to-pin derivative cost in the current
owner. The remaining quantitative input is separation from the nonzero
orbit targets, or an alternative signed estimate that does not charge the
near-pin derivative cost.

Intake screen: `mechanism_intake_screen.py` fired GAP on the prose word
"margin". The GAP exhibit in record 2047 concerns an imported theorem's
error term exceeding a margin; this record imports no such theorem and
uses only the exact fundamental-theorem-of-calculus estimate above. The
class is a vocabulary false positive for this scoped no-go.
