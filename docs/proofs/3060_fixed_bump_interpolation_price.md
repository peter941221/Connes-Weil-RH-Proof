# Fixed-bump interpolation price for the orbit correction (record 3060)

Date: 2026-10-19.

Status: parameterized paper construction with an explicit, generally poor
upper bound. It does not prove the selected sign inequality or price the
resulting tail allowance for an actual zero set.

## Node data and a fixed bump family

Let `Z={s_1,...,s_N}` be the distinct interpolation nodes used for one
radius-dependent correction. For the healthy orbit construction these are
the union of the source zeros in the chosen closed ball and the fixed healthy
target nodes. They satisfy

```text
0 <= Re(s_i) <= 3/2,
H = max_i |Im(s_i)|,
S = max(1, max_i |s_i|),
delta = min_(i != j) |s_i-s_j| > 0.
```

The committed healthy target set contains distinct fixed nodes `1/2`, `1`,
and `3/2`, so `N>=2` and `delta` is defined.

The target values `y_i` have modulus at most one: they are zero at the added
source-zero nodes and are zero or unit values at the fixed healthy targets.
Choose one nonnegative smooth bump `phi` supported in `(-1,1)` with integral
one. Write `B_k = integral |phi^(k)(v)| dv` for `k=0,1,2`.

Set

```text
h = min(1/N, pi/(2*max(H,1))),
eta = min(h/3, 1/(4*S), 1/4),
u_j = -1/2 + j*h,  j=0,...,N-1,
phi_eta(v) = eta^(-1)*phi(v/eta).
```

Each `x -> phi_eta(log(x)-u_j)` is smooth and supported in the fixed allowed
positive window `(exp(-1), exp(1))`. Its Mellin value at `s_i` is

```text
Mellin_j(s_i) = exp(s_i*u_j)*Phi_eta(s_i),
Phi_eta(s) = integral exp(s*v)*phi_eta(v) dv.
```

Since `|s_i|*eta <= 1/4`,
`|Phi_eta(s_i)-1| <= (1/4)*exp(1/4) < 1/2`, hence
`|Phi_eta(s_i)| >= 1/2`.

## Explicit matrix inverse bound

The interpolation matrix factors as `A = D*V`, where

```text
D_ii = exp(-s_i/2)*Phi_eta(s_i),
V_ij = lambda_i^j,
lambda_i = exp(h*s_i).
```

It is a row-scaled Vandermonde matrix. The height choice gives
`|h*(Im(s_i)-Im(s_j))| <= pi`. Using

```text
|2*sinh((x+i*y)/2)|^2 = 4*(sinh(x/2)^2 + sin(y/2)^2),
```
and `sin(|y|/2) >= |y|/pi` for `|y|<=pi`, we obtain

```text
|lambda_i-lambda_j| >= 2*h*delta/pi.
```

Also `|D_ii| >= exp(-3/4)/2`, while every entry of `A` has modulus at most
`exp(2)`. Since `V` is a Vandermonde matrix,
`det(V)=product_(i<j)(lambda_j-lambda_i)`. Therefore

```text
|det(A)| >= (exp(-3/4)/2)^N
            * (2*h*delta/pi)^(N*(N-1)/2),
||A||_2 <= N*exp(2),
||A^(-1)||_2 <= (N*exp(2))^(N-1)
                 * (2*exp(3/4))^N
                 * (pi/(2*h*delta))^(N*(N-1)/2).
```

The last inequality uses the product formula for singular values:
`|det(A)|` is their product and each is at most `||A||_2`.

Solving `A*c=y` gives
`sum_j |c_j| <= N*||A^(-1)||_2`, since `||y||_2 <= sqrt(N)`. The resulting
correction is the finite sum
`f(x)=sum_j c_j*phi_eta(log(x)-u_j)` and realizes every prescribed node value
exactly.

## Bound the decay constant

For `sigma` in `[0,1]`, the logarithmic slice of one translated bump is
`exp(-sigma*u)*phi_eta(-u-u_j)`. Its support lies in `|u|<=3/4`. The product
rule and `eta<=1` give

```text
sum_(k=0..2) integral |d^k/du^k slice_sigma(f)(u)| du
  <= exp(3/4)*(3*B_0+3*B_1+B_2)*eta^(-2)*sum_j |c_j|.
```

The source quadratic Fourier-decay theorem multiplies these three derivative
integrals by four. Thus the correction has a valid strip constant bounded by

```text
C_bump = K_phi*eta^(-2)*N*(N*exp(2))^(N-1)
         *(2*exp(3/4))^N*(pi/(2*h*delta))^(N*(N-1)/2),
K_phi = 4*exp(3/4)*(3*B_0+3*B_1+B_2).
```

Consequently it suffices to take

```text
orbitIndex >= max(0, ceil(log_2((6*pi)^2*C_bump/epsilon)))
```

for the source's sufficient product-tail condition
`(6*pi)^2*2^(-(orbitIndex+1))*C_bump < epsilon`.

## Cost comparison and verdict

The same divided-difference and strip-Plancherel argument as record 1738
gives a lower bound for any `m` distinct correction zeros `z_j` in the source
strip, all within distance `R` of a target point `rho` with `D(rho)=1`:

```text
C >= (sqrt(3)/(64*e))*m!/R^m.
```

The matrix bound has logarithmic cost containing
`N*(N-1)/2 * log(pi/(2*h*delta))`. It is finite for every fixed distinct
node set, but it can be far larger than this factorial lower bound. The lower
bound does not contradict this upper bound; their node sets and
quantitative parameters must be matched before comparing them. The present
construction proves quantitative existence, but its conditioning factor
depends on the minimum node separation and grows quadratically in the number
of nodes in the exponent. No data currently show that the resulting
`orbitIndex`, `C_S`, or 3058 allowance is affordable. Do not promote this as a
producer or as evidence that the actual minimum correction is large.

The exact next price is to insert the actual finite node set for a named
source zero, measure its certified `N`, `H`, `S`, and `delta`, then compare
`C_bump` with both the record-1738 lower bound and the same-owner core margin.
If it loses by orders of magnitude, freeze this fixed-bump basis and seek a
better conditioned interpolation construction.

Evidence:

- `ConnesWeilRH/Source/CC20YoshidaNearZeros.lean` defines the Mellin vectors
  and proves their span is the full finite target space.
- `ConnesWeilRH/Source/CC20YoshidaTail.lean` gives the derivative-integral
  formula for the quadratic strip constant.
- `docs/proofs/1738_selected_orbit_joint_symbol_and_tail_sampling.md` gives
  the factorial interpolation lower bound and the bridge from L1 cost to the
  strip constant.
