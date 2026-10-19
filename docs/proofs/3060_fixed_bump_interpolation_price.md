# Fixed-bump interpolation price for the orbit correction (record 3060)

Date: 2026-10-19.

Status: parameterized paper construction with an explicit upper bound. It
does not prove the selected sign inequality or price the resulting tail
allowance for an actual zero set.

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

Each positive-variable test `x -> phi_eta(log(x)-u_j)`, extended by zero
outside its positive support, pulls back to the compact smooth log-coordinate
function `u -> phi_eta(u-u_j)` supported in `(-1,1)`. Its Mellin value at
`s_i` is

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

It is a row-scaled Vandermonde matrix. The node constraints give `Re(s_i)>=0`,
`N>=2`, hence `h<=1/2`; they also give
`|h*(Im(s_i)-Im(s_j))|<=pi`. For `d=s_i-s_j`, set
`x=h*Re(d)` and `y=h*Im(d)`. Then `|x|<=3/4`, `|y|<=pi`. Using

```text
|2*sinh((x+i*y)/2)|^2 = 4*(sinh(x/2)^2 + sin(y/2)^2),
```
and `sin(|y|/2) >= |y|/pi` for `|y|<=pi`, together with
`sinh(|x|/2)>=|x|/2` and `1/2>=1/pi`, gives

```text
|lambda_i-lambda_j| >= 2*h*delta/pi.
```

Indeed, `|exp(h*d)-1|=2*|sinh((x+i*y)/2)| >= (2/pi)*sqrt(x^2+y^2)`.
Also `|exp(h*s_j)|=exp(h*Re(s_j))>=1`. Hence
`|lambda_i-lambda_j|>=2*h*|s_i-s_j|/pi>=2*h*delta/pi`.
The height restriction prevents the imaginary difference from wrapping around
the exponential period; the real-part difference is controlled by the
hyperbolic-sine term.

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
`f(x)=sum_j c_j*phi_eta(x-u_j)` and realizes every prescribed node value
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
integrals by four. Therefore the correction has a strip constant bounded by:

```text
C_bump = K_phi*eta^(-2)*N*(N*exp(2))^(N-1)
         *(2*exp(3/4))^N*(pi/(2*h*delta))^(N*(N-1)/2),
K_phi = 4*exp(3/4)*(3*B_0+3*B_1+B_2).
```

The following orbit-index choice suffices:

```text
orbitIndex >= max(0, ceil(log_2((6*pi)^2*C_bump/epsilon)))
```

since it makes the left side at most `epsilon/2` when the logarithm argument
is at least one; if it is below one, index zero also satisfies the strict
product-tail condition.

## Cost comparison and verdict

The same divided-difference and strip-Plancherel argument as record 1738
gives a lower bound for any `m` distinct correction zeros `z_j` in the source
strip, all within distance `R` of a target point `rho` with `D(rho)=1`:

```text
C >= (sqrt(3)/(64*e))*m!/R^m.
```

The matrix bound has logarithmic cost containing
`N*(N-1)/2 * log(pi/(2*h*delta))`. It is finite for every fixed distinct
node set, but can be far larger than the factorial lower bound of record
1738. The lower bound does not contradict this upper bound; their node sets
and parameters must be matched before comparing them. No data show that the
resulting `orbitIndex`, `C_S`, or 3058 allowance is affordable. This is not a
producer result or evidence that the actual minimum correction is large.

The next price is to insert the actual finite node set for a named source
zero, certify `N`, `H`, `S`, and `delta`, and compare `C_bump` with the
record-1738 lower bound and a same-owner core margin. The existing
`C1ExplicitHealthyCorrectionBudget` construction gives an L1 budget for the
actual owner, but no quadratic strip constant; that separate bridge remains
open.

Evidence:

- `ConnesWeilRH/Source/CC20YoshidaNearZeros.lean` defines the Mellin vectors
  and proves their span is the full finite target space.
- `ConnesWeilRH/Source/CC20YoshidaTail.lean` gives the derivative-integral
  formula for the quadratic strip constant.
- `docs/proofs/1738_selected_orbit_joint_symbol_and_tail_sampling.md` gives
  the factorial interpolation lower bound and the bridge from L1 cost to the
  strip constant.
