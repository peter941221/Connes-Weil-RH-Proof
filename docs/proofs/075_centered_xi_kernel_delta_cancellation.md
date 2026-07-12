# 075 Centered Xi-Kernel Delta Cancellation

Date: 2026-07-12

Result: the project theta kernel can produce an ordinary centered Xi inverse
transform. The additive `+1` in `completedRiemannXi` cancels the Dirac mass
created by the derivative jump at the theta split point.

## Log Coordinate

Let

```text
K(t)   = completedRiemannXiKernel(t),
k(x)   = K(exp(2x)),
psi(x) = exp(x/2) k(x),
u      = s-1/2.
```

The repository identity

```text
completedRiemannZeta0(s)
  = mellin(K,s/2)/2
```

becomes

```text
completedRiemannZeta0(s) = integral_R exp(u*x) psi(x) dx.
```

The small/large theta-kernel functional equation makes `psi` even.

## Jump And Delta

Above `t=1`, the modified kernel is `theta(t)-1`. Below `t=1`, it is
`theta(t)-t^(-1/2)`. These values agree at `t=1`, while the log derivative has
jump

```text
psi'(0+) - psi'(0-) = -1.
```

Therefore, in distributions,

```text
psi'' = classicalSecondDerivative(psi) - delta_0.
```

The project normalization is

```text
completedRiemannXi(s)
  = s(s-1) completedRiemannZeta0(s) + 1
  = (u^2-1/4) completedRiemannZeta0(s) + 1.
```

Under the centered bilateral Laplace transform, the `+1` is the transform of
`delta_0`. It cancels the derivative jump exactly. Hence the centered inverse
transform of Xi is the ordinary function

```text
PhiXi(x) = classicalSecondDerivative(psi)(x) - psi(x)/4
```

with its value at zero supplied by continuous extension.

## One-Factor Division

If an entire transform `H` with inverse `phi` satisfies `H(z)=0`, then

```text
H(s)/(s-z)
```

has inverse candidate

```text
q(x) = exp(-z*x) integral_[x,infinity) exp(z*y) phi(y) dy
     = -exp(-z*x) integral_[-infinity,x] exp(z*y) phi(y) dy.
```

The equality of the two tails is exactly the zero moment `H(z)=0`. Thus the
right formula controls `x -> +infinity` and the left formula controls
`x -> -infinity`; no homogeneous exponential tail remains. The same argument
can be iterated through the analytic multiplicity of a zero.

## Remaining Proof Obligations

```text
prove the derivative jump and continuous extension from the named theta API
prove explicit derivative tail bounds for PhiXi
transport analytic multiplicities around the full zero orbit
iterate the one-factor division estimate with uniform strip constants
```

This is a mathematical reduction, not yet a Lean theorem. It advances Plan
025 Gate X2 but does not authorize a route owner.

## Numerical Cross-Check

The reproducible probe
`docs/proofs/079_centered_xi_kernel_probe.py` evaluates the theta series at 80
decimal digits. It returns

```text
psi'(0+) = -0.5
psi'(0-) =  0.5
jump     = -1.0
```

and the regular kernel values approach a finite limit near `1.7868` from the
tested positive side. This checks the jump sign and scale only; the analytic
theta derivative bound remains the owner.
