# 081 Canonical Xi-Quotient Tail Lemma

Date: 2026-07-12

Result: the one-factor Xi quotient has the same two-sided superexponential
tail class as the centered Xi kernel. Finite orbit multiplicities preserve
this class. This advances Plan 025 Gate X2 from a heuristic to a concrete
real-analysis lemma.

## Base Kernel

For `x>0`, the centered theta expression has the form

```text
psi(x) = 2 exp(x/2) sum_(n>=1) exp(-pi*n^2*exp(2x)),
```

and `psi(-x)=psi(x)`. The centered Xi inverse is

```text
phi(x) = psi''(x) - psi(x)/4
```

after the delta cancellation in proof record 075.

Differentiating termwise, every fixed derivative satisfies a bound of the
shape

```text
|phi^(m)(x)| <= C_m (1+exp(2|x|))^(d_m)
                 * exp(-c_m*exp(2|x|))
```

for sufficiently large `|x|`, with positive `c_m`. The project theorems
`norm_completedRiemannXiKernel_le_exp_of_one_lt` and
`norm_completedRiemannXiKernel_le_inv_exp_of_mem_Ioo` provide the two theta
branches; the derivative version follows from the same uniformly convergent
theta series after termwise differentiation.

## One Zero Division

Let `z=a+ib` with `|a|<1/2`, and suppose the transform of `phi` vanishes at
`z`. Define

```text
q_z(x) = exp(-z*x) integral_[x,infinity) exp(z*y) phi(y) dy.
```

The zero moment gives the equivalent left-tail formula

```text
q_z(x) = -exp(-z*x) integral_[-infinity,x] exp(z*y) phi(y) dy.
```

For `x -> +infinity`, the first formula combines the superexponential tail of
`phi` with `exp(-a*x)`. For `x -> -infinity`, the second formula does the same.
Therefore, for every derivative order `m`,

```text
|q_z^(m)(x)| <= C_(z,m) (1+exp(2|x|))^(D_(z,m))
                  * exp(-c_(z,m)*exp(2|x|)).
```

The ODE `q_z' + z q_z = -phi` supplies the derivative recursion, so no
separate singular integral estimate is needed.

## Orbit And Multiplicity

Divide successively by each factor `(s-z)` according to the analytic order of
Xi at the four orbit points. At every repeated step the current transform
still vanishes at the next copy of `z`; hence the same two-tail formula applies.
The orbit is finite, so the final quotient has a finite constant depending on
the hypothetical zero but retains the same superexponential class.

## Decision

```text
one-factor tail mechanism: passes
finite multiplicity/orbit iteration: passes conditionally on termwise theta
  derivative bounds
Plan 025 X2: reduced to explicit theta-series estimates
remaining X2 work: write the derivative bounds and transform-domain theorem
```

This is not yet a Lean owner or a source-sign theorem. The next independent
gate remains X5: stable joint conditioning against the cutoff-dependent M4
bad space.
