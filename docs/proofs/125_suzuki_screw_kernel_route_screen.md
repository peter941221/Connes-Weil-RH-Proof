# 125 Suzuki Screw-Kernel Route Screen

Date: 2026-07-12

## Result

Suzuki's 2026 screw-kernel theorem gives a clean unconditional compact-operator
reduction, but its zero-energy injectivity target is explicitly RH-equivalent.
No lower Volterra or unique-continuation producer was found.  The reduction is
valuable infrastructure, but it is not yet a route worth entering in Lean.

Primary source:

```text
Masatoshi Suzuki, Weil's quadratic form via the screw function,
arXiv:2606.09096v1/v2.
https://arxiv.org/abs/2606.09096
```

## Unconditional Reduction

For `a>0`, let `g` be Suzuki's explicit continuous even screw kernel and let

```text
G_a = P_a G P_a : L2_0(-a,a) -> L2_0(-a,a),
(G u)(x) = integral g(x-y)u(y)dy.
```

Suzuki proves:

```text
QW_a(v) = <G_a Dv,Dv>,
A_a = Friedrichs extension of D* G_a D,
lambda_a = bottom spectrum(A_a),
lambda_a is continuous in a.
```

Here `G_a` is compact self-adjoint with a continuous kernel.  These are genuine
unconditional source theorems, not formal route assumptions.

## Exact RH Gate

The same paper states the consequence of continuity:

```text
RH false
  -> lambda_a < 0 for some a,
small a
  -> lambda_a > 0,
continuity
  -> lambda_a0 = 0 for some finite a0.
```

At zero generalized eigenvalue, the Neumann inverse drops out and the problem
is exactly

```text
ker(G_a0) != {0}.
```

Thus

```text
for every a>0, ker(G_a)={0}
```

is not a lower compactness lemma.  Together with Suzuki's continuity theorem,
it is an RH-equivalent nondegeneracy statement.

## Why Continuous Kernel Does Not Close Injectivity

Compactness and continuity of the kernel imply that `G_a` maps `L2` into a
more regular function space.  They do not imply injectivity.  At a nonzero
eigenvalue, `G_a u=lambda u` transfers regularity from `G_a u` back to `u`.
At zero energy,

```text
G_a u=0
```

contains no such inverse relation.  It is a first-kind integral equation, and
compact operators with continuous kernels can have nontrivial kernels.

The projection `P_a` weakens the pointwise equation further: `P_a G u=0`
only says that `G u` belongs to the removed constant direction on `(-a,a)`.
Differentiating produces a two-sided delay/integral equation containing all
visible prime shifts.  It is not triangular Volterra evolution from one
endpoint.

## Spectral-Side Uniqueness Gap

At the first hypothetical crossing, positive-semidefinite polarization would
annihilate the null vector against every localized test.  Turning that
annihilation into pointwise vanishing at every zeta zero requires a uniqueness
theorem for the resulting zero-frequency distribution.

The available form-domain regularity does not supply analytic or
quasianalytic continuation of that distribution.  A smooth almost-periodic
Fourier series may vanish on an interval without every coefficient vanishing;
ordinary exponential independence is insufficient without an exponential
coefficient bound.  Supplying the missing uniqueness estimate is another form
of the global zero-distribution problem, not a consequence of kernel
continuity.

## Nearby External Volterra Work

Freedman, arXiv:2606.29555, explicitly leaves outside its normalized
finite-core certificate:

```text
quotient-to-original Weyl lift,
uniform omega coverage for |omega|<1/2,
final Weyl/KLM-to-de Branges or RH bridge.
```

Those are precisely the global ownership steps needed before a Volterra
certificate could prove injectivity of the original screw kernel.

## Verdict

```text
continuous compact kernel owner: source-backed and unconditional
continuity of the lowest eigenvalue: source-backed and unconditional
all-a zero-energy injectivity: RH-equivalent
Volterra triangularization of the original kernel: absent
spectral-gap uniqueness theorem: absent
Lean owner for RH route: not authorized
RH: unproved
```

Reopening requires a named theorem that proves injectivity from a strictly
lower property of the explicit kernel.  Restating `ker(G_a)={0}`, a positive
Fredholm determinant, or a zero-free generalized eigenvalue is not a lower
producer.

