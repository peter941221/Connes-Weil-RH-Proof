# 066 Fixed-S Kernel Latest Source Audit

Date: 2026-07-12

Result: no newly published source found that closes the fixed-S M2 Lean gate.
The obstruction remains the concrete semilocal analytic carrier, not the
abstract positive-trace theorem.

## Search Target

The missing theorem is the same-object statement

```text
X_S = A_S / O_S^*
H_S = L2(X_S, quotient Haar measure)
A_(S,Lambda,g) = P_hat_Lambda P_Lambda U_S(g)
K_A is a measurable L2 kernel for A
integral |K_A|^2 < infinity
```

This is the producer needed by M2 before
`BasisHilbertSchmidtData.summable_normSq` can be instantiated with the actual
CC20 operator.

## Latest Primary Source

Alain Connes, *The Riemann Hypothesis: Past, Present and a Letter Through
Time*, arXiv:2602.04022 (February 2026):

<https://arxiv.org/abs/2602.04022>

Sections 7.3--7.6 describe the semilocal adele quotient, the trace formula,
infrared/ultraviolet cutoffs, and the prolate wave operator. The paper presents
these as a geometric strategy and discusses convergence of finite Euler
products; it does not state a fixed-S measurable kernel representative or an
integrable square majorant for `P_hat P U_S(g)`.

The same paper's bibliography points back to the semilocal operator source:

```text
Connes--Consani--Moscovici,
Zeta zeros and prolate wave operators: semilocal adelic operators,
arXiv:2310.18423v2.
```

The repository's earlier certificate already checked that source and found only
the quotient/scattering setup and bounded Sonin-space comparisons. Those
comparisons do not construct the quotient measure, complex `L2` realization,
orthogonal cutoffs, or kernel majorant required here.

## Decision

```text
M2 abstract trace layer: accepted
M2 fixed-S operator/kernel owner: still unavailable
M3B finite-S fallback: inactive
route consumer or root status: unchanged
```

Do not introduce a Lean field containing an arbitrary `L2` carrier, kernel, or
summability proof. That would make the positive trace conditional on stored
conclusions rather than source data. Reopening M2 requires either a concrete
construction of the semilocal quotient analytic model or a primary source that
supplies the displayed kernel theorem.

## New Archimedean Reduction

One useful source appeared in the latest search:

Alain Connes and Walter D. van Suijlekom, *Quadratic Forms, Real Zeros and
Echoes of the Spectral Action*, arXiv:2511.23257, Theorem 3.1:

<https://arxiv.org/abs/2511.23257>

For an even continuous kernel `h(x-y)` on a compact interval, the associated
integral operator is Hilbert-Schmidt and hence compact self-adjoint. This does
not instantiate the CC20 remainder directly, because `Qδ` has a singular
principal term. CC20's decomposition is instead

```text
Qδ = -2 δ_(rho=1) + k_I
D_infinity o Q = <xi, (-2 Id + K_I) xi>
```

The next concrete M3A subgoal is therefore reduced to the regular remainder:

```text
k_I is measurable on sqrt(I) × sqrt(I)
∫∫ ‖k_I(u,v)‖² dρ(u)dρ(v) < ∞
kernel operator(k_I) = K_I
```

The new paper supplies the generic compactness pattern once `k_I` is shown
continuous (or directly square-integrable); it does not prove the CC20-specific
`Qδ` subtraction. This is a narrower, source-aligned target than reconstructing
the full semilocal fixed-S quotient.
