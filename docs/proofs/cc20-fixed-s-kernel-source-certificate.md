# CC20 Fixed-S Kernel Source Certificate

Date: 2026-07-10

Decision:

```text
kernel formula and estimate: Fork B
archimedean-to-fixed-S projection transport: Fork F
Phase 0A kernel gate: failed
Phase 0B authorization: denied
```

## Target

Plan 012 needs one selected operator

```text
A_(S,lambda,g) = P_hat_(S,lambda) P_(S,lambda) U_S(g)
```

on a concrete complex `L2` coordinate, together with a measurable function
kernel `K_A`, an explicit square-integrable majorant, and a theorem identifying
the kernel action with `A`. The estimate must depend on the same finite set
`S`, cutoff `lambda`, and test `g` used by the route.

## Source Coordinate

For a finite set of places `S` containing the archimedean place, Connes 1999
uses

```text
A_S = product_(v in S) k_v
O_S^* = the S-unit group
X_S = A_S / O_S^*
H_S = L2(X_S)
```

and defines the scaling action by

```text
(U(lambda) xi)(x) = xi(lambda^(-1) x).
```

It defines the infrared and Fourier cutoffs by

```text
P_Lambda       = multiplication by 1_(|x| <= Lambda)
P_hat_Lambda   = F P_Lambda F^(-1)
R_Lambda       = P_hat_Lambda P_Lambda.
```

Source: Alain Connes, "Trace formula in noncommutative geometry and the
zeros of the Riemann zeta function", arXiv:math/9811068, Section VII,
source lines 1740-1808 and 1870-1888.

URL: https://arxiv.org/abs/math/9811068

CCM24 supplies a canonical spectral coordinate

```text
V_S : L2(X_S)^(K_S) -> L2(R, dm_S)
dm_S(s) = |product_(v in S) L_v(1/2-is)|^2 ds
```

under which the scaling generator is multiplication by `s` and the Fourier
grading is reflection `s -> -s`.

Source: Alain Connes, Caterina Consani, Henri Moscovici, "Zeta zeros and
prolate wave operators", arXiv:2310.18423v2, Proposition 4.2,
`mainc2m24fine.tex:786-804`.

URL: https://arxiv.org/abs/2310.18423

## Strongest Kernel Formula Found

Connes 1999 writes the scaling test operator on `A_S` as a distribution kernel:

```text
U(f) = integral f(lambda) U(lambda) d*lambda

k_f(x,y)
  = integral f(lambda^(-1)) delta(y-lambda*x) d*lambda.
```

For an operator on `A_S` that descends to `X_S`, its quotient trace is

```text
Tr(T) = sum_(q in O_S^*) integral_D k(x,qx) dx.
```

The transpose cutoff kernel is

```text
r_Lambda^t(x,y)
  = rho_Lambda(x) Fourier(rho_Lambda)(x-y).
```

Source: arXiv:math/9811068, Section VII, formulas (16)-(22), source lines
1937-1977.

Theorem 4 then proves the asymptotic trace formula

```text
Trace(R_Lambda U(h))
  = 2 h(1) log' Lambda
    + sum_(v in S) PV integral h(u^(-1))/|1-u| d*u
    + o(1).
```

Source: arXiv:math/9811068, Theorem 4, source lines 1893-1910 and proof lines
1925-2216.

## Missing Kernel Estimate

The sources above do not supply the plan's required theorem:

```text
K_A : X_S -> X_S -> C
K_A represents P_hat_Lambda P_Lambda U_S(g) on L2(X_S)
integral_(X_S x X_S) |K_A(x,y)|^2 < infinity.
```

The kernel displayed in Connes 1999 is distribution-valued before cutoff and
is used inside a quotient trace computation. The proof estimates the asymptotic
trace error. It does not state a measurable function representative for
`R_Lambda U(h)`, its Hilbert-Schmidt norm, or a pointwise/integral majorant for
the kernel norm square.

CC20 supplies explicit kernels only for the single archimedean place. For
example, its Lemma 1.4 gives

```text
k^u(lambda,mu)
  = 2 lambda^(-1/2) mu^(1/2) cos(2*pi*mu/lambda),
```

and Proposition 1.5 proves a localized quantized-differential operator is trace
class. These statements do not contain the nonarchimedean places or the
fixed-S cutoff operator above.

Source: Alain Connes and Caterina Consani, "Weil positivity and Trace formula,
the archimedean place", arXiv:2006.13771, `weil-compo.tex:346-362` and
`378-464`.

URL: https://arxiv.org/abs/2006.13771

## Transport Failure

The semilocal comparison maps do not transport orthogonal projections by bare
conjugation. CCM24 states that `eta_S` is not unitary and records

```text
N_S eta_S != eta_S N_infinity
|.|_S^2 eta_S(f) != eta_S(|.|^2 f)
```

outside the single archimedean place.

Source: arXiv:2310.18423v2, `mainc2m24fine.tex:805-823` and `837-861`.

CCM24 proves that `theta_S` is a bounded isomorphism of Sonin spaces and gives
the dual pairing

```text
<theta_S(f), eta_S(g)> = <f,g>.
```

It does not prove that `theta_S` or `eta_S` conjugates the archimedean support
projection to the fixed-S orthogonal support projection. It also does not
transport the archimedean kernel measure or Hilbert-Schmidt norm.

Source: arXiv:2310.18423v2, Proposition 4.7 and Theorem 4.6,
`mainc2m24fine.tex:983-1029`.

## Search Coverage

The audit checked the original TeX for:

```text
arXiv:math/9811068
arXiv:2006.13771
arXiv:2106.01715
arXiv:2207.10419
arXiv:2310.18423v2
arXiv:2511.22755
```

Official source pages:

```text
https://arxiv.org/abs/math/9811068
https://arxiv.org/abs/2006.13771
https://arxiv.org/abs/2106.01715
https://arxiv.org/abs/2207.10419
https://arxiv.org/abs/2310.18423
https://arxiv.org/abs/2511.22755
```

It also queried the arXiv author index for Connes and Consani through
2026-07-10 and searched arXiv for semilocal trace formulas together with
Hilbert-Schmidt kernels. No later source supplied the missing fixed-S estimate.

## Smallest Missing Lean Statement

The repository also lacks the concrete domain needed to state the estimate.
`RouteInputs.ccm24` is a `SemilocalModelSymbols` interface. Its fixed-S analytic
fields are propositions:

```text
canonicalHilbertModel : PlaceSet -> Prop
scalingActionImplemented : PlaceSet -> Prop
fourierGradingCompatible : PlaceSet -> Prop
boundedComparisonMap : PlaceSet -> Prop
boundedComparisonInverse : PlaceSet -> Prop
```

Source: `ConnesWeilRH/Basic.lean:163-181`.

`SourcePlaceCarrierData` adds an arbitrary real Hilbert carrier, and
`SourceCanonicalHilbertModelData` adds a real continuous-linear equivalence. It
does not add a measurable space, measure, complex `L2` realization, Fourier
operator, support projection, or quotient kernel.

Source: `ConnesWeilRH/Source/AnalyticCore.lean:792-859`.

Mathlib v4.30.0 contains the number-field adele ring in
`Mathlib/NumberTheory/NumberField/AdeleRing.lean` and an `L2` Fourier transform
for finite-dimensional real vector spaces in
`Mathlib/Analysis/Fourier/LpSpace.lean`. The repository search found no
construction of the semilocal quotient `X_S=A_S/O_S^*`, its quotient Haar
measure, its self-dual Fourier transform, or the `L2(X_S)` cutoff projections.

The first Lean API bottom is therefore:

```text
SourceCC20FixedSQuotientMeasureCoordinate:
  a concrete X_S quotient
  + quotient measure
  + complex L2 space
  + unitary Fourier operator
  + orthogonal P_Lambda and P_hat_Lambda
  + scaling representation U_S
```

Only after this object exists can Lean state the selected kernel estimate.

The implementation cannot define the certified kernel formula or majorant.
The first unavailable theorem remains:

```text
SourceCC20FixedSKernelEstimate:
  operatorKernel.kernel = certifiedFixedSKernelFormula
  and norm(operatorKernel.kernel x y) <= certifiedFixedSKernelMajorant x y
  and Integrable (fun (x,y) => certifiedFixedSKernelMajorant x y ^ 2).
```

The source package provides neither `certifiedFixedSKernelFormula` nor
`certifiedFixedSKernelMajorant` for the fixed-S operator.

## Verdict

```text
unsupported row: literal fixed-S K_A function kernel
unsupported row: square-integrable majorant
unsupported row: orthogonal-projection and kernel-measure transport
Lean API bottom: SourceCC20FixedSQuotientMeasureCoordinate
analytic bottom: SourceCC20FixedSKernelEstimate
transport bottom: SourceCC20FixedSEulerKernelTransport
decision: Fork B with Fork F as the transport sub-bottom
```

Plan 012 forbids replacing these rows with an arbitrary operator, kernel,
majorant, or `Prop`. Phase 0B and all later implementation phases therefore
remain unauthorized.
