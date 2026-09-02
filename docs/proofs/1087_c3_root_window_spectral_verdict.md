# 1087 - root-window finite-matrix reconnaissance and tail-factor correction

Date: 2026-09-01. Follows record 1086.

Status: numerical reconnaissance, corrected after a claim-strength audit. This
record proves no theorem about the infinite-dimensional form or C3. It records
one analytic tail identity and floating-point evidence from finite compression
models. The computation neither proves that the root-window detector set is
empty nor closes or retires a C3 construction.

## 1. The continuum question

Let

```text
a = log(2) / 2,
V_a = {h : CompactLogTest | supp(h) subset [-a,a],
             laplaceAt(h,s) = 0 for s in {0,1/2,1}},
A(h) = archimedeanTerm(h.convolutionSquare).
```

For a root-supported, triple-vanishing test, Lean proves

```text
qw(h) = -A(h).
```

The prime term vanishes here because the Hermitian square is supported inside
`(-log 2, log 2)`. For a root-supported `HealthyYoshidaDetectorData rho h`,
its strict local-Weil-sum field is therefore equivalent to `A(h) > 0`; its
other fields also require smooth compact support, triple vanishing, and
`laplaceAt(h, rho) ≠ 0`. The scan imposes only the three moment constraints.
It does not impose the detector value at `rho`.

The scan uses real-valued basis profiles. In an idealized exact Galerkin
setting, if a real finite-dimensional subspace `V_{a,K} subset V_a`, then

```text
lambda_{a,K}
  = sup {A(h) : h in V_{a,K}, ||h||_2 = 1}
  <= sup {A(h) : h in V_a, ||h||_2 = 1}.
```

This inequality fixes the direction of inference for a certified exact
subspace: its maximum is a lower bound for the full supremum. A negative value
cannot prove that the full supremum is nonpositive. Such a conclusion needs a
rigorous upper bound for the unresolved complement.

The program does not certify the premise `V_{a,K} subset V_a`. It imposes the
three moment constraints by floating-point quadrature and SVD. The enveloped
Legendre profiles use a smooth bump, but their computed constraint nullspace is
only approximate. The sine profiles are an independent L2 check; after zero
extension they are not C-infinity at the support endpoints and therefore are
not `CompactLogTest` values. The scan also omits general complex-valued
directions. None of the reported eigenvalues is a rigorous lower bound for the
continuum supremum.

## 2. What was computed

The reused probe
[`1020_lane_r_prime_free_spectrum.py`](1020_lane_r_prime_free_spectrum.py)
formed constrained matrices for

```text
r in {0.300, 0.320, 0.330, 0.340, 0.345, 0.346},
K in {8, 12, 16, 20, 24, 28, 32},
basis family in {sine, enveloped Legendre with p in {1,2,3}}.
```

This gives 168 configurations. Every computed matrix had a negative largest
eigenvalue. Representative rows are:

```text
r=0.346  sine K= 8  eig_max=-0.87580185  condG=1.00e+00
r=0.346  sine K=32  eig_max=-0.85351242  condG=1.00e+00
r=0.346  leg  K=32  eig_max=-0.89141329  condG=5.91e+10  (p=1)
```

For the sine family at `r=0.346`, the computed maxima were

```text
K        8          12         16         20         24         28         32
eig_max -0.87580   -0.86633   -0.86141   -0.85834   -0.85624   -0.85469   -0.85351
```

The run supports only these statements:

1. no sampled matrix had an eigenvector with a positive computed eigenvalue;
2. the sine and lower-order enveloped Legendre rows both give negative
   computed maxima;
3. the observed sine values rise slowly as `K` grows;
4. no convergence rate or complement bound was proved, so extrapolating the
   displayed sequence to the continuum is not justified.

The high-order enveloped Legendre rows are ill-conditioned. At `p=3, K=32`,
`condG` reaches `8.24e15`, and the largest printed moment residual reaches
`1.12e-8`. Those rows carry less diagnostic weight than the well-conditioned
sine rows; they do not provide an independent high-resolution confirmation.

The scan also does not establish monotonicity in the support radius. Changing
`r` changes the feasible functions and their whole autocorrelations. A
tail-only monotonicity argument is therefore invalid.

## 3. Tail-factor correction

The tail correction follows from the Lean definitions

```text
N_F(y) = exp(y/2) * (F(y) + F(-y)) - 2 * F(0),
D(y)   = exp(y) - exp(-y) = 2 * sinh(y).
```

See
[`archimedeanNumerator`](../../ConnesWeilRH/Dev/C1SameOwnerWeil.lean#L48)
and
[`archimedeanDenominator`](../../ConnesWeilRH/Source/CCM25Concrete/SelectedWeilFormula.lean#L103).
For a Hermitian square, `F(-y) = conj(F(y))` and `F(0)` is real, so the real
integrand is

```text
(exp(y/2) * Re(F(y)) - F(0)) / sinh(y).
```

The scan uses real-valued profiles, for which `F` is real and even.

If `F` is supported in `[-S,S]`, then for `y > S` it becomes
`-F(0)/sinh(y)`. Since

```text
d/dy log(tanh(y/2)) = 1 / sinh(y),
```

the exact tail is

```text
integral_S^infinity -F(0)/sinh(y) dy
  = F(0) * log(tanh(S/2)).
```

For a test supported in `[-r,r]`, its square has `S=2r`, so the tail is

```text
F(0) * log(tanh(r)),
```

not `2 * F(0) * log(tanh(r))`. The earlier factor two counted the numerator's
factor two without cancelling the identical factor in the denominator.

The companion script
[`1087_c3_roundtrip_cert.py`](1087_c3_roundtrip_cert.py) numerically checks that
the implementation using this tail agrees with a direct integration of the raw
integrand. The direct integration stops at `y=20`; the exact magnitude of the
omitted tail is printed separately and is below `5e-9` in this run. At
`r=0.346`, sine `K=32`, it printed:

```text
matrix value                         -0.85351242
closed form with the x1 tail         -0.85351242
direct raw-integrand quadrature      -0.85345597
absolute difference                  5.645e-05
x2-tail error against direct value   1.100e+00
FFT/correlation consistency error    6.7e-16
moment residuals                     <= 1.1e-17
omitted tail beyond y=20             < 5e-9
```

This cross-check distinguishes the two tail formulas by a wide numerical
margin. It is not an interval certificate for the continuum spectrum.

Applying the corrected tail to the three record-1086 tapers changes their
reported archimedean values to approximately

```text
taper ratio   0.95      0.80      0.60
A(h)         -1.679    -1.004    -0.263
```

Record 1086's three corrected values remain negative numerical results for its
particular `g_3` family. They say nothing about untested root-supported tests.

## 4. Claims supported and unsupported

Supported by the source identity and the numerical runs:

```text
+ the tail coefficient is x1, not x2;
+ the tested 1086 family remains negative after that correction;
+ all 168 approximate compression matrices have negative computed maxima;
+ no eigenvector with a positive computed eigenvalue was found at the tested
  resolutions.
```

Not supported by this record:

```text
- A(h) <= 0 for every h in V_a;
- negative definiteness of the infinite-dimensional restriction A|V_a;
- emptiness of the root-supported healthy-detector set;
- closure of the pinned-carrier or root-support transport programs;
- any no-go ruling or mandatory change of support radius;
- any Lean theorem about the sign of A or qw.
```

Agreement across finite bases checks the implementation. It does not turn the
sampled spaces into exact `CompactLogTest` subspaces. A valid no-go theorem
would need an upper enclosure such as

```text
sup_{h in V_a, ||h||_2=1} A(h) <= -epsilon
```

with `epsilon > 0`, proved by an exact analytic estimate or a validated
finite-section-plus-tail certificate.

## 5. Consequence for C3

Record 1087 does not decide C3. The formal detector construction uses a
convolution orbit, and its public theorem exports no ROOT-window support bound:

```lean
theorem exists_healthyDetectorData_of_sourceNontrivialZero_right
    (rho : sourceNontrivialZeroSet)
    (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re) :
    ∃ g : CompactLogTest, HealthyYoshidaDetectorData rho.1 g
```

See
[`C1HealthyYoshidaSpectralNegativity.lean`](../../ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean#L511).
That package yields `qw(g) < 0`. The unresolved B5 obligation is to prove
`qw(g) >= 0` for the same selected `g`.

At larger support, visible prime powers generally contribute. Triple vanishing
gives the exact identity

```text
qw(g) = -archimedeanTerm(F_g) - finitePrimeSum(F_g),
F_g = g.convolutionSquare.
```

Consequently the negative-detector condition is

```text
archimedeanTerm(F_g) + finitePrimeSum(F_g) > 0,
```

rather than the root-only gate `archimedeanTerm(F_g) > 0`. The existing orbit
detector supplies the negative side. C3 still needs a same-owner semi-local
certificate for the opposite inequality.

The minimal formal exit is now stated by
`healthy_sourceRH_of_right_detector_specific_qw_nonneg`: for every hypothetical
right-hand off-line zero, one matching `g` carrying both healthy detector data
and `0 <= qw(g)` implies `SourceRH`. This theorem is an implication only; no
producer of its nonnegativity premise is claimed here.

## 6. Reproduction

Run the following payload from `docs/proofs/` through the repository resource
runner documented in [`RESOURCE_SCHEDULING.md`](../../RESOURCE_SCHEDULING.md):

```bash
python3 1020_lane_r_prime_free_spectrum.py \
  --radii 0.30 0.32 0.33 0.34 0.345 0.346 \
  --basis-sizes 8 12 16 20 24 28 32 \
  --envelope-powers 1 2 3 \
  --basis-families legendre sine
```

Run the raw-integrand cross-check through the same runner:

```bash
python3 1087_c3_roundtrip_cert.py
```

Both require NumPy and SciPy. The generated `*.log` files are local,
git-ignored artifacts; the representative outputs needed to interpret the
record are reproduced above.
