# Plan 019: Adelic Cech--Hodge Boundary-Cancellation Feasibility

Date: 2026-07-11

Status: rejected at the H2/H3 interface. The exact CC20 trace remainder cannot
be an uncancelled boundary contribution of a scaling-equivariant positive
Hilbert complex. The detailed verdict is
`docs/proofs/019_adelic_cech_hodge_h2_verdict.md`.

## 1. Scope And Non-Goals

The experiment tests a cohomological reinterpretation of the Connes route:

```text
old weak path:
  ordinary positive trace = Weil form, after deleting or signing a remainder

new proposed path:
  supertrace on C0 -> C1 -> C2 = Weil form,
  with the nonzero ordinary-trace remainder assigned to exact/coexact sectors
```

The experiment does not:

```text
assume that the CC20 remainder vanishes;
assume Weil positivity, RH, real zeros, or Hermite--Biehler;
define a quotient or cohomology using zeta zeros;
promote an abstract mapping cone into a route producer;
create Lean APIs before the kernel identity is proved.
```

## 2. Route Obligation

```text
route obligation:
  construct a positive adelic Hilbert complex whose regularized supertrace is
  the complete Weil explicit formula

old weak path:
  supportSquareTrace = qwLambda, rejected by the nonzero CC20 remainder

new mathematical owner:
  one finite-S adelic Hilbert complex carrying summation, Fourier, scaling,
  differential, adjoint, and harmonic projection on the same objects

consumer to rewire:
  a future corrected Connes--Weil trace consumer; none is active at feasibility
  stage

forbidden circular inputs:
  SourceRH, zero locations, Weil positivity, selected detector coverage,
  Hermite--Biehler, a Hodge star assumed positive, or a differential selected
  after seeing the target remainder

smallest verification target:
  an exact archimedean/fixed-S kernel identity for the H2 boundary contribution

focused axiom audit:
  inactive until H2 supplies a theorem-grade mathematical identity
```

## 3. Source Evidence

Connes 1999 constructs the adele-class space, idele-class scaling action,
absorption-spectrum interpretation, and finite-S trace formula. The global
Hilbert trace formula is left open and is stated to be equivalent to RH:

```text
Alain Connes, Trace formula in noncommutative geometry and the zeros of the
Riemann zeta function
https://arxiv.org/abs/math/9811068
Introduction, especially the statements describing Theorems 1, 4, and 5.
```

Meyer constructs natural adelic source and diagonal spaces, their embeddings
`i_+` and `i_-`, the Poisson relation, and the global difference
representation. His global negative space is a bornological quotient, not an
unconditional unitary Hilbert representation; GRH is equivalent to real spectra
for self-adjoint elements of its star algebra:

```text
Ralf Meyer, On a representation of the idele class group related to primes
and zeros of L-functions
https://arxiv.org/abs/math/0311468
source lines 155-164, 232-247, 298-305, 3841-4027, 4420-4443.
```

CC20 identifies the local archimedean obstruction as the small-square trace
remainder. After applying `Q`, Theorem `thmqkey1` represents it by

```text
D o Q(xi * xi*) = <xi, (-2 Id + K_I) xi>,
```

where `K_I` is a compact Hilbert--Schmidt integral operator. The remainder is
not zero in general:

```text
Connes--Consani, Weil positivity and trace formula, the archimedean place
https://arxiv.org/abs/2006.13771
weil-compo.tex:178-209, 765-808, 875-877.

project verdict:
docs/proofs/cc20-012-mathematical-verdict.md
plan/012_2026-07-10_CC20_operator_kernel_trace_plan.md:14-24,1243-1249.
```

The Scaling Site currently lacks the required global H1/intersection theory.
The later spectral sheaf uses zeta ideals and is therefore not a lower
producer:

```text
Connes--Consani, The Riemann--Roch strategy
https://arxiv.org/abs/1805.10501
thecurve_K.tex:413-416.

Connes--Consani, Spectral realizations of zeros and the Scaling Site
https://arxiv.org/abs/2207.10419
Hochschild-zeta.tex:180-183,524-525.
```

## 4. Candidate Data-Bearing API

No Lean structure is authorized yet. The mathematical owner, if H2 passes,
must contain one same-object package:

```text
FiniteSAdelicHilbertComplex:
  finite place set S
  semilocal adele space A_S and S-unit quotient X_S
  Hilbert spaces C0_S, C1_S, C2_S
  closed densely-defined differentials d0_S, d1_S
  adjoints and closed-range proofs
  scaling action U_S commuting with the complex
  additive Fourier/Poisson identification
  exact, coexact, and harmonic projections
  trace-class smoothed actions on every sector
  source-normalized supertrace identity
```

The differential must be defined before comparing with `K_I`. The initial
candidate is the natural difference of the arithmetic summation and diagonal
embeddings:

```text
d_S(f,g) := i_+(f) - i_-(g).
```

Changing `d_S` by inserting a square root or functional calculus of
`-2 Id + K_I` is forbidden: that would store the desired remainder.

## 5. Rejection-First Gates

### H0. Non-circular ownership

Every space, inner product, differential, and adjoint must be constructed from
finite-S adeles, Haar measure, summation, Fourier transform, Poisson summation,
and cutoff data. Reject if zeta zeros or Weil positivity enter a definition.

### H1. Hilbert-complex legality

Prove that the natural mapping-cone differential is closed and densely defined,
that its adjoint is explicit, and that the relevant ranges are closed. A
bornological quotient or formal alternating sum does not supply a Hodge
decomposition.

### H2. Exact boundary-remainder identity

This is the first executable gate. Compute the kernel and trace contribution of
the exact/coexact sectors and compare it to CC20 term by term:

```text
Dirac jump at rho=1          -> coefficient -2
small-square Delta kernel    -> K_I
support interval I           -> same I and same measure
Q normalization              -> same differential convention
rank and pole corrections    -> H0/H2 sectors, if present
cutoff dependence            -> same parameter, no hidden limit
```

Pass only for literal equality on the same test object. Similar compactness,
equal Fredholm index, matching leading singularity, or an abstract realization
of an arbitrary self-adjoint operator as a Laplacian do not count.

H2 outcomes:

```text
pass:
  exact equality, possibly plus explicitly identified finite-rank H0/H2 terms

partial:
  equality on a strict source-defined subspace that still separates every
  possible off-line zero

rejected:
  unmatched compact kernel, wrong sign, wrong support/cutoff, or a differential
  manufactured from K_I
```

### H3. Scaling compatibility

Prove `U_S d = d U_S` and the corresponding adjoint/projection identities.
Otherwise the harmonic sector does not carry the desired spectral action.

### H4. Uniform local-to-global control

As `S` increases, prove uniform trace-norm/regularization estimates and
compatibility of harmonic projections. Euler products convergent only in
`Re(s)>1` are insufficient for the critical normalization.

### H5. Complete supertrace

Derive the full Weil explicit formula, including the archimedean principal
value, finite primes, pole terms, and multiplicities, as one supertrace. Reject
if this equality is assumed or is shown equivalent to RH without a lower proof.

### H6. Polarization

Derive from the constructed positive inner product that normalized scaling is
unitary on harmonic H1. A separately postulated Hodge star is forbidden.

## 6. Current H2 Experiment

The first comparison uses only the archimedean specialization because a
mismatch there rejects every global extension.

```text
Step H2.1  extract the exact CC20 kernel k_I(x,y)
Step H2.2  write the natural i_+ - i_- mapping-cone kernel
Step H2.3  compute d*d and dd* on their actual domains
Step H2.4  compare singular, compact, rank, and cutoff pieces
Step H2.5  issue pass / partial / rejected verdict
```

No Lean implementation begins before H2.5 passes.

## 7. Success And Rejection

```text
accepted feasibility:
  H0-H2 pass with a source-defined differential and exact kernel equality

accepted RH route:
  H0-H6 pass and the complete supertrace/polarization bridge is unconditional

partial:
  a genuine boundary identity exists but global or polarization control remains

rejected:
  H2 fails, or any later gate requires an RH-equivalent premise
```

Current verdict: rejected. For an equivariant differential, adjacent exact and
coexact sectors cancel in every legal supertrace. The cutoff projections needed
to reproduce the CC20 small-square kernel do not commute with scaling. The
actual operator `-2 Id + K_I` is also sign-indefinite on the relevant larger
window, whereas one signed boundary norm has fixed sign. Splitting off its
finite bad spectrum simply recovers CC20's old finite-codimension conditioning.
RH remains conditional and no project root has been removed or lowered.
