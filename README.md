# Connes-Weil RH Formalization

<p align="center">
  <a href="#status"><img alt="Research status: RH unproved" src="https://img.shields.io/badge/status-RH%20unproved-b42318?style=flat-square"></a>
  <a href="lean-toolchain"><img alt="Lean 4.30.0" src="https://img.shields.io/badge/Lean-4.30.0-5c7cfa?style=flat-square"></a>
  <a href="lakefile.toml"><img alt="Mathlib 4.30.0" src="https://img.shields.io/badge/Mathlib-4.30.0-0f766e?style=flat-square"></a>
</p>

A Lean 4 formalization of analytic and operator-theoretic components of the
Connes-Weil approach to the Riemann hypothesis. The repository distinguishes
proved Lean implications, assumptions exposed by those implications, results
quoted from the literature, and numerical experiments.

## Status

> [!IMPORTANT]
> The Riemann hypothesis is not proved in this repository. The current output
> theorem still depends on five project axioms, listed by
> [`RhOutputAxiomLedger.lean`](ConnesWeilRH/Dev/RhOutputAxiomLedger.lean).
> Axiom-clean lemmas below verify parts of the argument; they do not discharge
> those five assumptions.

Current mathematical status, 2026-09-01:

| Component                              | Status                         | Evidence |
| :------------------------------------- | :----------------------------- | :------- |
| Arithmetic value equals the zero-side spectral value on the healthy `CompactLogTest` | Proved in Lean | [`centerTwo_arithmetic_eq_spectral`](ConnesWeilRH/Dev/C1XiCenterTwoArithmeticAssembly.lean#L232) |
| Detector with `qw(g) < 0` from a hypothetical right-hand off-line zero | Proved in Lean | [`exists_healthyDetectorData_of_sourceNontrivialZero_right`](ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean#L511) |
| Finite visible-prime operator and trace readback | Proved in Lean; no sign conclusion | [`C1SelectedDetectorSemiLocalEulerBoundary.lean`](ConnesWeilRH/Dev/C1SelectedDetectorSemiLocalEulerBoundary.lean) |
| `qw(g) >= 0` for that same orbit-supported detector | Open | [C3 interface audit](docs/map/004_endpoint_literature_interface_audit.md) |
| Detector-specific contradiction implies `SourceRH` | Proved as a conditional Lean implication | [`healthy_sourceRH_of_right_detector_specific_qw_nonneg`](ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean) |
| ROOT-window finite-matrix scan | Numerical evidence only; no continuum sign theorem | [record 1087](docs/proofs/1087_c3_root_window_spectral_verdict.md) |

The binding project choice is a detector-specific, B5-shaped argument on the
healthy `CompactLogTest` type. Here "B5-shaped" means that positivity is needed
only for the test selected against a hypothetical off-line zero, not for every
compactly supported test. The [route map](docs/map/README.md) records this
quantifier choice and the frozen alternatives.

## 1. Mathematical setup

The Riemann hypothesis states that every nontrivial zero of the Riemann zeta
function lies on the critical line:

$$
\zeta(s)=0,\quad 0<\mathrm{Re}(s)<1
\quad\Longrightarrow\quad
\mathrm{Re}(s)=\frac12.
$$

For a compactly supported test `g`, the Weil criterion uses a Hermitian
convolution square. In multiplicative notation,

$$
g^{\sharp}(x)=x^{-1}\overline{g(x^{-1})},
\qquad
F_g=g\ast g^{\sharp}.
$$

Its Mellin transform satisfies

$$
\widetilde F_g(s)=\widetilde g(s)\widetilde g(1-s),
\qquad
\widetilde F_g\left(\frac12+it\right)
=\left|\widetilde g\left(\frac12+it\right)\right|^2.
$$

The Lean model works in the additive logarithmic coordinate. There the
involution is

$$
g^{\star}(x)=\overline{g(-x)},
\qquad
F_g=g^{\star}\ast g,
$$

implemented exactly as `g.involution.convolution g`; see
[`CompactLogTest.convolutionSquare`](ConnesWeilRH/Source/CCM25Concrete/CompactLogConvolution.lean#L114).

The same-test Weil value has two proved descriptions:

$$
\boxed{
\begin{aligned}
q_w(g)
  &=\mathrm{poleTerm}(F_g)
    -\mathrm{archimedeanTerm}(F_g)
    -\mathrm{finitePrimeSum}(F_g),\\
q_w(g)
  &=\mathrm{spectralWeilValue}(F_g).
\end{aligned}
}
$$

The first equality is the component definition and the second is the completed
center-2 contour theorem. Evidence:
[`psi_eq_components`](ConnesWeilRH/Dev/C1SameOwnerWeil.lean#L199) and
[`qw_eq_spectralWeilValue_centerTwo`](ConnesWeilRH/Dev/C1CenterTwoCriterionBridge.lean#L28).

The project uses the explicit predicate

```lean
∀ g : CompactLogTest,
  CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g →
    0 ≤ C1SpectralWeil.spectralWeilValue g.convolutionSquare
```

This is the all-test premise used by the conditional theorem
[`healthy_sourceRH_of_global_spectral_nonneg`](ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean)
and is stronger than the active detector-specific target. The project is not
trying to prove this universal statement as the first global result.

## 2. The active argument

The proof by contradiction has two independent inputs after an off-line zero is
assumed:

```text
                         assume an off-line zero rho
                                      |
                 +--------------------+--------------------+
                 |                                         |
                 v                                         v
      construct one CompactLogTest g             prove semi-local positivity
      with HealthyYoshidaDetectorData             for the same g and its finite
                 |                                visible prime-power set
                 v                                         |
              qw(g) < 0                                  qw(g) >= 0
                 |                                         |
                 +--------------------+--------------------+
                                      |
                                      v
                               contradiction
                                      |
                                      v
                       SourceRH -> Mathlib RH
```

Lean proves the negative-detector branch. The same-detector nonnegativity
branch remains open.

The minimal formal composition is

```lean
(∀ rho : sourceNontrivialZeroSet,
  (1 / 2 : Real) < rho.1.re →
    ∃ g : CompactLogTest,
      HealthyYoshidaDetectorData rho.1 g ∧
        0 ≤ C1SameOwnerWeil.qw g) →
  RHDefinitionBridge.standard.SourceRH
```

proved by `healthy_sourceRH_of_right_detector_specific_qw_nonneg`. The premise
requires both signs on one test; it is not an all-test positivity assumption.
No theorem currently constructs the nonnegative half of this pair.

### ROOT support versus orbit support

Triple vanishing removes the pole term. At ROOT support,

$$
\mathrm{supp}(g)\subseteq
\left[-\frac{\log 2}{2},\frac{\log 2}{2}\right],
$$

the Hermitian square is supported inside `(-log 2, log 2)`, so no prime power is
visible. Lean then proves

$$
q_w(g)=-\mathrm{archimedeanTerm}(F_g).
$$

See
[`qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_rootSupport_logTwoHalf`](ConnesWeilRH/Dev/C1HealthyYoshidaDetector.lean#L145).

The formal negative detector is constructed from a convolution orbit, and its
exported theorem supplies no ROOT-window support bound. The current proof
therefore cannot remove its visible prime powers. The applicable identity is

$$
\begin{aligned}
q_w(g)
  &=-\mathrm{archimedeanTerm}(F_g)
    -\mathrm{finitePrimeSum}(F_g).
\end{aligned}
$$

The detector's strict negative sign is equivalent to

$$
\mathrm{archimedeanTerm}(F_g)
+\mathrm{finitePrimeSum}(F_g)>0.
$$

A ROOT endpoint certificate proves `q_w(g) ≥ 0` only under ROOT support, where
the prime sum vanishes. Applying it to the orbit detector requires an additional
support theorem or a semi-local extension that includes the prime sum.

## 3. What is formalized

The table below lists the main reusable results. "Proved" means the declaration
has a focused `#print axioms` audit with only Mathlib's standard logical axioms;
it does not mean that its explicit premises have been discharged.

| Area                                  | Proved result | Lean evidence |
| :------------------------------------ | :------------ | :------------ |
| Hilbert-Schmidt trace cycles          | Absolute double-sum control and cross-space cyclic trace identities | [`PositiveTrace.lean`](ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean) |
| Nuclear expansion                     | Operator-norm summable rank-one expansion and compactness | [`traceProduct_eq_tsum_nuclearTerm`](ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L445) |
| Continuous kernels                    | Diagonal trace equals the integral of kernel-section inner products | [`pairData_trace_eq_kernel_inner`](ConnesWeilRH/Source/CC20Concrete/ContinuousKernelHilbertSchmidt.lean#L316) |
| Prime-power crossings                 | One crossing reads back to the exact Weil prime-power coefficient | [`eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow`](ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingKernel.lean#L390) |
| Finite prime sums                     | A compact self-adjoint operator has the required finite trace | [`ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperatorSum_eq_finitePrimeTerm_pow_sum`](ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L3187) |
| Global CC20 window                    | Exact zero-extension conjugation, compactness, and self-adjointness | [`GlobalLogKernel.lean`](ConnesWeilRH/Source/CC20Concrete/GlobalLogKernel.lean) |
| Xi zeros                              | Exact source-zero index and absolute spectral summability | [`CC20ZetaCounting.lean`](ConnesWeilRH/Source/CC20ZetaCounting.lean), [`C1SpectralSummability.lean`](ConnesWeilRH/Dev/C1SpectralSummability.lean) |
| Arithmetic-to-spectral bridge         | Same-test center-2 explicit formula | [`C1XiCenterTwoArithmeticAssembly.lean`](ConnesWeilRH/Dev/C1XiCenterTwoArithmeticAssembly.lean) |
| ROOT endpoint interface               | An endpoint certificate implies `qw(g) >= 0` at ROOT support | [`qw_nonneg_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf`](ConnesWeilRH/Dev/C1CC20ArchimedeanReadback.lean#L133) |
| Orbit detector                        | A hypothetical right-hand off-line zero yields `HealthyYoshidaDetectorData` | [`C1HealthyYoshidaSpectralNegativity.lean`](ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean) |
| Semi-local Euler boundary             | Visible prime powers are realized by boundary crossings with exact trace readback | [`C1SelectedDetectorSemiLocalEulerBoundary.lean`](ConnesWeilRH/Dev/C1SelectedDetectorSemiLocalEulerBoundary.lean) |
| Semi-local residual                   | The unresolved response is isolated and decomposed without assuming a sign | [`C1SelectedDetectorSemiLocalResidualDecomposition.lean`](ConnesWeilRH/Dev/C1SelectedDetectorSemiLocalResidualDecomposition.lean) |

Two operator-gap lemmas used by the ROOT endpoint reconstruction are
[`cc20GapCoercivity_transfer`](ConnesWeilRH/Dev/C1CC20OperatorGap.lean#L313)
and
[`cc20NegativeForm_le_rankOne`](ConnesWeilRH/Dev/C1CC20OperatorGap.lean#L344).
The center-2 gamma normal form is
[`normalized_gammaR_centerTwo_eq_constant_sub_tsum_integrals`](ConnesWeilRH/Dev/C1XiCenterTwoGamma.lean#L2457).

## 4. Open mathematics

### 4.1 Detector-specific semi-local positivity

This is the missing C3 theorem. For the `g` selected by the orbit detector, the
project must prove

$$
\begin{aligned}
0\le q_w(g)
  &=-\mathrm{archimedeanTerm}(F_g)
    -\mathrm{finitePrimeSum}(F_g).
\end{aligned}
$$

The finite-prime coefficients, their operator realization, and an exact
residual decomposition are already formalized. No landed theorem controls the
sign of that residual or produces the displayed inequality for the selected
detector.

### 4.2 ROOT-window endpoint certificate

Connes and Consani prove an archimedean compact-window result in
[arXiv:2006.13771](https://arxiv.org/html/2006.13771). Reconstructing their
argument in Lean still requires the paper-scale finite-section/Toeplitz
certificate, the exact prolate and tail data, and the same-test trace identity.
The details and two corrections to the published-parameter transcription are in
[route record 002](docs/map/002_one_shot_rh_route_verdict.md).

A newer unreviewed preprint,
[arXiv:2608.24827](https://arxiv.org/html/2608.24827), states in Corollary 9 that

$$
Q(f)\ge 8.9\times10^{-18}\lVert f\rVert_2^2
\quad\text{when}\quad
\mathrm{supp}(f)\subseteq[-0.8,0.8].
$$

This could supply a shorter ROOT proof after the Fourier/Mellin convention,
involution, sign, admissibility, and interval-certificate bridges are checked.
It would apply directly to the orbit detector only after a support bound placing
that selected detector inside `[-0.8,0.8]`; no such bound is currently proved.
The complete interface audit is [record 004](docs/map/004_endpoint_literature_interface_audit.md).

### 4.3 What record 1087 does not prove

Record 1087 computed negative largest eigenvalues for 168 floating-point
compression matrices built from real-valued sampled profiles at ROOT-scale
radii. A certified exact subspace `V_K subset V` would satisfy

$$
\sup_{h\in V_K}\frac{A(h)}{\lVert h\rVert_2^2}
\le
\sup_{h\in V}\frac{A(h)}{\lVert h\rVert_2^2}.
$$

The actual scan does not certify such a subspace. It enforces the moment
constraints by floating-point quadrature and SVD; its sine profiles, extended
by zero outside the window, are not C-infinity at the endpoints. It also does
not test general complex-valued directions. The reported numbers are therefore
not rigorous lower bounds for the full supremum. They say only that no sampled
matrix had an eigenvector with a positive computed eigenvalue. The scan did
not close the root-window problem, retire support transport, or change the
route.

## 5. Scope boundaries

The following distinctions prevent local or conditional results from being
reported as RH:

| Boundary                              | Reason |
| :------------------------------------ | :----- |
| ROOT positivity is not the B5 result  | The proved negative detector has orbit support, and its visible prime terms must be included. |
| A floating-point finite-matrix scan is not a continuum sign theorem | It certifies neither exact carrier inclusion nor an upper bound for the unresolved complement. |
| The normalized coverage theorem is audit-only | Its older additive convolution fails the required Mellin product law; see [`not_normalizedCC20MellinConvolutionLaw`](ConnesWeilRH/Source/CC20YoshidaConstruction.lean#L2727). |
| Axiom-clean does not mean premise-free | `#print axioms` does not report ordinary theorem parameters or hypotheses. |
| The output theorem is still conditional | [`unconditional_rh_skeleton`](ConnesWeilRH/Dev/UnconditionalSkeleton.lean#L8020) invokes project axioms listed in the output ledger. Its historical name is not a mathematical status claim. |

The universal all-test campaign is frozen. New work is accepted only when it
supplies the ROOT local certificate, the same-detector semi-local inequality,
or a direct healthy-test contradiction to `SourceRH`; see
[`RH_MAINLINE_FREEZE.md`](RH_MAINLINE_FREEZE.md).

## 6. Verification

Formal claims are checked in this order:

```text
source formula or theorem
          |
          v
exact project definition and convention bridge
          |
          v
Lean declaration
          |
          v
focused #print axioms audit
          |
          v
build log with a success footer and no error lines
```

Floating-point calculations are kept in `docs/proofs/` as candidate generation
or diagnostics. They are not cited as proofs of infinite-dimensional signs.

Build the imported source tree with:

```bash
lake build ConnesWeilRH
```

Research-frontier modules under `ConnesWeilRH/Dev/` are not all imported by the
root aggregate and must be targeted explicitly with their paired audit modules.
Repository build-resource admission is documented in
[`RESOURCE_SCHEDULING.md`](RESOURCE_SCHEDULING.md).

## 7. Sources

1. Alain Connes and Caterina Consani, *Weil positivity and Trace formula: the
   archimedean place*, [arXiv:2006.13771](https://arxiv.org/abs/2006.13771).

   The paper proves the single-archimedean-place compact-window result and
   develops the Sonin/prolate trace mechanism. It does not prove the general
   finite-place semi-local positivity theorem needed by C3.

2. Alain Connes, Caterina Consani, and Henri Moscovici, *Zeta Zeros and Prolate
   Wave Operators: Semilocal Adelic Operators*,
   [arXiv:2310.18423](https://arxiv.org/abs/2310.18423).

   This paper supplies the semi-local space and Fourier-transport framework.
   The repository's finite Euler-boundary modules formalize related operator
   identities but do not yet prove the required sign.

3. Marcus Chuk, *Weil positivity in compact windows: certified two-sided bounds
   and a Landau-Widom decay law*,
   [arXiv:2608.24827](https://arxiv.org/abs/2608.24827).

   This is an unreviewed preprint. Its compact-window lower bound is treated as
   an external candidate until the convention and certificate bridges in route
   record 004 are discharged.

The derivation of the Mellin square identity and explicit-formula convention
used by the project is recorded in
[`1070_weil_q_hunting_level1.md`](docs/proofs/1070_weil_q_hunting_level1.md).

## 8. Repository map

```text
ConnesWeilRH/
  Source/       imported definitions and proved infrastructure
  Route/        conditional route composition and equivalence audits
  Dev/          research-frontier leaves with focused audit modules

docs/map/       binding route and interface decisions
docs/proofs/    proof records, derivations, and numerical reconnaissance
scripts/        certificate and resource-aware build helpers
```

The final Mathlib target is
[`_root_.RiemannHypothesis`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/LSeries/RiemannZeta.lean).
The root import is [`ConnesWeilRH.lean`](ConnesWeilRH.lean).

## 9. License

Apache License 2.0. See [LICENSE](LICENSE).
