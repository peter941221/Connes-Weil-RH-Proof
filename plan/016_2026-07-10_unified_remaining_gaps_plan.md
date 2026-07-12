# 016 Unified Remaining Gaps Plan

Date: 2026-07-10

Status: rejected as an executable RH route. The lower CCM25 owner, abstract M2/M4
functional-analysis bottoms, and fixed-window finite-node interpolation are
implemented. The finite-node theorem does not produce a source Yoshida
detector: the normalized CC20 local sum is an additive/pole-pairing model.
The rejection-first audit found that the current Yoshida assembly is not a
detector producer. Its finite correction interpolates prescribed node values,
but the assembled transform multiplies those values by a rescaled base power.
That factor may vanish at `rho`. The far-tail threshold also grows after the
nearby interpolation radius is fixed, leaving an unproved coupled-radius
condition. No current theorem constructs one test that simultaneously detects
`rho`, interpolates every zero below its eventual tail threshold, and controls
all remaining zeros. Do not resume xi-counting, M2, M3A, M5C, consumer rewiring,
or root retirement under this plan. Reopen only with a new non-circular source
producer that closes both defects on the same test.

This plan absorbs the unfinished work from 012, 013, 014, and the proposed 015
final audit. The older plans remain evidence. They are no longer independent
execution entrypoints.

## 1. Decision

Use one plan document until the route reaches a proved mathematical fork.

```text
one active plan now:                     plan 016
pre-created subplans:                    none
proof certificates created on results:  allowed
Lean work before mathematical gates:     denied
```

The preferred route avoids the unsupported general finite-`S` remainder
claim. It puts the finite interpolation part of a Yoshida construction in one
fixed narrow positive interval. The resulting selected convolution square has
log-support strictly inside `(-log 2, log 2)`, so each finite prime-power
evaluation `n >= 2` vanishes. A source detector still requires the global
tail estimate over the other zeta zeros from CC20 Appendix C; finite Mellin
interpolation alone does not supply its strict zero-sum sign.

```text
primary route:   fixed narrow window -> no finite-prime terms -> source Yoshida tail
                 -> archimedean remainder
fallback route:  prove the missing general finite-S remainder theorem directly
forbidden move:  assume the fallback theorem from CCM24 or the 2026 survey
```

M5A fixes the positive window `(3/4, 5/4)`. Its log-width is proved strictly
less than `log 2`, and the actual convolution support theorem places the
selected square strictly inside the corresponding difference interval.

Plan 012 established two facts that change the route:

```text
P_hat P theta_S(g) has a direct Hilbert-Schmidt construction
supportSquareTrace = qwLambda is false on the full triple-vanishing class
```

The source formula must retain a trace remainder. Contract M0 proved the
trace-class-interface identity

```text
PositiveTrace_(S,Lambda_op)(g)
  = QW_lambda_qw(g,g)
      - Pole_lambda_qw(g)
      + D_(S,Lambda_op)(F_g).
```

The route's vanishing at `+/- i/2` kills `Pole_lambda_qw(g)` and leaves
`PositiveTrace = QW_lambda_qw + D`. The operator cutoff `Lambda_op` and CCM25
support parameter `lambda_qw` are distinct. No later phase may identify them or
set `D` to zero by a field choice. See
`docs/proofs/016_corrected_trace_identity.md`.

### 1.1 Scope and non-goals

Scope:

```text
all six explicit roots and the hidden provider
the selected CCM25 source owner
the corrected trace identity and explicit remainder
the fixed-window conditioned detector theorem
the archimedean-first route and the finite-S fallback decision
consumer rewiring, root retirement, and the closed final audit
```

Non-goals:

```text
no route-consumer rewiring before the stated mathematical gates
no construction of the rejected SourceWeilFormData API
no use of RH-equivalent coverage as a lower producer
no empty subplans before a proof or counterexample creates a real fork
```

## 2. Final Target And Current Boundary

The only completion target is a closed Lean theorem:

```text
theorem unconditional_rh_skeleton : _root_.RiemannHypothesis
```

The printed type must contain no explicit, implicit, instance-implicit, or
auto-implicit premise.

The current theorem has one hidden premise:

```text
forall [NormalizedSelectedSourceCoreTraceQWLambdaCalibrationProvider],
  RiemannHypothesis
```

Its axiom graph contains six project roots:

```text
normalizedCoreCC20PropositionC1SourceCriterionRoot
normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot
normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot
normalizedCoreS2B1TracePackageRemaindersRoot
normalizedCoreSourceWeilFormDataRoot
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
```

## 3. Root Classification

```text
+-----------------------------------------------------------+--------------------------+
| current obligation                                        | classification           |
+-----------------------------------------------------------+--------------------------+
| normalizedCoreSourceWeilFormDataRoot                      | inconsistent old API     |
| normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot    | honest lower data gap    |
| normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot          | false old trace contract |
| normalizedCoreS2B1TracePackageRemaindersRoot              | false old trace contract |
| normalizedCoreCC20PropositionC1SourceCriterionRoot        | RH-equivalent outlet     |
| normalizedSelectedFinalRouteDetectorCriterionCoverageRoot | RH-equivalent outlet     |
| calibration provider premise                              | hidden old-route premise |
+-----------------------------------------------------------+--------------------------+
```

Named guards:

```text
CCM25SourceDataGuards.not_nonempty_concreteSourceWeilFormData

normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_standardSourceRH
normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_mathlibRH
```

The first guard rejects construction of the old CCM25 owner. The last two
guards reject detector coverage as a lower producer.

### 3.1 Current code evidence

The six roots, hidden provider, and final theorem are in one active consumer
file:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:137
  normalizedCoreSourceWeilFormDataRoot

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:657
  normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1067,1076
  normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot
  normalizedCoreS2B1TracePackageRemaindersRoot

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1551
  normalizedCoreCC20PropositionC1SourceCriterionRoot

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2590-2597
  NormalizedSelectedSourceCoreTraceQWLambdaCalibrationProvider
  and the instance-backed input read-off

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:7786
  normalizedSelectedFinalRouteDetectorCriterionCoverageRoot

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:8042-8049
  final bridge and unconditional_rh_skeleton
```

The current normalized core encodes operator claims as scalar or logical
proxies rather than analytic operators:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:231
  normalizedCoreTraceAmplitude_eq_encodedEvaluationNorm

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:238
  normalizedCoreConvolutionStar_eq_add

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:264
  normalizedCoreHilbertSchmidtGate_iff_traceClass_cyclicLegal

ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:679-713
  positiveTrace_eq_qwLambda is derived through supportSquare_qwLambda
```

The negative guards and selected replacement owner have concrete anchors:

```text
ConnesWeilRH/Dev/CCM25SourceDataGuards.lean:24-42
  contradiction for Nonempty SourceWeilFormData

ConnesWeilRH/Route/CC20RouteRealization.lean:20198-20225
  detector coverage equivalence to SourceRH and Mathlib RH

ConnesWeilRH/Source/CCM25Concrete/SelectedWeilSquare.lean:25
  one selected test, its convolution square, and shared support bound

ConnesWeilRH/Source/CCM25Concrete/SelectedWeilFormula.lean:169
  archimedean integrability field and selected formula owner

ConnesWeilRH/Source/CCM25Concrete/SelectedArchimedeanIntegrability.lean:247,284
  one-sided origin control, exponential-tail control, and full Ioi integrability

ConnesWeilRH/Dev/UnifiedRemainingGapsM1Audit.lean:30-34
  import-facing signatures and focused axiom audit for the selected owner
```

These references name the old consumers and the replacement boundary. They do
not establish M3A, M5A, or M5B.

### 3.2 Consumer rewiring ledger

Each root has a named first consumer. A declaration rename does not retire the
root.

```text
old root:
  normalizedCoreSourceWeilFormDataRoot
first consumers:
  UnconditionalSkeleton.lean:318-323  normalizedCoreSourceAnalyticCoreFromTheorems
  UnconditionalSkeleton.lean:330-342  evaluation and Weil-form projections
replacement:
  M1 SelectedWeilFormulaOwner and same-owner projections
required change:
  remove the old SourceAnalyticCore construction; do not cast M1 back into the
  uninhabited SourceWeilFormData type

old root:
  normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot
first consumers:
  UnconditionalSkeleton.lean:805-811  normalizedCoreCCM25WeilObjectInputFromTheorems
  UnconditionalSkeleton.lean:835-844  normalizedCoreCCM25ArithmeticConstructorInputFromTheorems
  UnconditionalSkeleton.lean:1597-1600 normalizedSourceObjectCoreFinitePrimeExactFromTheorems
replacement:
  M1 finite global/restricted sums projected from the same SelectedWeilFormulaOwner

old roots:
  normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot
  normalizedCoreS2B1TracePackageRemaindersRoot
first consumers:
  UnconditionalSkeleton.lean:1585-1586 normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems
  UnconditionalSkeleton.lean:1085-1094 NormalizedCoreS2B1ActualScalarIdentificationFamily
  UnconditionalSkeleton.lean:2133-2136 normalizedRemaindersFromTheorems
replacement:
  M0/M2 corrected trace owner plus M3A/M4 archimedean remainder and sign theorem

old root:
  normalizedCoreCC20PropositionC1SourceCriterionRoot
first consumer:
  UnconditionalSkeleton.lean:1566-1575 normalizedCoreCC20RHExitObjectPackageFromTheorems
replacement:
  M6 global contradiction theorem, followed by a compatibility projection

old premise:
  NormalizedSelectedSourceCoreTraceQWLambdaCalibrationProvider
first consumer:
  UnconditionalSkeleton.lean:2595-2608 normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
replacement:
  M0 same-owner equality; no typeclass or stored scalar-identification input

old root:
  normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
first consumer:
  UnconditionalSkeleton.lean:7904-7907 normalizedSelectedFinalRouteSourceRHFrom08AFromTheorems
replacement:
  M6 theorem produces SourceRH from analytic data, then the final bridge consumes it
```

## 4. Unified Dependency Graph

```text
fixed narrow positive window J
  |
  +-- fixed-window Mellin separation
  |     |
  |     +-- every nonzero exponential polynomial is detected inside J
  |     +-- all interpolation bumps remain inside J
  |     |
  |     v
  |   finite-node candidate g_rho
  |
  +-- source Yoshida approximation
  |     |
  |     +-- genuine multiplicative convolution and involution
  |     +-- finite constraints near rho_0
  |     +-- uniform decay at every other nontrivial zero
  |     +-- source zero-sum has the strict off-line sign
  |     |
  |     v
  |   source Yoshida detector g_rho
  |
  +-- honest CCM25 owner for g_rho
  |     |
  |     +-- genuine g* * g
  |     +-- pole and archimedean terms
  |     +-- support(g* * g) is strictly inside (-log 2, log 2)
  |     +-- every n >= 2 finite-prime term vanishes
  |
  +-- archimedean operator/remainder owner
  |     |
  |     +-- P, P_hat, theta(g), A = P_hat P theta(g)
  |     +-- A is Hilbert-Schmidt
  |     +-- PositiveTrace = Tr(A* A) >= 0
  |     +-- D_infinity o Q = <xi,(-2 Id + K_I)xi>
  |     +-- xi perpendicular to finite B_I -> D_infinity <= 0
  |
  +-- corrected trace identity, with pole killed by Mellin vanishing
        |
        v
  sign contradiction for the same g_rho
        |
        v
  RiemannHypothesis

fallback only if the archimedean route fails for a named reason:

  finite S
    -> prove D_(S,1) o Q = <xi,(-c Id + K_(S,I))xi>
    -> reuse the same compact bad-space and conditioned-detector layers
```

The mathematical bottom is the source Yoshida approximation: finite-node
separation plus a tail estimate over all other zeta zeros in a genuine
convolution model. The general finite-`S` theorem is not a prerequisite unless
this primary route is rejected for a proved reason. Package renames,
calibration records, and detector coverage cannot replace this theorem.

## 5. Source Evidence

### 5.1 Fixed-S coordinate and operator

CCM24 constructs the unitary fixed-S coordinate and turns Fourier into
reflection:

```text
Alain Connes, Caterina Consani, Henri Moscovici
Zeta zeros and prolate wave operators
https://arxiv.org/abs/2310.18423
mainc2m24fine.tex:700-741, 786-804
```

The direct commutator construction and its cutoff extension are recorded in:

```text
docs/proofs/cc20-012-mathematical-verdict.md
```

### 5.2 Nonzero trace remainder

CC20 proves in the archimedean case:

```text
D o Q(xi * xi^*) = inner(xi, (-2 Id + K_I) xi),
```

where `K_I` is Hilbert-Schmidt. Source:

```text
Alain Connes, Caterina Consani
Weil positivity and Trace formula, the archimedean place
https://arxiv.org/abs/2006.13771
weil-compo.tex:755-808
```

The source theorem states compactness. Its proof gives the explicit kernel

```text
K_I(v,u) = Q delta(u/v)  when u >= v
         = Q delta(v/u)  when v >= u.
```

This kernel is real and symmetric, so self-adjointness is a separate theorem
to prove from the kernel formula; it is not an extra hypothesis imported from
the theorem statement. M4 itself needs only compactness and the real part of
the quadratic form.

The same source immediately gives a potentially shorter primary subroute:

```text
Corollary qeasy (weil-compo.tex:831-842)
D o Q <= 0 on C_c^infinity([u^-1,u]), u = 1.10246.
```

Its proof uses positivity of the convolution square and a direct local bound
on the remainder kernel, rather than a compact-operator conditioning space.
This is source evidence, not an accepted route move yet. Acceptance requires
two same-object bridges: the selected CCM25 test must be the `Q`-image of the
CC20 positive-definite test on the same narrow symmetric interval, and the
CC20 functional `D` must be proved equal to the M0-normalized remainder for
the selected owner. Until both bridges compile, M3A/M4/M5B remain active and
the corollary cannot be used to remove any root.

The zero-integral subspace still contains tests with nonzero remainder. Those
tests satisfy the route's three Mellin vanishing conditions after applying
`Q`. This rejects the old no-defect equality.

### 5.3 Honest CCM25 formula

CCM25 defines genuine convolution, involution, local terms, and QW:

```text
Zeta Spectral Triples
https://arxiv.org/abs/2511.22755
Equations 2.1, 2.2, 3.7, 3.10, 3.19, 3.20
```

The selected owner foundation already compiles in:

```text
ConnesWeilRH/Source/CCM25Concrete/CompactLogConvolution.lean
ConnesWeilRH/Source/CCM25Concrete/SelectedWeilSquare.lean
ConnesWeilRH/Source/CCM25Concrete/SelectedWeilFormula.lean
ConnesWeilRH/Source/CCM25Concrete/SelectedArchimedeanIntegrability.lean
```

The selected owner now proves Hermitian symmetry, reality of its pole,
archimedean and finite-prime values, full integrability over `(0,infinity)`,
exact global/restricted support, and the omitted-term discrepancy. The
import-facing audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

### 5.4 RH-level exit

CC20 Proposition C.1 and the compiled detector guards identify global Weil
positivity with RH. No checked source through 2026-07-10 proves the missing
global inequality.

### 5.5 Why the archimedean-first route is primary

The checked sources do not currently justify Contract M3B for general finite
`S`:

```text
CCM24
https://arxiv.org/html/2310.18423v2
  defers general-S Jacobi coefficients to a forthcoming paper
  gives the Sonin/negative-spectrum relation only up to a possible
  finite-dimensional discrepancy

Connes 2026 survey, Section 6.6
https://arxiv.org/html/2602.04022v1
  still lists the relevant simplicity/evenness and approximation-convergence
  steps as remaining work
```

The same survey's Theorem 7.1 supplies an archimedean inequality for tests in
the narrow window `[2^(-1/2), 2^(1/2)]` with the required Mellin vanishings.
This does not prove M5A or M5B, but it identifies a source-backed route that needs only
the already checked archimedean compact remainder. Therefore general finite
`S` is a fallback research problem, not an assumed dependency.

### 5.6 Yoshida detector boundary

CC20 Appendix C gives the required source criterion. For a finite set `F`
containing `{0,1}` and an off-line nontrivial zero `rho_0`, the proof requires
a compact smooth `g_0` with finite vanishing, `g_tilde(rho_0) = 1`, and

```text
|g_tilde(rho)| <= epsilon / |rho - rho_0|^2
for every other nontrivial zero rho.
```

Source: arXiv:2006.13771, `weil-compo.tex:2075-2085`.

The compiled normalized CC20 carrier cannot provide this theorem. Its
`starConvolution` is pointwise addition and its `weilLocalSum` is the negative
pole pairing. The axiom-free Lean guard
`not_normalizedCC20MellinConvolutionLaw` rejects Mellin multiplicativity on a
fixed-window interpolant. See
`docs/proofs/016_yoshida_model_verdict.md`.

## 6. Exact Mathematical Contracts

### Contract M0. Sign and statement freeze

The proved trace-class-interface equality contains:

```text
same S, g, and F_g
separate lambda_qw and Lambda_op
ordinary PositiveTrace
restricted QW_lambda_qw
source remainder D_(S,Lambda_op)
one source pole pairing and no unsupported rank term
```

The certificate derives `+QW`, `-Pole`, and `+D` from the CC20 and CCM25
conventions. It compares the archimedean, finite-prime, pole, and projection
terms. M2 owns the trace-class hypotheses used by the algebraic theorem.

Output:

```text
docs/proofs/016_corrected_trace_identity.md
```

Certificate status: complete.

### Contract M1. Selected CCM25 formula owner

The lower selected owner is complete:

```text
archimedean integrability on (0,infinity)
reality of the selected square evaluation
exact finite global and restricted prime-power sums
full and restricted formula equality
same-owner canonical atom and package projections
```

The owner cannot contain `SourceWeilFormData` or
`CommonFinitePrimeArithmeticSourceData` as an input.

The first four items compile and pass the focused axiom audit. The selected
owner itself is the canonical same-owner package. Projection into the old
all-test structures is forbidden because `SourceWeilFormData` is uninhabited.
The new selected route consumes this owner directly after M3A, M5B, and M5C
pass.

### Contract M2. Fixed-S positive trace owner

Turn the direct commutator proof into one mathematical theorem for each finite
cutoff:

```text
A_(S,Lambda_op,g) = P_hat_Lambda_op P_Lambda_op theta_S(g)
A is Hilbert-Schmidt
A* A is trace-class
Tr(A* A) = norm(A)_HS^2 >= 0
an L2 kernel represents A
```

The theorem uses the unitary `K_S`-invariant scattering coordinate. It does not
transport projections through `eta_S`.

The project-local ordinary-trace bottom now compiles in
`CC20Concrete/PositiveTrace.lean`: trace is defined independently as a Hilbert
basis diagonal series, and Hilbert-Schmidt summability proves that `A* A` is
trace-class with real nonnegative trace equal to the norm square. The remaining
M2 work is to construct that summability witness and an L2 kernel from the two
fixed-S commutator kernels.

### Contract M3A. Archimedean remainder specialization

Use the checked archimedean identity on one fixed support interval `I`:

```text
D_infinity o Q(xi * xi^*)
  = inner(xi, (-2 Id + K_I) xi),

K_I compact.
```

Connect this concrete `K_I` and `c=2` to the completed M4 theorem. This is the
primary route. It must preserve the exact source normalization used by M0 and
must not replace the remainder by zero.

The concrete API must define the Hilbert space `L2(sqrt I, d*rho)`, the
source-test-to-`xi` map, the displayed integral kernel, and the remainder
functional independently. It must then prove the kernel representation,
compactness, and the displayed remainder equality. Real symmetry may be used
to prove self-adjointness, but self-adjointness is not required by M4.

### Contract M3B. General finite-S remainder fallback

Set `Lambda_op=1`, matching the CC20 base model. Prove or reject this source
theorem for each fixed finite `S` and compact support interval `I`:

```text
D_(S,1) o Q(xi * xi^*)
  = inner(xi, (-c_(S,I) Id + K_(S,I)) xi),

c_(S,I) > 0,
K_(S,I) compact and self-adjoint.
```

A Hilbert-Schmidt kernel for `K_(S,I)` is preferred because it gives a direct
Lean target and a finite spectral obstruction. The archimedean theorem supplies
the base case `c=2`.

No checked source supplies this theorem. Work on M3B only if M5B/M5C proves
that the archimedean route cannot carry the global contradiction, or if a new
primary source supplies the missing theorem. Reject the finite-`S` fallback if
its remainder has an uncontrolled essential positive part or requires
infinitely many conditioning directions.

### Contract M4. Finite bad-space theorem

For any proved normal form `K - c Id` with `c > 0`, a full spectral projection
is unnecessary. Compactness of `K` gives a finite `c`-net of the image of the
unit ball. Define

```text
B = span of the finite net centers.
```

The finite-net argument proves:

```text
FiniteDimensional B
xi perpendicular to B
  -> Re <xi,(K - c Id)xi> <= 0
```

No structure may store the final inequality as a field.

This abstract theorem is complete in
`CC20Concrete/CompactBadSpace.lean`. It constructs `B_(S,I)` from compactness
and proves the sign by orthogonality and Cauchy-Schwarz. The import-facing audit
contains only `propext`, `Classical.choice`, and `Quot.sound`. M3A still has to
connect the checked archimedean `K_I` and threshold `2`; M3B would supply a
finite-`S` operator only on the fallback route.

### Contract M5A. Fixed-window Mellin separation and support

For the predetermined interval `J = (3/4,5/4)`, the completed theorem proves:

```text
every nonzero weighted Mellin coefficient family
  -> exists t in J with weightedMellinKernel rho coeff t != 0

every basis bump built from that point has support inside J

support of the selected convolution square
  is strictly inside (-log 2, log 2)
  -> every finite-prime term at n >= 2 is zero
```

After `t = exp u`, the kernel is a finite exponential polynomial. Vanishing
on an open log interval gives a derivative recurrence for all exponential
moments; evaluation at zero and the existing Vandermonde theorem recover every
coefficient. The implementation is in:

```text
CC20YoshidaConstruction.lean
  weighted_mellin_kernel_log_window_independence
  fixed_window_node_value_image_mellin_surjective

CCM25Concrete/SelectedYoshidaBridge.lean
  convolutionSquare_support_subset_difference
  fixedWindow_logWidth_lt_log_two
  fixedWindowSelectedSquare_finitePrimeTerm_eq_zero
```

The import-facing M5A audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. M5A does not include bad-space orthogonality; that remains M5C
and cannot be stated before M3A supplies the concrete `xi` space.

### Contract M5B. Source Yoshida approximation and zero-sum sign

For each hypothetical off-line zero `rho`, construct a compact test whose
source convolution square satisfies:

```text
support inside the fixed M5A interval
Mellin vanishing at 0 and +/- i/2
g_tilde(rho) = 1
uniform epsilon / |rho' - rho|^2 control at every other nontrivial zero rho'
strict source zero-sum sign for the genuine convolution square
```

This is the central unresolved theorem. A finite interpolation matrix may
handle the nearby constraints, but it cannot stand in for the global tail
bound. The theorem must use the same convolution and zero-sum functional that
the selected explicit formula uses.

The first tail layer now compiles in `CC20YoshidaTail.lean`:

```text
mellinLogSliceRaw_support_subset
mellin_eq_fourier_mellinLogSlice
mellin_vertical_quadratic_decay
exists_uniform_mellin_vertical_quadratic_decay
```

The Mellin transform is the Fourier transform of a compactly supported
log-slice. One constant now gives quadratic decay for every `sigma in [0,1]`.
The proof bounds the first three vertical derivative integrals across a common
compact support and applies the Fourier derivative estimate.

The nearby-zero layer now compiles in `CC20YoshidaNearZeros.lean`:

```text
sourceNontrivialZerosInClosedBall_finite
fixed_window_finite_mellin_surjective
fixed_window_nearby_zero_mellin_surjective
```

The first theorem places the source nontrivial zeros in a closed ball inside
Mathlib's finite compact intersection with `riemannZetaZeros`. The other two
theorems extend fixed-window interpolation to any finite complex node set and
then combine nearby zeros with extra route nodes. Their import-facing audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.

M5B remains partial. The next theorem must construct a normalized family whose
uniform coefficient is below the requested `epsilon` and derive the strict
sign from the genuine source zero sum. Exact nearby interpolation is complete,
but it does not reduce the uniform far-tail constant.

Yoshida 1992, Lemma 1, pp. 285-286 supplies the missing construction pattern:

```text
alpha = alpha_1 * ... * alpha_M * alpha_0^( * N)
Phi(s) = Phi_0(s)^N * product_i Phi_i(s)
```

The `alpha_i` factors kill the finitely many nearby zeros. The `N` copies of
`alpha_0` shrink the far tail through the transform product law. The repository
now formalizes the analytic algebra in `CC20YoshidaConvolution.lean`:

```text
convolution_support_subset_add_Ioo
laplaceAt_convolution
laplaceAt_convolutionIterate
convolutionIterate_support_subset_Ioo
laplaceAt_rescale
convolutionIterate_rescale_inv_natCast_support_subset_Ioo
laplaceAt_convolutionIterate_rescale_inv_natCast_convolution
convolutionIterate_rescale_inv_natCast_convolution_support_subset_of_budget
exists_residualWindow_correction_with_quadratic_decay
exists_residualWindow_nearbyZero_correction_with_quadratic_decay
convolutionIterate_rescale_convolution_vertical_quadratic_bound
convolutionIterate_rescale_convolution_distance_quadratic_bound
exists_residualWindow_nearbyZero_assembled_distance_bound_lt
```

The 2026-07-11 bridge closes the positive-variable coordinate mismatch:

```text
laplaceAt_compactLogTestOfWindow_eq_mellin
exists_uniform_laplaceAt_vertical_quadratic_decay
```

The module now also proves the quantitative implication

```text
uniform norm(laplaceAt alpha_0 s) <= q < 1
  -> enough convolution copies make the transform <= epsilon,
     including one bounded finite correction factor.
```

Normalized rescaling by `1/(N+1)` now cancels the support growth of the `N+1`
base copies exactly. The assembled theorem adds one finite correction factor
and proves containment in a prescribed outer window from explicit endpoint
budgets. These theorems are a conditional analytic engine: M5B must still
prove the source counting/summability inputs and strict source zero-sum sign.

The finite correction producer is now complete at this interface. Given any
residual log window around zero and arbitrary values on a finite node set, it
constructs one correction with those exact Laplace values and retains the
uniform quadratic strip bound of that same correction. Its nearby-zero
specialization uses the closed-ball source zeros together with the route nodes.

The base-factor contraction is discharged by
`exists_uniform_laplaceAt_vertical_half_contraction`: the existing uniform
quadratic bound supplies an explicit height beyond which its norm is at most
`1/2` across the closed critical strip. The transform and support laws now
produce one assembled source object from the completed residual-window
correction.

That quantitative step is now complete for the strip branch. The assembled
test satisfies a vertical quadratic bound with coefficient
`(1/2)^(N+1) * C`; a closed-strip geometry theorem converts it to a
distance-weighted bound around `rho`, and the final theorem chooses `N` so the
coefficient is smaller than any requested positive `epsilon`. It preserves the
same residual correction and finite node values. The hypotheses explicitly
separate the finite-height region and require sufficiently high imaginary
part. The later source-index theorem proves that the apparent negative-integer
branch is empty, so no separate negative-real-axis estimate remains.

The old `YoshidaDetector` route is explicitly unavailable for that assembly.
Its `weilSumPositiveIfOffLine` field stores the required strict sign, and its
consumer theorem only converts that stored sign into the RH-level CC20 exit.
M5B must instead define the source zero-sum on the same `CompactLogTest` that
owns the selected CCM25 formula, prove convergence from the new tail bound, and
derive its sign without either old detector field.

The global source nontrivial-zero set is now proved countable. The project also
defines its least strict dyadic shells about `rho`, proves that they form a
partition, and proves each shell finite from zeta-zero discreteness. The
axiom-clean theorem `sourceNontrivialZero_summable_of_dyadic_bounds` consumes

```text
shellCard(n) <= K * (n + 1) * 2^n
term(z)      <= B / (2^n)^2  for z in shell n
```

and returns `Summable`. The `(n + 1) * 2^n` rate is deliberate: it matches the
dyadic form of an `O(R log R)` Riemann-von Mangoldt estimate. A stronger
`O(R)` shell assumption would not match the known zero-counting scale.

Mathlib has no Riemann-von Mangoldt counting estimate. Discreteness and
compact-intersection finiteness do not imply the displayed shell bound.
However, the full `O(R log R)` theorem is stronger than the spectral consumer
requires. The sharp compiled criterion is now

```text
shellCard(n) <= K * q^n
term(z)      <= B / (2^n)^2
0 <= q < 4
```

because the shell totals are bounded by `K*B*(q/4)^n`. Thus any xi growth
estimate producing a dyadic zero-count ratio below `4` suffices; a standard
Riemann--von Mangoldt bound remains one valid route but is no longer the unique
or logically necessary bottom. M5B must prove such a source count, transfer
the Yoshida tail to the same zero index, then prove the spectral explicit
formula before defining the spectral `tsum` or claiming its strict sign.

The counting-index transport now compiles. Following
Hasanalizade--Shen--Wong, arXiv:2107.06506, p. 3, Lean defines the symmetric
height set corresponding to `N-bar(T)` and proves

```text
shell(rho,n)
  subset of {z | |Im z| <= |Im rho| + 2^(n+1)}.
```

The symmetric-height set is finite, its cardinality bounds the arbitrary-center
shell cardinality, and the summability consumer accepts its geometric dyadic
count directly. Thus the remaining counting gate is any source xi growth
estimate yielding ratio `q < 4`; no separate conjugation, negative-integer, or
shell-transport gate remains.

The dyadic algebra and Jensen reduction now compile. A global bound
`N-bar(T) <= A*T*log(T) + C*T` is sufficient for the spectral summability
consumer, with the center-dependent dyadic constant constructed in Lean. The
entire function

```text
xi(s) = s*(s-1)*completedRiemannZeta0(s) + 1
```

is proved equal to `s*(s-1)*completedRiemannZeta(s)` away from `0,1`. Source
nontrivial zeros inject into its finite-order divisor support, and Mathlib's
Jensen inequality bounds their closed-ball cardinality from a sphere norm
bound. At this stage the counting gate was reduced to a circle growth estimate
for this xi; the sharper geometric and right-half-plane reductions below lower
that input further. Index transport, distinct-versus-multiplicity conversion,
and Jensen plumbing are complete.

The final geometry bridge is compiled as well:

```text
{source zeros | |Im z| <= T}
  -> closedBall(center = 2, radius = T + 2)
  -> xi divisor
  -> Jensen sphere bound.
```

Thus the next proof no longer needs to mention source zero records. It must
bound `norm(completedRiemannXi z)` on circles centered at `2` strongly enough
to produce a dyadic Jensen count `K*q^n` for some `q < 4`.

The outer radius is now fixed to `2*(T+2)`, so Jensen's denominator is exactly
`log 2`. The compiled exponential interface is

```text
norm(xi z) <= exp(G(T)) on sphere(2, 2*(T+2))
  -> N-bar(T) <= (G(T) - log(norm(xi 2))) / log(2).
```

The direct compiled consumer now combines these circle bounds with Jensen and
quadratic spectral decay. The functional equation
`completedRiemannXi (1-s) = completedRiemannXi s` also folds every point to
`Re s >= 1/2` while increasing its norm by at most one. The remaining analytic
counting estimate is therefore a right-half-plane xi majorant whose induced
dyadic ratio is strictly below `4`; `O(T log T)` is sufficient but not required.

The import-facing consumer now states that remaining input on right-half-plane
balls directly. At dyadic level `n`, it is enough to bound xi for

```text
Re w >= 1/2
norm(w) <= 2 * (|Im rho| + 2^(n+1) + 2) + 3.
```

`sourceNontrivialZero_summable_of_xi_right_halfplane_ball_bounds` folds every
Jensen-circle point into that domain, preserves the xi norm, and carries the
result through Jensen to `Summable`. The next analytic proof may therefore
work solely with the Mellin integral defining `(hurwitzEvenFEPair 0).Lambda0`
and the existing exponential decay of its modified theta kernel.

That Mellin interface now compiles. `completedRiemannXiKernel` names
`(hurwitzEvenFEPair 0).f_modif`, and
`completedRiemannZeta0_eq_mellin_completedRiemannXiKernel` identifies the
pole-removed completed zeta with its Mellin transform. The real moment

```text
integral_(0,infinity) t^(sigma/2-1) * norm(kernel(t)) dt
```

controls `norm(completedRiemannZeta0 s)` at `sigma = Re s`, independently of
`Im s`; `norm_completedRiemannXi_le_kernelMoment` adds only the explicit
quadratic xi polynomial factor. The kernel equations also reduce both regions
to the decaying theta tail above one: for `t>1` it is `theta(t)-1`, while for
`0<t<1` it is `t^(-1/2)*(theta(1/t)-1)`. The remaining counting bottom is now
an explicit growth bound for this nonnegative real Mellin moment.

The kernel black box is now eliminated from that moment estimate. With

```text
C_theta = 2 / (1 - exp(-pi)),
```

Lean proves

```text
t > 1:
  norm(kernel(t)) <= C_theta * exp(-pi*t)

0 < t < 1:
  norm(kernel(t)) <= t^(-1/2) * C_theta * exp(-pi/t).
```

The proof uses Mathlib's explicit Jacobi-theta series bound and the compiled
kernel functional equation; it introduces no asymptotic premise. The next
local theorem must split the real moment at `t=1`, apply these two bounds, and
derive a coarse subquadratic logarithmic growth estimate.

Hasanalizade--Shen--Wong, Corollary 1.2,
[arXiv:2107.06506](https://arxiv.org/abs/2107.06506), counts zeros with
`0 < Re rho < 1` and `0 < Im rho <= T`. The current
`MathlibNontrivialZero` record does not carry a strip predicate, so the paper's
count cannot apply to it by definition alone. Two new functional-equation
bridges give the required honest split:

```text
sourceNontrivialZero_re_lt_one:
  Re rho < 1

sourceNontrivialZero_zero_lt_re_or_eq_neg_nat:
  0 < Re rho  or  rho = -n

sourceNontrivialZero_not_eq_neg_nat:
  rho != -n

sourceNontrivialZero_zero_lt_re:
  0 < Re rho
```

The first theorem uses Mathlib's zero-free right half-plane. The second sends a
zero outside the negative integers through `rho -> 1-rho` and reaches the same
zero-free region. The next theorem uses the functional equation to rule out
negative odd integers, the source record to rule out negative even trivial
zeros, and `riemannZeta_zero` to rule out zero. Thus the source count may apply
the paper's `N(T)` directly to the open-strip index. M5B still must formalize
that strip cardinal estimate on the same dyadic shells and apply the completed
assembled-test majorant.

Output after proof or rejection:

```text
docs/proofs/016_source_yoshida_approximation_verdict.md
```

### Contract M5C. Finite-conditioned archimedean sign

After M3A exposes the concrete `xi` space, add the M4 bad-space orthogonality
conditions to the source detector construction. The proof must retain M5B's
global tail estimate and strict source zero-sum sign.

```text
xi_rho perpendicular to the M3A/M4 bad space B_I
the M0-normalized remainder has the required sign
the same source detector remains strict
```

M5C is a route-rejection gate, not routine downstream work. Before constructing
the concrete bad space, test the shorter CC20 Corollary 3.8 route:

```text
Qeasy factorization target:
  selected Yoshida convolution square = Q(f)
  f is positive definite
  support(f) lies in [u^-1,u], u = 1.10246
```

The support constraint is feasible: normalized convolution powers and one
finite correction fit in an arbitrarily prescribed log window by splitting the
window budget between the base and correction. The decisive issue is the
factorization with positivity preserved. If it holds, Corollary 3.8 gives the
remainder sign directly and M3A/M4/M5C become unnecessary on the primary route.
If it fails, prove the failure and immediately test whether Mellin detection at
`rho` is independent of the concrete M4 bad-space functionals. If that joint
separation fails, reject the fixed-window route before doing further counting
or trace formalization.

### Contract M6. Global Weil contradiction

Combine M0-M5C on the same detector object:

```text
hypothetical off-line zero
  -> fixed-window detector kills every finite-prime term and the pole
  -> corrected archimedean trace identity and remainder control give opposite sign
  -> contradiction
```

This theorem may project to Proposition C.1 or detector coverage after the
analytic proof is complete. It cannot consume either RH-equivalent root.

### Contract ownership API

M1 uses the existing selected structures rather than the rejected global
source type:

```text
SelectedWeilSquareOwner
  sourceTest
  convolutionSquare
  shared support bound

SelectedWeilFormulaOwner
  square : SelectedWeilSquareOwner
  finiteSupport indexed by square
  proved archimedean integrability indexed by square
```

After M0 freezes the source identity, introduce one corrected fixed-S owner
with these ownership groups. The final Lean spelling may follow local namespace
conventions, but it may not weaken or split these groups:

```text
CorrectedFixedSTraceInput
  one SelectedWeilFormulaOwner
  S and visible-prime coverage
  lambda_qw for the CCM25 support window
  Lambda_op for the operator cutoff
  compact support interval I
  one route test g and its source transform F_g
  window, cutoff, coordinate, and admissibility proofs

FixedSPositiveTraceData, indexed by one CorrectedFixedSTraceInput
  P, P_hat, theta_S(g), and A = P_hat P theta_S(g)
  measurable L2 kernel for A
  Hilbert-Schmidt proof and norm
  A* A trace-class proof
  ordinary complex trace
  theorem that the trace is real and equals norm(A)_HS^2

FixedSRemainderData, indexed by the same CorrectedFixedSTraceInput
  source-normalized D_(S,Lambda_op)
  M0 corrected trace identity
  M3A operator K_I and c=2 in the primary archimedean specialization
  M3B operator K_(S,I) and c_(S,I) only in the finite-S fallback
  M4 finite bad space and sign theorem
```

M5B/M5C remain theorems that construct a fixed-window conditioned detector
from an off-line zero and the same remainder data. No owner may store detector
existence, strict Weil sign, SourceRH, or the final contradiction as a field.

## 7. Execution Phases

### Phase 0. Audit and freeze

1. Print the full types of the six roots, the provider, and the final theorem.
2. Freeze Contract M0 with source signs and one shared test.
3. Mark each old consumer as retained, replaced, or deleted.
4. Do not edit Lean route consumers in this phase.

Exit gate:

```text
M0 proof exists at the trace-class interface
old supportSquareTrace = qwLambda target is absent from the proposed route
provider contract is classified as reusable or deleted
```

### Phase 1. Finish the lower source owner

M1's lower selected owner is complete and import-facing verified. Keep the two
old 013 roots visibly active until the selected M3A/M5B/M5C route exists; do
not cast the owner into the rejected all-test API. Phase 6 performs the
consumer switch and root removal in one coherent change.

This phase does not claim route closure.

### Phase 2. Formalize the valid operator theorem

Prove M2 in a project-local `L2` and nuclear-trace layer. Keep the remainder in
every public read-off statement.

Do not project M2 into the old no-defect records.

### Phase 3. Connect the archimedean remainder

Connect the checked `-2 Id + K_I` identity to M4 without generalizing it to
finite `S`. Freeze the exact source normalization and the map from a selected
test to `xi`.

### 3.1 M3A regular-kernel analysis lane (closed 2026-07-12)

This lane is closed as an executable implementation lane. The Q-root survives
its local algebraic and Mellin rejection gates, but M3A's only planned consumer
still requires the rejected M5B all-other-zero detector through M5C. Do not
enter Lean or numerical kernel work under this plan. Preserve the steps below
only as an analysis contract for a future route with a new lower consumer; see
proof verdict 073.

```text
route obligation:
  connect the source archimedean remainder to CompactBadSpace with the same xi

old weak path:
  an abstract compact K_I proposition with no kernel/action owner

new mathematical owner:
  the regular remainder k_I after extracting the source -2 delta principal term

consumer to rewire:
  M4 finite conditioning space, after kernel-action and compactness are proved

forbidden circular inputs:
  SourceRH, QW positivity, detector coverage, arbitrary compact operators,
  or a stored `K_I` conclusion without its source kernel

smallest verification target:
  a project-local archimedean kernel module importing CompactBadSpace

focused axiom audit:
  kernel measurability, square-integrable majorant, kernel-action identity,
  compactness, and the `-2 Id + K_I` quadratic-form read-off
```

If a new lower consumer reopens this analysis contract, execute it in this
order:

1. Extract the exact CC20 formula at `weil-compo.tex:803-806` and define the
   regular kernel `k_I` on `sqrt(I) × sqrt(I)` after the `-2 delta` term is
   separated. The literal `Q delta(max(u/v,v/u))` expression is rejected as a
   function-kernel definition; see proof guard 067.
2. Before defining the kernel, replace the raw selected square by a genuine
   Q-root owner. The current `SelectedWeilSquareOwner` stores only `g* * g`,
   while M3A requires `Q(xi*xi*)`; its naive bridge is rejected by proof guard
   070. The replacement must retain compact support, smoothness, and finite
   Mellin constraints.

   Rejection-first update (2026-07-12): the natural candidate
   `g = (d/dx + 1/2) xi` survives the algebraic identity
   `(g* * g) = Q(xi* * xi)` after involution reverses the derivative. This is
   only a surviving candidate, not a proved owner: finite-node compatibility
   and the compact-domain convolution derivative theorem remain open. See
   proof record 071.

   Finite-node update (2026-07-12): this candidate also survives the Mellin
   gate. Under the repository's bilateral Laplace convention its multiplier
   is `1/2-s`; the only zero among `{0,1/2,1}` occurs at the already-zero
   target `s=1/2`, while the off-line detector node has nonzero multiplier and
   can be normalized by finite interpolation. The compact-domain derivative
   identity and source kernel action remain open. See proof record 072.
3. Fix one compact interval `I ⊂ (1/2,2)` and one logarithmic measure
   `d rho`; do not use an untyped `L2` carrier or change the source measure.
4. Prove measurability of `k_I` and an explicit integrable majorant for
   `‖k_I u v‖^2`.
5. Define the integral kernel action on the concrete `L2` space and prove it
   agrees with the source remainder operator on a dense compact-test core.
6. Use the square-integrable kernel result to obtain Hilbert-Schmidt, hence
   compact, status for `K_I`; retain real symmetry only as a separate lemma.
7. Prove the source quadratic-form identity
   `D_infinity o Q = inner xi (-2 Id + K_I) xi` for the same `xi`.
8. Instantiate `CompactBadSpace.exists_finiteDimensional_remainder_nonpositive`
   with threshold `2` and audit the resulting control space.
9. Only after steps 1-8 pass, expose the M3A owner to M5C; do not change route
   consumers or retire roots during this lane.

The generic compact-kernel pattern is source-backed by Connes--van Suijlekom,
arXiv:2511.23257, Theorem 3.1. That theorem is not an instantiation of M3A:
the CC20 `Q delta` contains the singular `-2 delta` term, so the regular-kernel
subtraction and same-object action identity remain mandatory.

Diagonal death test (2026-07-12): passed. The regular side has finite limit

```text
8 pi^2/9 + Si(4 pi)/(4 pi) - 1/2
```

at `rho=1+`; see proof verdict 068. Thus the next rejection-first target is
the exact kernel-action and M0 same-object normalization, not a diagonal
square-integrability obstruction. The bridge audit is recorded in proof
certificate 069; no symbols-only transport is accepted.

Lane exit gate:

```text
k_I is an actual source expression, not an owner field
kernel action is proved on the selected xi space
K_I is compact by the proved square-integrable kernel
the -2 coefficient and source remainder sign are unchanged
M4 receives the same operator and same xi
```

### Phase 4. Build a source Yoshida detector

M5A already gives finite-node interpolation and vanishing of all `n >= 2`
terms. Prove M5B with a genuine convolution square, the Appendix C tail bound,
and the source zero-sum sign. Then prove M5C by adding the finite bad-space
conditions from M3A/M4.

This phase decides the Connes-Weil route:

```text
M5B and M5C proved -> proceed to the archimedean global contradiction
M5B false          -> reject the fixed-window source-detector route
M5B RH-equivalent before analytic reduction
                   -> reject it as a lower producer
M5C false          -> reject finite conditioning and classify the failure
```

### 3.2 Status semantics for the active lane

The top-level status `rejected as an executable RH route` refers to the
current fixed-window Yoshida/M5B assembly, whose detector and global tail
quantifiers are not proved. It does **not** mean that the M3A archimedean
remainder theorem has a counterexample. M3A remains an unproved primary
producer, with milestone `U5A = pending`; the numbered `3.1` lane is an
explicit attempt to prove or reject that theorem from the source `Q delta`
decomposition. No unconditional RH claim or route rewiring is authorized
until M3A, M5B, M5C, and M6 pass independently.

Only after a named failure here may Phase 4B activate M3B, the general
finite-`S` fallback.

### Phase 5. Prove the global theorem

Prove M6 without `SourceRH`, RH, no-off-line-zero, Proposition C.1, detector
coverage, or a hidden calibration provider as an input.

Only this phase may turn the analytic owner into the final detector criterion.

### Phase 6. Retire old route contracts

Replace the old trace/remainder consumers with the corrected owner. Remove:

```text
normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot
normalizedCoreS2B1TracePackageRemaindersRoot
NormalizedSelectedSourceCoreTraceQWLambdaCalibrationProvider
```

Delete or demote the old equality records whose semantics require a zero
remainder.

### Phase 7. Retire RH-equivalent outlets

After M6 exists, derive the compatibility views and remove:

```text
normalizedCoreCC20PropositionC1SourceCriterionRoot
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
```

The M6 theorem must be the producer. An equivalence theorem cannot manufacture
its own forward direction.

### Phase 8. Final audit

Run the full closed-theorem gate and repository verification. This phase
absorbs the proposed plan 015.

## 8. Root Retirement Order

```text
+-------+------------------------------------------------------------+
| order | retirement condition                                       |
+-------+------------------------------------------------------------+
| 1     | selected CCM25 owner rewires both 013 consumers             |
| 2     | corrected trace owner replaces both S2-B1 root consumers    |
| 3     | old calibration provider disappears from the theorem type   |
| 4     | M6 replaces the two RH-equivalent roots                      |
| 5     | final signature and axiom graph contain no project boundary  |
+-------+------------------------------------------------------------+
```

Removing a root declaration before its consumer changes does not count.

## 9. Rejection Guards

Reject a candidate if it:

```text
assumes RH, SourceRH, or no-off-line-zero
stores detector coverage or Proposition C.1
restores supportSquareTrace = qwLambda without D_S
sets D_S, rank, pole, or Cdef terms to zero by construction
uses eta_S as a unitary projection transport
uses a selected test theorem as all-test coverage
uses the rejected SourceWeilFormData owner
uses a package equality to cast dependent data from another owner
constructs the hidden provider from the provider itself
proves only an axiom-clean weak model
```

## 10. Verification

All Lean commands run in the WSL ext4 verification mirror under the repository
lock.

Per-phase minimum:

```text
smallest owning module build
import-facing #check and #print
focused #print axioms
shortcut scan
git diff --check on Windows
```

Final commands include:

```lean
#check @unconditional_rh_skeleton
#print unconditional_rh_skeleton
#print axioms unconditional_rh_skeleton
```

Required final type:

```text
unconditional_rh_skeleton : RiemannHypothesis
```

Required final axiom output:

```text
no project roots
no sorryAx
Mathlib foundations only
```

Run the full repository build only after the local final audit passes.

## 11. Milestones

```text
+------+-----------------------------------------------------------+----------+
| ID   | result                                                    | status   |
+------+-----------------------------------------------------------+----------+
| U0   | six-root and hidden-premise audit                         | complete |
| U1   | old exact no-defect trace target rejected                 | complete |
| U2   | corrected signed trace identity proved                    | complete |
| U3A  | selected CCM25 owner complete and import-facing audited   | complete |
| U3B  | selected route consumes owner and two roots are removed   | pending  |
| U4   | fixed-S positive trace theorem formalized                 | partial  |
| U5A  | archimedean compact remainder connected to M4             | pending  |
| U5B  | general finite-S remainder fallback                       | inactive |
| U6   | finite bad-space sign theorem proved                      | complete |
| U7A  | fixed-window finite-node interpolation and prime vanishing| complete |
| U7B  | additive/pole toy detector path rejected                  | complete |
| U7C  | source Yoshida tail estimate and strict zero-sum sign     | partial  |
| U7D  | finite-conditioned source detector theorem                | pending  |
| U8   | global Weil contradiction proved from analytic data       | pending  |
| U9   | all old roots and hidden provider removed                 | pending  |
| U10  | closed theorem and full audit pass                        | pending  |
+------+-----------------------------------------------------------+----------+
```

Latest rejection milestone (2026-07-12): the pole-free anti-maximum candidate
is formally closed as a lower route. `docs/proofs/064_polefree_antimax_rejection.md`
records the mathematical countermodel, and
`docs/proofs/065_polefree_antimax_counterexample_lean_guard.md` records its
axiom-clean Lean guard. No U4-U8 status changes: this rejection removes a
possible fallback but does not provide the missing M2/M3A/M5B producer.

`U4` is partial because the abstract ordinary-trace layer is implemented, but
the explicit commutator kernels have not yet supplied its Hilbert-Schmidt
summability witness and measurable L2 kernel.

The 2026-07-12 source audit found no newer primary source that supplies the
missing fixed-S quotient measure, complex `L2` carrier, cutoff realization, or
kernel majorant. See
`docs/proofs/066_fixed_s_kernel_latest_source_audit.md`. Do not replace this
missing owner with an arbitrary carrier or stored summability proposition.

## 12. Outcomes

### Complete

All U0-U10 milestones pass. The theorem has a closed type, no project axioms,
and no hidden provider.

### Partial

A lower owner or operator theorem compiles, but U5A, U7C, U7D, or U8 remains open.
Report RH as conditional.

### Rejected

Reject the fixed-window route when a proved counterexample defeats M5B or M5C.
Reject the full Connes-Weil route only if the fixed-window route fails and the
finite-`S` fallback is also proved false or circular.

### Blocked

Use `blocked` only after the same external mathematical gap survives three
work rounds and no in-scope proof or rejection path remains.

## 13. Document Policy

Keep all planning in this file until one of these events occurs:

```text
M0 receives a proved source identity
M3A or M3B receives a proof or counterexample
M5B or M5C receives a proof or counterexample
the route is rejected
```

At those events, add one proof certificate under `docs/proofs/`. Do not create
empty phase plans or theorem-contract files in advance. Update this document's
milestone table and dependency graph after each result.

The historical roles are:

```text
012  operator proof and no-defect counterexample evidence
013  selected CCM25 owner implementation evidence
014  RH-equivalence and hidden-provider audit evidence
015  absorbed into Phase 8; no separate plan required
016  current route registry; no executable lane remains
```

## 14. Reopening Order

```text
1. Produce a new non-circular same-test detector/source-sign theorem that is
   strictly lower than the CC20 RH exit and closes the radius/count cycle.
2. Re-audit its consumer chain before reopening any local operator producer.
3. Only then execute the numbered M3A regular-kernel analysis contract.
4. Apply M4 and add its finite bad-space equations to the proved detector.
5. Finish M2 only if that same detector consumes the semilocal positive trace.
6. Prove M6, then rewire consumers and retire roots in one coherent change.
7. Activate finite-S M3B only after a named rejection of a reopened
   archimedean path and a surviving lower consumer.
```

No current task may remove an RH-level root or claim unconditional RH before
M6 has a proof from lower analytic data.
