# MEMORY.md

Last compressed: 2026-07-10.

This file is the current recovery snapshot for the repository. Git history owns
the deleted lowering chronology. Add a new entry only after a route-level proof
state changes, a branch is rejected by a named theorem, or verification reveals
a reusable failure mode.

## Current Result

Result: the repository does not contain an unconditional proof of the Riemann
Hypothesis.

Plan 016 Contract M0 is complete at the trace-class interface. The proved
source-normalized identity is

```text
PositiveTrace_(S,Lambda_op)(g)
  = QW_lambda_qw(g,g)
      - Pole_lambda_qw(g)
      + D_(S,Lambda_op)(F_g).
```

Plans 016--023 are rejected as executable RH routes. No active plan currently
meets the guaranteed-route standard. The first rejected Nyman block route is
plan 020: its
finite Nyman--Mobius identities are valid, but its M4 bottom retains the full
inverse-Gram non-cancellation inequality and therefore has not lowered the
RH-producing statement to an independent arithmetic theorem. Plan 021's exact
local divisor-gradient cancellation also fails globally because its future
multiple propagation increases the weighted energy.

The compactness rejection guard is now formalized in
`ConnesWeilRH.Source.CC20Concrete.CompactBadSpace.not_compact_eq_smul_id`.
It proves that a compact operator on an infinite-dimensional complex normed
space cannot equal a nonzero scalar multiple of the identity. The focused
M2/M4 import audit prints only `propext`, `Classical.choice`, and `Quot.sound`.
This is the abstract polarization/compactness guard behind the CC20
`-2 Id + K_I` counterexample; it does not yet encode the concrete CC20
remainder operator or claim that all Connes routes are impossible.

The first 023 feasibility result repairs the rejected Yoshida assembly at the
only valid algebraic level. The theorem
`exists_residualWindow_correction_full_product_interpolation` constructs a
residual-window correction whose complete rescaled convolution product, not
merely its correction factor, has prescribed values on a finite node set. It
requires the rescaled base factor to be nonzero at those nodes. The source and
audit modules build with only `propext`, `Classical.choice`, and `Quot.sound`.
This removes neither the finite-node base-nonvanishing gate nor the coupled
nearby-radius/far-tail gate, so Plan 016 remains rejected and no RH consumer
has been rewired.

The first 017 gate is low-cluster selection, not the final Hurwitz bridge. The
known prolate mechanism creates approximately `2 * lambda^2` near-radical
modes. Therefore a small Rayleigh quotient or a vanishing residual without a
relative spectral gap does not identify the lowest eigenvector. Current source
evidence supplies Gram--Schmidt candidates and numerical/graphical agreement,
but no QW/prolate operator-norm, Riesz-projection, effective-matrix, or relative
gap theorem. The immediate experiment computes the exact first two even
prolate-derived QW matrix entries, bounds coupling to the rest of the growing
cluster, and compares all errors with the proposed first gap. Do not build 017
route wrappers before this gate passes.

The first R1 source audit is partial rather than rejected. For the normalized
`h_0,h_4` prolate combination with zero integral, the remaining point defect is
exactly proportional to `chi_0-chi_2`, while its out-of-band Fourier leakage
norm is an exact combination of `1-chi_0^2` and `1-chi_2^2`. The full Poisson
formula expresses the lower support tail through those two defects. See
`docs/proofs/017_qw_prolate_r1_first_verdict.md`. This creates a concrete
analytic producer candidate below the numerical agreement, but no QW
spectral-projection estimate has been proved.

Keep cluster selection separate from full-bottom ownership. A low prolate
Rayleigh value or a first-even effective matrix cannot exclude lower negative
QW directions. Full-bottom ownership alone does not imply RH: the source
explicitly says that the lowest spectral value need not be nonnegative.
Full-bottom ownership plus a nonnegative lowest eigenvalue along a cofinal
sequence would imply positivity for every compactly supported Weil test and
therefore contains the RH-level arithmetic breakthrough. Treat ownership and
sign as separate gates.

The second R1 audit is also partial. `QW_lambda` is an unbounded closed form,
not an `L2` tail norm, so the exact Fourier leakage norm cannot by itself bound
the proxy's Rayleigh value. A formal truncation identity would follow if
`g_lambda=E(h_lambda)` were a radical vector in a common global form domain,
but the published radical theorem assumes both `h(0)=0` and `integral h=0`.
The finite-`lambda` proxy has zero integral and a nonzero point defect. A new
extended-domain Mellin/explicit-formula theorem and a logarithmic graph-norm
tail bound are therefore required. Qualitative high-frequency coercivity from
the archimedean `log |t|` symbol gives compact resolvent for fixed `lambda`, but
does not control the growing low/intermediate complement uniformly. See
`docs/proofs/017_qw_prolate_tail_and_bottom_verdict.md`.

Plan 017 is rejected as a guaranteed executable route, not as a proof that the
Connes spectral strategy is impossible. The real-zero/Hurwitz implication is
valid, but the large-support even-simplicity condition reduces to an open,
critically tight Herglotz resolvent inequality whose margin is only the
minuscule even/odd ground gap. The Poisson `L2` defect and qualitative
coercivity do not control that relative gap. The required compact-open transfer
from the explicit proxy to the genuine ground state is itself RH-closing and
has no lower projection theorem. See
`docs/proofs/017_final_feasibility_verdict.md`. Do not implement R2--R5 under
017 without a new arithmetic near-resonance theorem.

Plan 018 was the next feasibility experiment. No route currently meets the
project's guaranteed-route standard. Its selected object was Suzuki's explicit
unconditional screw-norm defect
`Delta(t) = ||S_t||_2^2/(2*pi) + g(t)`. Its half-line vanishing is equivalent
to RH, so it is not yet a producer. The next admissible milestone is an exact
unconditional off-critical defect formula followed by a sign, evolution, or
uniqueness theorem that forces `Delta=0` without importing Weil positivity.

CC20 fixes the remainder sign as `+D`; CCM25 fixes the restricted form as
archimedean plus pole minus finite primes. The route's vanishing conditions
kill the pole. They do not kill `D`. The proof certificate is
`docs/proofs/016_corrected_trace_identity.md`.

`lambda_qw` and `Lambda_op` are different source parameters. The first bounds
the CCM25 support window and prime-power sum. The second defines the operator
cutoff projections. No checked source proves their equality.

Plan 012 has a source-level mathematical rejection. The direct fixed-S
commutator argument constructs the selected Hilbert-Schmidt operator and its
`L2` kernel, but the active no-defect consumer is false for the genuine CC20
model. The evidence is recorded in:

```text
docs/proofs/cc20-012-mathematical-verdict.md
```

CC20 Theorem `thmqkey1` gives

```text
D o Q(xi * xi^*) = inner(xi, (-2 Id + K_I) xi)
```

with `K_I` compact Hilbert-Schmidt. On the infinite-dimensional zero-integral
subspace this form cannot vanish identically. A compact smooth witness yields
a positive-definite test that vanishes at `0` and `+/- i/2` but has nonzero
trace remainder. Thus the current exact equality
`supportSquareTrace = qwLambda` cannot be produced from the source operator.
Both 012 roots remain active, and no Lean file was changed for this verdict.

The final target is:

```text
_root_.RiemannHypothesis
```

The current theorem is conditional in two independent ways. Its axiom graph
contains the six project roots below, and its full type contains an
unconstructed typeclass premise:

```text
unconditional_rh_skeleton :
  forall [NormalizedSelectedSourceCoreTraceQWLambdaCalibrationProvider],
    RiemannHypothesis
```

`#print axioms` alone does not reveal ordinary or typeclass premises. Final
audits must print both the complete theorem type and its axioms.

The theorem `unconditional_rh_skeleton` compiles, but its axiom graph still
contains six project roots:

```text
normalizedCoreCC20PropositionC1SourceCriterionRoot
normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot
normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot
normalizedCoreS2B1TracePackageRemaindersRoot
normalizedCoreSourceWeilFormDataRoot
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
```

The first and last roots are RH-level:

```text
normalizedCoreCC20PropositionC1SourceCriterionRoot
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
```

Closing the other four data roots cannot prove RH while either RH-level root
remains active.

## Current Dependency Map

```text
unconditional_rh_skeleton
  |
  +-- B2 scalar-calibration provider                 [implicit premise]
  |
  +-- CC20 Proposition C1 source criterion            [RH-level]
  |
  +-- CCM25 finite-prime arithmetic source data       [016 M1; historical 013]
  |
  +-- S2-B1 remainder rows outside no-bulk            [016 M0-M4; historical 012]
  |
  +-- S2-B1 trace-package remainders                  [016 M0-M4; historical 012]
  |
  +-- source Weil-form data                           [016 M1; historical 013]
  |
  +-- selected detector criterion coverage            [RH-level; 016 M5-M6]
```

Remaining work has one active entrypoint:

```text
016  unified remaining gaps
```

Plans 012-014 remain historical evidence. Plan 016 absorbs their unfinished
work and the proposed 015 audit. Its central theorem is conditioned Yoshida
detector existence for the finite bad remainder space.

## 011 Accepted Result

Plan:

```text
plan/011_2026-07-10_S2B1_matched_scalar_identification_plan.md
```

The false universal scalar family was rejected by a zero/bump counterexample,
and the old no-argument scalar root was removed. The matched B2 scalar now comes
from the same `SourceTraceReadOffData` object used by the route.

Named evidence:

```text
not_normalizedCoreS2B1ActualScalarIdentificationFamily
normalizedSeedQWLambdaScalarIdentificationOfNormalizedPackageTraceData
normalizedSeedQWLambdaScalarIdentification_nonempty_iff_supportSquareQWLambdaReadOffSourceData
normalizedRouteBackedCC20SquareRestrictedSupportSquareQWLambda_of_traceFrontComparisonSplitB2Rows
normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleRows_nonempty_iff_components
```

The B2 route projection is proved. The QW/pole route remains B3/RH-level and is
not a lower producer.

## Current Analytic Model Gap

Three definitional theorems expose the present model:

```text
normalizedCoreTraceAmplitude_eq_encodedEvaluationNorm
normalizedCoreConvolutionStar_eq_add
normalizedCoreHilbertSchmidtGate_iff_traceClass_cyclicLegal
```

Their content is:

```text
trace amplitude = norm of the encoded test at zero
convolution      = pointwise addition
HS gate          = traceClass and cyclicLegal
```

This model has no concrete integral operator, Schwartz kernel, Hilbert-Schmidt
norm, trace-class positive square, or ordinary infinite-dimensional trace.
`SourceCanonicalHilbertModelData` supplies a Hilbert carrier and coordinate
equivalence only. `SourceScalingActionData` supplies continuous linear scaling
maps and group laws only.

Mathlib v4.30.0 contains finite-dimensional trace results in:

```text
Mathlib/Analysis/InnerProductSpace/Trace.lean
```

The repository search found no reusable infinite-dimensional
`HilbertSchmidtOperator`, `IsHilbertSchmidt`, or `TraceClass` framework. The
historical 012 design therefore selected a project-local measurable kernel
layer. Plan 016 Contract M2 retains that choice for the valid positive-trace
theorem. The layer uses an explicit nuclear decomposition to define ordinary
trace, proves agreement with every countable orthonormal-basis diagonal series,
and then proves equality with the kernel norm-square integral for the selected
positive square.

## 012 Ownership Correction

The first review of the historical plan 012 found a circular input boundary.
The existing
`SourceTraceReadOffData` already stores:

```text
hilbertSchmidtGate
positiveTraceNonnegative
fullTraceReadOffBridge
restrictedTraceReadOffBridge
```

It cannot produce the operator, Hilbert-Schmidt witness, ordinary trace, or
read-off theorem that those fields represent. Plan 012 therefore started from a
`SourceCC20PreTraceInputData` owner containing only route/test identity,
fixed-S/window/cutoff data, coordinate rows, and admissibility. The completed
analytic owner was meant to construct `SourceTraceReadOffData` downstream.
The later no-defect counterexample rejected that final projection. Plan 016
replaces it with a corrected owner that retains the source remainder `D_S`.

The same review established four additional gates:

```text
P and P_hat must be self-adjoint idempotents
theta(g*) must be the adjoint and represent the convolution square
ordinary trace must be independent of the kernel-mass definition
the complex ordinary trace must equal the real A* A kernel mass explicitly
remainder scalars must unfold to evaluations, defect operators, or strip data
```

One bounded factor and one Hilbert-Schmidt factor produce a Hilbert-Schmidt
product, not a trace-class product. Each cyclic trace move must use either two
Hilbert-Schmidt factors or a trace-class/bounded pair.

The historical execution-readiness review split the former circular Phase 0
into two gates:

```text
Phase 0A  source certificates for the fixed-S kernel and remainder transport
Phase 0B  generic L2 operator and nuclear-trace foundations
Phase 1   exact selected operator and kernel
Phase 2   fixed-S estimate for that kernel and Hilbert-Schmidt construction
```

The first source-only audit selected Fork B/F/H. A later direct mathematical
derivation superseded that feasibility judgment:

```text
K_S-invariant scattering coordinate     available
commutator Hilbert-Schmidt estimate      proved
L2 kernel representation                 proved
exact no-defect trace read-off            false
```

The evidence is recorded in:

```text
docs/proofs/cc20-fixed-s-kernel-source-certificate.md
docs/proofs/cc20-fixed-s-remainder-source-certificate.md
```

The direct proof uses CCM24's unitary scattering coordinate rather than the
nonunitary map `eta_S`. It writes the compressed operator as a sum of two
cross-half-line commutators. Their weighted `L2` kernel norms prove the
Hilbert-Schmidt property and give the ordinary positive trace.

The current consumer still cannot use that operator. CC20 Theorem `thmqkey1`
shows that its omitted remainder equals the quadratic form of `-2 Id + K_I`,
where `K_I` is compact Hilbert-Schmidt. That form does not vanish on the full
triple-vanishing test class. Plan 012 is rejected rather than blocked.

The 2026-07-10 WSL ext4 verification built
`ConnesWeilRH.Dev.UnconditionalSkeleton`. The first attempt replayed a stale
`ObjectTheoremBasePackage` import artifact and could not see its new constructor
input. Rebuilding that owning module repaired the cache, and the Dev target then
passed. An import-facing scratch audit printed these project roots for
`unconditional_rh_skeleton`:

```text
normalizedCoreCC20PropositionC1SourceCriterionRoot
normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot
normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot
normalizedCoreS2B1TracePackageRemaindersRoot
normalizedCoreSourceWeilFormDataRoot
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
```

The focused output contained the Mathlib foundations `propext`,
`Classical.choice`, and `Quot.sound`, plus those six project roots. It contained
no `sorryAx`. Both 012 roots remain active after a fresh import-facing build.

The repository's first Lean API bottom is
`SourceCC20FixedSQuotientMeasureCoordinate`. `RouteInputs.ccm24` exposes the
canonical model, scaling action, Fourier grading, and comparison maps only as
Props. `SourceCanonicalHilbertModelData` supplies an arbitrary real Hilbert
carrier without a measure or complex `L2` realization. Mathlib has an adele-ring
type but no repository-visible `X_S=A_S/O_S^*` quotient measure, semilocal
Fourier `L2` operator, or cutoff projections.

The project-local trace contract now uses an explicit countable nuclear
decomposition. `SourceCC20OrdinaryTrace` is the absolutely summable nuclear
series; basis-series equality supplies basis and decomposition independence.
The fixed-S estimate is proved only after Phase 1 constructs the exact
`operatorKernel`, removing the old Phase 0/Phase 1 dependency cycle.
`SourceCC20KernelCoordinateData` belongs to the pure
`Source/CC20KernelCoordinate.lean` module so Phase 0B trace foundations do not
depend on the Phase 1 operator module.

## Active Mathematical Boundaries

### CC20 trace boundary

The source paper uses the positive compressed scaling trace on
`L^2(R)^ev`:

```text
Tr(theta(g) S theta(g)*)
```

The project manuscript uses the fixed-S operator:

```text
A_(S,Lambda_op,g)
  = P_hat_(S,G)(Lambda_op) P_(S,G)(Lambda_op) theta_S(g)

PositiveTrace = Tr(A* A)
```

Plan 016 must keep the route test `g`, convolution square, operator, kernel,
Hilbert-Schmidt norm, positive trace, `QW_lambda_qw`, pole pairing, and nonzero
remainder `D_(S,Lambda_op)` on one data-bearing owner. It must keep
`lambda_qw` separate from `Lambda_op` and forbids the old no-defect projection.

### CCM25 finite-prime boundary

The current canonical source-data route must preserve one concrete owner across
source-Weil-form data, visible arithmetic, canonical atoms, package certificate
data, and direct term masses. Equality of `WeilFormSymbols` alone cannot
transport data whose type depends on the full owner.

Plan 013 owns:

```text
normalizedCoreSourceWeilFormDataRoot
normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot
```

Do not reopen support/visible wrappers, package read-off wrappers, evaluator
mass spellings, or route-symbol mass spellings as lower roots unless a named
Lean theorem rejects the canonical owner path.

Plan 013 Phase 0A produced that rejection for the current owner type. The
theorem

```text
CCM25SourceDataGuards.not_nonempty_concreteSourceWeilFormData
```

is axiom-free apart from `propext`, `Classical.choice`, and `Quot.sound`. It
uses a compact smooth bump with value `1` at `2`: the old global support
quantifier forces its finite-prime term at `2` to be zero, while the concrete
evaluator and `vonMangoldt(2) = log(2) > 0` make the same term positive. Thus
`normalizedCoreSourceWeilFormDataRoot` is an inconsistent root, not an
unfinished constructor target.

The replacement source bottom now compiles in three modules:

```text
CompactLogConvolution
  genuine f*(x) = star(f(-x)) and additive integral convolution

SelectedWeilSquare
  one compact test, its definitional square, support radius, exact finite
  global/restricted prime-power sets, and complex phase-preserving values

SelectedWeilFormula
  pole, archimedean, global-prime, and restricted-prime definitions on the
  same square owner
```

The remaining selected-CCM25 bottom in plan 016 Contract M1 is a proof that the
explicit archimedean integrand is integrable on `(0, infinity)`. The two roots
inherited from 013 remain active; no route consumer has been rewired yet.

### B3 and detector boundary

Detector-only coverage, QW/pole collapse, global mass cancellation, and the
selected final detector criterion have named equivalence guards at the
no-off-line-zero or RH level. They cannot close plan 016 from below.

Plan 016 Contracts M3-M6 must prove or reject the semilocal remainder normal
form, finite bad-space sign, conditioned detector, and global contradiction.
The RH-level detector outlet cannot serve as an input to those contracts.

The 2026-07-10 root audit proved the exact guards:

```text
normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_standardSourceRH
normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_mathlibRH
```

Their focused axiom output contains only `propext`, `Classical.choice`, and
`Quot.sound`. CC20 Proposition C.1 states the same global Weil-positivity/RH
equivalence. CCM25, the 2026 screw-function work, and the finite Guinand-Weil
dictionary do not supply the missing global positivity theorem. Plan 016 owns
the duplicate C1 root, hidden provider, and final detector root; the historical
014 audit supplies the rejection guards.

## 013 Windows Port

The selected CCM25 foundation from commit `07f946c` was ported file by file
into the Windows source of truth. Five new files match the remote blobs exactly;
the two existing files received only the reviewed import and guard additions.

The Windows snapshot passed these WSL ext4 targets:

```text
CompactLogConvolution
SelectedWeilSquare
SelectedWeilFormula
SelectedArchimedeanIntegrability
CCM25Concrete
CCM25SourceDataGuards
UnconditionalSkeleton
```

Both source-data rejection guards depend only on Mathlib foundations. The RH
skeleton still contains the same six project roots and the hidden provider.

## Rejected Shortcuts

Do not count any of these as proof progress:

```text
True or Set.univ producer fields
an arbitrary positiveTrace scalar
traceClass : Prop with no named operator
cyclicLegal : Prop with no per-move witnesses
stored Mellin or determinant rows
selected-test read-off presented as all-test coverage
SourceRH or no-off-line source-zero used as a producer
detector-only calibration used as 08A closure
equality of route symbols used to cast dependent canonical-owner data
moving between equivalent mass/package spellings
```

The accepted direction is data-bearing ownership followed by projection into
legacy route records.

## Lean Rules Worth Remembering

### Row-record destructuring

For an existential plus a conjunction whose final item is a structure, split
the outer pair before extracting the structure:

```lean
rcases h with ⟨r, hmatch⟩
have hr := hmatch.1
have rows := hmatch.2
```

A flat `rcases h with ⟨r, hr, rows⟩` can recursively destruct the final record.

### Type versus Prop

A data-bearing structure lives in `Type`. Use:

```text
P and Nonempty Rows
```

when only existence is needed, or use a Sigma/data structure when later code
must retain the witness. Do not write a `Type` record directly as a conjunct of
a proposition.

### Dependent owner transport

`owner.sameSymbols : routeSymbols = ownerSymbols` does not transport
certificate data that depends on the entire owner. Use a theorem that states
the required equality or `HEq` for every dependent component. Keep unproved
transport experiments outside compiled route APIs.

### Constructor names

When an inductive constructor has a mathematical name such as `rho`, use a
different local parameter name and write `.rho` at call sites.

### Import artifacts

Direct `lake env lean File.lean` can pass while imported `.olean` artifacts are
stale. Accepted verification requires an importing scratch file with `#check`
and `#print axioms`. If the import misses a new declaration after the smallest
build, remove only that module's stale artifacts and rebuild that target.

## Verification State

The unified 011 verification passed:

```text
WSL ext4 build targets: 5/5 passed
import-facing #check: passed
focused #print axioms: passed
sorryAx: absent from audited declarations
removed universal scalar root: absent
```

This verification applies to the current dirty Lean changes listed below. The
documentation compression and plan 016 do not change Lean, so they do not need
a new Lake build.

## Worktree State At Compression

The Windows repository is the sole source of truth. All source and document
edits, Git status decisions, commits, and pushes must happen there. WSL ext4
directories are disposable verification mirrors populated one way from the
Windows snapshot; WSL diffs and commits are not accepted project state.

As of 2026-07-10, Windows `main` is `c59e955` and `origin/main` is `07f946c`.
After fetching, `git rev-list --left-right --count HEAD...origin/main` reports
`6 179`. Do not resolve this divergence from WSL and do not overwrite Windows
with the remote branch. Any later reconciliation must preserve Windows as the
authority and inspect both histories before changing refs.

Completed 011 lane changes:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean
ConnesWeilRH/Route/CC20RouteRealization.lean
ConnesWeilRH/Route/TraceFrontEnd.lean
ConnesWeilRH/Source/ObjectTheoremBasePackage.lean
ConnesWeilRH/Source/S2B1TraceScale.lean
```

Pre-existing user changes must be preserved:

```text
ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceDataBridge.lean
ConnesWeilRH/Source/CCM25Concrete/PrimePowerArithmetic.lean
```

Never reset, overwrite, or clean these paths as part of another lane.

## Verification Workflow

Edit and manage Git only in the Windows repository. Sync its source snapshot
one way into WSL2 on ext4 for Lean verification. Never run Lake with Windows
Lean or from `/mnt/c`, and never commit or push from a WSL verification mirror.

Preferred persistent mirror:

```text
/home/peter/verify/Connes-Weil-RH-Proof
```

Before reuse, run `git rev-parse --show-toplevel`. If it does not return the
project mirror itself, create a fresh ext4 verification directory, seed its
`.lake` from the persistent cache, and copy sources while excluding `.git` and
`.lake`.

All Lake commands use:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build <smallest-target>
```

Verification order:

```text
direct Lean check while editing
smallest owning module build
import-facing #check
focused #print axioms
route/Dev build only at a milestone
shortcut scan
git diff --check
```

## Public Hygiene

Before any commit or push, inspect staged file names and staged content. Root
workflow files are private unless the repository explicitly owns them as public
artifacts.

Do not publish local absolute paths, verification directory names, private
workflow artifacts, JSON escape fragments, or mojibake in GitHub text. Read
back every public body or comment after posting.

## Next Frontier

Execute:

```text
plan/016_2026-07-10_unified_remaining_gaps_plan.md
```

## 2026-07-10 Yoshida Model Rejection

The normalized CC20 detector path is rejected as a source producer. Its
concrete operations are pointwise addition and negative pole pairing:

```text
convolutionStar f g = f + g
weilLocalSum g = -polePairing g
```

`not_normalizedCC20MellinConvolutionLaw` gives an axiom-free guard. A
fixed-window interpolant has Mellin value `1`; the normalized square has value
`2`, while a genuine convolution law gives `1`.

CC20 Appendix C, `weil-compo.tex:2075-2085`, requires a separate global
Yoshida approximation bound over every other nontrivial zero. The completed
M5A theorem only solves finite-node interpolation and selected finite-prime
vanishing. Plan 016 now labels the old additive/pole detector path U7B as
rejected and makes the genuine source convolution, zero-sum, and tail estimate
the M5B bottom. See `docs/proofs/016_yoshida_model_verdict.md`.

The Windows snapshot passed WSL builds for `CC20ConcreteTestSpace`,
`CC20YoshidaConstruction`, the Yoshida model audit, `UnconditionalSkeleton`,
and the current route audit. Reused `.lake` artifacts first replayed an
incompatible `ObjectTheoremBasePackage`; deleting only that module's artifacts
and rebuilding it repaired the verification copy. The final audit still shows
the calibration-provider instance premise and all six project roots. It shows
no `sorryAx`.

The next M5B layer now compiles in `CC20YoshidaTail.lean`. It turns a test
supported in a positive interval into a compactly supported log-slice and
identifies its Mellin transform with the Fourier transform of that slice.
`exists_uniform_mellin_vertical_quadratic_decay` proves one quadratic-decay
constant for every `sigma in [0,1]`. The proof bounds the first three vertical
derivative integrals across the common compact support and applies Mathlib's
Fourier derivative estimate. The import-facing audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

The nearby interpolation layer now compiles in `CC20YoshidaNearZeros.lean`.
Mathlib's compact-zero theorem proves that source nontrivial zeros in any
closed ball form a finite set. `fixed_window_finite_mellin_surjective` realizes
arbitrary Mellin values on any finite complex node set inside the same fixed
positive support window, and `fixed_window_nearby_zero_mellin_surjective`
applies it to nearby zeros together with extra route nodes. The import-facing
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

M5B remains partial. Appendix C still needs a normalized family with an
arbitrarily small uniform tail coefficient and the strict sign for the genuine
source zero sum. Finite interpolation now supplies the exact nearby values; it
does not make the far-tail constant small.

The original Yoshida mechanism is now fixed by primary-source evidence.
Yoshida 1992, Lemma 1, pp. 285-286 constructs

```text
alpha = alpha_1 * ... * alpha_M * alpha_0^( * N)
Phi(s) = Phi_0(s)^N * product_i Phi_i(s).
```

The finite correction factors kill the nearby zeros. A sufficiently large
convolution power makes the far-zero coefficient small. The new
`CC20YoshidaConvolution.lean` uses the genuine existing compact log convolution
and proves `laplaceAt_convolution`, the `(N+1)`-power formula, and the matching
support-growth formula. The remaining M5B bottom must connect the positive
variable Mellin interpolation and uniform tail bound to this log-coordinate
Laplace transform, choose factor windows whose summed support stays in M5A,
and complete the quantitative epsilon estimate.

The 2026-07-11 bridge milestone closes the first two analytic interfaces in
that last sentence. `laplaceAt_compactLogTestOfWindow_eq_mellin` identifies the
M5A positive-variable transform with the genuine compact-log Laplace transform,
and `exists_uniform_laplaceAt_vertical_quadratic_decay` transfers the uniform
quadratic strip bound to that same API. The convolution module now also proves
that a uniform source factor bound `norm(laplaceAt f s) <= q < 1` produces an
arbitrarily small uniform bound after a nonempty convolution iterate, including
one bounded finite correction factor. Its accompanying support theorem records
the exact extra log-window cost. This is an axiom-clean analytic engine, not a
construction of the required source factor or a proof of the strict source
zero-sum sign; M5B remains partial.

The next 2026-07-11 lemmas remove the missing far-height contraction and
convolution-power support premises:
`exists_uniform_laplaceAt_vertical_half_contraction` derives a height threshold
from the uniform quadratic estimate and proves norm at most `1/2` for every
real part in `[0,1]` outside that region. Thus any fixed-window base factor
already has the source-required far-zero contraction. The normalized rescaling
`r^-1 f(x/r)` has transform `Phi(r s)`. With `r=1/(N+1)`, its `N+1`-fold
convolution has the original base support rather than an `N+1`-times larger
support. The assembled theorem then adds one finite correction factor and
checks its residual window against any prescribed outer window. The focused
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

For any `L < 0 < U` and arbitrary values on any finite complex node set,
`exists_residualWindow_correction_with_quadratic_decay` constructs one
`CompactLogTest` supported in `(L,U)`, proves all requested Laplace values, and
retains one uniform quadratic-decay constant for that same correction. Its
nearby-zero specialization uses the union of the source closed-ball zero set
and the route nodes. The import-facing audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. The remaining bottom starts at the
source shell-card estimate and the spectral explicit formula; finite correction
existence is no longer open.

The assembled far-strip bound is now complete. The base contraction is applied
after the exact `1/(N+1)` rescaling, the same correction supplies its quadratic
strip constant, and multiplication gives an explicit
`(1/2)^(N+1) * C` vertical bound. A geometric lemma converts this into
`norm(z-rho)^2 * norm(Phi(z)) <= (6*pi)^2 * (1/2)^(N+1) * C` for sufficiently
high closed-strip points. The final existential theorem chooses `N` for any
positive `epsilon` and retains the same correction, finite interpolation
values, and assembled test. The import-facing audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

This closes the analytic same-index far-strip majorant. M5B now bottoms at the
source shell-card/Riemann--von Mangoldt estimate for strip zeros and the
spectral explicit formula plus strict sign for the same assembled
`CompactLogTest`.

The 2026-07-11 M5B owner audit rejects the old CC20 detector API as a source
producer. `YoshidaDetector.weilSumPositiveIfOffLine` stores the desired strict
Weil-sum sign as a structure field. The generic theorem following it merely
consumes detector existence and the finite-vanishing criterion to derive the
RH-level exit. The genuine `CompactLogTest` convolution and selected CCM25
formula owner must therefore receive a new absolute zero-sum definition,
convergence theorem, and strict-sign proof; no projection through
`YoshidaDetector` or `CC20YoshidaDetectorExists` is permitted.

The 2026-07-11 primary-source audit corrects the proposed M5B interface.
CC20 Appendix C (`arXiv:2006.13771`, `weil-compo.tex:2075-2085`) states the
geometric explicit-formula inequality as RH-equivalent and gives the required
Mellin tail construction; it does not define a free-standing source zero-sum
whose strict sign can be imported. The current
`SelectedWeilFormulaOwner.weilValue` likewise contains only the pole,
archimedean, and finite-prime geometric terms. No theorem equates it to a
spectral sum over zeta zeros. The next honest M5B bottom is a full spectral-side
explicit-formula theorem for the same `CompactLogTest`, including convergence.
Do not add a `tsum` or a strict-sign field without that theorem.

The first spectral-index prerequisite now compiles. The project defines one
global `sourceNontrivialZeroSet`, proves that it is contained in Mathlib's
`riemannZetaZeros`, and proves it countable from zeta-zero discreteness plus the
second-countability of the complex plane. Nearby-zero finiteness now uses that
same global set. The import-facing audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. This licenses a future `tsum` index; it
does not prove summability or the spectral explicit formula.

Mathlib does not contain a Riemann-von Mangoldt zero-counting estimate or a
summability theorem for the majorant
`rho |-> 1 / norm (rho - rho0)^2`. Countability and discreteness alone cannot
prove this series converges: a discrete subset of the complex plane may have
arbitrarily fast radial growth. Do not derive spectral convergence from
`sourceNontrivialZeroSet_countable` alone.

The dyadic summability consumer now compiles in
`CC20YoshidaNearZeros.lean`. It defines the least strict dyadic shell around a
candidate zero, proves the shells partition `sourceNontrivialZeroSet`, and
proves every shell finite by inclusion in a closed ball. The generic theorem
`summable_of_dyadic_shell_card_bound` and its source-zero specialization accept

```text
shellCard(n) <= K * (n + 1) * 2^n
term(z)      <= B / (2^n)^2
```

and produce `Summable`. The factor `(n + 1)` is required: Riemann-von
Mangoldt has `O(R log R)` growth, which becomes `O((n + 1) * 2^n)` on dyadic
radii. The near-zero audit built 3458/3458 jobs and reports only `propext`,
`Classical.choice`, and `Quot.sound`. M5B still lacks the source counting
theorem, the same-index Yoshida majorant, and the spectral explicit formula.

The first attempt to connect an external zero count exposed a source-index
mismatch. Hasanalizade--Shen--Wong, Corollary 1.2,
https://arxiv.org/abs/2107.06506, counts zeros with
`0 < Re rho < 1` and `0 < Im rho <= T`, while `MathlibNontrivialZero` has no
strip field. Two axiom-clean theorems now resolve this without changing that
public record. `sourceNontrivialZero_re_lt_one` proves the right strip bound.
`sourceNontrivialZero_zero_lt_re_or_eq_neg_nat` proves that every source zero
either has positive real part or is an explicit negative integer. The proof
uses `riemannZeta_one_sub` and `riemannZeta_ne_zero_of_one_le_re`. The near-zero
audit built 3458/3458 jobs and reports only `propext`, `Classical.choice`, and
`Quot.sound`.

The next axiom-clean refinement proves that the apparent negative-integer
branch is empty. `riemannZeta_neg_two_mul_nat_add_one_ne_zero` rules out negative
odd integers by the zeta functional equation, while
`sourceNontrivialZero_not_eq_neg_nat` combines that theorem with the stored
exclusion of negative even trivial zeros and `riemannZeta_zero`. Therefore
`sourceNontrivialZero_zero_lt_re` places every source spectral index in
`0 < Re rho < 1`. The import-facing audit built 3458/3458 jobs and reports only
`propext`, `Classical.choice`, and `Quot.sound`. The remaining counting bottom
is solely the strip Riemann--von Mangoldt/dyadic shell-card theorem.

The source-counting consumer is now aligned with the primary-source counting
index. Hasanalizade--Shen--Wong, arXiv:2107.06506, p. 3, defines the symmetric
count `N-bar(T)` by `0 < Re rho < 1` and `|Im rho| <= T`. The Lean set
`sourceNontrivialZerosInSymmetricHeight` has exactly that shape after the open
strip theorem. It is finite, and every dyadic shell centered at an arbitrary
selected zero `rho` embeds into the symmetric height window
`|Im rho| + 2^(n+1)`. The theorem
`sourceNontrivialZero_summable_of_symmetricHeight_dyadic_bounds` now consumes a
dyadic bound for that source count directly. The import-facing audit built
3458/3458 jobs and reports only `propext`, `Classical.choice`, and `Quot.sound`.
The remaining source-counting bottom is the Riemann--von Mangoldt bound itself,
not an index-transport or shell-geometry lemma.

The counting consumer is reduced further. Any global bound
`N-bar(T) <= A*T*log(T) + C*T` for `T >= 1`, with nonnegative `A,C`, produces
the exact arbitrary-center dyadic bound required by spectral summability.
`sourceNontrivialZerosInSymmetricHeight_dyadic_bound_of_linear_log_bound`
constructs the center-dependent constant, and
`sourceNontrivialZero_summable_of_linear_log_count_bound` connects it directly
to the consumer. The import-facing audit built 3458/3458 jobs and reports only
`propext`, `Classical.choice`, and `Quot.sound`.

The first Jensen counting layer now compiles in `CC20ZetaCounting.lean`.
`completedRiemannXi` is entire and equals
`s*(s-1)*completedRiemannZeta(s)` away from `0,1`; every source nontrivial zero
is a zero of the same xi. The proof anchors xi as nonzero at `s=2`, excludes
infinite analytic order, injects distinct source zeros into the xi divisor
support, and applies Mathlib's Jensen inequality. The remaining counting bottom
is an explicit circle growth bound for xi. The import-facing audit built
3492/3492 jobs and reports only `propext`, `Classical.choice`, and `Quot.sound`.

The symmetric-height geometry is also connected directly to Jensen. Every
source zero with `|Im z| <= T` lies in the closed ball centered at `2` with
radius `T+2`, using the proved open-strip bounds. Consequently
`sourceNontrivialZerosInSymmetricHeight_ncard_le_of_xi_sphere_bound` turns one
xi sphere bound around `2` into a bound for `N-bar(T)` without another source
index premise. The refreshed import audit remains 3492/3492 with only the three
Mathlib foundations.

The Jensen denominator is now normalized as well.
`sourceNontrivialZerosInSymmetricHeight_ncard_le_of_xi_exp_sphere_bound`
uses the outer circle of radius `2*(T+2)`. A bound `norm(xi z) <= exp(G)` on
that circle gives

```text
N-bar(T) <= (G - log(norm(xi 2))) / log(2).
```

The remaining analytic input is a nonnegative log-norm majorant `G(T)` of
linear-log size. The import-facing audit remains 3492/3492 with only `propext`,
`Classical.choice`, and `Quot.sound`.

Contracts M0 and the lower-owner part of M1 are complete. M1 now has a genuine
Hermitian convolution square, real pole/archimedean/finite-prime values, full
`Ioi 0` integrability, exact global and restricted sums, and an exact omitted
prime-power discrepancy. `SelectedWeilFormulaOwner.ofSquare` has no external
analytic premise.

The import-facing M1 audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. The two old CCM25 roots remain active because their all-test
consumer chain has 129 references and starts from the proved-uninhabited
`SourceWeilFormData`. Do not cast the selected owner back into that API. Build
M2, prove or reject M3 and M5, then switch the selected route and retire those
roots coherently.

The project-local positive-trace bottom now defines ordinary trace as a Hilbert
basis diagonal series and proves from Hilbert-Schmidt summability that
`Tr(A* A)` is real, nonnegative, and equal to the norm square. M2 remains
partial until the explicit fixed-S commutator kernels construct the required
summability witness and L2 kernel.

Contract M4's abstract theorem is complete. Compactness gives a finite net of
the image of the unit ball; the span of its centers is finite-dimensional, and
on its orthogonal complement the quadratic form of `K - c Id` is nonpositive.
This avoids implementing a spectral projection and uses no stored sign field.
The M2/M4 import audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

Primary-source research through 2026-07-10 found no finite-S theorem supplying
M3. CCM24 defers the general-S Jacobi coefficients to a forthcoming paper and
describes the Sonin/negative-spectrum match only up to a possible
finite-dimensional discrepancy. Connes's 2026 survey still lists the relevant
semilocal convergence and simplicity properties as remaining steps. M3 must be
derived directly or rejected; it cannot be imported from those sources.

Plan 016 makes the fixed-window archimedean route primary. Contract M5A is now
complete. Finite exponential-polynomial separation holds inside every fixed
positive window containing `1`; the chosen window is `(3/4,5/4)`. The actual
CCM25 convolution support is contained in the log-coordinate difference
interval, whose width is proved smaller than `log 2`, so every selected
finite-prime term at `n >= 2` vanishes. The M5A import-facing audit built
2963/2963 jobs and reports only `propext`, `Classical.choice`, and `Quot.sound`.

M5C cannot start from the abstract M4 theorem alone. The repository still has
no concrete archimedean `L2(sqrt I, d*rho)` space, source-test-to-`xi` map, or
integral operator `K_I` connecting the fixed-window test to M4. CC20 Theorem
`thmqkey1` (arXiv:2006.13771, `weil-compo.tex:765-808`) states the exact
remainder identity with `-2 Id + K_I` and proves compactness from an explicit
square-integrable symmetric kernel. The next gate is M3A: formalize those
objects and apply M4 at threshold `2`. Adding orthogonality as an owner field
would store the desired conclusion and remains forbidden. General finite-S M3
is an inactive fallback, not a route prerequisite.

Research checkpoint, not an accepted dependency move: CC20 Corollary
`qeasy` (arXiv:2006.13771, `weil-compo.tex:831-842`) proves directly that
`D o Q <= 0` for positive-definite tests supported in
`[u^-1,u]`, `u = 1.10246`. Its proof avoids the compact remainder operator by
bounding the local kernel against the value of the convolution square at zero.
This suggests a shorter narrow-window route that might bypass finite bad-space
conditioning. It is not yet usable in this repository: no theorem identifies
the selected CCM25 object with the source's `Q`-image on the same interval,
and no theorem identifies the CC20 functional `D` with the M0-normalized
remainder on the selected owner. It also does not supply M5B's all-other-zero
tail estimate or source zero-sum owner. Do not mark M3A, M4, M5B, or M5C
complete or inactive on this evidence alone.

The spectral counting requirement is now strictly lower than the full
Riemann--von Mangoldt theorem. `summable_of_geometric_shell_card_bound` proves
that quadratic dyadic pointwise decay is summable under any shell count
`K*q^n` with `0 <= q < 4`; the source-zero and symmetric-height specializations
preserve the same index. `sourceNontrivialZero_summable_of_xi_geometric_sphere_bounds`
connects a geometric sequence of xi circle bounds through the existing Jensen
theorem directly to spectral summability. The standard `O(T log T)` route
remains available but is no longer a necessary contract.

`completedRiemannXi_one_sub` proves the xi functional equation in the project
normalization. Every point can be folded to `Re s >= 1/2` without changing the
xi norm and with at most one unit of additional radius. The remaining M5B
counting bottom is an explicit right-half-plane xi growth estimate whose
induced dyadic ratio is below `4`, followed by the same-index spectral explicit
formula. RH remains conditional.

The right-half-plane reduction is now connected to the final summability
consumer. `sourceNontrivialZero_summable_of_xi_right_halfplane_ball_bounds`
accepts xi bounds only for `Re w >= 1/2` inside the explicit dyadic ball
`norm(w) <= 2*(|Im rho| + 2^(n+1) + 2) + 3`. It folds each Jensen-circle point
with `completedRiemannXi_one_sub`, proves the radius budget by the triangle
inequality, and returns spectral `Summable`. Its import audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. The next counting proof starts
at the modified theta-kernel Mellin integral, not at zero-index transport or
Jensen geometry.

The first xi-growth producer layer now compiles.
`completedRiemannXiKernel` is the existing
`(HurwitzZeta.hurwitzEvenFEPair 0).f_modif`, not a new analytic assumption.
`completedRiemannZeta0_eq_mellin_completedRiemannXiKernel` exposes Mathlib's
exact Mellin definition, and `norm_completedRiemannZeta0_le_kernelMoment`
removes all dependence on the imaginary part by taking the norm under the
integral. `norm_completedRiemannXi_le_kernelMoment` then adds the explicit
`norm(s)*norm(s-1)` factor and `+1`.

The same module proves the kernel's two concrete branches. Above one it is the
theta kernel minus its constant term. Below one, the theta functional equation
rewrites it as `t^(-1/2)` times the same tail evaluated at `1/t`. The import
audit reports only `propext`, `Classical.choice`, and `Quot.sound`. The next
counting bottom is the quantitative growth of the nonnegative real moment
`completedRiemannXiKernelMoment`; no source-zero transport, Jensen geometry,
or complex Gamma/Stirling theorem remains in that local obligation.

The modified theta-kernel tail is now explicit. With
`completedRiemannXiKernelTailConstant = 2/(1-exp(-pi))`, the large branch is
bounded by `C*exp(-pi*t)`. The small branch is bounded by
`t^(-1/2)*C*exp(-pi/t)` through the exact functional equation. Both theorems
compile from Mathlib's Jacobi-theta series estimate and introduce no new
premise. The remaining local proof is the real integral split at one and its
coarse subquadratic log-growth estimate.

The large-branch moment now reaches an elementary discrete bound. The compiled
chain is

```text
integral_rpow_mul_exp_neg_mul_Ioi_eq_gamma
integral_pow_mul_exp_neg_pi_eq_factorial
integral_pow_mul_exp_neg_pi_le_pow_self
```

Thus the integer moment is exactly `pi^(-(n+1))*n!` and is at most `n^n`.
Its logarithm has the required `n*log n` scale rather than the unusable
quadratic scale. The import-facing audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. The remaining local bottom is to split
`completedRiemannXiKernelMoment` at one, transport the small branch by
`t -> 1/t`, dominate a general real parameter by a nearby integer moment, and
feed the resulting dyadic subquadratic bound into the existing `q < 4`
consumer.

## 2026-07-11 Rejection-First Route Order

Do not continue xi-counting merely because its local bottom is available. The
highest-value next gate is the CC20 Corollary 3.8 (`qeasy`) factorization:

```text
selected Yoshida square = Q(f),
f positive definite,
support inside [u^-1,u], u = 1.10246.
```

CC20 Theorem 3.6 confirms that M3A's abstract `-2 Id + K_I` shape is genuine;
M3A is therefore primarily an ownership/normalization formalization risk, not
the most likely mathematical rejection. The more dangerous issue is whether
the same detector can satisfy the finite bad-space constraints while retaining
nonzero Mellin value at `rho`.

Test `qeasy` first because it can remove that issue entirely. The compiled
`convolutionIterate_rescale_inv_natCast_convolution_support_subset_half_budget`
shows that support width does not obstruct this subroute: an arbitrary outer
log window can be divided between the normalized base power and correction.
The unresolved rejection gate is algebraic positivity-preserving factorization,
not support. If factorization fails, immediately test joint separation of the
`rho` Mellin evaluation from the concrete M4 bad-space functionals. Reject the
fixed-window route if that joint separation is false; do not finish peripheral
counting or trace layers first.

## 2026-07-11 Plan 016 Rejection

The rejection-first audit rejects plan 016 as an executable RH route. The
assembled Yoshida theorem does not preserve correction interpolation:

```text
Phi_assembled(rho)
  = Phi_base(rho/(n+1))^(n+1) * Phi_correction(rho).
```

Thus `Phi_correction(rho)=1` does not imply detection; a zero base factor makes
the assembled value zero. The compiled rejection guard is
`laplaceAt_convolutionIterate_rescale_inv_natCast_convolution_eq_zero_of_base`.

The same assembly also has an unclosed radius/count cycle. The nearby radius
`R` is fixed before the correction constant and convolution count `n` exist,
while the far estimate begins only beyond `(n+1)*T`. No current bound or
fixed-point theorem proves that the original nearby set covers every zero below
that later threshold. Therefore finite nearby interpolation plus the current
far estimate does not yield one Appendix C detector.

The `qeasy` support budget is feasible but cannot repair the absent detector;
it supplies only the local remainder sign. M5B is rejected in its current form,
and M5C/M6/root retirement are inactive. Do not resume xi-counting, M2, or M3A
under plan 016. A future plan may reopen the broad strategy only after a new
non-circular producer proves full-product normalization and a simultaneous
all-zero tail bound on the same compact test.

## 2026-07-11 Plan 018 D1 Rejection

The Suzuki screw-norm defect has an unconditional absolutely convergent
one-dimensional integral formula, and finite symmetric zero truncations split
exactly into a `K_R-I` Gram term plus an off-critical conjugation term. The
source does not supply an absolutely convergent zero-pair expansion or a
summable pair majorant: local absolute convergence of `P_t` and global `L2`
membership of `S_t` do not justify termwise expansion of the norm. Gram
positivity controls `K_R`, not `K_R-I`, so it gives no defect sign. Plan 018 is
rejected at D1 as a guaranteed route; no Lean API or RH root changes result.

## 2026-07-11 Plan 019 H2/H3 Rejection

The proposed adelic Cech--Hodge regrading of the CC20 remainder fails at the
H2/H3 interface. In a scaling-equivariant Hilbert complex, legal exact and
coexact trace contributions pair and cancel, leaving no `K_I` remainder. The
support/Fourier cutoff product that actually generates the CC20 small square is
non-idempotent, has prolate eigenvalues in `(0,1)`, and does not commute with
full scaling. Moreover `-2 Id + K_I` has a positive direction on the larger
window and a negative infinite-dimensional tail, so it is not one signed
boundary norm. Splitting off its finite bad eigenspace is exactly the existing
finite-codimension conditioning, not a new producer. Plan 019 is rejected; no
Lean API or RH root changes result.

## 2026-07-11 Plan 020 Nyman--Mobius Dyadic Experiment

Plan 020 began as the rejection-first research entrypoint. It leaves the
Connes route and uses the exact discrete Nyman--Beurling--Baez-Duarte criterion
`RH <=> d_N -> 0` in the weighted sequence space with weights
`1/(n*(n+1))`. For each dyadic block it selects the explicit direction

```text
b_N = sum_(N<k<=2N) mu(k)/k * gamma_k.
```

Orthogonal projection gives an exact finite energy decrement. A uniform bound

```text
certificate_capture >= (c/log N) * d_N^2
```

would force `d_N -> 0` because the dyadic factors have a divergent harmonic
exponent. The bridge is valid and does not read zeta zeros. Its central lower
bound is unproved and must be obtained from finite residue/divisor sums rather
than Littlewood, Mertens square-root cancellation, or convergence of the
natural Mobius approximants.

The first WSL2 experiment is positive but non-rigorous. With tail cutoff two
million, the normalized `mu(k)/k` capture at `N=16,32,64,128` is approximately
`0.426, 0.578, 0.554, 0.616`. Results are stable across cutoffs from `250000`
to `2000000`; exact or interval inner products remain mandatory because the
Gram systems become increasingly ill-conditioned. See
`plan/020_2026-07-11_nyman_mobius_dyadic_certificate_plan.md` and
`scratch_nyman_block.py`.

Initial judgment: Plan 020 had passed the exact criterion, projection identity,
and dyadic closure gates, and has survived a first numerical rejection test.
It is not yet a guaranteed RH route. The next and most likely rejection gate is
M4: expand the Mobius block correlation and projected energy exactly and decide
whether divisor orthogonality supplies a strict `c/log N` margin without an
RH-equivalent cancellation estimate.

The first M4 audit did not reject the route. Exact periodic summation proves
`<gamma,gamma_k>=log(k)/k` and gives every Gram entry as a finite digamma sum
over one `lcm(j,k)` period. Exact and two-million-term results agree through
`N=32`. A larger cutoff experiment gives normalized `mu(k)/k` captures about
`0.4140` at `N=256` and `0.5802` at `N=512`, so no scale collapse is visible.

The audit also identified the actual analytic bottom. The correlation and
projected energy contain the inverse old Gram matrix `G_N^-1`; the elementary
Mobius divisor identity does not remove it. Baez-Duarte's direct natural
Mobius approximations are known to diverge in `L2` (arXiv:math/0011254,
Propositions 4.4--4.7), but that theorem does not cover Plan 020 because each
block is first projected by `(I-P_N)`. At that checkpoint Plan 020 remained
active but unresolved, not guaranteed. See
`docs/proofs/020_nyman_mobius_m4_first_verdict.md`.

The first structural M4 subroute is rejected. Vasyunin's finite-support
biorthogonal family satisfies `<gamma_m,f_n>=delta_(m,n)`, but it is the dual
of the infinite minimal system. The finite canonical dual is `P_N f_n`, which
reintroduces `G_N^-1`; at `N=64`, it retains only about 14.8 percent of the
squared norm of `f_64`. A Cholesky positivity conjecture found in
arXiv:2011.02847 is unproved and would not close the signed target-coordinate
sum even if true. Do not reopen this subroute.

One valid M4 reduction remains: with
`S_N=sum_(N<k<=2N) mu(k)/k^2`, the vector
`b_N-N*S_N*gamma_N` vanishes in the first `N-1` coordinates and
`w_N=(I-P_N)(b_N-N*S_N*gamma_N)`. Its values are explicit short weighted
Mobius floor sums. This localizes the denominator but not the numerator; the
projection still removes a material fraction of its energy. See the updated
020 verdict.

The source audit found unconditional power-saving upper bounds for related
Mobius--Vasyunin short sums in Maier--Rassias, arXiv:1705.09921, Theorem 1.1.
They may help the localized denominator but have the wrong inequality direction
for M4: the numerator needs a uniform inverse-Gram non-cancellation lower bound.
The active mathematical bottom is now named
`inverse-Gram Mobius non-cancellation`. Plan 020 remains unresolved rather than
rejected, while both the Vasyunin-direct-inverse and Cholesky-positivity
shortcuts are rejected.

The next M4 sign audit rejects pointwise positivity. The sequential
Gram--Schmidt target coordinate has the wrong sign relative to `-mu(n)` already
at the squarefree index `n=31`; exact periodic and two-million-term Gram
computations agree on the negative value. There are 24 squarefree sign failures
through `n=256`. Do not seek a proof that every Mobius-weighted future
correlation is nonnegative.

The certificate is robust to replacing `mu(k)/k` by `mu(k)/k^alpha` over the
broad range `-1<=alpha<=2`, so its numerical behavior is not fine exponent
tuning. The Bettin--Conrey--Farmer log taper is weaker in the block experiment,
and its published asymptotic assumes RH plus a moment bound on
`1/zeta'(rho)`. The remaining 020 numerator bottom is block-average Mobius
dominance with individual sign failures allowed.

A good/bad contribution audit shows that even fixed-fraction block dominance
is not a sound intermediate target. For `mu(k)/k`, the bad/good absolute mass
ratio grows from about `0.051` at `N=32` to `0.509` at `N=512`. M4 survives
numerically because the projected Schur energy shrinks concurrently. The only
admissible remaining bottom is therefore the coupled normalized inequality,
not separate coarse numerator and denominator bounds.

The final rejection-first round rejects Plan 020 as an executable RH route,
without claiming that M4 is mathematically false. A matrix-free CUDA projection
run extended the selected direction to `N=4096`. The normalized values
`log(N)*capture/d_N^2` at `N=1024,2048,4096` were approximately
`0.2948,0.5869,0.2664` at cutoff `250000`; cutoff `100000` gave `0.2965` and
`0.2834` at the two low scales. Both normal-equation residuals were below
`1e-11`. This replaces the earlier stable-margin impression with strong dyadic
oscillation and descending low subscales, but it is not a rigorous zero-infimum
certificate because the projected energy is below the crude tail-mass bound.

The route-level rejection is structural. Vasyunin duality, Cholesky positivity,
pointwise signs, fixed-fraction good/bad dominance, power weights, and the BCF
log taper all fail to lower M4. The surviving coupled inequality retains
`G_N^-1`, implies RH through the checked dyadic closure, and has no independent
unconditional arithmetic producer. Burnol supplies only the lower obstruction
on `d_N^2 log N`; the matching BCF Mobius asymptotic assumes RH plus a moment
bound on `1/zeta'(rho)`. Plan 020's exact formulas remain reusable evidence, but
do not reopen this route without a genuinely lower inverse-Gram theorem.

## 2026-07-11 Plan 021 Divisor-Gradient Flow Rejection

The self-derived divisor-gradient correction is rejected. The exact identity

```text
Delta gamma_k(n) = 1/k - 1_(k divides n)
```

allows unique coefficients in `N<k<=2N` that cancel every gradient of the old
optimal residual on `N<n<=2N`. CUDA checks confirm the local cancellation to
about `1e-16`. Globally, however, the same coefficients hit all later multiples
and increase weighted Hilbert energy. At `N=32,64,128,256,512,1024,2048`, the
raw energy ratios were approximately
`15.73,1.31,3.35,10.13,2.98,2.60,4.72`; after old-space reprojection the ratios
were still `1.91,1.17,1.31,1.78,1.09,1.16,1.18`, all worse than one.

Optimally scaling the reprojected correction no longer realizes gradient
cancellation and merely creates another one-dimensional certificate. Its
normalized capture oscillates and reaches about `0.0353` at `N=256`; proving a
uniform positive angle again requires the residual and inverse old projection
that blocked Plan 020. Plan 021 is therefore rejected, no Lean API is created,
and RH remains conditional. See
`docs/proofs/021_divisor_gradient_flow_rejection.md`.

## 2026-07-11 Plan 022 Shifted-Mobius Frame Candidate

Plan 022 is worth deeper research and has not been rejected. For each fixed
shift `1<=d<=8`, its block coefficient is

```text
1_(d divides k)*mu(k/d) - harmonicMean_(N,d),  N<k<=2N.
```

The harmonic mean makes the coefficient sum weighted by `1/k` exactly zero,
so every resulting sequence direction vanishes for all coordinates `n<=N`.
The proposed certificate uses the unprojected eight-direction Gram matrix;
because orthogonal projection only decreases its denominator, this is a
conservative lower bound for the real dyadic decrement and contains no Schur
inverse in that denominator.

The fixed `D=8` frame survives `N=128,256,512,1024,2048,4096`. At `N=4096`,
cutoff `250000`, `log(N)` times conservative normalized capture is about
`0.1657`; the frame min/max eigenvalue ratio is about `9.03e-3`, the first-`N`
coordinate leakage is `2.1e-17`, and the target normal-equation residual is
`7.8e-12`. A `D=64` robustness cohort gives about `0.2076` at the same scale.

The next mathematical bottom is an unconditional aggregate lower bound for
the eight squared residual correlations, paired with an explicit frame-energy
upper bound. A rewrite through `G_N^-1`, per-scale fitted coefficients, or a
Mertens square-root estimate is rejected. No Lean API is active until this
finite divisor-sum bound has a strict positive margin. See
`plan/022_2026-07-11_shifted_mobius_frame_plan.md` and
`docs/proofs/022_shifted_mobius_frame_first_verdict.md`.

The second 022 round selects one fixed direction inside the frame. The
eight-correlation vectors align across scales with `-mu(d)/d`, leading to the
global coefficient `Q=theta*mu`, where `theta(d)=-mu(d)/d` for `d<=8`.
Anchoring the dyadic block by one old `gamma_N` gives a sequence `h_N` that
vanishes for `n<N` without changing its correlation with `r_N`. The exact
divisor identity `1*Q=theta` collapses the untruncated divisor sum to fixed
support `1..8`.

The fixed direction survives double precision through `N=4096`; at cutoff
`250000`, `log(N)` times normalized capture is about `0.1213`, its energy is
about `0.1748`, the first-`N-1` leakage is `1.4e-17`, and the normal residual is
`7.8e-12`. Calibrated float32 rejection tests remain positive at `N=8192` and
`N=16384`. The primary proof bottom is now a uniform constant energy bound and
a `c/log N` correlation bound for this same anchored convolution.

Three shortcuts are rejected: isolating the first dyadic block ignores a
same-order far tail; the pure-new exact-orthogonal `(N,3N]` intersection loses
target capture rapidly; and the general moment-zero Bessel constant grows
linearly with `N`. See
`docs/proofs/022_fixed_convolution_second_verdict.md`.

The fixed correlation has now survived every integer scale `16<=N<=512`
without a sign change; the smallest normalized value is about `0.1029` at
`N=100`. Calibrated rejection runs remain positive through `N=16384`. This is
not pointwise positivity: bad pointwise products retain about 25--43 percent of
the good mass. The first dyadic block is positive in every tested scale and is
the candidate finite-divisor main term; the smaller far tail can oppose it, as
at `N=1024`.

No smooth scaling limit for the optimal residual block is visible. Adjacent
dyadic residual profiles are often negatively correlated. The proof must use
the exact optimality/orthogonality equations together with `1*Q=theta`, not a
continuum residual ansatz. The direct target correlations are not dominant:
the old projection component is often two to three times larger, so merely
dropping it is also rejected.

The third 022 audit identifies the fixed sequence as a centered Mertens bridge.
For `P_Q(x)=sum_(k<=x)Q(k)`, finite convolution gives
`P_Q(x)=sum_(d<=8)theta(d)M(floor(x/d))`. Because `theta(1)=-1` and
`sum_(2<=d<=8)|theta(d)|/sqrt(d)<0.758`, a standalone square-root bound for
`P_Q` would recursively give square-root Mertens control. The proposed separate
constant-energy proof is therefore rejected as an RH-level input.

Plan 022 remains active only in coupled form. On the first block,
`h_N(n)=N*S_N-(P_Q(n)-P_Q(N))`; the same centered bridge occurs in its energy
and in its correlation with `r_N`. The active theorem is the uniform
`c/log N` lower bound for their squared angle, without separately bounding the
Mertens bridge or expanding `r_N` through `G_N^-1`. See
`docs/proofs/022_mertens_bridge_third_verdict.md`.

The final 022 audit rejects the route as an independent producer. For fixed
`h_N`, the normalized angle at `N=4096` is only about `0.00269` when the old
projection stops at `N/2`, then grows to `0.12684` after the full shell
`(N/2,N]` is included. Across tested scales, the optimal shell update supplies
about 46--84 percent of the final correlation.

The explicit multiscale space
`V_16+span(h_16,h_32,...,h_N)` does not repair this ownership failure. Its
squared distance plateaus near `0.014256` through `N=65536`. The fixed
convolution family is not dense; its positive correlation with `r_N` is
inherited from the complete optimal shell. Proving that correlation therefore
restores the growing Schur/inverse-Gram non-cancellation bottom of Plan 020.
Plan 022 is rejected, no Lean API is created, and RH remains conditional. See
`docs/proofs/022_final_rejection.md`.

## 2026-07-11 Qeasy Full-Product Positive Base

Plan 023 supplies an axiom-clean algebraic repair for the full-product base
zero obstruction. `exists_convolutionSquare_base_fullProduct_normalized` in
`ConnesWeilRH/Source/CC20YoshidaFullProduct.lean` constructs, for every finite
node set and every symmetric log budget `(-a,a)`, a compact factor `h` such
that

```text
f = h* * h,
support(f) subset (-a,a),
Phi_f(z/(n+1)) = 1.
```

The construction interpolates `h` on the Hermitian closure of the rescaled
nodes, using the proved identity

```text
Laplace(h*)(s) = conjugate(Laplace(h)(-conjugate(s))).
```

This is a genuine positive-definite base, not a stored positivity field. The
WSL import-facing build of `CC20YoshidaFullProduct` and its audit passed; the
new declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`.

It does not reopen the Connes route. The P0 residual correction has arbitrary
finite Laplace values and is generally not a convolution square. Convolving it
with the positive base therefore need not be positive-definite, so the complete
P0 assembly cannot be fed to CC20 Corollary `qeasy`. The next safe mathematical
target is one positive-definite assembled detector whose finite
zero/detection pattern and convolution-power tail control are proved on the
same object. Do not treat base positivity as final-test positivity.

The first 023 attack confirms that P2, not finite-node base nonvanishing, is
the likely death point for the narrow-support route. Yoshida's original Lemma
1 (1992, pp. 285--286) increases its convolution count without a fixed-support
constraint. The `qeasy` normalization fixes support but moves the far threshold
to `(n+1)*T`. Current Lean theorems produce
`R -> correction -> C,T -> n`, with no control proving
`R >= (n+1)*T`. Thus they cannot make one detector control all zeros. See
`docs/proofs/023_qeasy_radius_count_verdict.md`.

CC20's printed Corollary `qeasy` is broader in wording, but its proof
(`weil-compo.tex:834-840`) invokes positive-definiteness through
`|f(x)| <= f(0)`. Any route use must establish that hypothesis for the final
test itself, not merely for a base before an arbitrary correction.

The P2 attack also lowered the finite part cleanly. The axiom-clean theorem
`exists_convolutionSquare_base_fullProduct_indicator` constructs a final
finite 0/1 detector of the form `h* * h`: its full-product value is one at a
marked node and zero at every other finite node satisfying the explicit
Hermitian-reflection separation condition. This removes arbitrary correction
factors from the finite detector layer. The remaining source specialization is
to derive that separation from the open-strip source-zero facts and the route
nodes; it does not address the P2 radius/count fixed point or global tail.

That source specialization is now complete. The axiom-clean theorem
`exists_sourceZero_nearby_convolutionSquare_indicator` uses the finite set
`sourceNontrivialZerosInClosedBallFinset rho R union routeNodes`. From a source
nontrivial zero `rho`, `R >= 0`, and nonnegative real parts for `routeNodes`, it
returns one compact factor `h` whose square has narrow symmetric support,
full-product value one at `rho`, and value zero at every distinct nearby source
or route node. The source open-strip theorem discharges the strict marked-node
condition. This does not solve P2: the remaining required same-object theorem
still has to produce `R`, a convolution count `n`, and a tail threshold `T`
with `R >= (n + 1) * T`.

Plan 023 is rejected as an independent RH route. This is a semantic rejection,
not a claim that the P2 fixed-point inequality is false. Completed P2 plus its
planned `qeasy` transfer produces the concrete Yoshida detector-existence
input consumed by `cc20_proposition_c1_from_yoshida_detector` in
`Source/CC20YoshidaCriterion.lean`; that theorem concludes
`RHDefinitionBridge.standard.SourceRH`. Thus P2--P3 is an RH-level theorem in
detector language and cannot lower the route. Do not reopen 023 through tighter
endpoint, interpolation, or radius/count estimates; a future narrow-support
lane needs a consumer strictly weaker than source RH.

The 023 finite positive-definite construction is retained as a component, not
a route. Its safe reusable declarations are `laplaceAt_involution`, the
full-product convolution-square formulas, the finite source-zero indicator,
and the support-preserving convolution-square power formula. They may not be
used to rebuild Yoshida detector existence or detector coverage. The attempted
024 `eta_S`-transport formulation is rejected: its local
commutator/kernel/ordinary-trace content is the already completed Plan 012
operator layer, while transport needs post-`Q` equalities that CCM24's
nonunitary `eta_S` cannot supply. This does not reject direct fixed-S work in
the unitary scattering coordinate `u_S`. That narrow opening must retain
`D_S o Q=<xi,(-2 Id+K_(S,I))xi>` and prove a non-circular same-detector
finite-codimension conditioning theorem; the no-defect equality is false.
See `docs/proofs/024_pre_cutoff_scattering_consumer_screen.md`.

The direct fixed-S conditioning route is now rejected under the current source
detector consumer. Plan 016 requires M5C to retain M5B's global tail estimate
and strict source zero-sum sign while adding finite bad-space orthogonality.
M5B's same-test all-other-zero tail is exactly the P2 contract rejected in 023
as an RH-level detector theorem. Finite spectral conditioning can control
`D_S`, but cannot create the missing independent source sign. An abstract
finite-codimension sign theorem remains mathematically open but cannot reopen
the route without a new consumer strictly weaker than M5B.

The direct variable-S Gate A is rejected. The exact cocycle decomposition is
`D_(uv)=D_v+D_u+Cross`; it makes the mixed term trace-legal but does not remove
the pure finite-place `D_v` from the positive-trace remainder. For
`v=u_p`, the translation-series calculation makes `D_p` a Dirac comb at
`k log p`. Its central coefficient is exactly `p^(-1) log p>0`. After
`Q=-partial^2+1/4`, choose a smooth wave packet of width less than `log p` and
modulate it by `exp(isx)`: all noncentral atoms vanish and the quadratic form
grows like `p^(-1) log(p) s^2`. It is therefore not represented by
`-c Id+K` with bounded compact `K`. A reproducible `p=2` grid probe independently
shows stable phase splitting and quadratic growth. See
`docs/proofs/025_variable_s_two_gate_verdict.md`,
`docs/proofs/026_semilocal_cocycle_renormalization.md`, and
`docs/proofs/025_finite_euler_remainder_probe.py`.

The operator-ideal part of the mixed cross term still passes. Writing `T=PVP`
gives `T-vTv*=[T,v]v*` and
`[T,v]=PV[P,v]+[P,v]VP`. For each Euler translation by `m log p`, composition
with the Schwartz convolution `V_h` has Hilbert--Schmidt norm squared
`|m| log(p) * norm(h)_2^2`; derivative/Sobolev factorization gives trace class
with polynomial growth in `m`, while the Euler coefficients decay
geometrically. Hence the cross term is trace-legal, but this cannot repair the
pure finite-place second-order term. Reopening Gate A requires an exact
pre-read-off cancellation theorem or a different pre-cutoff trace/supertrace;
the compact mixed-kernel theorem alone is no longer a route gate.

The second gate is not structurally false. Writing the final positive factor
as `H=B*correction` makes both finite Mellin values and bad-space
orthogonality linear in the residual correction. Joint interpolation is
equivalent to finite linear independence of the pulled-back Mellin and
bad-space functionals. It needs an actual nonzero minor for the concrete bad
vectors, but no universal dependence has been found. The matrix is inactive
because Gate A is rejected; it becomes relevant only after a different
pre-cutoff trace/supertrace supplies a new bounded remainder owner.

The variable-window freedom upgrades this second gate to an abstract
surjectivity proof under the intended owner hypotheses. Mellin pullbacks are
distinct exponentials, while bad-space pullbacks are compactly supported
convolutions of a fixed nonzero base with independent compactly supported
vectors. A global linear relation vanishes outside the latter support, forcing
all exponential coefficients to zero; the remaining convolution relation
vanishes only when all bad-vector coefficients vanish, by the entire Fourier
product identity. Finitely many compact witnesses then fit in one residual
window and give an invertible evaluation matrix. The actual owner must still
prove its source-factor map has this linear convolution form and its bad
vectors have the required compact support.

The first direct P2 escape is rejected: one fixed narrow-support detector
cannot interpolate zeros at every other source zero. Its Mellin transform is a
finite-exponential-type entire function with `O(R)` disk-zero count if nonzero,
while distinct zeta zeros are not `O(R)`. Yoshida uses this exact contradiction
on p. 321 of the 1992 paper. Thus P2 genuinely requires a finite nearby set
plus a far-tail estimate; it cannot be replaced by infinite interpolation.

The first pre-cutoff escape screen rejects two apparent repairs of the finite
Euler Dirac obstruction. CCM24's dual `theta_S/eta_S` pairing preserves the
archimedean positive trace but cancels the finite Euler factors, so it cannot
read the semilocal Weil form. The inner factorization `u_p=z/B_a` cancels the
central defect in a graded dilation, but the difference of the two degree-one
model-space projections has exact eigenvalues `+p^(-1/2),-p^(-1/2)`; the
resulting supertrace is intrinsically indefinite.

One source-backed candidate survives: form the ordinary positive trace
`norm(Pi_- C_S(g) Pi_+)_HS^2` across the positive and negative spectral
subspaces of the semilocal prolate operator before scalar scattering
elimination. Unlike the diagonal positive compression, this has no
growing-rank bulk. CCM24 explicitly proposes this spectral conditioning but
keeps the operator domain formal and supplies no trace-to-Weil comparison.
The exact finite-cutoff version is rejected because its kernel is continuous
and cannot equal prime-power Dirac atoms unless the remainder stores them
again. The surviving version is asymptotic: prove common-form-domain
distributional convergence to the Weil functional. Jacobi sections 16--32
give a zero translation energy at the origin and moderately stable energy at
`log 2` for `lambda=0.5`, but still suffer positive-threshold spectral
pollution and are not route evidence. See
`docs/proofs/027_pre_cutoff_euler_dilation_escape.md`.

The surviving prolate route now has a concrete arithmetic mechanism. The
Euler perturbation of the cyclic-pair measure satisfies
`log |L_p(1/2-is)|^2 = 2 sum_(k>=1) p^(-k/2) cos(k s log p)/k`.
In strong orthogonal-polynomial asymptotics this analytic weight perturbation
enters through the Szego/scattering phase; differentiating that phase supplies
`log p`, while its Fourier modes are exactly the prime powers. Thus the
finite-prime Weil atoms can in principle arise as the subleading limit of the
continuous cross-spectral kernels without reintroducing the fixed-cutoff
Dirac remainder. Existing bulk-universality and periodically modulated Jacobi
results do not provide the required global subleading trace theorem. The new
bottom is to extract this first phase correction in
`norm(Pi_- C_S(g) Pi_+)_HS^2` with a uniform common-form-domain error.

The first prolate-edge attack separates three projection regimes. Replacing
the prolate projection by the ordinary degree cutoff is rejected because its
cross energy is an OPE linear-statistic variance and is universal at leading
order. The actual source q-series has a non-decaying formal edge correction:
`a_n(q)^2=(n+1/2)(n+1)(1+2sqrt(2)(alpha_(n+1)-alpha_n)q+...)` with
`alpha_n~(-1)^n/sqrt(pi n)`, so the coefficient of `q` in `a_n(q)` is of order
`sqrt(n)`. This is analytic source evidence, not merely the stable numerical
cross-check through `n=128`.

Fixed `q=1/p` is now controlled through the finite Schur transfer at the level
of reproducible numerical evidence. The source Lambert
q-matrix has rank-one vectors growing polynomially and therefore no naive
trace-class infinite limit. Its polynomial kernel is the self-dual Meixner
kernel `2F1(-m,-ell;1/2;2)`. The exact Meixner Poisson kernel reduces on the
diagonal and every fixed-width boundary entry to a Jacobi polynomial. Darboux
asymptotics gives phase `4n arctan(q^r)` and proves that, after source
normalization, each Lambert layer contributes a coherent oscillatory
`n^(-1/2)` boundary wave. The determinant-ratio owner reduces exactly to the
last-row Schur complement for `s_n=Delta_n/Delta_(n-1)`.

The source moment normalization includes an overall `1-q`; the correct Gram
bound is `(1-sqrt(q))/(1+sqrt(q)) I <= G_n(q) <=
(1+sqrt(q))/(1-sqrt(q)) I`. Direct exact-kernel parity blocks through degree
513 pass this bound. At `p=2`, the adjacent Schur pivots retain an oscillatory
`a_n(q)-a_n(0)` of `sqrt(n)` size. Its fitted phase is
`pi-4 arctan(q)=4 arctan(tanh(log(p)/2))`, the Cayley phase of the dilation by
`p`; fits on `32..512` through `256..512` stabilize near amplitude `0.6514`
while residual RMS falls from `0.0337` to `0.0101`. This rejects exact Schur
cancellation as the easiest death mechanism, but remains numerical evidence.
The next proof bottom is the nonzero-amplitude Schur--Cayley asymptotic,
followed by the common-domain semilocal prolate cross-trace-to-Weil limit. See
`docs/proofs/028_prolate_fio_prime_coefficient.md`,
`docs/proofs/029_prolate_jacobi_edge_survival.md`, and
`docs/proofs/030_meixner_lambert_resummation.md`, and
`docs/proofs/031_schur_cayley_phase_verdict.md`.

The Schur bottom now has an exact operator owner. With
`U_p=exp(-i log(p)D)` and `q=1/p`, the source Gram operator is the Poisson
kernel `(1-q)(I-sqrt(q)U_p)^-1(I-sqrt(q)U_p*)^-1=T_p* T_p`; its scalar Poisson
series contains every prime power. The finite pivot is exactly
`dist(T_p e_n,T_p V_(n-1))^2`. In the lowest-weight `SU(1,1)` disk model the
squeeze has Cayley parameter `tanh(log(p)/2)`, proving that the observed phase
is `pi-4 arctan(q)` rather than a fitted numerical artifact. The minimal new
theorem is `log s_n=log sigma+n^-1/2 Re(B exp(i n omega))+O(n^-1)` with
`B(q) != 0`; it directly yields the `sqrt(n)` Jacobi wave. Guarded degree-513
fits for `p=2,3,5,7,11` all select their exact Cayley phase, and the small-q
amplitude approaches the rigorous first-variation constant `2sqrt(2/pi)q`.
No checked Szego theorem closes the result: the available locally Toeplitz
Moyal theorem requires exponential off-diagonal decay, while the squeeze is a
broad Fourier integral operator. See
`docs/proofs/032_su11_wiener_hopf_reduction.md`.

The classical squeeze crosses the number-action boundary transversely at
`tan(theta)^2=p`, so the local stationary symbols cannot vanish through a
degenerate phase. Direct fits of the minimal expansion give nonzero complex
boundary coefficients for `p=2,3,5,7,11`, with positive real parts and
`B(q)/q` approaching `2sqrt(2/pi)`. The proposed proof split is to establish
real-analytic `B(q)` and its source-backed nonzero derivative at zero, use an
explicit remainder for all sufficiently large primes, then interval-certify
the finite small-prime set from the same two-crossing formula. Analyticity by
itself is not enough for the small primes.

The second prolate gate has changed owner. The invented cross transition
`norm(Pi_- C_g Pi_+)_HS^2` is no longer the active source-backed trace. The
natural whole-line prolate extension has discrete spectrum unbounded in both
directions, so `Pi_+` is infinite rank. Exact-Jacobi sections show bare
translation cross energy growing with section size, while fixed Schwartz
multipliers provide no stable evidence for the proposed nonzero large-cutoff
limit. CC20 instead names the one-sided Sonin trace
`Tr(C_g* S C_g)=norm(S C_g)_HS^2` and proves
`Tr(rho(f)S)=W_infinity(f)+E(f)` together with a conditioned Weil lower bound.
The finite-S escape is to construct the same one-sided semilocal Sonin or
negative-prolate trace at the fixed support cutoff. Its immediate rejection
test is the `S={infinity,2}` analogue of `E`: after `Q`, it must have only
finitely many bad directions. If the raw finite-Euler noncompact translation
block survives in this same-object remainder, the replacement is rejected
before any full self-adjoint prolate API is built. See
`docs/proofs/033_two_gate_escape_verdict.md`.

The two gates now meet in the exact metric Sonin projection. CCM24 proves that
`theta_S` is a bounded isomorphism from the archimedean Sonin space onto the
semilocal one. With `H_S=theta_S*theta_S`, its orthogonal projection is
`theta_S R(R H_S R)^-1 R theta_S*`. For one prime,
`H_p=|1-p^-1/2 U_p|^2`, the inverse orientation of the Gate 1 Poisson Gram
operator. This keeps Euler arithmetic, unlike the rejected theta/eta pairing,
and bypasses formal semilocal prolate self-adjointness and the large-cutoff
cross limit. The CC20 one-sided Sonin trace inherits trace class from the
archimedean factorization because the metric and compressed inverse are
bounded. The remaining theorem is the fixed-S remainder sign.

At second Euler order, the metric projection cancels the old raw central
`p^-1 I` obstruction before read-off. If `J=(I-R)U_pR`, the first projection
variation is `-(J+J*)`, while the second diagonal blocks are `-J*J` and
`JJ*`. Thus the old wave-packet argument against an uncancelled scalar
`D_p o Q` does not reject this object. The next gate is the trace-class sign of
the smoothed defect pair together with identification of the `U_p^2` term as
the `p^2` Weil atom. See
`docs/proofs/034_metric_sonin_projection_escape.md` and
`docs/proofs/035_metric_projection_second_variation.md`.

The entire metric projection flow has logarithmic generator
`-U_p(I-aU_p)^-1=-sum_(m>=1)a^(m-1)U_p^m`. Hence every prime-power translation
appears before read-off; integration gives `a^m/m`, and the scaling
differential gives `m log(p)`, leaving the exact Weil coefficient
`p^(-m/2)log(p)`. Projection-interrupted words contain the nonlinear central,
boundary, and mixed-prime remainders. The arithmetic main channel is now
structurally correct to all orders; the remaining rejection test is whether
the interrupted words are trace class with only finitely many bad directions
after `Q`. See `docs/proofs/036_metric_projection_logarithmic_flow.md`.

The metric Sonin remainder now passes the operator-ideal gate, conditional on
the exact single-crossing Weil read-off. CC20 proves
`P P_hat P=R_Sonin+K_prol` with positive trace-class `K_prol` and
`Tr(K_prol) approximately 2.237484835`; its `quantsmooth` lemma makes
Schwartz-smoothed cutoff crossings trace class. A single translated crossing
has Hilbert--Schmidt norm squared `|m|log(p)norm(h)_2^2`; two crossings are
trace class, and geometric Euler coefficients dominate every polynomial
factor introduced by `Q`. Thus the finite-Euler remainder is compact relative
to the archimedean `-2 Id` essential part. The final gate is no longer
compactness but `norm(K_S)<2`, or a proof that the finite `>=2` eigenspace is
already killed by route vanishing. Arbitrary bad-vector orthogonality would
reopen the restricted-test RH exit. See
`docs/proofs/037_metric_sonin_ideal_closure.md`.

The single-crossing finite-prime read-off is now exact. For the half-line
crossing `J_b=(I-P)U_-b P` and test convolution `C_h`, diagonal kernel
intersection gives `Tr(C_h* C_h J_b)=b(h* * h)(b)`. Taking
`b=m log(p)` and multiplying by the metric logarithmic-flow coefficient
`p^(-m/2)/m` yields the exact Weil atom
`p^(-m/2)log(p)(F(p^m)+F(p^-m))` for the same convolution square. Thus the
old noncompact partial translation belongs to the Weil main term rather than
the remainder. After this subtraction, only multi-crossing and
trace-class-prolate words remain. The unresolved gate is the global CC20 angle
orientation/sign and the norm of the resulting compact operator. See
`docs/proofs/038_single_crossing_weil_read_off.md`.

The finite-prime sign also matches. Metric projection variation contributes
the negative of the crossing pair, while CCM25 defines
`QW=archimedean+pole-sum_p W_p`; the local atom itself stays positive. Hence
the one-crossing metric trace and CCM25 `QW` agree in coefficient, test square,
prime-power position, and sign. No extra sign convention remains at read-off.

CCM24's de Branges realization fixes the final sign gate precisely. All
semilocal Sonin spaces map to the same vector space of entire functions, and
`upsilon_S theta_S=upsilon_infinity`; only the inner product changes. Hence
the algebraic subspace vanishing at `{0,1/2,1}` is independent of `S`.
This must not be justified by analytic pointwise invertibility of the Euler
factor, since `1-p^(-1/2-it)` vanishes at `t=i/2`. Equivalent norms do not
prove that reproducing-kernel vectors or compact bad eigenspaces stay fixed.
The last active theorem is that `-2Id+K_S` is negative on the common
triple-vanishing subspace, equivalently a certified norm bound there or
ownership of the `>=2` eigenspace by the three evaluation kernels. See
`docs/proofs/039_debranges_bad_space_gate.md`.

Plan 024 now indexes the metric Sonin projection lane as the candidate
implementation of Plan 016 Contract M3B. It is intentionally brief and remains
prep-only: no Lean owner is authorized before the `S={infinity,2}` compact
remainder has strict Rayleigh bound `<2` on the common de Branges subspace
vanishing at `{0,1/2,1}`. See
`plan/024_2026-07-12_metric_sonin_projection_plan.md`.

Plan 024 is now rejected as an executable M3B lane after a source-line
common-domain audit. The positive trace-class prolate angle correction
`sum lambda_n^2 |zeta_n><zeta_n|`, whose trace is about `2.237484835`, is not
CC20's post-`Q` compact operator. Theorem `thmqkey1` instead defines an explicit
`Q delta` kernel on the convolution-root space `L2(sqrt I,d*rho)`, while the
later `E o Q` sign argument uses a distinct normalized `Q epsilon` kernel.
CCM24's `B_lambda` realizes semilocal Sonin vectors, not this test-root space.
Thus the proposed form `<F,K_S F>` for `F in B_lambda` had no same-object
operator/norm owner. The local single-crossing coefficient remains valid, but
the global fixed-S trace decomposition and residual compact kernel are
unproved. Do not run finite sections or create a Lean owner until one theorem
constructs that kernel on the test-root Hilbert space and represents the route
Mellin conditions there. See
`docs/proofs/040_metric_sonin_domain_rejection.md`.

The 2026 finite Galerkin/Herglotz escape screen does not supply a new RH
producer. arXiv:2607.02828 does provide two exact reusable results: every
finite Galerkin vector maps to an explicit band-limited Guinand--Weil test with
the same cutoff-free zero sum, and the omitted post-band archimedean tail is a
strictly positive Cauchy--Stieltjes Gram increment with an explicit norm
budget. These results validate the finite coordinate system and reject
finite-cutoff negative eigenvalues inside the tail budget, but they do not
prove the cutoff-free matrix positive. Positivity of all cutoff-free matrices,
after a determining-family theorem, is Weil positivity itself. The 2026 scalar
Herglotz reduction is also not lower: it leaves one odd-sector resolvent
inequality open, while Yoshida Proposition 1(1) proves odd Weil positivity is
equivalent to RH. Finally, Yoshida Lemma 1 avoids the detector radius cycle by
allowing support to grow with the convolution power; Plan 016's fixed-window
rescaling removes exactly that freedom. The remaining honest alternatives are
an explicit global fixed-S post-Q kernel/sign theorem or a genuinely lower
arithmetic proof of the cutoff-free finite matrix signs. See
`docs/proofs/041_finite_galerkin_escape_screen.md`.

The endpoint metric Sonin projection is now mathematically rejected, beyond
the earlier common-domain objection. Pulling its trace back through `theta_S`
gives the exact same-object identity
`L_S-L_infinity=Tr(R C (I-R) H_S R (R H_S R)^-1)`. For one prime, writing
`a=p^-1/2`, `V=U+U*`, and
`A_a=(1+a^2)R-a R V R`, the correction is
`-a Tr(R C Q V R A_a^-1)`. Its second-order single-crossing term is
`-a^2 Q(U^2+U*^2)R`. Since a two-step crossing has length `2 log(p)`, this
produces `2 a^2 log(p)` times the same square evaluation, whereas the `p^2`
Weil atom has coefficient `a^2 log(p)`. The excess remains an infinite-rank
single crossing and cannot be compact. The earlier logarithmic-flow argument
missed the extra direct contribution from the moving projection factors. Keep
the local half-line trace lemma, but do not use the endpoint metric projection
as a finite-S positive trace or M3B owner. See
`docs/proofs/042_metric_sonin_second_prime_power_rejection.md`.

The cutoff-free finite Weil matrix attack now has a rigorous cancellation
verdict. Using the arXiv:2607.02828 Arb closed-form builder, interval LDL
certified positive inertia for representative matrices through dimension 129.
The project probe then reevaluated fixed high-precision minimum vectors with
Arb. At `(c,N)=(13,16)` it enclosed a positive Rayleigh quotient near
`8.5686e-35`; at `(100,16)` it enclosed one near `4.8601e-53`. Midpoint
diagnostics reach about `1.5843e-87` at `(100,32)`. Along these directions the
pole contribution is positive and order one, while the Gamma and prime
contributions are negative and cancel it to the displayed scale. This rejects
fixed coercive margins, diagonal dominance, and separate block-norm domination
as uniform proof mechanisms. The surviving coupled rank-one Krein/Herglotz
condition is exact but remains open and RH-level by the Yoshida odd-positivity
criterion. The reusable probe is
`docs/proofs/043_cutoff_free_weil_spectrum_probe.py`; the verdict is
`docs/proofs/044_cutoff_free_weil_cancellation_verdict.md`. Run WSL Arb cases
serially: concurrent WSL process fan-out triggered a service-level
`E_UNEXPECTED` unrelated to the mathematics.

The first two quantum-mechanical escape routes are rejected in their stated
forms.  For the arithmetic Lindblad proposal, matching a prime-power Weil atom
with `sqrt(w)(U-I)` forces the diagonal compensation `2w Id`.  At cutoff
`c=13`, the full compensation is about `9.9437688`, while the certified
pole-plus-Gamma Rayleigh value on the `N=16` minimum direction is only about
`0.0880103`; the required residual is therefore negative by about `9.8557585`.
Orthogonal noise channels remove cross terms but cannot remove this `J*J`
diagonal.

The ordinary prime-loop metric graph is independently rejected.  Edges of
length `log(p)` are unbounded, so fixed-width interior bumps give an infinite
orthonormal bounded-energy sequence and rule out compact resolvent for a local
self-adjoint graph Hamiltonian.  Adding dilation channels produces an open
scattering system whose prime data are resonances rather than discrete
self-adjoint eigenvalues.  A graded supertrace or nonlocal network is a new
route and receives no positivity from these rejected mechanisms.  See
`docs/proofs/045_quantum_lindblad_graph_rejection.md`.

The next original-route screen rejects four further mechanisms.  The exact
matrix-valued von Mangoldt path has positive Krein boundary masses at prime
events, but its smooth-cell cutoff curvature is indefinite; `Q_N^-1` and
`log det Q_N` have no fixed curvature either.  The coupled Schur impedance
`1/<1,Q_N^-1 1>` remains positive in the tested cells but its first and second
cutoff derivatives change sign, and it controls the even all-ones direction
rather than the odd RH gate.

The proposed `PF_infinity` Markov-cycle bridge in arXiv:2602.01248 uses a false
positive-sum closure: its determinant expansion has mixed-kernel columns.
The genuine Xi Fourier kernel cannot itself be a non-Gaussian
`PF_infinity` density because its bilateral Laplace transform is entire.
Finally, effective large-shift Jensen hyperbolicity leaves the ray
`n=0,d->infinity`, which is exactly RH.  The reusable closed-form diagnostic is
`docs/proofs/046_cutoff_schur_flow_probe.py`; the verdict is
`docs/proofs/047_original_route_rejection_screen.md`.  No new Lean owner or RH
consumer was authorized.

The Robin/colossally-abundant and generic de Bruijn--Newman lanes are also
rejected as lower producers. On CA numbers, Ramanujan's RH-conditional deficit
is `Theta(1/sqrt(log n))`, while Robin's false-RH oscillation has positive
excursions `(log n)^(-b)` for some `b<1/2`. The ordinary zero-free-region PNT
error is asymptotically larger than this margin, so it cannot decide the strict
sign; proving the needed uniform sign is the RH-level gate itself. Forward
de Bruijn heat flow contracts a known zero strip and yields real zeros only at
positive time. Running it backward is not zero-preserving, while setting the
initial strip width to zero assumes RH. PF infinity is unavailable and PF5
already fails. See `docs/proofs/048_robin_heatflow_rejection.md`. No Lean owner
or route consumer changed.

The graded extension of the arithmetic Lindblad channel is now rejected as a
positive mechanism. The exact pair
`sqrt(w/2)(U-I)` and `sqrt(w/2)(U+I)` cancels the forced diagonal in supertrace
and leaves precisely `-w(U+U*)`. This is an algebraic read-off success but a
sign failure: its Fourier symbol is `-2w cos(theta)` and has both signs. More
generally, any difference of positive local `I,U` channel Gram matrices with
zero total diagonal and nonzero correlation has spectrum
`[-2|c|,+2|c|]`. Finite sums have a nonzero zero-mean trigonometric symbol and
remain indefinite; finite-codimensional route vanishing conditions cannot
remove either essential spectral side. The WSL probe is
`docs/proofs/049_graded_prime_supertrace_probe.py`; the proof verdict is
`docs/proofs/050_graded_lindblad_supertrace_rejection.md`. No Lean owner or RH
consumer changed.

The nonlocal stoquastic/gauge-Laplacian escape is rejected at the smallest
exact cutoff-free Weil matrices. The official arXiv:2607.02828 source bundle
was restored and its Arb builder rerun. At `(c,N)=(13,2)`, all 10 nonzero
triangles have positive edge-sign product; at `(13,4)`, all 84 do. A cyclic
edge product is invariant under arbitrary diagonal phases, whereas three
simultaneously nonpositive real edges would have negative product. Hence no
diagonal sign or phase gauge makes these matrices stoquastic. The same
`(13,2)` matrix remains Arb-certified positive, so this rejects only the
Perron--Frobenius graph-energy mechanism, not finite positivity. The reusable
probe is `docs/proofs/051_stoquastic_weil_probe.py`; the verdict is
`docs/proofs/052_stoquastic_weil_gauge_rejection.md`. No Lean owner changed.

The conditional-kernel screen now imposes the actual CC20 triple vanishing on
the exact finite Guinand--Weil square tests. In the even dictionary,
`s=0,1/2,1` maps to `z=+i/2,0,-i/2`; evenness merges the endpoints.
Directly from the Volterra definition, `g_v(0)=log(c)*v_0^2`, while the source
pole-square theorem makes `g_v(i/2)=0` exactly the pole-neutral linear row.
Thus the same-object coefficient subspace is `v_0=0` intersected with that
row, not the paper's moment-neutral condition.

Arb compression at `c=13`, `N=4,8,16` certifies positive total inertia on
dimensions `3,7,15`, with midpoint minimum scales about `1.40e-6`, `3.86e-14`,
and `7.42e-25`. The pole block vanishes exactly, but Gamma has one negative
direction near `-0.25` at every level and the prime block has growing negative
inertia with minimum midpoint reaching about `-5.47e4`. Triple vanishing
therefore does not produce separate positive kernels; only the full coupled
Gamma--prime cancellation remains, which is the constrained Weil sign itself.
An independent `c=29,N=8` run has the same outcome: positive total inertia,
two negative Gamma directions, and four negative prime directions.
See `docs/proofs/053_triple_vanishing_weil_probe.py` and
`docs/proofs/054_triple_vanishing_conditional_kernel_verdict.md`. No Lean owner
or consumer changed.

The coupled finite Weil source has an exact Loewner shape but rejects the
standard operator-monotone escape. If `psi_c` is its odd divided-difference
source and `Phi_c(x)=sqrt(x)*psi_c(sqrt(x))`, the positive-frequency even block
is twice the Loewner matrix of `Phi_c` on square nodes. Arb verifies this
identity on the `1^2,...,4^2` off-diagonal entries. Yet the same official
closed forms certify `Phi_c(1/4)>Phi_c(1)` by about `0.7641`, `1.3945`, and
`3.0139` at cutoffs `c=13,29,100`. Since operator-monotone and complete
Bernstein functions are scalar nondecreasing, no positive-measure Loewner
representation proves this source positive. Positive finite node matrices do
not contradict this continuous failure. See
`docs/proofs/055_loewner_bernstein_probe.py` and
`docs/proofs/056_loewner_bernstein_rejection.md`. No Lean owner changed.

The lattice-only Bernstein/Stieltjes fallback also fails before any spectral
claim. For `a_n=Phi_c(n^2)`, a discrete Bernstein measure would force ordinary
increments to decrease, while a positive squared-node Stieltjes measure would
force adjacent secant slopes in `n^2` to decrease. Arb proves both grow already
from nodes `1,2,3`. The square-secant growth is about `0.0042444`, `0.0025804`,
and `0.00084713` for `c=13,29,100`; all intervals are strictly positive.
An `N`-dependent rational Pick interpolant reconstructed after a positive LDL
is only an equivalent finite positivity certificate and supplies no common
arithmetic measure. See `docs/proofs/057_discrete_bernstein_probe.py` and
`docs/proofs/058_discrete_bernstein_rejection.md`. No Lean owner changed.

The fixed-cutoff band-growth Schur route is also rejected in its inverse-based
form. Reflection splits `Q_N` into nested even and odd blocks, so each new
frequency has scalar pivot `s_N=a_N-b_N^T A_(N-1)^-1 b_N`. Arb certifies all
tested pivots positive through `(c,N)=(13,16)` and `(29,8)`, but the inverse
correction cancels the new diagonal by up to 15 decimal orders. At `c=29,N=8`,
the even ratio `s_N/a_N` is about `1.10e-15` and the odd ratio is about
`1.82e-14`; pivots also oscillate with `N`.

Algebraically the parity blocks are Loewner matrices of
`Phi(x)=sqrt(x)psi(sqrt(x))` and, up to diagonal factors,
`Chi(x)=psi(sqrt(x))/sqrt(x)`. Their rank-two displacement identity holds for
arbitrary sign-indefinite sources and gives no positivity. Calling the Schur
pivot an RKHS residual norm assumes old-kernel positivity; the determinant
ratio is equivalent to the same PSD induction. No inverse-free arithmetic
square identity survived. See `docs/proofs/059_parity_schur_band_probe.py` and
`docs/proofs/060_parity_schur_inverse_rejection.md`. No Lean owner changed.

A source-backed pole-free constraint route survives the latest rejection
screen. Zenodo 20682834 proves the exact jump-Dirichlet-plus-potential identity
for `A_tilde=A_a-W_(0,2)` and an unconditional positivity-improving simple
ground state, but only numerically claims one negative even eigenvalue.
Same-object Arb compression shows that mean-zero `v_0=0` alone retains the
negative direction, while pole neutrality `<C,v>=0` alone removes it at
`(c,N)=(13,4),(13,8),(13,16),(29,8)`. The exact scalar is
`G(0)=<C,A_tilde^-1 C>`: Arb gives `G(0)` just below `-1/2`, whereas the full
critical quantity `1+2G(0)` is only `10^-15` to `10^-35`. Thus `G(0)<0` has a
stable sign margin and is a distinct intermediate target.

The soft mean-zero estimate using `min J` fails: Arb values of
`2aJ(2a)+kappa_a(0)` range from about `-2.81` at `c=5` to `-10.72` at `c=100`.
The active analytic gate is instead the zero-energy anti-maximum statement
`A_tilde^-1 C<0`, or an equivalent proof that `A_tilde` is nonnegative on
`C-perp`. Ordinary Perron theory does not imply it, and the continuum
index-one statement remains unproved. See
`docs/proofs/061_polefree_poincare_probe.py`,
`docs/proofs/062_polefree_constraint_resolvent_probe.py`, and
`docs/proofs/063_polefree_constraint_survivor.md`. No Lean owner changed.

The pole-free constraint candidate is now rejected as an executable lower
route. Its finite `G(0)<0` evidence remains correct, but no checked source
mechanism produces the continuum sign. The exact matrix
`A=[[-4,-1],[-1,1]]` with `C=(1,1)` is an irreducible Dirichlet form plus
bounded potential, has exactly one negative eigenvalue with positive ground
vector, and has positive `C`; nevertheless `A^-1 C=(-2/5,3/5)` and
`<C,A^-1 C>=1/5>0`, while the form is negative on `C-perp`. Thus
Dirichlet/Perron/index-one data are insufficient.

Suzuki Section 8 retains the nonlocal screw operator in the generalized
problem `G_a u=lambda(-Delta_N)^-1u`; its use of `lambda=0` explicitly begins
with `Assume RH`. Abstract anti-maximum principles work near a principal
spectral pole and cannot cross the whole first gap to zero. The remaining
continuum scalar is the pole-neutral Weil sign and is RH-level without a new
arithmetic identity. See `docs/proofs/064_polefree_antimax_rejection.md`. No
Lean owner changed.

2026-07-12 formal guard: `ConnesWeilRH/Dev/PolefreeAntimaxCounterexample.lean`
and its import audit mechanically prove the same countermodel. The declarations
show `A*Ainv=I`, `Ainv*C=(-2/5,3/5)`, `<C,Ainv C>=1/5>0`, while `v=(1,-1)` is
`C`-orthogonal and has `<v,A v>=-1`. The isolated WSL ext4 target
`ConnesWeilRH.Dev.PolefreeAntimaxCounterexampleAudit` passed under the repository
lock; its axiom output is only `propext`, `Classical.choice`, and `Quot.sound`.
This is a reusable rejection guard, not progress toward an RH producer.

2026-07-12 M2 source audit: a targeted search of 2025--2026 primary sources,
including Connes, *The Riemann Hypothesis: Past, Present and a Letter Through
Time*, arXiv:2602.04022, Sections 7.3--7.6, found no fixed-S measurable kernel
or square-integrable majorant for `P_hat Lambda P Lambda U_S(g)`. The survey
still presents the semilocal quotient/prolate construction as a strategy and
does not add the missing `X_S` quotient measure, complex `L2` carrier, cutoff
operators, or Hilbert-Schmidt theorem. See
`docs/proofs/066_fixed_s_kernel_latest_source_audit.md`. M2 remains blocked at
the concrete analytic owner; the abstract positive-trace layer is not being
rewritten to hide that premise.

The same search found a useful M3A reduction in Connes--van Suijlekom,
arXiv:2511.23257, Theorem 3.1: a continuous even compact-interval kernel gives
a Hilbert-Schmidt compact self-adjoint integral operator. It does not close
CC20 directly because `Qδ` contains the singular `-2δ_(rho=1)` principal term.
The next source-aligned target is the regular remainder `k_I`: prove its
measurability, square-integrable majorant, and kernel-action identity for
`K_I`. See the appended section in
`docs/proofs/066_fixed_s_kernel_latest_source_audit.md`.

2026-07-12 M3A fatal-implementation guard: the literal expression
`K_I(v,u)=Q delta(max(u/v,v/u))` cannot be used as an ordinary HS function
kernel. In logarithmic coordinates `Q delta` contains the `-2 Dirac_0` term,
which is already the essential `-2 Id` in CC20's quadratic-form identity. The
valid owner must define only the regular remainder `k_I` after subtracting that
distribution. See `docs/proofs/067_m3a_literal_qdelta_kernel_guard.md`.

The next diagonal death test did not reject the corrected M3A kernel. From the
explicit CC20 Sine-Integral formula, the regular side has finite limit
`8*pi^2/9 + Si(4*pi)/(4*pi) - 1/2`, approximately `8.39172410732812`, at
`rho=1+`. It is analytic away from the diagonal and bounded on every compact
ratio interval after continuous extension, so no local non-`L2` singularity
remains. See `docs/proofs/068_m3a_diagonal_regular_part_verdict.md`. The next
cheap rejection gate is the exact kernel-action and M0 same-object bridge.

The same-object audit is recorded in
`docs/proofs/069_m3a_same_object_bridge_audit.md`. No contradiction is known,
but no Lean bridge currently proves `F_g = Q(xi*xi*)` or
`D_infinity(F_g) = <xi,(-2 Id+K_I)xi>` on one common measured space. The route
remains pending; symbols/HEq/support equality cannot substitute for this
dependent analytic transport.

2026-07-12 harder M3A gate: the current `SelectedWeilSquareOwner` stores raw
`g* * g`, while CC20 M3A requires `Q(xi*xi*)`. The naive bridge is therefore
semantically false before kernel action is considered. A valid reopening needs
a genuine compact smooth Q-root owner whose square carries the Mellin factor
`t^2 + 1/4`; support equality or HEq by symbols is insufficient. See
`docs/proofs/070_m3a_q_image_owner_mismatch.md`.

2026-07-12 Q-root rejection-first gate: the old raw-square owner remains
invalid, but the natural candidate `g=(d/dx+1/2)xi` survives the first
algebraic test. Involution reverses the derivative, so
`(g* * g)=(-d+1/2)(d+1/2)(xi* * xi)=Q(xi* * xi)` on the compact convolution
domain. This does not prove finite-node/Mellin compatibility or the required
kernel-action theorem. See
`docs/proofs/071_m3a_q_root_algebraic_gate_survives.md`.

2026-07-12 Q-root Mellin gate: with
`laplaceAt(f,s)=integral exp(s*x)f(x)`, compact-support integration by parts
gives `laplaceAt((d+1/2)xi,s)=(1/2-s)laplaceAt(xi,s)`. The multiplier vanishes
at the route node `s=1/2`, but that node's desired value is already zero; the
other two route zeros are preserved. At the off-line detector `rho`, the
hypothesis `rho.re != 1/2` makes the multiplier nonzero, so finite-window
Mellin surjectivity can prescribe `(1/2-rho)^-1` before applying the root.
This rejects no candidate and leaves the compact-domain convolution identity
and same-object kernel action as the next hard gate. See
`docs/proofs/072_m3a_q_root_mellin_gate_survives.md`.

2026-07-12 M3A upstream-consumer death verdict: the Q-root survives the local
algebraic, support, normalization, and finite-Mellin gates, but this does not
reopen Plan 016. M3A/M4 only give a finite-codimension local remainder sign;
M5C still requires M5B's strict same-test source sign, hence the rejected P2
all-other-zero detector contract. That contract has an unresolved
radius/count cycle and becomes RH-level when combined with the CC20 exit.
Therefore no Q-root Lean implementation or `K_I` empirical stage is authorized
under Plan 016. See
`docs/proofs/073_m3a_upstream_consumer_death_verdict.md`.

2026-07-12 producer hunt selected a new research candidate: remove the full
functional-equation/conjugation orbit of one hypothetical off-line zero from
`completedRiemannXi`, tune the finite orbit values by a polynomial, inverse
transform the quotient, and then cut it off in physical space. The quotient
vanishes exactly at all non-target zeros before cutoff, so one summable
physical-tail estimate may replace Plan 023's circular nearby-radius/later-
threshold assembly. Existing Xi kernel, analytic-order, functional-equation,
and zero-counting infrastructure makes the first gates concrete. No lower
consumer or analytic tail theorem is yet proved, so Lean work remains denied.
See plan 025 and
`docs/proofs/074_canonical_xi_quotient_candidate.md`.

2026-07-12 Plan 025 Xi-kernel reduction: in centered log coordinates,
`psi(x)=exp(x/2)*completedRiemannXiKernel(exp(2x))` is even. Its first
derivative jump at zero is `-1`, so `psi''` contains `-delta_0`; the `+1` in
`completedRiemannXi=(u^2-1/4)completedRiemannZeta0+1` contributes the opposite
Dirac mass. Thus the centered Xi inverse is the ordinary function
`psi''-psi/4`. If `H(z)=0`, division by `s-z` has inverse
`exp(-zx)*integral_[x,infinity] exp(zy)phi(y)dy`; the zero moment also gives
the left-tail formula and cancels the homogeneous exponential. See
`docs/proofs/075_centered_xi_kernel_delta_cancellation.md`.

2026-07-12 Plan 025 convention/sign gates: centered variable `u=s-1/2`
aligns additive involution `u -> -conjugate(u)` with the source orbit
`s -> 1-conjugate(s)`. The current `logPullbackRaw=g(exp x)` is uncentered and
cannot be reused; a future owner must include the half-density factor. On the
four-point off-line orbit, assigning centered transform values `1,-1,0,0`
along the two involution pairs gives a strictly negative square zero-sum.
Multiplication by `u*(u^2-1/4)` adds the route zeros and stays nonzero on the
target orbit. See proof records 076 and 077.

2026-07-12 Plan 025 compact-cutoff reduction: if the iterated Xi-orbit
quotient inverse has uniform weighted derivative tails, integration by parts
gives cutoff error `C_(A,N)*(1+|t|)^(-N)` on the whole closed centered strip,
with `C_(A,N)->0`. At every non-target zero both square factors are errors, so
the zero contribution is quadratic and summable by the existing shell-count
consumer. Apply the multiplier `u*(u^2-1/4)` as a differential operator after
cutoff to impose triple vanishing exactly. This removes the old radius/count
cycle at the reduction level. See proof record 078.

2026-07-12 Plan 025 X5 mechanism: translating the canonical quotient inverse
`q_c(x)=q(x-c)` makes orbit evaluation rows exponential in `c`, while compact
M4 bad-space representatives produce decaying convolution rows. Analytic
continuation and two-sided translation tails give algebraic independence before
cutoff. Uniform conditioning after cutoff remains open because the M4 space
depends on the cutoff interval. See
`docs/proofs/080_canonical_xi_badspace_joint_separation.md`.

2026-07-12 Plan 025 X2 tail reduction: the centered theta series gives each
Xi-kernel derivative a bound of the form
`poly(exp(2|x|))*exp(-c*exp(2|x|))`. Dividing by one orbit zero via the ODE
`q'+zq=-phi` and the two zero-moment integral formulas preserves the same
two-sided superexponential class. Finite analytic multiplicity iteration is
therefore finite for each hypothetical zero. See
`docs/proofs/081_canonical_xi_quotient_tail_lemma.md`.

2026-07-12 Plan 025 lower-consumer death: the canonical Xi quotient can only
prove the converse Weil implication (an off-critical zero produces a compact
triple-vanishing test with negative `QW`). The active route's positivity input
is separate: `Route/Exhaustion.lean` requires `FixedSPositiveTraceReadOff`
inside `FullWeilPositivity`, and the CC20 exit consumes `hpositive` rather than
proving it. The M4 form `-2 Id + K_I` and its compact-control-space lemma do not
provide that sign. Plan 025 is therefore rejected as a lower producer; further
quotient-tail or conditioning work is research only unless a new independent
nonnegativity theorem is found. See proof 082.

2026-07-12 correction: proof 082 was too strong as a route verdict. The Xi
quotient need not prove global Weil positivity by itself. A possible lower
consumer is the existing fixed-interval CC20/M4 finite-codimension sign:
after choosing one cutoff interval, impose the finite bad-space orthogonality
rows on the same Xi quotient cutoff; compactness then makes `-2 Id + K_I`
strictly negative on the complement, while the quotient supplies the negative
Weil test and the source bridge supplies the opposite sign. This bypasses the
old radius/count cycle but leaves a real gate: joint orbit/bad-space separation
inside the smooth compact source algebra and exact same-square transport. See
`docs/proofs/083_xi_quotient_compact_badspace_rescue.md`.

2026-07-12 Plan 025 fixed-interval gate: the rescue reduces first to finite
joint functional separation on one bounded interval. The rows are three exact
Mellin-zero constraints, four removed-orbit values, and finitely many M4
bad-space inner products. Translation tails plus the Fourier identity theorem
give abstract independence, matching the repository's existing
`positive_interval_expanded_mellin_surjective_of_linear_dual_separation`
pattern. The next cheap death gate is whether all rows are defined on and
closed under the same centered smooth compact source test algebra. See proof
084.

2026-07-12 Plan 025 current-owner death: the abstract joint separation cannot
be instantiated in the present source API. `SourceTestAlgebra` has no additive
or scalar structure, so finite witness combinations do not produce source
tests. The only concrete carrier uses `convolutionStar f g = f + g`, and
`not_normalizedCC20MellinConvolutionLaw` proves this fails Mellin
multiplicativity (a value `1` squares to `2`, not `1`). Reopening requires a
genuine multiplicative, linearly closed source test carrier with the same trace
and Weil read-offs. See proof 085.

2026-07-12 successor design Plan 026: use `TestFunction = SchwartzMap ℝ ℂ`
directly, with additive-group convolution and reflection-conjugation
involution. This restores complex linear combinations for the Xi/M4 joint
constraints and removes the `f+g` Mellin defect. Required gates are Schwartz
convolution closure, centered Mellin multiplicativity, compact-support
transport, same-square prime/pole read-off, and CC20 trace transport. No Lean
route integration is authorized before these gates pass.

2026-07-12 Plan 026 carrier evidence: `Source/CCM25Concrete/CompactLogConvolution.lean`
already defines `CompactLogTest` with genuine integral convolution,
reflection-conjugation involution, compact-support closure, Hermitian square,
and nonnegative zero value. The blocker is API shape, not existence of the
carrier: `SourceTestAlgebra` demands a bijection with all Schwartz functions,
which no compact-support carrier can satisfy. Proof 086 records the required
split between an injective source encoding and explicit compact witness data.

2026-07-12 Plan 026 normalization gate: the existing theorem
`laplaceAt_compactLogTestOfWindow_eq_mellin` proves the raw log pullback/Mellin
identity by `t=exp(u)`. Centering the spectral variable with `u=s-1/2`
converts `s -> 1-conjugate(s)` to `u -> -conjugate(u)`; no additional pointwise
half-density factor is needed. The remaining issue is owner integration, not
normalization. See proof 087.

2026-07-12 Plan 026 multiplicativity gate: `CC20YoshidaConvolution.lean`
already proves `laplaceAt_convolution` by Fubini through
`MeasureTheory.integral_convolution`, plus the iterate power law. Together
with the Mellin pullback theorem, the genuine compact log carrier passes the
convolution/multiplicativity gate. Only the old full-Schwartz source API
integration remains. See proof 088.

2026-07-12 Plan 026 API escape: keep the existing full legacy equivalence by
 using the ambient `Test = TestFunction = SchwartzMap ℝ ℂ` with identity
 encoding and Mathlib's genuine Schwartz convolution. Carry compactness
 separately through `CompactLogTest` witnesses instead of making compact tests
 the carrier subtype. This preserves finite linear combinations; the new hard
 gate is explicit transport of the same convolution square into CC20/CCM25.
 See proof 089.

2026-07-12 Plan 026 carrier narrowing: `WeilFormSymbols` in `Basic.lean` already
uses `TestFunction = SchwartzMap ℝ ℂ` for `qw`, `psi`, and `convolutionStar`.
Therefore the ambient Schwartz escape does not require a route-type rewrite.
The remaining issue is reconstructing source arithmetic and CC20 trace data
with the genuine convolution on this same carrier. See proof 092.

2026-07-12 Plan 026 source-algebra probe: the existing
`AnalyticCore.SourceTestAlgebra` compiles with `Test := TestFunction`, identity
legacy equivalence, Mathlib Schwartz convolution, and reflection/conjugation
involution. No route-type rewrite is needed. The remaining owner is genuinely
mathematical: rebuild sourceNoDefectTrace, CC20 trace, and CCM25 arithmetic
read-offs for this same square. See proof 093.

2026-07-12 Plan 026 same-square transport: the WSL-verified ambient probe
proves `ambientConvolution f.test g.test = (f.convolution g).test` using
Mathlib's `SchwartzMap.convolution_apply`, the project's compact-log
convolution formula, and `MeasureTheory.convolution_def`. The carrier mismatch
is therefore removed at the function level. The remaining bridge is CC20 trace
amplitude plus CCM25 prime/pole read-off on that same encoded square. See proof
091.

2026-07-12 Plan 026 compiled carrier probe: `Dev/SchwartzAmbientOwnerProbe.lean`
defines the ambient `SchwartzMap ℝ ℂ` carrier, genuine Mathlib convolution,
reflection/conjugation involution, and proves the Fourier product identity.
The WSL ext4 verification run passes. This removes the type/API objection but
does not yet transport the same square into CC20/CCM25. See proof 090.

2026-07-12 Plan 026 death: `SourceFinitePrimeExactSupportData` quantifies over
all `F : A.Test` while requiring one finite exact prime-index carrier. With
`A.Test = SchwartzMap ℝ ℂ`, genuine prime translations are not finitely visible
for arbitrary noncompact Schwartz tests. The ambient convolution/type probe
therefore cannot become a genuine source owner under the current package. A
reopen needs cutoff-indexed finite support plus a proved prime tail, not merely
another convolution wrapper. See proof 094.

2026-07-12 scope correction to proof 094, then Plan 027 death: although
`ConcreteCCM25ArithmeticPackage W f lambda` is outerly per common test, its
`rows` field expands to `FixedLambdaArithmeticSourceTestCertificatesForAllTests
W`, restoring the universal ambient-test quantifier. Plan 027 is therefore
dead by proof 095. Plan 028 bypasses package rows entirely and targets a direct
fixed-detector `ExactSupportAtLambda` plus local QW formula.

2026-07-12 Plan 028 probe pass: a standalone `FixedDetectorWeilData` over
`WeilFormSymbols`, `ExactSupportAtLambda`, local QW/QW-lambda formulas, and pole
normalization compiles without `ConcreteCCM25ArithmeticPackage`,
`SourceRouteTraceData`, or `ForAllTests`. The fixed-detector consumer is
therefore type-level viable; filling its Xi source fields and CC20/M4 sign
bridge remains open. See proof 097.

2026-07-12 Plan 028 exact consumer audit: despite its name,
`SourceQWEqualsNegCC20WeilSum` contains no numerical QW/CC20 equality. The
actual sign theorem consumes a separately stored
`NormalizedRouteBackedYoshidaLocalSumReadOff`, whose equality is rewritten
directly against positive-trace nonnegativity. Therefore local arithmetic
certificates do not close the route; the fixed-test local-Weil-sum equals
negative-positive-trace theorem is the decisive M0/M3 bridge. See proof 098.

2026-07-12 Plan 028 inequality correction: the old exact
`NormalizedRouteBackedYoshidaLocalSumReadOff` is not a valid universal target;
CC20 has the nonzero `-2 Id + K_I` remainder. On the M4 control-space
complement, threshold `1` gives the strict bound `<= -norm(xi)^2`. The missing
theorem is a fixed-test inequality transporting this sign to the full QW while
keeping finite-prime and pole terms on the same square. Archimedean compactness
alone is insufficient. See proof 099.

2026-07-12 Plan 029 candidate: bypass noncompact finite-prime translation
operators at the one-test level by imposing exact autocorrelation zeros
`(g* * g)(±log n)=0` for every visible prime power. In a translated-bump frame,
the Xi orbit/triple-zero/M4 rows are linear in coefficients while each prime
condition is a finite Hermitian quadratic equation `c* A_n c=0`. The cheap
death gates are positive definiteness on the linear constraint kernel and a
new support-growth/count cycle. See proof 100 and Plan 029.

2026-07-12 Plan 029 convergence obstruction: translation autocorrelation is
continuous in `L2`. If compact quotient cutoffs `g_A -> q` exactly null
`<g_A,T_(log n)g_A>` for all large `A`, then the canonical quotient inverse
must itself satisfy `<q,T_(log n)q>=0`. Xi orbit divisibility gives no such
prime-log autocorrelation identity. Exact finite nulling therefore cannot be a
small correction to the quotient cutoff; Plan 029 is high risk before any
numerics or Lean. See proof 101.

2026-07-12 Plan 030 candidate: deform the quotient by
`H_new=H_rho+Xi*R*A`, with `R=s*(s-1/2)*(s-1)`. The correction is exactly zero
at every source zero and at the three route nodes, so it preserves the full
detector value pattern while changing critical-line density and prime-log
autocorrelations. Physical corrections are differentiated Xi-kernel
convolutions and may retain superexponential tails. The first death gate is independence of
the finite prime-moment derivative rows on controlled Xi-null directions; the
later risk is unbounded tail constants as visible primes grow. See proof 102.

2026-07-12 Plan 030 derivative gate: the first variations of finitely many
prime-log autocorrelations are independent on Xi-null directions. A linear
dependence would force `conj(H_rho)*Xi*R*sum c_j exp(i a_j t)=0` on the critical
line; the analytic prefactor has only discrete zeros and distinct exponential
frequencies are independent. Testing `A` and `iA` recovers complex separation.
Nonlinear reachability and uniform tail/type control remain open. See proof
103.

2026-07-12 Plan 031 linearization: write
`H_0=Xi*R*S/P_rho`. The formal null correction `-S/P_rho` has poles only at the
removed off-critical orbit, a positive distance from the critical line. Its
critical-line inverse Fourier transform therefore decays exponentially;
compact truncations give entire exponential-type `A_T` approximating it in
weighted Sobolev norms. Then `H_T=H_0+Xi*R*A_T` preserves every zeta-zero value
exactly while becoming small on the whole critical line, potentially
controlling all prime moments at once. The decisive gate is continuity of the
full QW/prime functional in the resulting form topology. See proof 104 and Plan
031.

2026-07-12 Plan 031 rational-tail gate: Hermite interpolation gives
`deg S < deg P_rho`, so the critical-line ratio is proper rational. Partial
fractions `c/(it-u_j)^k` have one-sided inverse Fourier transforms of the form
`x^(k-1) exp(-|Re u_j||x|)`. The off-line orbit supplies a positive minimum
rate `delta`; smooth physical truncation therefore gives entire exponential-
type approximants with exponentially small differentiated tails. See proof
105.

2026-07-12 Plan 031 prime-density death: a pole distance `delta` gives at best
`exp(-delta T)` Paley--Wiener error and `exp(-2 delta T)` autocorrelation error,
while absolute visible prime weight through log radius `T` grows as
`exp(T/2)`. The resulting bound `exp((1/2-2 delta)T)` fails for any hypothetical
off-line zero with `delta<=1/4`. Thus critical-line smallness alone cannot close
the full QW; structured prime cancellation is required. See proof 106.

2026-07-12 Plan 028 blast-radius audit: `Route/Bridge.lean` embeds
`ConcreteCCM25ArithmeticPackage` through the entire source-QW, finite-prime,
and exhaustion chain. A fixed-detector rescue needs a parallel
`FixedDetectorWeilData` record carrying only one square, exact support, local
pole/prime read-offs, and QW formula; piecemeal constructor patches would
reintroduce the broad `ForAllTests` premise. See proof 096.

2026-07-12 Plan 027 death: `ConcreteCCM25ArithmeticPackage` hides a universal
certificate. Its `rows` field expands to
`FixedLambdaArithmeticSourceTestCertificatesForAllTests W`, i.e. certificates
for every ambient `f,g` and every cutoff. The outer fixed detector parameters
do not remove this quantifier. Plan 028 therefore bypasses the package entirely
and targets a fixed-detector `ExactSupportAtLambda` plus local QW formula; the
next gate is whether the route consumer can accept that narrow certificate.

2026-07-12 Plan 028 local-owner evidence: `SelectedWeilSquareOwner` plus
`SelectedFinitePrimeSupportData.ofOwner` already constructs exact finite
prime-power sets for one compact convolution square, and
`SelectedWeilFormulaOwner` assembles pole, archimedean, restricted/global prime
terms, and `weilValue`. This bypasses the broad `ForAllTests` package. The
remaining missing theorems are source-QW read-off and the CC20/M4 same-square
inequality. See proof 107.

2026-07-12 Plan 028 spectral audit: the selected local owner completely defines
the pole, archimedean, and exact finite-prime `weilValue`, but no theorem in the
repository identifies it with the source-nontrivial-zero sum for the same test.
The zero-index module still calls this a future spectral-side explicit formula.
This same-square spectral identity is now the next analytic root, independent
of the rejected broad package. See proof 108.

2026-07-12 Plan 032 normalization verdict: Burnol's unconditional compact-test
explicit formula matches `SelectedWeilFormulaOwner` exactly under
`g(u)=u^-1/2 f(log u)`. The pole evaluations become the selected Laplace values
at `+/-1/2`, and the finite local terms become the owner's von
Mangoldt-weighted `n^-1/2[f(log n)+f(-log n)]`. At infinity, the apparent
integrand difference integrates to `-2 log(2)f(0)` and cancels the owner's
`log(4)` constant shift. The spectral theorem is therefore a valid classical
target, not a sign or normalization mismatch. The current Lean stack has no
ready Xi Hadamard/log-derivative zero expansion or residue theorem closing the
contour proof, so formalization is substantial. More importantly, it still
does not close Plan 028: M4 controls only the archimedean remainder, while a
growing Xi-quotient cutoff sees finite primes and needs an unproved same-object
finite-S sign. The next death gate is a prime-free fixed-window detector or a
correct all-prime-power semilocal subtraction. See Plan 032 and proof 109.

2026-07-12 Plan 030 exact-null death: a nonzero compactly supported log test
has a finite-exponential-type bilateral Laplace transform and therefore only
`O(T)` zeros in a disk of radius `T`. A function divisible by completed Xi would
contain `Theta(T log T)` nontrivial zeta zeros by the Riemann--von Mangoldt
count. Hence an exact compact `Xi*R*A` correction is identically zero. The
noncompact deformation remains mathematically meaningful, but any physical
cutoff loses exact zero preservation and must pay the full quantitative
prime/tail error. Proof 110 rejects Plan 030 as an executable exact-null route;
proof 103 remains only a local derivative fact.

2026-07-12 Plan 033 log-Poisson screen: the positive operator
`L_p=2 log(1+p^-1/2)I-log((I-p^-1/2U_p)^*(I-p^-1/2U_p))` has the exact
`p^-m/2/m` Fourier series and therefore repairs the endpoint projection's
coefficient algebraically. Its square-root half-line block has a positive
trace, but that trace is a continuous quadratic Hankel energy of the
square-root kernel, not the linear discrete Weil prime-power evaluations.
Using `L_p` linearly retains the atoms but leaves infinite bulk and loses
positivity. Proof 111 rejects this shortcut as a lower owner; a different
same-object factorization would be required.

2026-07-12 Plan 032 source audit: the original CCM24 paper
(arXiv:2310.18423v2, `mainc2m24fine.tex:186-201, 761-804, 934-1032`) proves
semilocal cyclic-pair and Sonin-space transport, but explicitly presents
semilocal Weil positivity as a program and defers a second semilocal prolate
operator. It contains no fixed-S inequality `QW_S >= positive trace` and no
post-Q finite-S remainder sign. Proof 112 records this as a source gap; the
transport theorems cannot be used as a lower producer.

2026-07-12 Plan 035 prime-free death: on the M4 bad-space complement, the
corrected prime-free identity gives
`PositiveTrace=QW+D_infinity` with `PositiveTrace>=0` and
`D_infinity<=-||xi||^2`; hence `QW>=||xi||^2>0` for every nonzero root. A
negative Xi detector cannot survive the proposed finite bad-space
orthogonalization. This rejects proof 083's prime-free rescue and the first
branch of Plan 032. Plan 028 now has only one mathematical branch: a genuinely
semilocal finite-S same-object remainder theorem, which CCM24 does not supply.
See proof 113.

2026-07-12 Plan 036 route verdict: Plan 028 is rejected as an executable RH
route. The same-square arithmetic owner and Burnol normalization pass, but the
prime-free M4 branch is impossible, the endpoint metric projection doubles the
`p^2` atom, exact compact Xi-null directions are impossible, the positive
log-Poisson shortcut loses the linear read-off, and CCM24 supplies no finite-S
sign theorem. Reopening requires a genuinely new same-object finite-S positive
trace whose noncompact `p^m` channel has coefficient `p^-m/2/m` before crossing
length and whose remaining post-Q operator is `-2 Id+compact`. No route Lean is
authorized. See proof 114.

2026-07-12 Plan 037 multiplier screen: radial differentiation of
`2 log(1+p^-1/2)I-log((I-p^-1/2U_p)^*(I-p^-1/2U_p))` produces a positive
multiplier with the exact final prime-power coefficients. Its scalar
compensation is sharp: `2 log(p)/(sqrt(p)+1)` per prime. Rational independence
of prime logarithms lets all phases approach `pi` simultaneously, forcing the
compensations to add and diverge over cofinal finite-prime sets. Direct
translation-multiplier positivity is therefore rejected; only a
non-translation-invariant boundary cancellation could reopen Plan 036. See
proof 115.

2026-07-12 Plan 038 factorization screen: the positive symbol
`log|1-p^-1/2U_p|^2-2log(1-p^-1/2)` has exact negative Weil Fourier
coefficients. Factoring it as `B_p*B_p` and taking a positive half-line cross
trace introduces the extra boundary term `P B_p* P B_p P`. A compact test square
with support below `log(p)` has zero finite-prime atom but a strictly positive
cross norm, so the linear read-off is false. Proof 116 rejects this shortcut;
the extra boundary term must be controlled by a new identity, not dropped.

2026-07-12 Plan 039 positive-difference death: the exact decomposition into
`(I-U_p^m)^*(I-U_p^m)` factors reads the desired negative prime atom but forces
the scalar compensation `C_p=2log(p)p^-1/2/(1-p^-1/2)`. Already
`C_2 approximately 3.346>2`, so the one-prime post-Q essential scalar becomes
positive rather than `-2+compact`. Finite-dimensional conditioning cannot
remove it. Proof 117 rejects the termwise positive difference route before
numerics or Lean.

2026-07-12 Plan 040 compact-boundary no-go: any positive half-line owner that
looks like `P(cI+V_S(D))P+K` with compact/boundary-local `K` retains the prime
multiplier's essential lower symbol. Long wave packets translated away from the
boundary converge to a frequency Weyl sequence and make `K` disappear, forcing
the same divergent scalar compensation from Plan 037. Compact Schur/Hankel/
Wiener-Hopf corrections therefore cannot reopen the route. Only a genuinely
noncompact pre-read-off cancellation remains conceivable. See proof 118.

2026-07-12 Plan 041 Fredholm/Fock death: the formal Euler logarithm has the
right `1/m` coefficients, but raw `U_p` and `Q U_p P` are infinite-rank and
not trace class, so their Fredholm/bosonic determinants are undefined. Smoothing
allows only regularized `det_2`, which drops the `m=1` channel and replaces raw
translation powers by test-dependent powers. Proof 119 rejects this
noncompact-cancellation shortcut.

2026-07-12 Plan 042 higher-Q death: CC20's `Q` is the minimal
support-preserving filter whose pole-node multiplier zeros turn the single cusp
jump into `-2 delta`. Higher differential polynomials create delta derivatives
and unbounded root-derivative energies, not `-c Id+compact`; scalar rescaling
scales prime and archimedean terms together. Proof 120 rejects using a higher
Q filter to absorb finite-prime compensation.

2026-07-12 Plan 043 adelic screen: the sharp positive prime compensation
`2log(p)/(sqrt(p)+1)` cannot be canceled by Burnol's allowed global character
renormalization. Principal shifts are `v_p(q)log(p)` with integer valuations
and total zero by the product formula. Real local exponents would break
principal-idele self-duality and change the explicit formula. Proof 121 rejects
adelic scalar cancellation as a route mechanism.

2026-07-12 Plan 044 Clifford screen: anticommuting prime channels cancel mixed
words algebraically, but any positive Gram realization of the signed first
prime couplings is constrained by `c >= w^T C^-1 w`. A zero spinor state loses
the linear atoms; a state retaining them pays the Schur diagonal cost. Since
 `sum_p log(p)^2/p` diverges, the cofinal finite-S shortcut is rejected. See
 proof 122.

2026-07-12 Plan 045 negative spectral projection screen: a new finite Jacobi
probe evaluated the source-shaped one-sided negative-prolate trace with a
Schwartz multiplier. For `lambda=1, tau=0.10`, the p=2 minus archimedean trace
difference oscillates across section sizes 128--512 (about `1.03e-4` to
`1.43e-4`), while every negative eigenvector carries order-one tail mass in
the final basis quarter. This is boundary-pollution evidence, not convergence
or a Weil read-off. No Lean owner is authorized. The only admissible spectral
reopening remains a common self-adjoint semilocal projection with exact
same-test Weil read-off and `p^(-m/2)/m` coefficient before the crossing
length. See proof 123 and `docs/proofs/123_semilocal_negative_projection_probe.py`.

2026-07-12 Plan 046 same-range uniqueness no-go: every bounded positive owner
of the form `T_S R phi(A_S) R T_S*` has bulk
`Tr(C A_S phi(A_S) R)`. Requiring the exact archimedean bulk at the operator
owner level forces `phi(A_S)=A_S^-1`, hence uniquely recovers the rejected
metric Sonin projection. Another positive weight leaves a noncompact
multiplier bulk, while finite-rank or compact range corrections cannot repair
the excess noncompact `p^2` single crossing. A viable finite-S owner must now
use a genuinely different noncompact range and prove its same-object trace
identity from scratch. See proof 124.

2026-07-12 Plan 047 Suzuki screw-kernel screen: arXiv:2606.09096 supplies a
genuine unconditional compact self-adjoint owner `G_a`, the identity
`QW_a(v)=<G_a Dv,Dv>`, and continuity of the localized ground value. The same
continuity theorem makes all-`a` zero-energy injectivity RH-equivalent: if RH
fails, a first crossing has `ker(G_a) != {0}`. Kernel continuity does not prove
injectivity of this first-kind equation, and projection to zero mean leaves a
two-sided prime-delay equation rather than a Volterra triangularization.
Freedman's normalized Volterra certificate still omits the quotient lift,
uniform parameter coverage, and final RH bridge. No Lean owner is authorized.
See proof 125.

2026-07-12 same-square defect-dominance first gate: the new candidate in proof
126 was tested at `S={infinity,2}` on the endpoint metric Sonin owner. Its
factor-two `p^2` mismatch leaves one excess atom
`E_2(h)=log(2) F_h(2 log(2))`. A normalized compact `C-infinity` bump of radius
two has overlapping positive support at that shift, so `E_2(h)>0` exactly; the
WSL2 probe gives `F_h approximately 0.52811915` and
`E_2 approximately 0.36606430` from 4096 through 131072 grid points. Thus this
defect is not a vanishing cutoff tail for the same-range endpoint owner. The
abstract candidate remains open only for a genuinely different noncompact
range with a new same-object identity. No Lean owner is authorized. See proof
127 and `docs/proofs/127_same_square_p2_defect_probe.py`.

2026-07-12 Euler-log graph projection screen: a genuinely different
noncompact range was constructed from
`L_a=Q sum_(m>=1) a^m U^m/m P`. Its orthogonal graph projection is positive and
passes the `p^2` gate: the two second-order diagonal traces cancel for an even
translation-invariant same-square test, leaving the correct `1/2` coefficient.
At order `a^3`, however, graph normalization adds
`-L_1 L_1* L_1=-QUP` on an infinite-dimensional interval subspace, producing
the wrong crossing length. Prescribing the exact Euler-log off-diagonal block
cannot repair this: every projection off-diagonal has norm at most `1/2`,
while at `p=2` disjoint translated intervals give norm strictly greater than
`1/sqrt(2)`. The candidate is rejected; no Lean owner is authorized. See proof
128 and `docs/proofs/128_euler_log_graph_projection_probe.py`.

2026-07-12 positive-owner batch screens: three ways to bypass the projection
`1/2` norm bound were rejected in proof 129. A Schur-positive block forces a
`K*K` diagonal bulk, two ancillas merely add that PSD cost, and the norm-
compressed `tanh` block changes the `U^3` coefficient from `1/3` to `-1`.
Random boundary averaging (proof 130) leaves the `m log(p)` crossing coefficient
unchanged; random crossing-scale averaging would require incompatible masses
`1/m` for every `m`. Finally, a positive Poisson-kernel mixture (proof 131)
would require moments `a^m/m`; moment uniqueness forces the measure `dt/t`,
whose total mass at zero is infinite. No finite positive owner survives this
batch, and no Lean declaration is authorized.

2026-07-12 boundary-potential absorption screen: replacing vanishing defect by
an archimedean graph-norm inequality gives the first partial pass. For one
prime `p=2`, the generalized eigenvalue of the boundary potential
`V_2(x)=sum_{m>=ceil(x/log 2)} 2^(-m/2)/m` against
`|h'|^2+|h|^2/4` is about `0.44`, below one. The same probe gives `0.889` for
`{2,3}`, `1.318` for `{2,3,5}`, and `2.111` for `{2,3,5,7,11}`. Analytically,
for a fixed bump supported in `(0,delta)` with `delta<log 2`, the defect is
bounded below by `sum_{p in S} p^(-1/2) ||h||^2`, while the graph norm is fixed;
the cofinal owner therefore fails. Disjoint prime windows only remove cross
terms and retain the additive Schur costs. See proof 132 and
`docs/proofs/132_boundary_potential_absorption_probe.py`.

2026-07-12 shared Brownian-Gram candidate: replacing independent prime
channels by one nested half-line channel gives `C_ij=min(log p_i,log p_j)` and
weights `w_i=p_i^(-1/2)`. The exact Brownian inverse formula is
`w^T C^(-1)w = w_1^2/b_1 + sum (Delta w_i)^2/Delta b_i`. With
`w(b)=exp(-b/2)`, secant Cauchy-Schwarz yields the cofinal bound
`1/(2 log 2)+1/8 = 0.846347... < 1`. Direct computations for 1, 5, 20, 80,
and 120 primes agree and approach `0.846`. This is the first candidate to pass
the cofinal Schur-cost gate. Remaining bottoms are a same-square boundary-data
Gram estimate and a trace read-off without mixed-prime terms. No Lean owner is
authorized yet. See proof 133 and `docs/proofs/133_shared_brownian_gram_probe.py`.

2026-07-12 shared-Gram same-object death: the actual crossing Gram is
`G_ij(h)=min(log p_i,log p_j) F_h(log p_i-log p_j)`, not the ideal Brownian
matrix. A compact smooth test with support width `<log(3/2)` makes all mixed
autocorrelations vanish for `{2,3,5}`, while retaining the finite-codimension
pole constraints. The Schur cost then becomes
`sum_{p in {2,3,5}} 1/(p log p)=1.149027...>1`. Thus proof 133's bounded
`0.846` cost is only an ideal model and cannot be used for a same-square owner.
See proof 134.

2026-07-12 support-aware boundary screen: restricting the defect to visible
prime powers `m log(p)<=lambda` removes the artificial cofinal fixed-test
divergence, but the local graph-norm generalized eigenvalue still grows past
one: approximately `0.581` at `lambda=2`, `1.706` at `lambda=3`, `3.734` at
`lambda=4`, and `22.03` at `lambda=7`. This is numerical screening rather than
an analytic no-go because the true mixed autocorrelation Gram may lower the
bound. Do not add a Lean owner without a uniform estimate or an exact mixed-Gram
bound. See proof 135 and `docs/proofs/135_visible_boundary_absorption_probe.py`.

2026-07-12 actual mixed-Gram adversarial screen: the exact Gram
`min(log p,log q)F_h(log p-log q)` can lose its shared discount for real compact
oscillatory factors. With `h=bump_lambda*cos(kx)`, the `{2,3}` cost at
`lambda=1.4` rises from `0.741` at `k=0` to `1.253` at `k=5` and `1.453` at
`k=10`; at `lambda=3`, eight visible primes give costs near `4.9`. This is
still a numerical screen until finite pole-node constraints are imposed, but
it blocks any unconditional mixed-Gram discount argument. See proof 136 and
`docs/proofs/136_actual_mixed_gram_probe.py`.

2026-07-12 shared mixed-Gram route NO-GO: four disjoint compact smooth bumps
with centers `0.05,0.52,1.12,1.75` and small radius have support width above
`log 5`, while their support differences avoid
`log(3/2),log(5/3),log(5/2)`. Rank-nullity supplies a nonzero vector satisfying
the finite pole rows. Its autocorrelations at all three prime-ratio shifts are
exactly zero, so the same-object `{2,3,5}` crossing Gram is diagonal and the
minimum Schur cost is
`1/(2 log 2)+1/(3 log 3)+1/(5 log 5)=1.149027...>1`. This is a route-level
NO-GO for the shared mixed-Gram positive owner, not a claim that RH is
impossible. See proof 137 and
`docs/proofs/137_pole_neutral_decorrelated_bump_probe.py`.

2026-07-12 compact bad-space evaluation-span consumer admitted to Lean. The
new theorems
`mem_controlSpace_orthogonal_of_le_evaluationSpace` and
`exists_finiteDimensional_remainder_nonpositive_on_evaluationSpace` prove that
if an evaluation space contains the finite compact-remainder control space,
then its vanishing subspace inherits the nonpositive `K-threshold*Id` form.
The API uses only compactness, a positive threshold, and submodule containment;
it imports no RH or Weil-positivity premise. The smallest source build and
import-facing Dev audit pass in an isolated WSL2 ext4 snapshot, with only
`propext`, `Classical.choice`, and `Quot.sound`. The remaining concrete producer
is the CC20 containment of the control space in the span of the three
evaluation kernels. See proof 138.

2026-07-12 sine-integral regular-kernel foundation: Mathlib's `Real.sinc` and
interval-integral FTC support an axiom-clean `sineIntegral` object. A second
object, `sineIntegralQuotient x = integral_{0..1} sinc(x*t)`, gives a continuous
extension of `Si(x)/x` without hiding a removable singularity. The source and
import-facing audit pass in the isolated WSL2 ext4 snapshot with only
`propext`, `Classical.choice`, and `Quot.sound`. This does not yet prove the
explicit `Q`-regular kernel, its Hilbert-Schmidt bound, or the CC20
evaluation-span containment. The nonzero quotient identity is now proved by
interval-integral change of variables, and `deriv_sineIntegral` now gives the
FTC derivative `Real.sinc`. The nonzero quotient derivative is also now proved
by local equality and the quotient rule. See proof 139.

2026-07-12 second differential layer: `hasDerivAt_sinc_of_ne_zero` and
`hasDerivAt_deriv_sineIntegralQuotient` are now proved for nonzero points.
The second derivative uses the FTC derivative of `sineIntegral`, the quotient
rule, and the derivative of `x^2`; its audit remains standard Mathlib axioms.
This still does not give the full second derivative of `cc20DeltaRegular` or a
`K_I` kernel action identity. See proof 141.

2026-07-12 CC20 delta regular profile candidate: `cc20DeltaRegular` now uses
the continuous `Si(x)/x` extension to define the ordinary pre-Q scaling
profile and proves it continuous in Lean. This is intentionally separate from
the route API. Applying `Q`, proving a measurable square-integrable kernel, and
proving its action identity remain open. The same module now proves the full
pre-Q derivative on `1 < rho` by chain and product rules. The WSL2 import audit
is axiom-clean. An explicit non-diagonal algebraic `cc20QDeltaRegularCandidate`
is now recorded from the first and second profile derivatives; its equality to
the differential operator and its kernel action remain open. See proof 140.

The first-order portion is also exposed as
`deriv_cc20DeltaRegular_of_one_lt`, proving the explicit derivative profile is
Lean's actual `deriv` on `1 < rho`.

`hasDerivAt_inv_sqrt` now proves the positive-domain derivative
`(1/sqrt rho)'=-1/(2*rho*sqrt rho)`, leaving only the composite quotient
second-derivative transport and final product-rule assembly for the full
`cc20DeltaRegular` second derivative.

`hasDerivAt_siQuotientDerivativeProfile_comp` now supplies the reusable
second-order chain rule for any differentiable inner function whose value is
nonzero, so both CC20 affine branches share one audited proof.

2026-07-12 Q-delta differential identity: the branch-sum first and second
derivatives, full `cc20DeltaRegular` second derivative, and
`multiplicativeQ_cc20DeltaRegular_of_one_lt` are now proved in Lean. Thus the
explicit `cc20QDeltaRegularCandidate` is the actual multiplicative-coordinate
`Q(delta)` on `rho > 1`, not merely a symbolic formula. This remains a
one-variable non-diagonal scalar result; measurability, square-integrability,
the diagonal Dirac split, and the CC20 two-variable kernel action are open.
See proof 142.

2026-07-12 two-variable regular kernel: `ratioRadius=max(u/v,v/u)` is now
defined on positive coordinates and proved continuous, symmetric, at least
one, and equal to one exactly on the diagonal. `cc20RegularKernel` uses the
source-backed finite diagonal value and the proved non-diagonal Q-delta
formula; it is measurable and symmetric with explicit diagonal/off-diagonal
read-offs. A global Haar-plane Hilbert-Schmidt claim is false because the
ratio-only kernel is invariant under common scaling. The correct next domain
is CC20's fixed `sqrt(I) x sqrt(I)`, with `I` contained in `(1/2,2)`. The
diagonal limit and compact-domain square-integrability proofs remain open.
See proof 143.

2026-07-12 diagonal series check: symbolic expansion of the explicit
non-diagonal Q-delta formula at `rho=1+e` is
`8*pi^2/9 + Si(4*pi)/(4*pi) - 1/2 + (4*pi^2-1)e + O(e^2)`, matching the
source-backed diagonal extension exactly. This is only a calculation guide;
the Lean finite-order Taylor/limit proof is still missing. See proof 144.

The first zero-order regularity layer is now proved: positive and negative
`sinc` slope bounds imply `hasDerivAt_sinc_zero` with derivative zero. The
remaining diagonal limit still needs higher-order quotient data.

2026-07-12 diagonal limit closed axiom-clean: two L'Hopital reductions prove
`hasDerivAt_deriv_sinc_zero` with value `-1/3`, then the corresponding
integral-average profile has second derivative `-1/9` at zero. The explicit
second-derivative profile is algebraically decomposed on the punctured
neighborhood as `sinc'(x)/x - 2*(sin x - Si(x))/x^3`, yielding its limit
`-1/9`. `sineIntegralQuotientSecondDerivativeExtension` fills the removable
point and is continuous. The continuous Q-delta candidate now evaluates at
`rho=1` to exactly `8*pi^2/9 + Si(4*pi)/(4*pi) - 1/2`; the original candidate
has a proved right-hand limit to that value. On the actual positive-coordinate
domain, `ratioRadius >= 1`, so the scalar extension is continuous on `Ici 1`
and `cc20RegularKernel` is continuous at every diagonal point. Import-facing
WSL audits remain limited to `propext`, `Classical.choice`, and `Quot.sound`.
This still does not prove square-integrability, the CC20 kernel action, the
`K_I` trace read-off, or RH.

2026-07-12 compact rectangle L2 gate: fixed the concrete interval
`cc20SqrtI = [1/2,2]` in positive coordinates (corresponding to
`I=[1/4,4]`) and its product rectangle. `continuousOn_cc20RegularKernel_sqrtIRectangle`
uses the already proved scalar `Ici 1` continuity and `ratioRadius >= 1`.
The interval is represented by `x |-> <max x (1/2), positivity>`. Since the
open positive subtype has no canonical `volume` MeasureSpace, the honest L2
statement is made in the real coordinates carrying standard product volume:
`integrableOn_cc20RegularKernelReal_sq_sqrtIRectangle`. This is the analytic L2
gate for the same ordinary regular kernel, not yet the kernel-action identity
or the source trace owner.

2026-07-12 same-object L2 owner: `RegularKernelL2Data` binds the real
coordinate kernel, compact domain, kernel/domain equalities, and the proved
square-integrability field in one structure. Its finite square-integral theorem
is audited without storing an operator action or Hilbert--Schmidt conclusion.
This is an owner boundary for the next operator construction, not an RH route
consumer.

2026-07-12 integral-average zero regularity: `sinc_diff_bound_unit` gives the
uniform bound `|sinc x - 1| <= x^2/4` on `|x| <= 1`. Integrating this bound over
`t in [0,1]` proves `sineIntegralQuotient_sub_one_bound`; the interval-integral
subtraction must be supplied explicitly with `intervalIntegral.integral_sub`
and `volume` annotations. The resulting squeeze proof establishes
`hasDerivAt_sineIntegralQuotient_zero : HasDerivAt sineIntegralQuotient 0 0`.
The WSL2 import audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. This is still only scalar diagonal-limit groundwork; no `K_I`
operator, two-variable action identity, or unconditional RH proof exists.
2026-07-12 compact-interval operator: `continuousAt_cc20RegularKernel` and
`continuous_cc20RegularKernel` lift the ordinary ratio kernel from the compact
rectangle to the full positive-coordinate plane. The real-coordinate kernel
is continuous after the `max(x,1/2)` positivity map. A fixed interval operator
`cc20RegularKernelIntervalOperator` is defined by integrating the same kernel
over `[1/2,2]`; parametric interval-integral continuity proves continuous
outputs for continuous inputs. `cc20RegularKernelContinuousLinearMap` packages
the operator on `ContinuousMap ℝ ℝ`, with audited additivity and scalar
homogeneity. The construction remains below the CC20 source action: it does
not prove an `L2` extension, Hilbert--Schmidt estimate, `K_I` identity, trace
read-off, or RH. See proof 148.

2026-07-12 compact operator norm bound: the interval `[1/2,2]` is now a
compact subtype, the same ordinary kernel is packaged as a compact-domain
`ContinuousMap`, and its integral action on continuous functions satisfies
the explicit supremum-norm estimate `||T f|| <= (3/2)||K||||f||`.
`cc20CompactContinuousLinearOperator` is therefore a genuine
`ContinuousLinearMap`. The clamp used to totalize the real-variable integrand
is proved equal to the original variable on the integration interval. This
still does not establish an `L2` bound, Hilbert--Schmidt extension, CC20 `K_I`
action identity, trace read-off, or RH. See proof 149.

2026-07-12 compact interval measure: `cc20CompactMeasure` is the explicit
subtype measure `Measure.comap Subtype.val volume` on `[1/2,2]`. Lean proves
its total mass is exactly `ENNReal.ofReal (3/2)` and registers it as a finite
measure. This is the measure parameter for the forthcoming `ContinuousMap.toLp`
and `L2` estimate; it does not yet provide that estimate or an RH consequence.
See proof 150.

2026-07-12 L2 kernel-section prelude: every fixed-output section
`y |-> cc20RegularKernelReal(x,y)` and every continuous compact-interval input
is now proved `MemLp ... 2 cc20CompactMeasure`. The section's continuous
supremum norm is bounded by the same compact two-variable kernel norm. These
are the exact premises for the pending Holder/Cauchy--Schwarz operator bound;
the full `L2 -> L2` extension and RH remain open. See proof 151.

2026-07-12 L2 Holder layer: on `cc20CompactMeasure`, the same kernel section
and continuous input satisfy a formal pointwise Holder estimate. The square
root input factor is identified with `lpNorm f 2` and with the norm of
`ContinuousMap.toLp 2 cc20CompactMeasure ℝ f`. The output integral is proved
continuous in its compact output coordinate, additive, and homogeneous, and
`cc20CompactMeasureToLpLinearMap` maps continuous inputs into `Lp ℝ 2`.
The remaining bottom is the global output `L2` norm estimate needed by
`LinearMap.extendOfNorm`; no full `L2` extension, CC20 action identity, or RH
result exists yet. See proof 152.

2026-07-12 L2 extension closed: the pointwise Holder bound was made uniform
using the compact kernel supremum and the two square-root interval-mass
factors, giving a global `L2` norm estimate. `ContinuousMap.toLp_denseRange`
and `LinearMap.extendOfNorm` now construct the genuine same-kernel operator
`cc20CompactL2Operator : Lp ℝ 2 cc20CompactMeasure →L[ℝ] Lp ℝ 2
cc20CompactMeasure`, with an audited agreement theorem on every continuous
input. This is an analytic operator owner only; the CC20 source action,
Hilbert--Schmidt trace read-off, arithmetic terms, and RH remain open. See
proof 153.

2026-07-12 compact-kernel symmetry: the compact real-coordinate kernel on
`[1/2,2] × [1/2,2]` is now proved symmetric by explicit transport through the
positivity clamp and the positive-coordinate ratio-kernel symmetry theorem.
This is only the kernel symmetry prerequisite for a possible self-adjointness
proof; it does not identify the operator with CC20 `K_I` or provide a trace
read-off. See proof 154.

2026-07-12 L2 symmetry closed: the bilinear kernel is integrable on the
compact product, and `integral_integral_swap` proves the continuous-input
double-integral symmetry. `ContinuousMap.inner_toLp` transfers this to the
dense L2 subspace, and `DenseRange.induction_on₂` extends it to all inputs:
`inner ℝ (cc20CompactL2Operator u) v = inner ℝ u
(cc20CompactL2Operator v)`. This is an axiom-clean symmetric operator owner,
but not yet a Hilbert--Schmidt trace owner or CC20 `K_I` source action. See
proof 155.

2026-07-12 same-measure kernel L2 gate: `cc20CompactRegularKernel` is now
proved `MemLp ... 2` on the exact product measure
`cc20CompactMeasure.prod cc20CompactMeasure`, its squared norm is integrable,
and Fubini identifies the product square integral with the iterated section
integral. This removes the measure mismatch before Hilbert--Schmidt Parseval;
the remaining bottom is `sum_i ||T e_i||^2 = integral |K|^2`. See proof 156.

2026-07-12 real Hilbert--Schmidt summability: the compact operator now has the
full-`L2` kernel coefficient representation
`cc20CompactL2Operator u = toLp (x |-> inner u K_x)`. For every real Hilbert
basis, finite sums of `||T e_i||^2` are bounded by the integral of the squared
`L2` norms of the same kernel sections. Pointwise Bessel inequality and
`summable_of_sum_le` therefore prove
`cc20CompactL2Operator_basis_normSq_summable`. This closes genuine real
Hilbert--Schmidt summability without an RH or Weil-positivity premise. The
project's positive-trace interface is complex, so a legal complex same-kernel
operator or complexification remains necessary; the exact product-kernel
Parseval equality and CC20 `K_I` action identity also remain open. See proof
157.

2026-07-12 real Hilbert--Schmidt Parseval identity: the section energy is now
proved equal to the squared regular-kernel integral on the exact product
measure. For arbitrary real Hilbert bases, the operator `tsum` is bounded by
that product energy. For every countably indexed real Hilbert basis,
`cc20CompactL2Operator_basis_normSq_eq_product_kernel_energy` proves the exact
identity `sum_i ||T e_i||^2 = integral ||K||^2`. The proof uses the full-`L2`
kernel coefficient representation, pointwise Hilbert-basis Parseval, the
already proved summability to justify integral/`tsum` exchange, and Fubini.
No RH or Weil-positivity premise enters. A complex same-kernel operator and the
source CC20 `K_I` action/read-off remain open. See proof 158.

2026-07-12 complex Hilbert--Schmidt positive trace: the same ordinary real
regular kernel is now lifted pointwise to a complex kernel and defines the
genuine complex-linear operator
`cc20CompactComplexL2Operator : Lp C 2 ->L[C] Lp C 2`. The linear orientation
is `inner K_x u`, not `inner u K_x`; the latter would be conjugate-linear.
For continuous inputs, Lean proves the explicit integral formula with
`(cc20CompactRegularKernel (x,y) : C) * f y`. Complex Bessel inequality gives
summability on every complex Hilbert basis, and
`cc20CompactComplexBasisHilbertSchmidtData` now directly inhabits the existing
`PositiveTrace.BasisHilbertSchmidtData` consumer. Its positive composition has
an ordinary trace with nonnegative real part. This closes complex
Hilbert--Schmidt/positive-trace legality for the regular kernel, but not the
source CC20 `K_I` action, Dirac split, trace read-off, or RH. See proof 159.
