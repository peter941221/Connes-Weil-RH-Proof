# AGENTS.md

This file is the project-local operating rule for
`Connes-Weil-RH-Proof`. It overrides global defaults inside this repository.
Read this file and `MEMORY.md` before starting a new lane.

## 1. Project Target

The only final target is an unconditional Lean proof of:

```text
_root_.RiemannHypothesis
```

A manuscript, theorem contract, route certificate, source package, selected
test, or axiom-clean theorem about a weak model does not meet that target.

Correctness order:

```text
statement has enough semantics
  -> producer is genuinely lower than the consumer
  -> Lean proof is axiom-clean
  -> active RH route consumes the stronger result
```

Before accepting a lane, name:

```text
route obligation:
old weak path:
new mathematical owner:
consumer to rewire:
forbidden circular inputs:
smallest verification target:
focused axiom audit:
```

## 2. Current Proof State

The repository does not yet prove RH unconditionally.
`unconditional_rh_skeleton` depends on six project roots:

```text
normalizedCoreCC20PropositionC1SourceCriterionRoot
normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot
normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot
normalizedCoreS2B1TracePackageRemaindersRoot
normalizedCoreSourceWeilFormDataRoot
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
```

These two roots are RH-level and must not be treated as lower producers:

```text
normalizedCoreCC20PropositionC1SourceCriterionRoot
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
```

The active route registry is:

```text
016  unified remaining gaps, rejected as an executable route
025  canonical Xi-quotient detector, research-only; no executable consumer
026  Schwartz multiplicative source owner, broad core rejected (proof 094)
027  per-detector arithmetic package rescue, dead hidden universal field (095)
028  direct fixed-detector certificate consumer, executable route rejected (114)
029  fixed-detector prime autocorrelation nulling, rejection-first
030  Xi-nullspace exact compact correction rejected by zero density (110)
031  Xi rational-pole cancellation, direct prime-control version rejected (106)
032  Burnol same-square formula aligned; semilocal sign gate active (109)
033  log-Poisson positive-owner shortcut rejected (111)
034  CCM24 semilocal positivity source gap recorded (112)
035  prime-free Xi/M4 detector branch rejected (113)
036  fixed-detector executable verdict; new finite-S identity required (114)
037  positive Euler multiplier compensation no-go (115)
038  log-factor positive cross read-off rejected (116)
039  positive difference prime scalar rejected at p=2 (117)
040  compact Wiener-Hopf boundary repair rejected (118)
041  Fredholm/Fock Euler-log cancellation rejected (119)
042  higher-Q differential filter rejected (120)
043  adelic scalar compensation mismatch (121)
044  Clifford prime-channel Gram shortcut rejected (122)
```

Plans 025 and 028 are research-only with no executable consumer. Do not create
Lean owners or rewire consumers until a successor satisfies Plan 036's
same-object finite-S trace contract. Plans 026-027 are rejected by universal
finite-prime fields; do not wire their ambient probe into the route.

For Plan 028, use the existing `SelectedWeilSquareOwner` and
`SelectedWeilFormulaOwner`: they give one genuine compact convolution square,
exact per-square finite-prime support, and explicit pole/archimedean/prime
values without `ForAllTests`. Do not rebuild a broad arithmetic package.

The name `SourceQWEqualsNegCC20WeilSum` is not evidence of an equality: its
structure has no numerical QW/CC20 field. The actual route sign consumes the
separately stored `NormalizedRouteBackedYoshidaLocalSumReadOff`. Any fixed-test
consumer must prove that equality from the genuine CC20 trace object.

For Plan 028, even that exact equality is the wrong target: the nonzero
`K_I` remainder survives triple vanishing. The allowed target is a fixed-test
inequality on the M4 bad-space complement, with finite-prime and pole terms
transported on the same square. Archimedean compactness alone is insufficient.

Burnol's compact-test explicit formula matches `SelectedWeilFormulaOwner`
term by term after setting `g(u)=u^-1/2 f(log u)`. The apparent archimedean
integrand difference integrates to `-2 log(2) f(0)` and is exactly canceled by
the owner's `log(4)` constant shift. This validates the intended spectral
identity but does not supply its Lean proof or the finite-S CC20/M4 sign. See
Plan 032 and proof 109.

Historical evidence remains in plans 012-014. Plan 015 is absorbed into 016
Phase 8. Do not execute the older plans as independent lanes.

Plan 012's operator subproblem is viable. In the `K_S`-invariant scattering
coordinate, two explicit commutator kernels prove that
`P_hat P theta_S(g)` is Hilbert-Schmidt. The rejected step is the exact equality
`supportSquareTrace = qwLambda`. CC20 Theorem `thmqkey1` writes the omitted
remainder as `-2 Id + K_I` with `K_I` compact Hilbert-Schmidt; it remains nonzero
on some tests satisfying the route's three vanishing conditions. See
`docs/proofs/cc20-012-mathematical-verdict.md`.

The accepted 011 result removed the false universal matched-scalar root. B2 now
reads the scalar from the same `SourceTraceReadOffData`. QW/pole collapse
remains B3/RH-level.

## 3. Execution Cadence

Work top-down from the active route consumer. Do not stop after a local helper,
wrapper theorem, field split, compatibility bridge, or declaration rename.

A substantial milestone must change the route judgment. Examples:

```text
an entire candidate producer is rejected by named Lean guards
a consumer switches to a stronger data-bearing API
the old weak path is no longer active
a dependency layer reaches one named mathematical/API bottom
a target is proved RH-equivalent or false by a concrete counterexample
```

Normal proof rounds should attack 10-20 black boxes, branches, or dependency
layers unless a route closes or a build-blocking conflict appears.

Default build cadence:

```text
do not run lake build after each helper
do not run focused axiom audits after each helper
continue until a substantial milestone
build and audit when Peter asks or the milestone needs formal evidence
```

Record only milestone-grade progress:

```text
update the active plan after a real dependency move or rejection
update MEMORY.md after route-level progress or a reusable failure
do not append routine scratch attempts or helper-by-helper chronology
```

## 4. Single-Agent Rule

Automatic subagents, LangGraph fallback, CLI coding agents, and worker fan-out
are paused. Use one coordinating agent unless Peter explicitly restores
subagents.

Peter may run several independent AI sessions manually. Those sessions are not
subagents and must own disjoint semantic lanes.

At manual session start, record:

```text
AI session start:
  owner:
  cwd:
  lane:
  old weak path:
  files allowed:
  files forbidden:
  smallest WSL build:
  focused axiom audit:
  expected output:
```

At handoff, record:

```text
AI session handoff:
  status: accepted / partial / blocked / rejected / analysis-only
  files changed:
  declarations changed:
  old paths removed:
  remaining blockers:
  WSL build:
  focused axiom audit:
  next safe action:
```

Two sessions must not edit the same declaration, route consumer, old weak path,
plan document, or final audit chain. A later session that discovers overlap
must stop editing and switch to read-only analysis or another lane.

Another session's dirty diff is evidence, not accepted progress. The main
worktree plus an import-facing WSL build and axiom audit decides acceptance.

## 5. File Ownership And Safety

The Windows repository is the only source of truth for this project. Its files,
Git index, branch, and `git status` define the accepted project state.

Required ownership boundary:

```text
edit source and project documents only in the Windows repository
stage, commit, fetch, merge, and push only from the Windows repository
sync source snapshots one way from Windows to a WSL ext4 verification mirror
never treat a WSL branch, commit, dirty diff, or generated artifact as authoritative
if WSL experimentation changes source, reproduce the exact semantic edit on Windows
verify the Windows-backed snapshot again before accepting or publishing it
```

Do not copy a whole WSL worktree back over Windows. Port reviewed file-level edits
into Windows, preserve concurrent Windows changes, and let the Windows diff decide
what belongs to the project.

The worktree may contain user or other-session changes.

Required behavior:

```text
read git status and the relevant diff before editing
preserve unrelated changes
work with overlapping changes instead of overwriting them
port precise semantic edits rather than copying whole files
never reset, clean, or revert work that you did not create
```

Destructive operations require explicit approval:

```text
git reset --hard
git checkout -- <path>
recursive deletes
branch deletion
force push
```

## 6. Lean Integrity Standard

Do not introduce or hide proof gaps through:

```text
sorry
admit
axiom
opaque placeholders
unsafe proof shortcuts
True or Set.univ producer fields
stored conclusions disguised as source data
```

An axiom-free proof of a weak statement does not count. The theorem statement
must remove a real active dependency.

Prefer data-bearing owners when several facts must refer to the same object.
Separate propositions can silently mix different witnesses.

Required same-object examples:

```text
route test and convolution square
operator and Schwartz kernel
kernel and Hilbert-Schmidt norm
positive trace and support-square trace
source Weil-form and evaluation data
canonical atoms and package certificate data
restricted/global masses written with one evaluation object
```

## 7. Lean Failure Modes

### 7.1 Row-record destructuring

Do not flatten an existential/conjunction when its final item is a structure:

```lean
rcases h with ⟨r, hmatch⟩
have hr := hmatch.1
have rows := hmatch.2
```

A flat pattern can recursively destruct `rows` and bind the first field under
the record name.

If the final proposition is `Nonempty Rows`, split the outer conjunction first,
then extract the witness.

### 7.2 Type and Prop universes

A Lean structure with data lives in `Type`. It cannot appear directly as the
right side of `P ∧ Rows`.

Use:

```text
P ∧ Nonempty Rows
```

when existence suffices. Use a Sigma type or a containing data structure when
the witness must remain available.

### 7.3 Dependent owner transport

An equality between route symbols and owner symbols does not transport data
whose type depends on the whole owner, evaluation object, source test, or
proof-valued cutoff.

Do not rely on broad `simp`, `rw`, or `cases owner.sameSymbols`. Supply an
owner-level equality/`HEq` theorem that names each dependent component. Keep an
unproved transport experiment outside the compiled route API.

### 7.4 Constructor collisions

If an inductive constructor is named `rho`, do not also name a local parameter
`rho` in pattern equations. Use another local name and `.rho` at constructor
sites.

### 7.5 Controlled simplification

Avoid broad `simp` on source evaluation read-off or finite-prime normalization.
It can unfold through norm identities or unrelated disjunctions. Apply the
named point read-off theorem, rewrite `legacyValueAt_apply`, then use
`simpa only` with the intended identities.

### 7.6 Import artifact freshness

`lake env lean path/to/File.lean` may pass while import-facing `.olean` or
`.ilean` artifacts remain stale.

Accepted verification requires an importing scratch file containing:

```lean
#check declaration_name
#print declaration_name
#print axioms declaration_name
```

If a smallest module build succeeds but the import cannot find the declaration,
delete only that module's build artifacts and rebuild the same module. Do not
widen to a full build unless the narrow repair fails.

### 7.7 Axiom audits do not detect theorem premises

`#print axioms` reports axioms used by a declaration but does not reject
ordinary or typeclass parameters. A theorem can have an axiom-clean proof and
still be conditional.

Every final no-argument audit must include:

```lean
#check @declaration_name
#print declaration_name
#print axioms declaration_name
```

Reject a final theorem whose printed type contains any explicit, implicit,
instance-implicit, or auto-implicit premise.

### 7.8 Yoshida model guard

The normalized CC20 carrier is a rejected toy model for source detector work:

```text
convolutionStar f g = f + g
weilLocalSum g = -polePairing g
```

`not_normalizedCC20MellinConvolutionLaw` proves that it fails Mellin
multiplicativity. Do not use its finite-node interpolation or its detector
record as a source zero-sum sign. A valid Yoshida producer needs the genuine
multiplicative convolution, the zero-sum functional, and the Appendix C
all-other-zero decay estimate.

### 7.9 Mellin tail quantifiers

`exists_uniform_mellin_vertical_quadratic_decay` supplies one quadratic-decay
constant for every real Mellin coordinate `sigma` in `[0,1]`. Its proof uses
the joint `(sigma,u)` log-slice, common compact support, continuous parameter
integrals, and the first three vertical derivatives.

This theorem controls the far-zero tail of one fixed test. Appendix C still
requires a normalized family whose constant is small enough for the chosen
`epsilon`, together with exact interpolation at the finitely many nearby zeros.
Do not claim the Yoshida approximation from uniform decay alone.

### 7.10 Yoshida convolution-power support budget

Yoshida Lemma 1 shrinks the far tail with convolution powers and finite
correction factors. In log coordinates, convolution adds support intervals.
Normalize the base factor by `r^-1 f(x/r)` with `r=1/N` before taking `N`
copies. `laplaceAt_rescale` proves the transform becomes `Phi(r s)`, while
`convolutionIterate_rescale_inv_natCast_support_subset_Ioo` proves the total
base support stays fixed. The finite correction still needs a disjoint residual
window. `exists_residualWindow_correction_with_quadratic_decay` realizes
arbitrary finite Laplace-node values in any such window while retaining the
same correction's uniform strip-decay constant. Use the named
`...support_subset_of_budget` theorem for the assembled product. Never use an
unscaled transform power law, mix correction witnesses, or omit the correction
budget.

### 7.11 Xi divisor counting

For the project-local Jensen route, use
`completedRiemannXi(s) = s * (s - 1) * completedRiemannZeta0(s) + 1`.
The `+1` is forced by Mathlib's `completedRiemannZeta_eq`; changing its sign
breaks the identity with `s * (s - 1) * completedRiemannZeta(s)`. A zero value
alone does not imply a nonzero `divisor`, because `untop0` sends infinite
analytic order to zero. Anchor xi as nonzero at `s=2` and exclude infinite
order before counting divisor support.

The far-strip tail is now an axiom-clean producer.
`exists_residualWindow_nearbyZero_assembled_distance_bound_lt` chooses enough
support-preserving base copies so the same assembled test satisfies
`norm(z-rho)^2 * norm(Phi(z)) < epsilon` on every sufficiently high point of
the closed critical strip. `sourceNontrivialZero_zero_lt_re` and
`sourceNontrivialZero_re_lt_one` prove that every source spectral index lies in
the open critical strip. The apparent negative-integer branch is empty; do not
add a separate negative-real-axis summability obligation.

### 7.12 Spectral counting threshold

Quadratic Yoshida pointwise decay does not require the full
Riemann--von Mangoldt `O(R log R)` count. A dyadic shell bound

```text
shellCard(n) <= K * q^n,  with 0 <= q < 4
```

already gives a geometric shell total `K*B*(q/4)^n`. Use
`sourceNontrivialZero_summable_of_xi_geometric_sphere_bounds` as the sharp
consumer. The standard linear-log count remains sufficient, but do not call it
the unique remaining bottom. Xi's functional equation folds growth estimates
to `Re s >= 1/2` with at most one unit of extra norm budget.
Use `sourceNontrivialZero_summable_of_xi_right_halfplane_ball_bounds` when
proving the analytic majorant; it is the narrowest active consumer and removes
all left-half-plane and Jensen-circle geometry from the remaining proof.
For the producer, use `completedRiemannXiKernelMoment` and
`norm_completedRiemannXi_le_kernelMoment`. The modified kernel is already the
Mathlib theta functional-equation kernel; use its named small/large interval
equations instead of introducing a separate Gamma/Stirling premise.
The explicit tail constant is `completedRiemannXiKernelTailConstant`. Use the
named exponential bounds on both sides of `t=1`; do not fall back to the weaker
existential `IsBigO` theorem.

### 7.13 Nyman--Mobius block guard

Plan 020 uses the discrete weighted sequence criterion with
`gamma_k(n)={n/k}`. Keep its projected dyadic block separate from the known
divergent natural Mobius partial sums. The active direction is

```text
w_N = (I-P_N) sum_(N<k<=2N) mu(k)/k * gamma_k,
```

where `P_N` is the orthogonal projection onto the whole old span. Removing
`P_N` changes the object and re-enters the natural-approximation divergence
theorems. Conversely, those divergence theorems do not reject the projected
block certificate.

The exact target correlation is `<gamma,gamma_k>=log(k)/k`. Every Gram entry
has a finite periodic digamma formula over `lcm(j,k)`. Use that formula or
certified interval bounds before accepting large-scale numerics. The current
M4 bottom contains `G_N^-1`; a bare divisor identity for `mu` does not control
the angle between the block and the optimal residual. Do not create a Lean
route API until a uniform positive `c/log N` capture bound is proved without
Littlewood or square-root Mertens input.

Vasyunin's explicit finite-support biorthogonal family is the dual of the
infinite minimal system, not the finite old span. Its finite canonical dual is
`P_N f_n`, which restores `G_N^-1`; do not claim that it explicitly inverts a
finite Gram matrix. The useful exact reduction is instead
`w_N=(I-P_N)(b_N-N*S_N*gamma_N)`, where
`S_N=sum_(N<k<=2N) mu(k)/k^2`; the unprojected vector vanishes before coordinate
`N` and is an explicit short weighted-Mobius tail. This only localizes the
denominator and does not establish the required correlation lower bound.

Do not impose the pointwise sign rule
`sign(<gamma,e_n>)=sign(-mu(n))`: the first squarefree counterexample is
`n=31`, and both exact periodic and long-cutoff computations confirm it. Plan
020 can only use the coupled normalized correlation/Schur-energy inequality
with individual bad signs.
Changing `mu(k)/k` to a nearby power weight does not remove the bottom, and the
Bettin--Conrey--Farmer log taper has only a conditional RH-level asymptotic;
neither is a lower producer.

Do not strengthen M4 to a fixed-fraction good-sign dominance statement. The
bad/good numerator mass is already about `0.509` at `N=512` and increases over
the tested dyadic scales. The certificate remains large because its projected
Schur energy decreases concurrently. Preserve the coupled ratio
`correlation^2/(projectedEnergy*d_N^2)`; separate coarse estimates can destroy
the observed mechanism.

Plan 020 is rejected as an executable RH route. GPU rejection runs through
`N=4096` show strong dyadic oscillation and descending low subscales, but do not
rigorously prove a zero infimum because the projected energy lies below the
crude cutoff-tail bound. More importantly, every structural attack leaves the
full coupled inverse-Gram non-cancellation inequality, which itself implies RH;
no independent arithmetic producer was found. Do not reopen 020 through larger
floating-point runs, Vasyunin duality, pointwise signs, fixed good/bad margins,
power-weight tuning, or the conditional Bettin--Conrey--Farmer taper.

The divisor-gradient flow proposed after Plan 020 is also rejected. Although
the explicit block coefficients cancel every residual gradient on
`N<n<=2N`, their later divisor hits increase the global weighted energy at all
tested scales through `N=2048`, even after old-space reprojection. Optimally
damping the correction restores the same inverse-projection angle lower bound
as Plan 020. Do not reopen this construction without a new mechanism that
controls future-multiple propagation before the global energy estimate.

Plan 022 was the next research candidate. It uses the first eight
moment-zero shifted-Mobius block directions. Each direction vanishes exactly in
sequence coordinates `n<=N`; its conservative certificate uses unprojected
energy and therefore removes the old Schur inverse from the denominator. GPU
checks through `N=4096` survive, including a cutoff-`250000` value about
`0.1657` for `log(N)` times normalized capture. Do not call this an RH route
until the aggregate eight-correlation lower bound is reduced to a positive
finite divisor main term with a strictly smaller unconditional error. Do not
replace the fixed frame by per-scale fitted coefficients.

Within Plan 022, the primary object is now the fixed anchored convolution with
`theta(d)=-mu(d)/d` for `d<=8`, `Q=theta*mu`, and
`h_N=sum_(N<k<=2N) Q(k)gamma_k-N*(sum Q(k)/k)*gamma_N`. Its global divisor sum
collapses exactly to `theta`, it vanishes in coordinates `n<N`, and its
high-cutoff normalized certificate is about `0.1213` at `N=4096`. The general
moment-zero Bessel shortcut and the pure-new exact-orthogonal-window shortcut
are rejected. Any proof must use the fixed convolution collapse and must not
recover the correlation by expanding `r_N` through `G_N^-1`.

For the fixed 022 convolution, do not use a pointwise sign claim or a smooth
scaling limit for `r_N`. Consecutive-scale numerics support a positive total
correlation, but 25--43 percent pointwise cancellation remains and residual
block profiles are not stable across scales. The active proof shape is a
positive `(N,2N]` finite-divisor main term from `1*Q=theta`, followed by a
strict bound for the possibly opposing `n>2N` tail.

The fixed coefficient partial sum is a finite Mertens combination:
`P_Q(x)=sum_(d<=8) theta(d)M(floor(x/d))`. Since `theta(1)=-1` and the remaining
square-root recursion coefficient is below `0.758`, a standalone square-root
bound for `P_Q` would already recover square-root Mertens control. Do not use
that as a lower energy producer. Preserve the coupled angle
`correlation^2/(residualEnergy*bridgeEnergy)`; the centered Mertens bridge must
remain on both sides.

Plan 022 is rejected as an executable route. Constraint-depth tests show that
the fixed convolution angle is generated by the full optimal shell
`(N/2,N]`; the shell update supplies about 46--84 percent of the final
correlation. The standalone dictionary
`V_16+span(h_16,h_32,...,h_N)` has squared distance plateauing near `0.014256`
through `N=65536`. Thus the fixed directions are not dense and the angle proof
reintroduces Plan 020's growing Schur/inverse-Gram bottom. Keep the convolution
identities as evidence, but do not reopen 022 without a genuinely lower owner
for the optimal shell update.

### 7.13 QW--prolate tail domains

`QW_lambda` is an unbounded closed quadratic form. Small additive-Fourier
leakage in `L2` does not by itself imply a small `QW_lambda` Rayleigh value.
Any prolate-tail estimate must control the archimedean logarithmic form norm,
the pole evaluation, and the finite-prime translations on one common form
domain.

The published global radical statement for the summation map `E` uses the
codimension-two Schwartz space with both `h(0)=0` and `integral h=0`. The
finite-`lambda` `h_0,h_4` proxy has zero integral but a nonzero point defect
proportional to `chi_0-chi_2`. Do not apply the radical theorem to this proxy
without a new extended-domain Mellin/explicit-formula proof. A formal identity
between the restricted proxy form and its outside-tail form is not accepted
until membership, cross-pairing convergence, and the radical identity are
proved for the same object.

### 7.14 Semilocal prolate Schur guard

The fixed-`q` Lambert q-matrix must be evaluated through its exact Meixner
Poisson kernel, not through underflowing Gaussian quadrature.  In the source
moment normalization the finite Gram bound includes the factor `1-q`:

```text
(1-sqrt(q))/(1+sqrt(q)) I
  <= G_n(q)
  <= (1+sqrt(q))/(1-sqrt(q)) I.
```

Do not restore the unscaled squared bounds.  Direct parity-block Schur probes
through degree 513 pass this guard and show a `sqrt(n)` Jacobi deformation
whose dominant phase is the metaplectic Cayley phase
`pi-4 arctan(q)=4 arctan(tanh(log(p)/2))`.  This rejects finite-section Schur
cancellation as an easy death mechanism but is not an asymptotic proof.  Do
not create a Lean route owner until the nonzero-amplitude Schur asymptotic and
the common-domain prolate cross-trace-to-Weil limit are proved.

The exact pre-cutoff owner is not the Lambert matrix itself. With
`U_p=exp(-i log(p) D)`, it is the bounded Poisson operator

```text
G_p=(1-q)(I-sqrt(q)U_p)^-1(I-sqrt(q)U_p*)^-1.
```

Its scalar Poisson expansion contains every `p^r`, and its compression pivot is
`dist(T_p e_n,T_p V_(n-1))^2`. The remaining Gate 1 theorem is the nonzero
half-space `SU(1,1)` Wiener--Hopf coefficient, not a generic inverse-Gram
bound. Locally Toeplitz/Moyal determinant theorems requiring exponential
off-diagonal decay do not apply to the broad squeeze canonical relation.

### 7.15 Prolate positive-trace owner guard

Do not use `norm(Pi_- C_g Pi_+)_HS^2` as the active Weil trace merely because
it is positive. CCM24 proposes spectral conditioning but does not define this
cross object or prove its trace read-off. The whole-line prolate spectrum is
discrete and unbounded in both signs, so the positive projection is not finite
rank. Exact-Jacobi sections show that the bare translation cross energy grows
with the section, while fixed Schwartz multipliers give no stable evidence for
a nonzero large-cutoff Weil limit.

The source-backed positive object from CC20 is the one-sided Sonin trace

```text
Tr(C_g* S C_g)=norm(S C_g)_HS^2.
```

CC20 proves an inequality between the archimedean Weil form and this trace,
not equality: `Tr(rho(f)S)=W_infinity(f)+E(f)` with an explicit remainder.
For finite `S`, first compute the same-object semilocal remainder and its
post-`Q` ideal/sign at `S={infinity,2}`. Do not build the full semilocal
self-adjoint prolate API until this one-prime remainder survives the
noncompact finite-Euler translation guard.

For the metric projection
`T_a R(R T_a* T_a R)^-1 R T_a*`, do not reintroduce the raw `a^2 I`
as a scalar remainder. Its first variation is `-QUR-RU*Q`; its second diagonal
blocks are `-J*J` and `JJ*` for `J=QUR`. The scalar term cancels against the
inverse compressed metric before `Q`. Any rejection must now use the smoothed
defect-pair trace or the `U^2` coefficient, not the old isolated-wave-packet
argument against `D_p o Q`.

For the full Euler parameter flow use
`X_a=-U_p(I-aU_p)^-1=-sum_(m>=1)a^(m-1)U_p^m` and
`R_a'=(I-R_a)X_aR_a+R_aX_a*(I-R_a)`. The direct `U_p^m` channel integrates to
`a^m/m` and the scaling differential supplies `m log(p)`. Treat words
interrupted by Sonin projections as the remainder; do not read mixed-prime or
defect words as Weil atoms.

CC20's exact angle decomposition is
`P P_hat P=R_Sonin+sum lambda_n^2|zeta_n><zeta_n|`, with
`sum lambda_n^2` finite. Combine this trace-class correction with the
`quantsmooth` lemma and the smoothed partial-translation estimate: after the
single-crossing `U_p^m` channel is assigned to the finite-prime Weil term,
every multi-crossing or prolate-correction word is trace class, and geometric
Euler decay survives all polynomial `Q` weights. This only proves the ideal
class `-2 Id+compact`; never infer `norm(K)<2` or triple-vanishing control from
compactness alone.

The single half-line crossing is no longer an open coefficient heuristic. If
`J_b=(I-P)U_(-b)P` and `C_h` is convolution, then
`Tr(C_h* C_h J_b)=b(h* * h)(b)`. With `b=m log(p)` and logarithmic-flow
coefficient `p^(-m/2)/m`, this is exactly the finite-prime Weil coefficient
`p^(-m/2)log(p)` on the same square. Assign this noncompact single-crossing
block to the Weil main term. Only multi-crossing and prolate-correction words
may enter the compact remainder.

The project sign is fixed: the metric first variation is the negative of the
crossing pair, and CCM25 has `QW=archimedean+pole-sum_p W_p`. Thus the local
positive atom remains positive while its contribution to both the metric trace
variation and `QW` is negative. Do not add another finite-prime sign flip.

The semilocal de Branges diagram preserves the underlying entire function and
hence the algebraic vanishing subspace at `{0,1/2,1}`. Do not justify this by
pointwise invertibility of the analytically continued Euler multiplier:
`1-p^(-1/2-it)` vanishes at `t=i/2`. Equivalent de Branges norms do not keep
reproducing-kernel vectors or compact bad eigenspaces fixed. The final sign
gate must prove a norm bound on the common vanishing subspace or show that the
`>=2` eigenspace belongs to the span of its three evaluation kernels.

### 7.14 Finite-S scattering compactness guard

For `S={infinity,p}`, the finite Euler scattering phase has a Fourier series
with a nonzero `log p` translation coefficient. Its cross-half-line Hankel
block contains a partial translation between intervals of length `log p`.
That operator has infinite rank and is not scalar modulo compact operators.

Do not claim a finite-S post-`Q` normal form `-c Id + K` with compact `K` by
formally replacing `u_infinity` with `u_S`. A valid proof must first exhibit a
source-backed semilocal identity that cancels every finite-prime translation
block before the compactness assertion. The noncompactness of the raw
quantized differential alone is not a proof about an independently
renormalized `D_S`; keep that distinction explicit. See
`docs/proofs/025_variable_s_two_gate_verdict.md`.

The exact cocycle is `Omega(uv)=v*Omega(u)v+Omega(v)`, but it does not remove
the pure finite-place remainder from the positive-trace identity. The direct
decomposition is `D_(uv)=D_v+D_u+Cross`. The mixed `Cross` term is trace-legal
after smoothing. The pure `D_p` is a Dirac comb at `k log p`; its central
coefficient is `p^(-1) log p`. After `Q=-partial^2+1/4`, a wave packet of
width less than `log p` sees only that central atom and its modulations give a
quadratic form growing like `p^(-1) log(p) s^2`. Hence the direct finite-S
post-`Q` remainder is not `-c Id + K` with bounded compact `K`.

Do not move `D_p` into the finite local Weil term without a new exact
same-object trace identity; doing so changes the read-off. Reopening this lane
requires either a pre-read-off cancellation of the finite Dirac comb or a
different pre-cutoff trace/supertrace in which it never appears. See
`docs/proofs/026_semilocal_cocycle_renormalization.md`.

### 7.15 Pre-cutoff Euler escape guard

Two pre-cutoff shortcuts are rejected. The CCM24 dual maps `theta_S,eta_S`
transport the archimedean positive trace, but their dual pairing cancels the
finite Euler factors and therefore loses the finite-prime Weil terms. The
inner factorization `u_p=z/B_a`, `a=p^(-1/2)`, cancels the central Dirac defect
in a graded supertrace, but the two defect projections differ by an operator
with eigenvalues `+a,-a`; it is not positive.

The only current pre-cutoff candidate is the cross-spectral transition
`Pi_- C_S(g) Pi_+` for the semilocal prolate operator attached to the
Euler-weighted cyclic pair. Its Hilbert-Schmidt norm square is positive and,
unlike `Pi_+ C_S(g) Pi_+`, has no growing-rank bulk. Do not create a route
owner from its formal source formula. First prove a self-adjoint realization.
A finite-rank cross-spectral trace has a continuous kernel, so it cannot equal
the prime-power Dirac terms at a finite cutoff. Do not seek an exact
finite-cutoff QW read-off.
The only surviving contract is common-form-domain distributional convergence
of these continuous kernels to the Weil functional as the cutoff grows.
The candidate arithmetic term is the first Szego/scattering-phase correction
from `log |L_p(1/2-is)|^2`; its Fourier modes give `p^k` and phase
differentiation gives `log p`. Bulk Christoffel--Darboux universality alone is
insufficient because it discards exactly this subleading term.
Finite Jacobi sections suffer spectral pollution and are not evidence for that
convergence. Projected-test RH sufficiency remains a separate gate.
See `docs/proofs/027_pre_cutoff_euler_dilation_escape.md`.

Do not replace the genuine prolate positive projection by the degree cutoff
onto the first `N` orthogonal polynomials. The resulting cross energy is an
orthogonal-polynomial-ensemble variance whose leading limit is universal and
loses analytic Euler weight perturbations. Conversely, do not infer fixed
`q=1/p` edge survival only from the `q=0` Taylor coefficient. The source
coefficient in `a_n(q)` grows like `(-1)^n sqrt(n)`, but the expansion is not
uniform in `n`.

For fixed `q`, use the source Lambert rank-one decomposition and the hidden
Meixner identity
`p_ell(m)=2F1(-m,-ell;1/2;2)`. Its exact Poisson kernel reduces on the diagonal
to `P_n^(-1/2,0)(1-8t/(1+t)^2)` and has fixed-q phase
`4n arctan(q^r)`. Darboux asymptotics proves an `n^(-1/2)` normalized q-matrix
edge term even at `q=1/2`; do not reuse the erroneous double-weight Hadamard
contour, which predicts the wrong scale. The infinite rank-one vectors are not
in ordinary unweighted `ell^2`, so no naive trace-class Fredholm limit is
allowed. Transfer the fixed-q kernel through the exact Schur complement for
`Delta_n/Delta_(n-1)` before making a prolate-edge claim. See
`docs/proofs/029_prolate_jacobi_edge_survival.md` and
`docs/proofs/030_meixner_lambert_resummation.md`.

### 7.16 Metric Sonin common-domain guard

Do not identify the positive trace-class term
`sum lambda_n^2 |zeta_n><zeta_n|` in the CC20 angle decomposition of
`P P_hat P` with either CC20 post-`Q` compact operator. The former acts in
`L2(R)_ev` and has trace about `2.237484835`. The operator in Theorem
`thmqkey1` acts on `L2(sqrt I,d*rho)` with kernel `Q delta(max(u/v,v/u))`;
the later `E o Q` operator uses the distinct normalized `Q epsilon` kernel.

For M3A, do not implement that displayed `Q delta` expression literally as a
measurable Hilbert-Schmidt function kernel. In logarithmic coordinates it
contains the singular `-2 Dirac_0` term, which is already the `-2 Id` essential
part of `thmqkey1`. First subtract that distribution and define only the regular
remainder `k_I`; then prove its measurable square-integrable kernel and action
identity. Otherwise the owner double-counts `-2 Id` and fails the HS gate.
The regular side itself is not killed by a diagonal singularity: its right
limit at `rho=1` is
`8*pi^2/9 + Si(4*pi)/(4*pi) - 1/2`. Do not repeat the local `L2` death test;
the next gate is the exact kernel-action and M0 same-object normalization.

The current `SelectedWeilSquareOwner` stores raw `g* * g`; CC20 M3A requires
`Q(xi*xi*)`. Never identify them by support, symbols, `rfl`, or `HEq`. A valid
owner must carry a genuine compact smooth Q-root whose square has Mellin
multiplier `t^2 + 1/4`. See `docs/proofs/070_m3a_q_image_owner_mismatch.md`.

CCM24's `B_lambda` realizes the Sonin space, not the compactly supported
convolution-root space. Never write a Rayleigh form `<F,K_(S,I)F>` with
`F in B_lambda` unless one theorem transports the operator, norm, trace
identity, and Mellin conditions through an explicit same-object unitary map.
Equivalent norms and the commuting de Branges diagram do not supply that map.

Plan 024 is rejected as executable. Reopening it requires an explicit global
fixed-`S` post-`Q` kernel on the test-root Hilbert space before any finite
section, interval certification, or Lean owner. See
`docs/proofs/040_metric_sonin_domain_rejection.md`.

### 7.17 Finite Galerkin and Herglotz guard

The exact finite Guinand--Weil dictionary of arXiv:2607.02828 is a valid
coordinate theorem: each finite Galerkin vector produces one explicit
band-limited Weil test with the same zero sum. Its positive archimedean tail
theorem is also a valid certification guard. Neither theorem proves the sign of
the cutoff-free matrix.

Do not use positivity of every cutoff-free finite Weil matrix as a lower source
root. Once the finite test family is proved determining, that assertion is
Weil positivity and hence RH-level; without the determining theorem it cannot
close the route. Likewise, do not use the scalar odd-sector Herglotz inequality
as a lower producer. Yoshida Proposition 1(1) proves that odd positive
definiteness of the Weil form is equivalent to RH, and the 2026 Herglotz source
explicitly leaves its scalar inequality open.

Yoshida's detector avoids a radius cycle only because its convolution power may
grow the support. Rescaling all factors into one fixed narrow window changes the
far threshold and requires a new coupled-radius theorem. See
`docs/proofs/041_finite_galerkin_escape_screen.md`.

### 7.18 Metric projection prime-power coefficient guard

The endpoint metric Sonin projection is rejected as a finite-S Weil trace
owner. For one prime, with `a=p^-1/2`, `V=U+U*`, and
`A_a=(1+a^2)R-a R V R`, its exact trace correction is

```text
-a Tr(R C Q V R A_a^-1).
```

Expanding `A_a^-1=R+a R V R+O(a^2)` gives the second-order
single-crossing word `-a^2 Q(U^2+U*^2)R`. Its crossing length is
`2 log(p)`, so it contributes twice the `p^2` Weil atom. The excess is a
noncompact single crossing and cannot be placed in the compact remainder.

Do not recover the missing `1/2` from the logarithmic generator alone.
Differentiating the moving projection factors supplies another direct channel.
The local crossing trace formula remains valid; its coefficient from the
endpoint metric projection is wrong for every prime power beyond the first.
See `docs/proofs/042_metric_sonin_second_prime_power_rejection.md`.

### 7.19 Cutoff-free Weil cancellation guard

The arXiv:2607.02828 cutoff-free matrices are rigorously positive in the tested
Arb certificates, but the positive margin is not blockwise. On minimum
directions, order-one pole, Gamma, and prime Rayleigh terms cancel to below
`10^-53`; at `(c,N)=(100,32)` the midpoint diagnostic is about `1.58e-87`.

Do not use fixed coercivity, diagonal dominance, separate absolute block
bounds, or finite-`T` negative eigenvalues as a route. A valid source-side proof
must preserve the coupled low-rank/Krein cancellation. The remaining scalar
Herglotz sign is open and RH-level, not a lower producer. See
`docs/proofs/044_cutoff_free_weil_cancellation_verdict.md`.

Run Arb/WSL matrix certificates serially. Launching many concurrent WSL Arb
processes can fail at the WSL service layer with `E_UNEXPECTED`; this is an
environment failure, not a matrix-sign result.

### 7.20 Quantum Lindblad and prime-loop guards

Do not rewrite each negative prime correlation as the positive Lindblad jump
`w ||(U_(m log p)-I)h||^2` and discard its diagonal term.  Matching the Weil
atom forces the additional compensation `2w||h||^2`.  At `c=13`, the complete
compensation is about `9.94377`, while the certified pole-plus-Gamma remainder
on the `N=16` minimum direction is only about `0.08801`.  The required residual
is strictly negative by an order-nine margin.  Orthogonal environment channels
do not repair it because they preserve each `J*J` diagonal.  More generally, a
positive `I,U_b` channel with off-diagonal coefficient `-w` has a positive
Gram block with `ab>=w^2`, so its diagonal cost satisfies `a+b>=2w`; the
standard jump already achieves the minimum.

Do not build an ordinary local self-adjoint quantum graph with one edge of
length `log(p)` per prime as a Hilbert--Polya owner.  The edge lengths are
unbounded, so disjoint fixed-width interior bumps form an infinite orthonormal
bounded-energy sequence; the graph Hamiltonian has no compact resolvent.
External dilation channels turn the object into an open scattering system and
move the prime data to resonances, not discrete self-adjoint eigenvalues.

A graded supertrace or nonlocal network is a different route.  It must supply
a new positive consumer and may not inherit the rejected Lindblad or ordinary
metric-graph argument.  See
`docs/proofs/045_quantum_lindblad_graph_rejection.md`.

The minimal graded Lindblad escape is also rejected. The even/odd pair
`sqrt(w/2)(U-I)`, `sqrt(w/2)(U+I)` cancels the forced identity term exactly,
but its supertrace is `-w(U+U*)`, with Fourier symbol `-2w cos(theta)`. Any
local `I,U` grading with zero diagonal and nonzero prime correlation has the
same two-sided spectral obstruction. Finite sums are nonzero zero-mean
trigonometric symbols, and finite-codimensional vanishing conditions do not
restore positivity. Do not call diagonal cancellation a positive factorization
or select its positive spectral sector as the physical space. See
`docs/proofs/050_graded_lindblad_supertrace_rejection.md`.

Do not claim that a diagonal sign or phase gauge turns the exact cutoff-free
Weil matrices into stoquastic Hamiltonians or graph Laplacians. Arb-certified
matrices at `(c,N)=(13,2)` and `(13,4)` contain only frustrated positive
triangles: the invariant product of three edge entries is positive, while an
all-nonpositive gauged triangle would have negative product. Replacing `Q` by
`alpha I-Q` controls the top rather than the bottom of the spectrum and does
not prove Weil positivity. See
`docs/proofs/052_stoquastic_weil_gauge_rejection.md`.

For the finite Guinand--Weil square dictionary, do not model CC20 triple
vanishing as three arbitrary coefficient rows or substitute moment neutrality.
In the even sector the points `s=0,1/2,1` become `z=+i/2,0,-i/2`; the endpoints
coincide by evenness, `g_v(0)=log(c)*v_0^2`, and `g_v(i/2)=0` is exactly the
source pole-neutral row. On this same-object subspace the pole block vanishes,
but Arb probes through `N=16` show that both Gamma and prime compressed blocks
are indefinite and cancel on rapidly shrinking total scales. Do not call the
coupled restricted matrix a lower conditionally positive kernel without an
explicit pre-sign Gram identity; uniform positivity of that coupled family is
the constrained Weil gate. See
`docs/proofs/054_triple_vanishing_conditional_kernel_verdict.md`.

The complete finite Weil divided-difference source also fails the standard
Loewner/operator-monotone escape. In the positive-frequency even sector its
off-diagonal block is twice the Loewner kernel of
`Phi(x)=sqrt(x)*psi(sqrt(x))` on squared nodes, but official Arb closed forms
give `Phi(1/4)>Phi(1)` for `c=13,29,100`. Do not infer continuous Pick,
operator-monotone, or complete-Bernstein structure from positivity at the
finite integer-square nodes. A Cholesky factor after LDL is not a lower
positive-measure representation. See
`docs/proofs/056_loewner_bernstein_rejection.md`.

Do not replace the failed continuous Loewner route by a discrete Bernstein or
squared-node Stieltjes assertion. For `a_n=Phi_c(n^2)`, Arb at `c=13,29,100`
shows that both ordinary increments and adjacent `n^2` secant slopes increase
already from `n=1` to `n=3`; positive Bernstein/Stieltjes measures require
them to decrease. A rational Pick interpolant recovered separately after each
finite positive LDL consumes the desired matrix sign and is not a lower or
uniform source owner. See `docs/proofs/058_discrete_bernstein_rejection.md`.

Do not use the nested parity Schur complement as a lower proof unless its
inverse is eliminated by a new arithmetic identity. At fixed `c`, even and odd
blocks each add one coordinate and have pivot
`a_N-b_N^T A_(N-1)^-1 b_N`, but Arb probes show cancellation of the diagonal
by up to 15 decimal orders and nonmonotone pivots. At `c=29,N=8`, the even and
odd pivot/diagonal ratios are about `1.10e-15` and `1.82e-14`. The parity blocks
are Loewner kernels; low displacement rank gives no sign, and interpreting the
pivot as an RKHS distance assumes prior positivity. See
`docs/proofs/060_parity_schur_inverse_rejection.md`.

The pole-free constraint route remains open under a narrower guard. The source
proves a jump-Dirichlet form and a simple positive ground state for
`A_tilde=A_a-W_(0,2)`, but not that its even sector has exactly one negative
eigenvalue. In finite Arb models, mean-zero alone retains one negative
direction while pole neutrality `<C,v>=0` alone removes it. The resulting
target is `G(0)=<C,A_tilde^-1 C><0`, numerically near `-1/2`; do not replace it
by the much sharper full condition `1+2G(0)<=0`, or assume index one from the
source's numerics. The minimum-kernel Poincare bound is false by a large margin.
Reopening work must prove the zero-energy anti-maximum sign on the exact common
form domain, possibly through the screw/Krein string. See
`docs/proofs/063_polefree_constraint_survivor.md`.

The pole-free anti-maximum route is rejected as a lower producer. Do not infer
`<C,A_tilde^-1C><0` from a Dirichlet form, negative off-diagonal kernel,
positive simple ground state, or even Morse index one: the exact countermodel
`A=[[-4,-1],[-1,1]]`, `C=(1,1)` has all those properties but gives
`<C,A^-1C>=1/5>0` and remains negative on `C-perp`. Suzuki's inverse-Neumann
reformulation keeps `G_a` nonlocal and takes `lambda=0` only after assuming RH.
Anti-maximum principles near the principal pole do not control zero across the
first spectral gap. See `docs/proofs/064_polefree_antimax_rejection.md`.

### 7.21 Cutoff-flow, total-positivity, and Jensen guards

Positive boundary masses at prime events do not make the cutoff path a
positive canonical-system flow.  The smooth-cell curvature `Q_N''(u)` is
indefinite already at small `N`; inverse curvature and `log det` curvature also
change sign.  The coupled Schur impedance `1/<1,Q_N^-1 1>` is positive in the
tested cells but neither monotone nor completely monotone, and it belongs to
the even all-ones direction rather than Yoshida's odd RH gate.

Do not use closure of `PF_infinity` under finite positive sums.  That closure
is false in general: expanding a determinant gives mixed-kernel columns not
controlled by total positivity of the individual kernels.  The genuine Xi
Fourier kernel is also not a non-Gaussian `PF_infinity` density, because its
two-sided superexponential decay makes its bilateral Laplace transform entire,
incompatible with the Schoenberg meromorphic product except in the Gaussian
case.

Large-shift Jensen hyperbolicity does not cover RH.  Bounds of the form
`n>=c*exp(d/2)` leave the entire ray `n=0,d->infinity`, whose hyperbolicity is
the original Laguerre--Polya/RH assertion.  See
`docs/proofs/047_original_route_rejection_screen.md`.

### 7.22 Robin and heat-flow guards

Do not treat restriction of Robin's inequality to colossally abundant numbers
as a lower producer. It remains an RH-equivalent sign gate. The conditional CA
deficit is of order `1/sqrt(log n)`, and false RH gives larger positive
excursions with exponent below `1/2`. A standard zero-free-region PNT error is
asymptotically too large to settle that sign. Reopening this lane requires a
genuinely unconditional signed square-root-scale cancellation theorem, not a
coarse Mertens estimate or more CA enumeration.

Forward de Bruijn heat flow only contracts a zero strip already known at an
earlier time. It cannot prove `Lambda<=0` by backward transport, since inverse
heat flow is not a real-zero preserver. At time zero, zero starting width is
already RH. Do not use positivity or log concavity of the Xi kernel as a
substitute: these are low-order conditions; `PF_infinity` is impossible for the
non-Gaussian Xi kernel and a PF5 minor is already negative. See
`docs/proofs/048_robin_heatflow_rejection.md`.

### 7.23 Dead-consumer guard

Do not implement a locally viable producer when its only route consumer is
already rejected or RH-level. The M3A Q-root `(d/dx+1/2)xi` survives its
algebraic and finite-Mellin checks, but M3A/M4 only produce a
finite-codimension local remainder sign. Plan 016's M5C still needs the
rejected M5B all-other-zero detector. Do not start Q-root Lean work, `K_I`
numerics, or consumer rewiring without a new lower source-sign consumer. See
`docs/proofs/073_m3a_upstream_consumer_death_verdict.md`.

### 7.24 Burnol explicit-formula and semilocal guard

For a selected additive log square `f`, use the centered multiplicative test
`g(u)=u^-1/2 f(log u)`. Burnol's formula then has exactly the owner's pole,
archimedean, and finite-prime terms. Do not reopen normalization debates or add
another half-density factor.

Do not treat this classical identity as the missing positive producer. The
archimedean CC20 theorem controls `D_infinity=-2 Id+K_I` only. A detector whose
support square reaches `log 2` sees finite primes and needs the same-object
finite-S remainder `D_S`. Raw Euler partial translations are noncompact, and
the rejected endpoint metric projection gives twice the required `p^2` atom.
Either keep a strict negative detector in a prime-free fixed window or prove a
source-backed subtraction with coefficient `p^(-m/2)/m` for every prime power
before claiming a compact post-Q remainder. Formalize the spectral explicit
formula only after this sign gate survives. See Plan 032 and proof 109.

### 7.25 Xi-null compact-support zero-density guard

Do not claim that a nonzero compactly supported source test can be an exact
`Xi*R*A` null direction. Its bilateral Laplace transform is entire of finite
exponential type and has only `O(T)` zeros in radius `T`, while completed Xi
contains `Theta(T log T)` nontrivial zeta zeros by the Riemann--von Mangoldt
count. A noncompact Xi deformation may preserve zero values, but cutting it off
loses that preservation and requires a complete quantitative prime/tail bound.
The derivative-row independence in proof 103 is local evidence only. See
`docs/proofs/110_xi_null_compact_support_zero_density_death.md`.

### 7.26 Log-Poisson positive-owner guard

The positive functional-calculus operator
`2 log(1+p^-1/2)I-log((I-p^-1/2 U_p)^*(I-p^-1/2 U_p))` has the correct
`p^-m/2/m` Fourier coefficients. Do not infer a Weil positive trace from it:
factoring it through a half-line boundary replaces the linear discrete
prime-power read-off by a continuous quadratic Hankel energy of its square-root
kernel. Inserting it linearly retains the atoms but leaves an infinite bulk
trace and no positivity. See Plan 033 and proof 111.

The original CCM24 source proves `theta_S`/Sonin transport only. Its own
introduction presents semilocal Weil positivity and a second semilocal prolate
operator as future work; it does not prove the fixed-S `QW` inequality or the
post-Q remainder sign. Treat `groundstate`, `isosonin`, and the Hilbertian
diagram as domain transport, never as a positive consumer. See proof 112.

In a prime-free window, the M4 complement cannot contain a negative detector.
The corrected identity `PositiveTrace=QW+D_infinity`, together with
`D_infinity<=-||xi||^2`, gives `QW>=||xi||^2` there. Finite orbit/bad-space
row independence does not preserve the complete zero sum. Do not reopen proof
083 by claiming that orthogonalization keeps its negative sign. See Plan 035
and proof 113.

Plan 028 is rejected as executable after the combined gates 042 and 109-113.
Reopening requires one new finite-S positive trace on the test-root Hilbert
space, with each `p^m` single crossing assigned at coefficient `p^-m/2/m` and
only a compact self-adjoint post-Q remainder left after subtraction. No checked
source currently owns that theorem. See Plan 036 and proof 114.

Do not reinterpret the endpoint metric projection's excess `p^2` channel as a
defect norm that decays with the cutoff. At `p=2`, a fixed compact positive
smooth bump has exact excess
`log(2) F_h(2 log(2))>0`; the overlapping support makes positivity elementary.
This rejects same-range endpoint implementations of a vanishing
same-square-defect bound. A new attempt must change the noncompact range and
derive its trace identity from scratch. See proof 127.

The Euler-log graph range is also rejected. Although its orthogonal projection
has the correct `p` and `p^2` channels, the inverse graph metric inserts an
extra `-a^3 QUP` channel at third order. Do not try to prescribe the exact
Euler logarithm as a projection off-diagonal: every projection off-diagonal has
norm at most `1/2`, whereas the `p=2` Euler-log crossing has norm greater than
`1/sqrt(2)` on disjoint translated intervals. See proof 128.

Further positive-owner guards are recorded in proofs 129-131. Schur-positive
blocks and ancilla doubling pay the unavoidable `K*K` diagonal cost; scalar
norm compression changes the `p^3` coefficient; positive boundary/scale
averaging cannot create the `1/m` factor; and a positive Poisson mixture with
all `a^m/m` moments uniquely requires the infinite measure `dt/t`. Do not
reopen these variants as finite positive same-object owners.

The boundary-potential absorption candidate has a real local pass at `p=2`
(numerical graph-norm ratio about `0.44`) but fails cofinally: a fixed test
supported below `log(2)` sees a lower bound proportional to
`sum_p p^(-1/2)`, while its archimedean graph norm is fixed. Sparse prime
windows only make the positive Schur costs additive. See proof 132.

The shared Brownian-Gram construction in proof 133 is the only current
cofinal-cost survivor. Its nested boundary vectors have Gram matrix
`C_ij=min(log p_i,log p_j)` and the exact weight vector `p^(-1/2)` has uniform
Schur cost at most `1/(2 log 2)+1/8<1`. Do not promote it to a route owner
until the same convolution square proves the boundary-data Gram estimate and
the finite-prime read-off has no mixed-prime terms.

Proof 134 closes that gate for the current Brownian proposal: the exact
same-square Gram contains `F_h(log p-log q)`, and a narrow compact test
diagonalizes it. For `{2,3,5}` the resulting cost is already
`sum 1/(p log p)>1`. Do not use the ideal `min(log p,log q)` matrix as source
data or promote proof 133 to a route owner.

The support-aware refinement in proof 135 counts only `m log(p)<=lambda`, but
its simple local graph-norm bound exceeds one near `lambda=3` and grows with
the window. Treat this as a numerical screen until an analytic mixed-Gram
estimate is proved; no Lean owner is authorized from the scan alone.

Proof 136 adds an adversarial gate: real compact oscillatory factors can make
the actual mixed-prime Gram nearly diagonal, pushing the Schur cost above one
even for `{2,3}`. Treat mixed-autocorrelation discounts as untrusted until the
same test also satisfies all pole-node constraints.

The radial log-Euler derivative gives a sharp diagnostic positive multiplier:
its Fourier coefficients are the exact `p^-m/2` Weil channels, but positivity
requires the scalar compensation `2 log(p)/(sqrt(p)+1)` per prime. Rational
independence of distinct prime logs makes these minima add over finite `S`, so
the compensation diverges cofinally. Do not use direct translation-multiplier
positivity as the finite-S owner; any viable construction must cancel the scalar
through a non-translation-invariant boundary identity. See Plan 037 and proof
115.

The sign-reversed log factor
`log((I-p^-1/2U_p)^*(I-p^-1/2U_p))-2log(1-p^-1/2)I` is positive and has the
correct `-p^-m/2/m` coefficients, but its outer-factor half-line cross norm
contains an unavoidable extra boundary term. A test square supported below
`log(p)` has zero Weil prime atom while that cross norm is positive. Do not
identify a positive cross factorization with a linear local atom. See Plan 038
and proof 116.

Any proposed positive half-line owner of the form `P(cI+V_S(D))P+K` with
compact/boundary-local `K` inherits the full prime multiplier's essential
symbol: translated long wave packets escape the boundary and kill `K`.
Therefore compact Schur/Hankel/Wiener-Hopf corrections cannot cancel the sharp
prime scalar compensation. A viable owner must perform a genuinely noncompact
pre-read-off cancellation and assign that channel explicitly to the Weil main
term. See Plan 040 and proof 118.

Do not use `-log det(I-aU_p)` or a bosonic Fock partition trace on the raw
prime translation: `U_p` and its half-line crossing are infinite-rank and not
trace class. Smoothing followed by `det_2` removes the `m=1` channel and makes
higher powers test-dependent, so it no longer reads the same Weil square. See
Plan 041 and proof 119.

Do not amplify the archimedean `-2 Id` by replacing CC20's minimal
`Q=-(rho*partial_rho)^2+1/4` with a higher differential polynomial.  The cusp
then produces delta derivatives and unbounded root-derivative energies, not a
bounded scalar plus compact remainder. Scalar rescaling changes prime and
archimedean terms together. See Plan 042 and proof 120.

Do not realize each negative prime atom by the positive difference
`p^-m/2 log(p)||(I-U_p^m)h||^2`. It forces the scalar compensation
`2 log(p)p^-1/2/(1-p^-1/2)||h||^2`; at `p=2` this is about `3.346`, already
larger than the archimedean essential coefficient `2`. The resulting post-Q
operator has positive essential scalar and is not `-2 Id+compact`. See Plan
039 and proof 117.

Do not use the adelic product formula to cancel the positive prime scalar
compensation. Principal-character renormalizations are indexed by integer
valuations `v_p(q)` and contribute `v_p(q)log(p)`, while the sharp cost is
`2log(p)/(sqrt(p)+1)`. Arbitrary real local exponents leave the principal-idele
self-duality class and change the explicit formula. See Plan 043 and proof 121.

Do not use anticommuting Clifford/fermionic prime channels to evade diagonal
cost. A positive Gram block realizing signed first-prime couplings `w_p` obeys
the Schur bound `c >= w^T C^(-1)w`; zero spinor expectation erases the desired
linear atoms, while retaining them restores the bound. See Plan 044 and proof
122.

Plan 045 negative spectral projection screen: finite Jacobi sections do not
support a route owner. At `lambda=1, tau=0.10`, the p=2 minus archimedean
smoothed negative-projection trace oscillates across sizes 128--512, and every
negative eigenvector has order-one tail mass in the final basis quarter. Treat
finite-section negative projections as boundary-pollution diagnostics only.
The only admissible spectral reopening remains a common self-adjoint
semilocal projection with an exact same-test Weil read-off and the
`p^(-m/2)/m` pre-crossing coefficient. See proof 123.

Do not replace the rejected metric Sonin projection by another positive
functional-calculus weight on the same transported range. For
`B_phi=T_S R phi(A_S) R T_S*`, the trace bulk is
`Tr(C A_S phi(A_S) R)`. Exact archimedean bulk forces
`A_S phi(A_S)=I`, hence `phi(A_S)=A_S^-1` and recovers the rejected endpoint
projection. Any other weight leaves a noncompact multiplier bulk; a compact or
finite-rank range correction cannot repair the excess single-crossing `p^2`
channel. See proof 124.

Suzuki's continuous screw-kernel reduction does not by itself open a Lean
route. The unconditional theorems construct compact self-adjoint `G_a` and
prove continuity of the localized ground value, but the all-`a` statement
`ker(G_a)={0}` is exactly the RH-closing nondegeneracy gate. Kernel continuity
does not prove injectivity of this zero-energy first-kind equation, and the
projected equation is a two-sided prime-delay problem rather than a triangular
Volterra equation. Require a strictly lower injectivity theorem before adding
this owner. See proof 125.

## 8. WSL Verification

WSL2 is a verification environment, not a source workspace. Author and manage
Git only in the Windows repository, then copy the Windows source snapshot into
an ext4 verification mirror. Never run Lake through Windows Lean or from
`/mnt/c`.

Preferred persistent verification mirror:

```text
/home/peter/verify/Connes-Weil-RH-Proof
```

Before syncing into it, run:

```text
git rev-parse --show-toplevel
```

The result must be the project mirror itself. If it returns `/home/peter` or a
different path, do not sync over the directory. Create a fresh ext4
verification directory, seed its `.lake` from the compatible persistent cache,
and copy current sources while excluding `.git` and `.lake`.

Do not overwrite a dirty mirror. Record the divergence and use an isolated ext4
verification directory. Do not commit or push from either mirror. A successful
WSL build accepts the tested Windows snapshot only; it does not transfer source
ownership to WSL.

All Lake commands must use the repository lock:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build <target>
```

Verification order:

```text
1. direct Lean check during implementation
2. smallest owning module build
3. import-facing #check and #print
4. focused #print axioms
5. route or Dev build after the local target passes
6. full build only for a final milestone or explicit request
7. shortcut scan and git diff --check
```

Accepted focused axiom output may contain Mathlib foundations such as:

```text
[propext, Classical.choice, Quot.sound]
```

It must not contain `sorryAx` or new project axioms outside the explicitly
audited remaining roots.

## 9. CC20 Operator/Trace Rule

The current normalized core does not implement operator theory. Named evidence:

```text
normalizedCoreTraceAmplitude_eq_encodedEvaluationNorm
normalizedCoreConvolutionStar_eq_add
normalizedCoreHilbertSchmidtGate_iff_traceClass_cyclicLegal
```

Do not treat the current `positiveTrace`, `traceClass`, `cyclicLegal`, or
`hilbertSchmidtGate` fields as analytic closure.

A valid CC20 trace producer must tie one route test to:

```text
half-density convolution square
theta-smoothed compressed operator
measurable Schwartz kernel
square-integrability proof
Hilbert-Schmidt norm
adjoint/composition kernel
ordinary positive trace
five per-move cyclicity witnesses
source-normalized trace identity with explicit remainder
rank and pole corrections required by that identity
```

Keep the regularized Connes trace separate from the ordinary positive trace of
`A* A`. Do not write `Tr(A* A) = QW_lambda`. Contract M0 must derive the exact
signs and all remainder, rank, and pole terms from the sources. Contract M3
must then prove or reject the proposed control of the nonzero remainder `D_S`.

Keep the CCM25 support parameter and operator cutoff separate:

```text
lambda_qw   bounds support and the QW_lambda prime-power sum
Lambda_op   defines P_Lambda_op and P_hat_Lambda_op
```

No checked source identifies them. Contract M0 proves
`PositiveTrace = QW_lambda_qw - Pole + D_(S,Lambda_op)`. The vanishing
conditions kill the pole, not the remainder. Use `Lambda_op=1` for the M3
specialization unless a later theorem requires another cutoff.

`SourceTraceReadOffData` is an old downstream route bundle, not a lower analytic
producer. It already stores a Hilbert-Schmidt gate, positive-trace
nonnegativity, and full/restricted read-off bridges whose no-defect semantics
the 012 counterexample rejects. Do not construct it as analytic closure. A CC20
operator/kernel construction must start from a pre-trace owner that contains
route/test, window, cutoff, coordinate, and admissibility data only. Plan 016
may introduce a corrected downstream owner after ordinary trace and the
explicit-remainder theorems have been proved. Project to the old bundle only
when a theorem proves that projection for the selected object.

For the project-local kernel strategy, define ordinary trace independently of
the kernel mass and prove their equality. A legal cyclic trace move requires
either two Hilbert-Schmidt factors or one trace-class factor and one bounded
factor. Bounded-times-Hilbert-Schmidt alone does not supply a trace-class
product. The ordinary trace of a complex operator is complex-valued. Derive the
route's real positive scalar through an explicit theorem for `A* A`; do not hide
that conversion in simplification.

Mathlib v4.30.0 has finite-dimensional trace results but no repository-visible
infinite-dimensional trace-class/Hilbert-Schmidt framework suitable for this
lane. Contract M2 in plan 016 retains the project-local kernel strategy proved
during the historical 012 work unless new library evidence changes that
judgment.

The Phase 0A source audit established three fixed-S limits:

```text
Connes 1999 Theorem 4:
  supplies R_Lambda = P_hat_Lambda P_Lambda, a semilocal quotient-kernel
  trace calculation, and an asymptotic trace formula for R_Lambda U(h)
  does not supply a measurable L2 function kernel, an HS majorant, or
  ordinaryTrace(A* A) = hsNormSq

CCM24:
  supplies bounded semilocal/Sonin comparison maps
  states eta_S is nonunitary and does not intertwine the semilocal Hermite or
  multiplication operators with their archimedean versions
```

Do not transport orthogonal projections, kernel measures, Hilbert-Schmidt
norms, or post-`Q` remainder terms through the CCM24 comparison by bare
conjugation. The historical 012 source bottoms were
`SourceCC20FixedSQuotientMeasureCoordinate`,
`SourceCC20FixedSKernelEstimate`,
`SourceCC20FixedSEulerKernelTransport`, and fixed-S post-`Q` remainder
transport. Plan 016 no longer treats them as independent execution gates:
Contract M2 owns the valid kernel theorem, while Contracts M0 and M3 own the
nonzero remainder. Do not reopen the old Phase 0B route.

CC20 Corollary `qeasy` is a local remainder-sign tool, not a detector theorem.
Its printed corollary statement is broader than its proof: the proof uses
positive-definiteness via `|f(x)| <= f(0)`. Any `qeasy` route must prove that
the final compact test, rather than only a pre-correction base, is a genuine
convolution square. Normalized support-preserving Yoshida powers move the
far-tail threshold to `(n+1)*T`; do not claim a global detector unless one
same-object theorem also gives a nearby radius `R >= (n+1)*T`.

## 10. CCM25 Canonical Owner Rule

The canonical finite-prime path must preserve one source owner through:

```text
source Weil-form
source evaluation data
visible arithmetic
canonical atom normalization
package certificate data
restricted/global direct term masses
```

Do not lower the route by moving among equivalent wrapper spellings. The
following are compatibility views unless a named theorem proves otherwise:

```text
package atom read-off
source-test read-off
common evaluator-value mass
route-symbol global mass
global archimedean cancellation
psi/pole collapse
direct global unfiltered term mass
```

Support data plus visible arithmetic is insufficient when package atoms can
come from another source. Package-atom alignment and same-owner transport are
mandatory.

The former concrete `SourceWeilFormData` target is uninhabited. Its global
support carrier requires every indexed atom to be nonzero for every test,
including the zero test; coverage then forces all concrete finite-prime terms
to vanish. The axiom-free guard is:

```text
CCM25SourceDataGuards.not_nonempty_concreteSourceWeilFormData
```

Do not construct, wrap, or transport that rejected type. Plan 013 replaces it
with a selected compact log-coordinate owner whose convolution is an integral,
whose values retain complex phase, and whose finite support depends on the same
selected convolution square.

## 11. B3 And RH-Level Guards

Detector-only coverage is not a lower producer after detector existence is
available. The detector calibration family, transport detector family,
QW/pole collapse, and selected final detector criterion have named RH-level or
no-off-line-source-zero equivalence guards.

Do not use these as closure for 012 or 013:

```text
SourceRH
no-off-line source-zero
CC20 Proposition C1 source criterion
selected detector criterion coverage
psi equals pole
detector-only calibration coverage
```

Plan 016 owns the attempt to remove or reject this outlet. It combines the
corrected trace remainder, selected CCM25 owner, conditioned detector theorem,
root retirement, and final audit in one dependency graph.

## 12. Coding And Review

Follow existing namespaces, naming, imports, and theorem layout. Make local,
reversible changes. Extract helpers only when they remove proof duplication or
preserve a same-object invariant.

For a nontrivial change:

```text
state the old weak path
add the lower data/API
prove projection or compatibility theorems
rewire the real consumer
prove the old path is inactive
add negative guards for the shortcut being removed
```

Comments should explain mathematical ownership or a Lean elaboration hazard.
Do not narrate obvious code.

## 13. Documentation

`AGENTS.md` stores stable working rules. `MEMORY.md` stores the current route
snapshot and milestone evidence. Plan documents store executable dependency
trees.

Keep root documents concise. Git history owns superseded chronology. When a
new theorem changes the active root, update the source-of-truth section instead
of appending another contradictory “current root” paragraph.

Every plan must state:

```text
scope and explicit non-goals
current code evidence with file and line references
source evidence with URLs or manuscript lines
exact data-bearing APIs
consumer rewiring path
rejection guards
smallest build and focused axiom audit
success, partial, blocked, and rejection criteria
```

## 14. Git And Public Hygiene

Use imperative commit subjects no longer than 72 characters. Commit and push
only coherent milestones and only when requested or authorized.

Before commit or push:

```text
git status --short
git diff --check
git diff --cached --name-status
git diff --cached --check
inspect staged file ownership
scan staged content for local paths and private workflow artifacts
```

Do not stage private workflow files unless the repository explicitly owns them
as public artifacts:

```text
AGENTS.md
MEMORY.md
RUNBOOK.md
HANDOFF.md
CONTEXT.md
WORKLOG.md
.codex/
local outreach or draft templates
```

Public GitHub text must not contain:

```text
Windows or WSL absolute paths
temporary verification directory names
private workflow artifact names
JSON escape fragments
mojibake
```

After posting or editing public text, read back the upstream body and verify
the rendered content. Resolve a review thread only after the matching fix is
complete, then read back the thread state.

## 15. Handoff Standard

A milestone handoff must answer:

```text
result: good / partial / blocked / rejected
RH status: unconditional or still conditional
files changed:
declarations added or changed:
active root removed or lowered:
old weak path inactive evidence:
build target and result:
import-facing audit result:
focused axioms:
remaining mathematical bottom:
next safe action:
```

Do not claim “proved RH” from a successful build. The final claim requires plan
016 Phase 8 to show that `#print axioms unconditional_rh_skeleton` contains no
project roots and no `sorryAx`, followed by the full repository verification
gate.
