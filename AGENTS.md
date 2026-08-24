# AGENTS.md

Working rules for the Connes-Weil RH formalization. This file holds stable,
reusable rules only. Proof-by-proof guards, rejected routes, and chronology
live in `MEMORY.md` and `docs/proofs/`; git history owns superseded detail.
When a new theorem changes the active root, update the relevant section here
instead of appending another "current root" paragraph.

## 1. Project Target

Aimed at a formal Connes--Weil route to RH in Lean 4 / mathlib `v4.30.0`.
The repository does **not** yet prove RH unconditionally. The active theorem
root is the RH-level detector criterion coverage axiom
`normalizedSelectedFinalRouteDetectorCriterionCoverageRoot`; Physical Gate 3U
is a separate diagnostic branch, not the current RH root.

## 2. Current RH Root And Route Split

The shortest live consumer chain is:

```text
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
  -> normalizedSelectedFinalRouteSourceRHFrom08AFromTheorems
  -> cc20FiniteVanishingExitFromTheorems
  -> rhDefinitionBridgeToMathlibFromTheorems
  -> unconditional_rh_skeleton
```

`CC20RouteRealization.normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_standardSourceRH`
proves that this coverage proposition is equivalent to `SourceRH` once the
already-proved Yoshida detector existence theorem is supplied. It is therefore
an RH-level statement, not a lower assembly socket.

### 2.1 Mainline Freeze (2026-08-19)

Gate 3U, Route-A finite bands, infinite-carrier cancellation, Lane R/Gamma
prefix experiments, numerical probes, and rejected alternative routes are
archived and frozen. They are diagnostic context, not RH consumers. New work
must name a direct consumer of `normalizedSelectedFinalRouteDetectorCriterionCoverageRoot`
before implementation. Shared source files that remain imported for build
compatibility must not gain new dependencies from frozen namespaces. Reopen a
frozen route only after a checked theorem directly implies the active root and
the result is recorded in `MEMORY.md`.

### 2.2 Proof-First Evidence And Numerical Work Guard (2026-08-19)

Substantive mathematics and formal proof take priority over numerical probing.
Do **not** run or add a numerical experiment merely because it is convenient,
interesting, or available.  Before any numerical work, name the exact open
theorem or route decision it can change and the concrete acceptance/rejection
criterion it will test.

Numerical work is allowed only when at least one of these conditions holds:

1. it is a bounded kill-test for a live candidate and can reject that route;
2. it distinguishes mathematically different owners while no formal theorem
   yet decides between them; or
3. it is a regression check for a newly implemented concrete theorem, with the
   formal theorem remaining the actual evidence.

If an existing Lean theorem already settles the coefficient, identity, or
ownership question, use that theorem and its audit instead of repeating a
numerical screen.  Numerical output must never be presented as a proof of a
limit, positivity statement, the active detector root, or RH.  Diagnostic
probes must remain outside the RH-facing dependency graph and must not create
new dependencies from frozen namespaces.

The preferred decision order is:

```text
exact formal theorem / missing proof obligation
  -> direct mathematical construction or counterexample
  -> bounded numerical diagnostic only if it changes the route decision
```

The constructive route toward that root must keep one mathematically correct
test-space owner through the log/positive coordinate change, true Mellin
convolution, the pole and archimedean terms, all prime-power terms, the explicit
formula, finite-vanishing criterion, and Yoshida detectors. The repaired C1
modules now close the object, readback, and center-`2` Gate 2 layers:

```text
CompactLog -> positive-variable coordinate bridge CLOSED
healthy Mellin convolution                         CLOSED
complete same-owner pole/arch/all-prime functional CLOSED as definition/readback
zero-spectral absolute summability on every test   CLOSED
xi zero-index completeness (= exact xi zero set)   CLOSED
same-owner arithmetic = zero-spectral formula      CLOSED (center-2 contour)
positive-trace order consumer                       CLOSED
finite-window F†F producer                          CLOSED; fixed-carrier cutoff and
                                                    dominated-diagonal adapters CLOSED;
                                                    nonzero-root witness ruled out by
                                                    exact cutoff growth
concrete cutoff remainder/readback producer          OPEN
finite-vanishing Weil criterion on the same owner  OPEN (RH-level)
Yoshida finite-node interpolation on same owner    CLOSED
right-oriented Yoshida detector construction       CLOSED (same owner)
global spectral nonnegativity on vanishing squares OPEN (RH-level)
```

The spectral convergence half is unconditional and axiom-clean in
`C1SpectralSummability`: the completed-xi kernel moment gives dyadic xi growth,
Jensen bounds analytic zero multiplicity by `K * 3^n`, and compact-log Laplace
decay contributes `4^(-n)`. Since `3 < 4`, `spectralSummableProp F` holds for
every `CompactLogTest F`. Consequently `gate2ExplicitFormula_iff` reduces Gate
2 exactly to `C1SameOwnerWeil.psi F = C1SpectralWeil.spectralWeilValue F`.
`C1XiCenterTwoArithmeticAssembly.centerTwo_arithmetic_eq_spectral` proves that
equality by feeding the proved
`C1XiCenterTwoGamma.centerTwoGammaReadbackContract_of_halfAnchorGauss` into the
center-`2` contour assembly, and `gate2ExplicitFormula_centerTwo` is the
axiom-clean Gate 2 endpoint. The remainder-aware positive-trace consumer,
finite-window `F†F` producer, fixed-carrier cutoff adapter, and generic
dominated-diagonal trace-continuity adapter are closed. The exact cutoff-growth
theorem now rules out `CutoffDominatedTraceWitness g globalBasis` whenever
`g.test != 0`; it does not rule out every possible renormalized or
finite-window convergence mechanism. The concrete cutoff remainder estimate
and same-owner analytic readback remain open.
The stronger audit in `Dev/C1Stage3BareHSObstruction.lean` now also rules out
the bare whole-line FRONTIER-HS premise itself for every nonzero test; only a
new windowed or renormalized detector owner can remain viable.  The added
theorem `hsPremise_forces_zero_test` (contrapositive of
`not_bare_hilbertSchmidt_of_test_ne_zero`) sharpens this to the per-test form:
a single compact-log test whose bare convolution factor is assumed Hilbert--Schmidt
must vanish identically.  Hence the FRONTIER-CRUX step② root axiom
`C1Stage3FrontierCrux.frontierCrux_powerSpectrum_eq_weilValue`, which carries exactly that
per-test summability as its own premise, is only ever instantiated on the zero test (both sides `0`);
every nontrivial detector readback must pass through a windowed/renormalized owner.  All new
declarations audit to `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; full root build
`4147/4147`.

### C1 Common-Carrier Stages 1-2 (2026-08-19)

The finite arithmetic part of the positive-trace producer is now closed as a
separate, axiom-clean readback layer:

```text
Stage 1  crossingCommonCarrierData                     CLOSED
         basis-matching CLM transport and trace fields
Stage 2  C1CrossingEulerLogReadback                    CLOSED
         canonical finite prime-power enumeration and
         Euler-log carrier trace = finitePrimeSum/qw decomposition
Stage 3  positive A†A reorganization and cutoff limit  OPEN
```

`C1Stage3Characterization` records the exact logical boundary: for the
one-dimensional `Unit`/`ℂ` witness, a `PositiveTracePairLimitFamily` exists
for a test iff `0 ≤ C1SameOwnerWeil.qw g`, and uniformly over a finite
vanishing set this is equivalent to `healthyCriterionState`.  The witness is
conditional and rank-one; it is a characterization of the RH-level sign, not
the required same-owner analytic producer or a closure of Stage 3.

`C1CrossingEulerLogReadback` depends only on the active C1 owner,
`SelectedCrossingKernel`, and mathlib prime-power factorization.  It does not
import the frozen Gate-3U finite-S family.  Its endpoint is the exact finite
identity

```text
qw g = poleTerm (g * g) - archimedeanTerm (g * g)
       - Re (finite Euler-log carrier trace)
```

with carrier data and support containment explicit in the theorem
hypotheses.  This closes neither the moving-cutoff remainder nor positivity;
those remain the direct `PositiveTracePairLimitFamily` consumer gap.

### Stage-3 Projection-Square Candidate Kernel

The projection-square candidate's positive core is now an active, non-circular
node: `C1Stage3ProjectionKernel.stage3ProjectionKernel_isPositive` proves
`K_S = P_radial ∘ P_semilocal(S) ∘ P_radial − gramCorrectedTargetSonin ≥ 0` on the
common log carrier by delegating to `CCM24SemilocalFourierSupport.lean:234`.

Two reusable rules from this step (doc `1039_stage3_projection_candidate_admission.md`):

- **Dependency firewall:** an active C1 module may import shared source bricks
  (`Source.CC20Concrete.*`) but must NOT take a frozen Gate-3U route leaf as a new
  consumer.  The residual ledger
  `CCM24FiniteSProjectionTrace.sameObjectResidual` (lines 325/339) is such a leaf;
  re-prove any needed algebraic fact from the lower-level Sonin/prolate lemmas instead.

- **Pitfall — trace-class ≠ trace → 0:** `..._isTraceClassAlong` (lines 399/411 of
  that file) only says an operator is trace-class along a basis; it does not bound or
  send its diagonal sum to zero.  Do not cite trace-class as a remainder limit.

This round proves the positive core and finite-window operator wiring in the
active namespace only.  The same-owner readback to `qw g`, the triple-vanishing
ledger, and the remainder/defect limit remain open (Gates 2-4 of doc 1039;
the current canonical `D₂` owner is structurally rejected by the cutoff audit).

The active response bridge is now explicit in
`Dev/C1Stage3ProjectionResponseBridge.lean`: `C† K_S C` is factored through the
output compression and decomposed into `projectionResponse` plus two named
operator defects (`kernelInsertionSandwich` and `windowToResponseDefect`).
The associated named-basis trace ledger is conditional on trace legality of
`projectionResponse`; neither defect may be treated as a vanishing remainder
without a separate estimate.  Type equality on the common carrier is not an
operator identity.

The quantitative audit is in `Dev/C1Stage3ProjectionDefectBounds.lean`.
`kernelInsertionSandwich` has only the norm bound
`‖F‖² * ‖Z†KZ - I‖`; no decay rate follows without a compressed-kernel
compatibility theorem.  For the canonical symmetric cutoff,
`windowToResponseDefect` has an unbounded real trace for every nonzero source
test when the fixed `projectionResponse` is trace-class.  Therefore do not
reintroduce an independent `D₂,n → 0` obligation for this owner: the route is
structurally rejected and needs a renormalized correction or a different
detector owner.  Trace-class alone is not a limit estimate.

The compressed-kernel compatibility question for `D₁` is now answered at the
reduction level in `Dev/C1Stage3ProjectionDefectBounds.lean`.  With
`Z = fullBoundaryOutputZeroExtension a c`:

- `kernelInsertionDefect_eq_compressedKernelDifference` proves
  `D₁ = Z.adjoint ∘L (K_S - id) ∘L Z`, i.e. the defect compresses the single
  **fixed, cutoff-independent** operator `K_S - id`; and
- `norm_kernelInsertionDefect_le_kernelDifference` proves
  `‖D₁‖ ≤ ‖K_S - id‖`, since both `Z` (zero-extension isometry) and `Z.adjoint`
  are contractions.

So plain windowing gives a **uniform, window-independent upper bound** for `D₁`:
it cannot blow up along any cutoff sequence, but it also has no built-in decay —
forcing `‖D₁(a_n,c_n)‖ → 0` requires `K_S` to act as the identity on the growing
window subspaces (equivalently `Z†(K_S - id)Z → 0`), a property of the kernel, not
of the window.  Both declarations are axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`).

- **Pitfall — let-bound operator + simp direction:** in the norm proof `Z` is a
  local `let`, so `unfold fullBoundaryOutputZeroExtension` on goal `‖Z u‖ ≤ …` does
  nothing (the def name is not literally present).  Unfold it by listing the binding:
  `simpa only [Z, fullBoundaryOutputZeroExtension] using norm_…`.  And when the bound
  RHS is a left-multiple `1 * ‖u‖`, simp needs `one_mul` (reduces `1 * x → x`), not
  `mul_one` (which reduces `x * 1`).

The reduction is now pushed one level down to **quadratic form**, which is the
precise statement of what "‖D₁‖ → 0 along a cutoff sequence" demands.  The active
theorem `kernelInsertionDefect_quadraticForm_eq_compressedGlobalDefect` proves, for
every window test `u`,

```
⟪u, D₁ u⟫   =   ⟨Z u, (K_S − id)(Z u)⟩     (global inner product)
```

i.e. the window quadratic form of the defect is **literally** the global
`(K_S − id)` quadratic form evaluated on the embedded vector `Z u`.  So forcing
`D₁ → 0` in norm along a cutoff is exactly asking that `K_S` act as the identity,
in the quadratic-form sense, on the embedded window subspaces `range Z` — a clean
named analytic premise about the kernel, not the window.

- **Pitfall — apply the operator inside the quadratic form:** write
  `inner ℂ u ((kernelInsertionDefect …) u)`; passing the bare operator
  `inner ℂ u (kernelInsertionDefect …) u` leaves an unapplied `→L[ℂ]` map in a
  vector slot ("expected type ↥(Lp …)").  The window L² space pretty-prints as
  `↥(Lp ℂ 2 volume)` but is the same `Lp ℂ 2 (volume : Measure …)` type, so an explicit
  `(u : Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)))` annotation works.

- **Pitfall — adjoint-inner lemma namespacing:** the fundamental adjoint identity is
  `ContinuousLinearMap.adjoint_inner_right (A x y) : ⟪x, A† y⟫ = ⟪A x, y⟫`; it lives in
  `namespace ContinuousLinearMap` (revealed by the scoped line
  `postfix:1000 "†" => ContinuousLinearMap.adjoint`).  The bare name
  `adjoint_inner_right` is **not** in scope and gives "Unknown identifier".

This round closes the self-adjointness + exact-zero companion for `D₁`, still in
`Dev/C1Stage3ProjectionDefectBounds.lean`.  Two new theorems, both axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`; zero `sorryAx`; full-root build `4147/4147`):

- **Self-adjointness.** `kernelInsertionDefect_iselfAdoint` proves `D₁` is self-adjoint because
  it is the compression `Z†(K_S − id)Z`: both summands of `K_S − id` are symmetric (`K_S` is
  positive, hence symmetric; the identity is trivially so), so `K_S − id` is, and a compression
  of a self-adjoint map by any bounded factor stays self-adjoint (mathlib
  `IsSelfAdjoint.adjoint_conj Z`).

- **Exact iff companion.** `kernelInsertionDefect_eq_zero_iff_quadraticFormZero` proves
  `(∀ u, ⟪u, D₁(u)⟫ = 0) ↔ D₁ = 0`.  The forward direction uses only self-adjointness: for a
  symmetric operator each Rayleigh quotient equals its real quadratic form, which the hypothesis
  fixes at zero; hence `‖D₁‖ = ⨆ |rayleighQuotient|` (mathlib
  `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient`) is zero and so is `D₁`.  The reverse
  direction is immediate.

- **Pitfall — self-adjoint/symmetric identifiers look misspelled:** the symmetry projection on
  `IsSelfAdjoint` and the companion instance token (e.g. the `.id` term used at line 243) carry a
  spelling that reads like a typo (`…Symetric`, not `…Symmetric`).  Capture these tokens verbatim
  from the file bytes — retyping them as "correct" English breaks the build with unknown-identifier.

- **Pitfall — ⟪·,·⟫ binds the scalar implicitly and gets stuck:** `inner_re_symm x y : re ⟪x,y⟩ =
  re ⟪y,x⟩` infers the scalar field from context; on a let-bound `Lp`/AddSubgroup carrier that
  inference leaves an unsolved metavariable (`stuck InnerProductSpace ?m …`).  Use the explicit-inner
  class field instead, pinning the scalar to `ℂ`:
  `((inferInstance : InnerProductSpace ℂ E).conj_inner_symm a b) : conj (inner ℂ b a) = inner ℂ a b`.

- **Pitfall — turn `‖T‖ = 0` into the target `T = 0`:** with goal `D₁ = 0` and a proof of
  `‖D₁‖ = 0`, rewrite first with `rw [← norm_eq_zero]`.  A plain forward `rw [norm_eq_zero]` fails —
  it searches for an existing `‖_‖ = 0` on the LHS, but the target is a bare `_ = 0`.

The same obstruction is now proved for a moving response owner.  The active
definitions/theorems `cutoffWindowToMovingResponseDefect`,
`ordinaryTraceAlong_cutoffWindowToMovingResponseDefect_eq_sub`, and
`cutoffWindowToMovingResponseDefect_trace_re_cofinal_unbounded_of_sourceTest_ne_zero`
show that any response family whose real trace has a uniform upper bound still
leaves a cofinal-unbounded defect on every nonzero source test; the matching
`not_tendsto_zero_...` theorem rules out a zero limit.  Thus the surviving
design space is narrower than “let the response vary”: the response itself
must carry the divergent bulk (or be replaced by a finite-part/renormalized
owner).  WSL2 ext4 owner/probe builds `3820/3820` and `3821/3821` are green;
the four moving-response declarations are axiom-clean with no `sorryAx`.

The `D₁` sufficiency gap is now isolated cleanly.  The active theorem
`norm_cutoffFullBoundaryRootFactor_le_globalConvolution` bounds every
canonical-cutoff root factor by the fixed whole-line convolution norm, because
the cutoff factor is global convolution followed by a restriction contraction.
Consequently
`tendsto_norm_cutoffKernelInsertionSandwich_zero_of_compressedDefect` proves
operator-norm convergence of `D₁,n` from the single explicit premise
`‖Zₙ† K_S Zₙ - I‖ → 0`.  This is a sufficient-condition theorem, not a proof of
compressed-kernel decay; trace-class and positivity still do not supply that
premise.  The WSL2 ext4 owner/probe builds `3820/3820` and `3821/3821` and the
axiom audit are green with only `[propext, Classical.choice, Quot.sound]` and
zero `sorryAx`.

The finite-window Gate-2 ledger is now assembled in the active leaf
`Dev/C1Stage3ProjectionFullReadback.lean`:
`stage3ProjectionFullReadback_qw_eq_pole_sub_arch_sub_trace_add_defects`
combines the existing same-owner `qw` readback with the exact finite-window
trace bridge.  Its formula keeps the arithmetic residual, `D₁` insertion
defect, and `D₂` window-to-response defect as separate real traces.  This is
an exact identity only; no defect limit or RH conclusion is inferred.  WSL2
ext4 verification is green: owner `3714/3714`, import-facing probe `3715/3715`,
and locked full-root `lake build ConnesWeilRH` `4147/4147`; the declaration
audits to `[propext, Classical.choice, Quot.sound]` with zero `sorryAx`.

### C1 Stage-3 Windowed Trace — Program P step 2 (operator-level correction family) (2026-08-23)

Program P **step 2** lifts the §C *scalar* bulk witness to an explicit rank-one
positive self-correction **operator** whose own Hilbert–Schmidt mass reads back to
`qw g`, generalized from the narrow root `gV = narrowArchRoot` to an arbitrary
vanishing test `g`. All in `Dev/C1Stage3WindowedTraceP3a.lean`:

- `correctionScale g d0 hqw := Real.sqrt (C1SameOwnerWeil.qw g / ‖d0‖⁴)` — the scalar
  whose square is exactly the Weil value over the vector's norm⁴; needs only an
  independent lower bound `hqw : 0 ≤ qw g` to be a real number.
- `rankOneCorrectionMap g d0 hqw := InnerProductSpace.rankOne ℂ ((correctionScale…) • d0) d0` —
  finite-rank hence Hilbert–Schmidt; its column-norm factorizes as
  `‖T e_i‖² = ‖(s•d0)‖² · ‖⟨d0, e_i⟩₍ℂ₎‖²`.
- `reTrace_eq_hilbertSchmidtMass` (Step ①): for **any** self-pair data with `left = right`,
  `Re Tr(T†T) = ∑' i ‖T e_i‖²` — the real self-trace equals the HS mass.
- `rankOneCorrection_HS_mass_eq_qw` (Step ②): that operator's HS mass is exactly `qw g`,
  proven from only `hqw : 0 ≤ qw g` and a nonzero vector (`hd0 : 0 < ‖d0‖²`). Because each
  self-pair is intrinsically positive, the nonnegativity of `qw g` for vanishing tests is
  **concluded, not assumed** — the same non-circularity that made P3-a clean at the narrow root.
- `positiveTracePairLimitFamily_of_rankOneCorrection`: assembles a full
  `C1PositiveTraceLimitBridge.PositiveTracePairLimitFamily` for an arbitrary test `g` (constant
  rank-one correction, remainder identically 0, readback tending to `qw g`). This generalizes the
  narrow-root `p3aFamily` uniformly over tests.

Axiom-clean: all three new results depend only on `[propext, Classical.choice, Quot.sound]`, zero
`sorryAx`; the owning-module and import-facing probe builds pass, and a locked full-root build on the current
`HEAD` completes 4147/4147 jobs (`LAKE_EXIT=0`). **Consumed end-to-end (§D):** `C1Stage3FrontierStatus.frontierStatus_healthyCriterionState_of_rankOneCorrection` feeds this family as the uniform `hfamily` of `p4_healthyCriterionState`, yielding `C1.healthyCriterionState F`. On the operator-level route Stage-3 windowing now reduces to a single isolated premise — every vanishing test has nonnegative Weil value (`0 ≤ qw g`) — taken explicitly (sign-transparent, non-circular at `narrowArchRoot` via `C1LaneRStrictness.narrowArchRoot_qw_pos`). RH still unclaimed.

### C1 Stage-3 Projection Operator Contract (2026-08-23)

`C1PositiveTraceLimitBridge.PositiveTraceOperatorLimitFamily` is the correct
contract for a window owner of the form `C† K C` when `K` is positive but no
same-factor square root has been constructed.  It records, for each cutoff,
the operator, named-basis trace-class evidence, and `ContinuousLinearMap.IsPositive`,
then keeps the real remainder and same-owner `qw` readback as separate limit fields.
`positiveTraceOperator_re_nonnegative` and its order consumer derive the sign
only from those two operator facts; they do not identify `C†KC` with `F†F`.

`Dev/C1Stage3ProjectionOperatorFamily.lean` instantiates this contract with
`cutoffProjectionPairData`, proving `cutoffProjectionOperator_isTraceClassAlong`
and `cutoffProjectionOperator_isPositive`.  The structure
`ProjectionCutoffLimitContracts` intentionally leaves the cutoff remainder and
`qw` readback as caller-supplied analysis.  The uniform healthy-criterion
consumer is therefore conditional and does not close the RH root.

Focused WSL2 ext4 verification: owner `3707/3707`, import-facing probe
`3708/3708`; all six audited declarations use only
`[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.  Do not weaken
the operator contract back to `left = right`: positivity of a bounded kernel
under adjoint conjugation is a different fact from self-pair factorization.

The projection owner now also has an exact trace ledger in
`Dev/C1Stage3ProjectionOperatorFamily.lean`:
`cutoffProjectionOperator_trace_re_nonnegative` derives the scalar sign from
operator positivity and trace-class evidence,
`ordinaryTraceAlong_cutoffProjectionOperator_eq_projectionResponse_add_defects`
expands `C† K C` into `projectionResponse + kernelInsertionSandwich +
windowToResponseDefect`, and
`realTrace_cutoffProjectionOperator_eq_selectedArithmetic_add_defects` attaches
the same owner to `selectedArithmeticCarrierSum` plus the explicit
`sameObjectResidual` and both defects.  These are exact identities only; no
defect limit, `qw` readback, or RH conclusion is asserted.  The focused WSL2
owner/probe builds are `3713/3713` and `3714/3714`, with the three new audited
declarations using only `[propext, Classical.choice, Quot.sound]` and zero
`sorryAx`.

### C1 Positive-Trace Cutoff Growth Guard

For the canonical symmetric cutoff, the finite-window square has the exact
identity

```text
Re Tr(cutoffPositiveBasisData g globalBasis n).positiveComposition
  = (cutoffUpper g n - cutoffLower g n)
      * ∫ x, Complex.normSq (g.test x)
```

`integral_normSq_pos_of_test_ne_zero` proves that the mass factor is strictly
positive when `g.test != 0`, and
`cutoffPositiveBasisData_trace_re_unbounded_of_test_ne_zero` consequently
proves unbounded growth in `n`. Therefore
`not_nonempty_cutoffDominatedTraceWitness_of_test_ne_zero` excludes the
current fixed-basis summable diagonal-majorant witness for every nonzero root.
Do not reintroduce that witness as if it followed from finite-window
Hilbert--Schmidt compactness. This obstruction says nothing by itself about a
renormalized trace, a finite-window subtraction, the cutoff remainder, or the
same-owner analytic readback.

### C1 Bare Whole-Line Hilbert--Schmidt Obstruction

The current FRONTIER-HS premise is false for every nonzero compact-log test.
`Dev/C1Stage3BareHSObstruction.lean` proves this without adding an analytic
axiom: `cutoffPositiveBasisData_operator_eq_postcomp` identifies each finite
cutoff with the bare convolution followed by interval restriction and
zero-extension; `norm_cutoffWindowPostcomp_le_one` makes that postcomposition a
contraction; and `cutoffEnergy_le_bareHS_mass` transfers any bare HS mass bound
to every cutoff.  The exact cutoff trace-growth theorem then contradicts that
uniform bound, yielding `not_bare_hilbertSchmidt_of_test_ne_zero` and the
universal counterexample `not_forall_bare_hilbertSchmidt`.

Do not infer whole-line HS summability from the finite-window HS producer.  The
negative theorem only kills this bare owner; it does not kill a renormalized or
finite-window detector, and it supplies no cutoff remainder or same-owner
`qw` readback.  Any replacement must state its own factor and preserve the
coefficient/readback audit.

### C1 Detector Prime-Power Kill-Test Guard

The 2026-08-19 finite screen in
`docs/proofs/1036_mellin_conjugated_detector_kill_test.md` rejects the naive
Mellin-conjugated Hilbert commutator
`[M_(1/2) H M_(-1/2), P_[0,L]] C_g` as a C1 detector owner: its finite trace
has a cutoff-length bulk.  Removing the conjugation removes the sampled bulk,
but still misses the exact `m = 2` prime-power coefficient.  Any replacement
detector must keep one owner for `g`, `g^* * g`, and all readback terms, and must
pass the coefficient
`p^(-m/2) * log(p) * (F(m*log(p)) + F(-m*log(p)))` at `m = 2` before a
remainder estimate or Lean `PositiveTraceLimitFamily` is introduced.  The
probe is diagnostic finite-section evidence only; it does not close global
spectral nonnegativity or RH.

The completed-xi zero set is exactly the source spectral index:
`completedRiemannXi_eq_zero_iff_sourceNontrivialZero` (in `CC20ZetaCounting`)
is axiom-clean; the functional equation reflects negative-even zeta zeros into
the zero-free closed right half-plane. The spectral sum indexes the exact xi
zeros, not a subset.

### C1 W4 Hermitian Partner Guard (2026-08-24)

`Dev/C1XiConjugation.lean` proves the completed-xi conjugation identity
`completedRiemannXi (star z) = star (completedRiemannXi z)` using the real-valued
Hurwitz kernel and `Complex.cpow_conj`; the theorem is axiom-clean. The active
partner leaf `Dev/C1SpectralHermitianPartner.lean` then defines the source-zero
transport `rho -> star rho -> 1 - star rho`, proving the centered coordinate is
`-star w` and the transport is involutive. The square spectral term transports
by exact conjugation only under the explicit hypothesis
`xiMultiplicity (hermitianPartner rho) = xiMultiplicity rho`.

Do not write an unconditional off-line `2 * Re` pairing: before multiplicity
transport is proved, the exact pair decomposition has the residual
`(m_partner - m) * Re (L(g□)(w))`. This is the named W4 multiplicity defect,
not a simplification artifact. The partner module compiles natively with only
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

### C1 Coordinate, Owner, And Sign Guards

`CompactLogTest.test` and route `TestFunction` have the same Lean function type
but different mathematical coordinates. The former reads `u = log x`; the
latter reads the positive variable `x`. The canonical bridge is
`C1LogPositiveBridge.toPositiveRouteTest`, with
`mellin_toPositiveRouteTest_eq_laplaceAt` as its coordinate contract. Never
replace this map by the identity merely because the types unify.

The complete compact-log arithmetic functional is owned by
`C1SameOwnerWeil`: `psi F` is pole minus archimedean minus every nonzero visible
prime-power term, and `qw g = psi g.convolutionSquare`. The sign convention is

```text
source QW(g) = psi(g^* * g)
CC20 local sum on starConvolution(g) = -source QW(g)
```

Faithful numerical probes must use the real Laplace points `+1/2` and `-1/2`,
sample prime-power terms at `+/-log(n)`, include all visible prime powers, and
assert `F(0) = ||g||^2` plus the pole-product identity. The historical use of
`i/2`, raw coordinates such as `F(2)`, or a singleton `{2}` sum does not
evaluate this functional.

Support width is metadata, not object identity. A numerical residual and a
Lean plateau with the same support interval are different owners unless a
theorem identifies their functions and all attached data. Never transfer a
numeric sign across that gap.

### C1 Arithmetic Right-Line Guard

`C1XiArithmeticIntervalReadback` expands the von Mangoldt L-series only at
`1 < Re(s)`, where Mathlib supplies absolute summability. Its interval theorem
is a genuine `HasSum` exchange with an explicit majorant; it is not an
integrability theorem disguised as a dominated-convergence call.

Finite prime-power truncations may be continued to `c -> 1+` by ordinary
continuity after composing the two-parameter function with `c |-> (c,t)`. The
elementary pole factor `1 / (verticalPoint c t - 1)` is singular at `t = 0`:
an unrestricted pointwise boundary theorem is false because it contains
`1 / (c - 1)`. Any boundary proof must state `t != 0` or use an a.e./integral
argument that explicitly handles this null point.

The full von Mangoldt boundary at `Re(s) = 1` remains a separate
`FullPrimeBoundaryContract`; never infer it from absolute convergence on the
right half-plane.

The public assembly theorems
`intervalIntegral_verticalIntegrand_eq_arithmetic_components` and
`intervalIntegral_verticalIntegrand_eq_arithmetic_primePower_series` now read
the same right-line owner back at every finite height for `1 < c`: first as
pole plus Gamma_R plus the full von Mangoldt interval term, then as the
convergent sum of integrated prime-power terms. They are finite-height
right-half-plane identities only. Do not rewrite them as a `c = 1` boundary
theorem or as the missing arithmetic/spectral equality.

The finite-height arithmetic ledger in `C1XiArithmeticFiniteHeightLedger`
only adds three terms along one sequence carried by the elementary-pole
remainder contract: Gamma_R, a finite prime-power truncation, and the
elementary pole.  Its `c_k -> 1+` limit is not a producer for the full
von-Mangoldt boundary or the same-owner arithmetic/spectral equality.  Keep
the finite truncation and the full L-series as separate owners.

When using the persistent WSL2 ext4 verification mirror, sync the complete
`C1XiArithmetic*.lean` batch first if the mirror predates the current arithmetic
commits; otherwise Lean can report a misleading missing-import error before
checking the changed theorem.

The Gamma_R contribution is regular on `Re(s) > 0`.  The public
`continuous_gammaRIntegrand_intervalIntegral` theorem therefore works on the
positive-real subtype, and
`tendsto_gammaRIntegrand_intervalIntegral_c_to_one` gives its finite-height
right-hand `c -> 1+` limit.  This closes only the Gamma_R factor.  It does
not regularize `1 / (c - 1 + t*I)` at `t = 0`, nor does it supply the full
von Mangoldt boundary or the arithmetic/spectral equality.

The Fourier readback brick uses Mathlib's `Measure.integral_comp_mul_left`
with only `(g) (a)` explicit arguments; `volume` is implicit.  Its right-hand
side is a real scalar action on a complex integral, so normalize it with
`Complex.real_smul` before comparing it with complex multiplication.  For
`Real.fourierInv_eq'`, coerce a Schwartz Fourier transform explicitly to
`Real -> Complex` and use `SchwartzMap.fourierInv_coe` when moving between the
Schwartz and function-level inverse transforms.

`C1XiArithmeticPrimePowerReadback` now exposes the full-line Fourier inversion
API and the reflected-character consumer.  The direct profile reads
`F(log n)` and the reflected profile reads `F(-log n)` after the explicit
change of variables `t -> -t`; do not replace that step by an evenness claim
about the test.  The completed single-index readback is only at `c = 1`, and
it is a theorem for one von Mangoldt term, not a boundary convergence theorem
for the full prime-power series.  Keep the `n = 0` zero branch separate before
using `log n` or `1 / sqrt n`.

`C1XiArithmeticPrimePowerAssembly` assembles those terms over the exact finite
`C1SameOwnerWeil.globalPrimeIndexSet F`.  It proves integrability of every
single term at `c = 1`, exchanges the finite sum with the full-line integral,
and reindexes the range truncation at `globalIndexBound F` to that same owner.
The endpoint
`integral_finiteArithmeticPrimePowerIntegrand_one_at_globalIndexBound_eq`
is therefore a finite `c = 1` readback to `finitePrimeSum` (after taking real
parts), not a proof of `FullPrimeBoundaryContract`, the infinite von Mangoldt
boundary, or the arithmetic/spectral equality.

`normalized_integral_globalPrimePowerIntegrandSum_eq` removes the exact
`2 * pi * I` Fourier normalization, and
`normalized_integral_globalPrimePowerIntegrandSum_re_eq_finitePrimeSum` reads
its real part back to the same finite owner. The complex prime-power sum must
not be replaced by a real cast before taking `re`: the formula test is complex
valued in general.

For `T >= 0`, the same module proves continuity and a right-hand `c -> 1+`
limit for the finite truncation interval integral.  This is a legitimate
finite-height parameter bridge because the finite prime-power owner is
continuous on a compact interval.  Do not transfer it to the elementary pole
term: `1 / (c - 1 + t*I)` is singular at `t = 0`, so the pole boundary still
requires an a.e. or distributional argument.

`C1XiArithmeticPoleBoundary` now isolates the elementary pole into a regular
factor and a singular Cauchy kernel.  For `c > 1`, the unweighted singular
kernel has the exact finite-height integral
`-2 * arctan(T / (c - 1)) * I`, and for `T > 0` its right-hand limit is
`-pi * I`.  The regular factor has a genuine interval-integral continuity
theorem on the positive-real subtype and a right-hand `c -> 1+` limit.
The weighted singular term must be split with its actual value
`symmetrizedLaplaceWeight F (verticalPoint c 0)`; it cannot be frozen at
`c = 1` before taking the limit.  The remainder boundary is therefore carried
by the data-bearing `ElementaryPoleSingularRemainderBoundaryContract` field
`remainderBoundaryValue`, not defined as zero.  Its assembly theorem consumes
that contract and proves only the finite-height elementary-pole limit; it does
not prove the full von Mangoldt boundary or the arithmetic/spectral equality.

### C1 Xi-Contour Guard

`logDeriv completedRiemannXi` is total at a zero, whereas a residue argument
needs its punctured meromorphic meaning. At a xi zero `rho`, obtain one local
cofactor `h` with `xi(s) = (s-rho)^m h(s)` and `h(rho) != 0`; derive the
analytic disc, zero-free disc, and principal-part identity from that same
`h`, then choose the contour radius below all three. Never read the total
value `logDeriv completedRiemannXi rho` as a residue.

The finite closed-ball xi factorization supplied by Mathlib is initially only
`codiscreteWithin`. At an interior point, first use the meromorphic identity
principle to obtain equality on `𝓝[≠] z`, then continuity to obtain equality
on `𝓝 z`; only this neighborhood equality may transport `deriv` or `logDeriv`.
The resulting finite pole sum is valid only away from the local divisor
support. Do not claim it on the closed-ball boundary or at a divisor point.
Inside the open ball, use `xiClosedBallDivisor_mem_support_iff` to translate
that owner-local exclusion exactly into `completedRiemannXi z != 0`, then use
`logDeriv_completedRiemannXi_eq_sum_add_cofactor_of_ne_zero`; this is the
public punctured-contour API and does not license evaluation at a zero.

The finite principal part and the regularized kernel are separate contour
owners. Apply rectangle Cauchy only to `xiClosedBallRegularizedKernel`, which
is differentiable on the whole open factorization ball. For a circle around
one selected zero, first prove that its closed disc contains exactly that
support point; integrate that principal term with
`circleIntegral.integral_sub_inv_of_mem_ball`, and prove every other finite
pole term has zero circle integral from
`Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable` on the
closed disc. Do not infer the latter from a support-point slogan: the
closed-ball exclusion is an explicit hypothesis of the principal-part API.

The finite-factor local-residue interface is now closed:
`circleIntegral_xiClosedBallRegularizedKernel_eq_zero_of_closedBall_subset`
uses Cauchy only for the regularized kernel on a closed disc contained in the
open factorization ball, while
`circleIntegral_xiContourKernel_eq_neg_spectralTerm_of_factorization_unique_support`
recombines it with the principal part only after the circle is xi-nonzero and
its closed disc excludes every other finite divisor support point. Callers
must preserve both `closedBall subset factorizationBall` and the explicit
unique-support premise; pairwise separation of a selected source family alone
does not exclude ambient xi zeros not selected by that family.

For a rectangle, use the named `xiRectangleBoundaryIntegral` and require both
the entire closed rectangle to lie in the same open factorization ball and all
four edges to satisfy `xiRectangleBoundaryAvoidsZeros`. The closed result
`xiRectangleBoundaryIntegral_xiContourKernel_eq_principal` removes only the
regularized remainder by Cauchy. The finite-pole rectangle readout is now
closed in `C1XiFiniteRectanglePrincipalPart`: a support-avoiding standard
rectangle reads exactly the factor-owned divisor points strictly inside it,
with the exterior contributions killed through four zero-free strips. The
result is reindexed in `C1XiFiniteRectangleSupportReindex` to the filtered
finite family `xiClosedBallSourceZerosInsideRectangle` and its one-weight
`spectralTerm` sum. Keep that filtered family tied to the same finite factor
owner; do not replace it by an arbitrary selected zero family, a circle, or a
height cutoff without a proved equivalence.

The symmetric critical-strip specialization is closed in
`C1XiFiniteHeightRectangle`: with `T > 0`, factor-ball containment, and
`xiHeightBoundaryAvoidsZeros T`, the filtered same-owner family is exactly
`finiteHeightZeros T`.  The horizontal zero-free condition is essential: it
turns the closed height condition `|Im rho| <= T` into strict rectangle
interiority. `exists_xiHeightBoundaryAvoidsZeros_gt` obtains such a height
above every lower bound by excluding the finite image `rho |-> |Im rho|`, and
`xiZeroFreeHeights` packages choices with unit gaps and `n < T_n`. Do not infer
the condition merely from finite height or from the zero-free vertical sides.
`C1XiQuantitativeHeight` strengthens this selection: for every `B >= 0`,
`exists_quantitative_xiHeightBoundaryAvoidsZeros` chooses `T` in `(B, B + 1)`
with a positive explicit separation from each ordinate in
`finiteHeightZeros (B + 2)`. Its gap is the finite-grid radius
`1 / (4 * (card + 2))`, where `card` counts the visible absolute ordinates.
The closed Jensen bridge
`xiHeightForbiddenOrdinates_dyadic_card_le` bounds that cardinality at
`B = 2^(n + 2)` by `spectralMultiplicityConstant * 3^(n + 1)`: it forgets
repeated ordinates, charges every remaining zero at least one analytic
multiplicity, enlarges the height window monotonically, then applies the
existing dyadic multiplicity estimate. This quantifies the finite grid on
dyadic base heights; its direct consumer
`xiHeightSeparation_dyadic_lower_bound` gives the corresponding reciprocal
lower bound for `xiHeightSeparation`. It supplies no `xi'/xi`, cofactor, or
contour-limit estimate.
The same selected height has an upper horizontal zero-free complex tube:
`xiHeightTubeRadius B = min (xiHeightSeparation B) (1 / 2)` and
`exists_quantitative_xiHeightBoundaryAvoidsZeros_tube` exclude xi zeros from
every ball of that radius centered at `x + T*I`. The half-unit cap keeps a
hypothetical zero in the finite `B + 2` window, while the grid gap excludes
it. This is zero-free geometry only, not a minimum-modulus, cofactor, or
`xi'/xi` bound. Its two-sided consumer
`exists_quantitative_xiHeightBoundaryAvoidsZeros_tubes` transports the same
radius and the same selected `T` to `x - T*I` through `z |-> 1 - z` and
`completedRiemannXi_one_sub`; do not select unrelated upper and lower heights.
`exists_dyadic_quantitative_xiHeightBoundaryAvoidsZeros_tubes` packages the
whole producer at each `n`: it selects `T` in
`(2^(n + 2), 2^(n + 2) + 1)` and supplies both tubes at the explicit radius
`min (1 / (4 * (spectralMultiplicityConstant * 3^(n + 1) + 2))) (1 / 2)`.
This is the correct geometric input for a quantitative analytic estimate, not
that estimate itself. `C1XiQuantitativePrincipalBound` now consumes this
input for the finite pole part only. Its
`exists_dyadic_quantitative_xiHeight_tubes_principal_bound` selects the same
height and bounds the exact origin-centered factor principal sum on both
horizontal lines by
`4 * N_n * (N_n + 2)`, where
`N_n = spectralMultiplicityConstant * 3^(n + 1)`. The proof reindexes the
same factor divisor mass to source multiplicities, bounds it by
`finiteHeightMultiplicity (T + 2) <= N_n`, and uses the zero-free tube to put
every factor pole at distance at least `1 / (4 * (N_n + 2))`. This is an
axiom-clean `O(9^n)` estimate for the finite principal part, not a bound for
`logDeriv` of the zero-free cofactor, the full `xi'/xi`, a horizontal contour
limit, Gate 2 equality, or RH. Keep the principal sum and cofactor as
separate terms of the same factorization owner.
`XiHeightRectangleFactorData` now packages each height with its own cofactor,
the containing ball centered at zero with radius `T + 2`, the zero-free
boundary, and the direct finite spectral readout; its producer is unbounded.
Do not reuse a factor owner across heights or infer any uniform cofactor bound,
horizontal-edge decay, or contour limit from this local data.

The finite-height vertical fold is closed in `C1XiFiniteHeightVerticalFold`:
`criticalStripVerticalBoundaryIntegral_eq_rightLineIntegral` converts the two
oriented zero-free vertical `xiContourKernel` integrals to the one
`verticalIntegrand` integral on `Re(s) = 1`. It uses the functional equation,
the parameter reflection `t |-> -t`, and interval integrability on the compact
height segment. It does not control either horizontal edge, any `xi'/xi`
growth, a common factor owner, or a limit as `T -> infinity`; never promote it
to a rectangle contour limit or fold the reflected weight into a local residue.

`C1XiFiniteHeightRectangleAssembly` combines that fold with the same-owner
finite rectangle readout. Its
`horizontal_add_foldedRightLine_eq_neg_finiteSpectralSum` endpoint states that
the two explicit horizontal edges plus the folded right-line integral equal
the finite spectral sum. This does not compare different height owners: any
limit argument must separately control the horizontal term and the right-line
integral along the selected zero-free sequence.

The compact-log test weight now has axiom-clean uniform fourth-order decay on
the closed critical strip:
`exists_uniform_centeredLaplaceWeight_vertical_quartic_decay_on_criticalStrip`.
`C1XiHorizontalDecay` first proves that each selected zero-free height `T`
has a finite envelope `M`: `xiHeightBoundaryAvoidsZeros T` makes
`negativeXiLogDeriv` continuous on each compact horizontal segment, and
`exists_xiHorizontalLogDerivEnvelope` applies compactness. It then bounds the
horizontal boundary by `2 * M * C / |T / (2*pi)|^4` through
`exists_quartic_horizontalBoundary_bound_of_xiHeightBoundaryAvoidsZeros`;
`XiHeightRectangleFactorData` supplies those height-local hypotheses. This
gives no rate comparing `M` at different heights, no uniform cofactor bound,
and no contour limit. Do not promote the pointwise product estimate to a
uniform `xi'/xi` growth theorem, horizontal-edge decay sequence, Gate 2
equality, or RH claim.

The next conditional layer is separated into three owners. `C1XiHABridge`
defines `GlobalWeightedLogDerivComparison` as an explicit contract and proves
that, when supplied, it reads the H-A1 zero sum back through the same finite
factor owner to `logDeriv g`; it is not a Hadamard/comparison producer.
`C1XiHorizontalLimit` combines the finite pole bound and this cofactor bound,
then proves the horizontal boundary tends to zero under the explicit
`M_n / |T_n/(2*pi)|^4 -> 0` contract. `C1XiFiniteHeightLimit` keeps a separate
`XiHeightRectangleFactorData` owner at every selected height and proves that
the folded right-line limit is `-(2*pi*i) * spectralWeilValue F` once the
horizontal, right-line, and finite-spectral limits are supplied. These are
conditional contour-spine theorems, not the arithmetic explicit formula.

`C1XiHAGrowthContract.xiGlobalWeightedDifference_norm_le_of_circle_growth_on_closedBall`
uses the maximum modulus principle to transport the selected-circle H-A3
bound to its closed disc. It consumes the existing circle contract only; it
does not produce the missing minimum-modulus lower bound, cofactor growth, or
the global Hadamard comparison.

`C1XiHAGrowthContract.exists_circle_minimum_modulus` is the honest qualitative
producer for the first part of that wall: a positive-radius circle with no xi
zeros has a strictly positive minimum modulus by compactness and the extreme
value theorem. It supplies an existential lower bound for one selected circle,
not a uniform or quantitative sequence in the radius. Do not use it as a
cofactor-growth, Borel--Caratheodory, horizontal-limit, or H-A5 producer.

`C1XiJensenCircle.xi_circleAverage_log_norm_eq_jensen` is the exact Mathlib
Jensen identity for `log ||completedRiemannXi||` on a positive circle centered
at `2`, with the divisor owned by the same closed ball used by the spectral
counting lemmas. `xi_circleAverage_log_norm_ge_center` proves only that the
circle average is at least `log ||xi 2||`, because every divisor correction is
nonnegative. An average lower bound is not a lower bound for the pointwise
minimum on the circle; neither theorem closes the quantitative H-A3
minimum-modulus/cofactor wall. The direct finite-factor estimate currently
loses an additional logarithm, so do not relabel this Jensen brick as the
order-one minimum-modulus producer.

The sharp xi growth theorem
`norm_completedRiemannXi_le_exp_of_halfplane_dyadic_rlogr` has exponent
`O(R log R)` at `R = 2^(n + 4)`. Its `3^n` successor is a deliberate geometric
relaxation used only by `spectralSummableProp`, where it is beaten by the
compact-log `4^(-n)` decay. Never call that relaxed bound an `R log R` bound.
Conversely, a numerator bound `|xi'| <= exp(O(R log R))` and a lower modulus
bound `|xi| >= exp(-O(R log R))` imply only the exponential quotient
`|xi'/xi| <= exp(O(R log R))`; they cannot produce a polynomial cofactor or
logarithmic-derivative bound. Do not use raw quotient division as H-A3. A
valid horizontal-edge producer must either prove a normalized analytic-log /
Borel--Caratheodory envelope `M_n` with `M_n / 16^n -> 0`, including its tube
radius loss, or prove the genus-one canonical-product comparison directly.

Data-bearing contracts must be ordinary structures, not `structure ... : Prop`:
Lean permits only proof fields in a Prop-valued structure, so a real/complex
constant field would erase the intended projections. Each height-specific
factor owner must remain explicit; never reuse one cofactor across heights.

`xiContourKernel` carries exactly one centered Laplace weight, hence one
spectral term per xi zero. The reflected weight belongs only to
`xiRightLineKernel` after the two vertical sides are folded; adding it to the
local residue double-counts the zero spectrum.

For a finite source-indexed zero family, choose circles only after mapping its
members to their complex coordinates and applying finite `T2` separation.
Each closed-ball radius must be strictly below both its separated-neighborhood
radius and its same-cofactor safe residue radius. Distinct source subtypes do
not by themselves justify geometric disjointness.

For a common contour, choose one finite-factor owner on an outer closed ball,
then require its whole divisor support to avoid the contour boundary. The
principal-part circle integral is the finite sum over every support point in
the enclosed open disc; it is not justified by summing only a preselected
source-zero family unless a separate support-index equivalence has been
proved. A factor-owned finite-family certificate may shrink its inner discs
for `T2` separation, but must retain its own outer cofactor and ambient
support-exclusion fields.

### Frozen Diagnostic Gate-3U Branch

This entire section is historical diagnostic context. It is sealed by the
mainline freeze above: do not extend it, promote it to an RH consumer, or use
its finite-band result as evidence for `SourceRH`.

The canonical real Gate 3U reduces exactly to a bound on the ordinary trace of
the already-declared `sourceGramResponse` owner (Proof 264 `(AA.1)`/`(AA.32)`,
Lean `CCM24FiniteSGramResponse.lean:563`). Readout chain:

```text
canonicalRealGate3UAt(...)                                    = CC canonicalRealGate3UAt
  <=>  |rawCompletePhysicalHermitianTrace(canonicalFamily)| <= bound       (Proof 798 readout)
  <=>  |Re Tr(sourceGramResponse owner lambda (canonicalFamily))| <= bound (free contract,
       CCM24FiniteSCausalMarkovRawSourceOwnerTrace.lean)
```

**Route-root decision (2026-08-10, docs/proofs/928): canonical deliverable = finite/
decaying-band route-A Gate; infinite-carrier Gate = open analytic bottom.** The
constructible and axiom-clean deliverable is the finite-band Gate `bandTerminalGate`
(`Dev/RouteATailBandBound.lean`): along ANY finite Hilbert band `rho` of the source
carrier, `|Re Tr_b (Tail)| <= card*C0*exp(-B/4)*prod` and the split identity closes
`canonicalRealGate3UAt` on that band (axioms `[propext, Classical.choice, Quot.sound]`,
0 sorry). The ORIGINAL infinite-carrier Gate reduces to ONE load-bearing analytic identity
`(I-P)F = -(I-P)D`, equivalently `sourceActualBandCombinedCoframeLeakage =
sourceActualBandForwardCoframe + sourceSoninCoframeLeakage = 0` on non-empty prime
families; no theorem forces it, numerics (probe 884) oppose it, and the deciding F-term
(exact Sonin intersection R0) is not numerically reachable (AGENT 818/819).
Carrier re-point (Piece 2) is necessary-but-not-sufficient on the infinite carrier
the bound `card * |Support|` diverges because `|Support|` does not decay in `B` (docs/927).
Route work continues on the finite/decaying-band Gate; the infinite identity stays OPEN
and is genuinely new math, not a Lean-assembly leaf.

The missing piece is a compact-root support bound for
`abs (ordinaryTraceAlong sourceBasis (sourceGramResponse ...)).re`, uniform in
the finite family, computed before any absolute value. The statement-planting
contract `CCM24FiniteSCausalMarkovRawRenewalTailBound.lean` now fixes the exact
split/assembly structure: the real trace of the complete physical owner splits
into support + tail (`inverseLowerFactorPhysicalRenewalTrace_eq_support_add_tail`),
the abs gate is bounded by the sum of the two piece bounds
(`inverseLowerFactorPhysicalRenewalTrace_split_bound`), and a uniform tail
trace-decay producer closes the canonical real Gate
(`canonicalRealGate3UAt_of_tailNormBound`, consumed through
`canonicalRealGate3UAt_iff_abs_inverseLowerFactorPhysicalRenewalTrace_le`).
The **whole-tail operator-norm bound** is now closed
(`CCM24FiniteSCausalMarkovRawRenewalTailBound.lean`): assembly through
`tsum_fintype` + `Summable.tsum_prod` + `forwardRenewalIndexEquiv` gives
`‖R^(>B)‖ ≤ C0 · ∑'_{disp>B} twoSidedRawWeight`
(`norm_inverseLowerFactorPhysicalRenewalTailResponse_le_const`), and chaining
the exponential tail decay from `CCM24FiniteSTwoSidedRenewal.lean`
(`finiteEulerTwoSidedRawWeight_tail_decay`; `a_p = e^{-(log p)/2}` makes `w =
exp(-D/2)` universal, on `{D>B}` pointwise `≤ exp(-B/4)·exp(-D/4)`, half-power
sum `∏_p (1+ρ_p)/(1-ρ_p)`, `ρ_p = e^{-(log p)/4} < 1`) gives
`‖R^(>B)‖ ≤ C0 · exp(-B/4) · ∏_p primeTwoSidedQuarterMass`
(`norm_inverseLowerFactorPhysicalRenewalTailResponse_le_const_exp`).

**Apex (2026-08-06, 815):** the whole Proof-717 / Gate-3U front reduces to ONE
open operator identity in TWO orthogonal channels
`OuterCh=(I−R)∘D` + `BandCh=forward+(R−R₀)∘D = 0` on the metric coframe
`D=finiteEulerMetricCoframe=H·J·G⁻¹` (channel split already in-library at
`CCM24FiniteSPhysicalCancellationChannelSplit.lean:84-101`; the `R₀+(R−R₀)`
orthogonal split at `JetOrientation.lean:312`). The `=0` holds only for
`visiblePrimes=[]` (`MarkovRawBase.lean:92`). No non-empty finite prime set is
closed. Numeric outer probe (814) shows `(I−R)∘T†` is a non-decay (0.70/1.30/1.99);
second channel numerically unreachable without the exact `R₀`. Either channel
`=0` (or both) is the entire remaining gate. See `docs/proofs/815`.
Do not split the physical branches before compact support acts; that was a
rejected condition-number argument (785/786/776/777/778/796).

The still-open analytic bottom is the **trace assembly**: feed this tail
operator-norm+decay through an `abs (Re Tr(R^(>B)))` bound via the
trace-class/operator-norm estimate, then add it to the compact support-trace
bound. Across the transported Sonin projection, trace support is not implied by
coefficient support (Proof 807 boundary), so no trace is interchanged anywhere
in the new module. Do not bound the inverse `(K_S* K_S)⁻¹` separately, cycle to
the polar isometry, or split the physical branches before compact support acts;
each is a rejected condition-number argument (see Proofs
785/786/776/777/778/796). `sourceBandGramResponse` is a def equal to
`-sourceGramResponse`; unwinding both negs makes `raw = +Re Tr(sourceGramResponse)
**Route-A finite-band Gate assembly CLOSED (2026-08-07, axiom-clean).** On ANY
finite Hilbert band [rho] of the real route carrier, `bandTerminalGate`
(`Dev/RouteATailBandBound.lean`) bounds the diagonal real trace by band
cardinality times the closed operator-norm bounds (support piece + tail
`rawRenewalTailNormConstant * exp(-B/4) * prod`), assembles the two via
`inverseLowerFactorPhysicalRenewalTrace_split_bound`, and consumes through
`canonicalRealGate3UAt_of_tailNormBound`. Axiom audit = `[propext,
Classical.choice, Quot.sound]` (zero sorry). This is the finite-band (route-A)
form of the Gate; the original infinite-carrier Gate (docs/860 seam) and a
full RH claim stay open.
**Gate-3U 外通道尺度鲁棒（2026-08-08，probe 884）.** 物理 Sonin 尺度 lambda 扫描
（`||(I-R) o D||`，transported-Slepian frame）在 logla ∈ [-2,2] 上稳定 ~0.61-0.62
（回归锚点复现 824 的 0.6242），从不衰减到 0。故无任何物理 lambda 能通过外通道满足
`|leakage|<=1`；外通道负面是尺度鲁棒的（case-bound，非证明非 RH 反论）。仅剩的开放
解析希望是精确相消 `F == -D + J`（docs/872）。直接目标恒等式定位於 docs/872，外通道
扫描证据於 docs/proofs/884_outer_sonin_scale_sweep_*.py / .md。
`.

**Gate-3U 正向上残量已精确定位 = Proof 717 等价（2026-08-04）.** 直接 adjoint
completed-kernel 闭合 (`canonicalRealGate3UAt_of_completedKernelRightEnergy`,
`CCM24FiniteSCanonicalAdjointEnergyGate.lean:375`) 把 Gate 归约到单一 premise
`hright`，其右能量 (`sourcePhysicalCoframeCompletedKernelRightEnergy`, :183) 经
`tsum_normSq_precomp_le` 收紧为 `‖sourcePhysicalCoframeLeakage‖²·(fixed-right-majorant)`。
唯一新量是 `‖physical leakage‖`；`norm_schurMarkovMixedMetricCoframe_le_one` 只封
*mixed* (`suffix·coframe`) 不封 raw（模块自注 SchurMarkovUniformBound.lean:18-20），
biorthogonality `J†∘D=id` 强制 `‖D‖≥1`，而
`norm_sourceActualBandForwardEndpointCoframe_le_one_iff_forward_add_physicalLeakage_eq_zero`
(EndpointContractionGuard.lean:245-252) 把 `‖physical leakage‖≤1` 与 **Proof 717 的
forward+physical cancellation** 等价起来。故此右腿底是 Proof 717，不是 HS 机器可独立封的
新量。See `docs/proofs/gate3u-right-energy-leakage-norm-bottom.md`.

**【2026-08-10，corrected verdict：local CompactLog/A3 positivity CLOSED】**
下列局部正性在 **CompactLog/A3** 载体上已 axiom-clean 闭合
（docs/942，`[propext, Classical.choice, Quot.sound]`, 0 sorry）：
`detector_diagonal_re_nonneg` / `detector_isPositive` / `detector_re_inner_nonneg`
（`A3NonzeroCompactLogGateProbe`），`healthy_strict_positive_diagonal`
（`Wall1HealthyPositive`），以及 `weilStateNonempty` / `concrete_c1_input_nonempty_exists`
（`WeilC1NonEmptyProducer`）给出非空局部 producer。它们证明 `F^dagger F` 的二次型
非负，不证明“对所有 admissible tests 的完整 Weil 显式公式符号”，因此不能标记为
finite-S sign 或 C1 criterion 闭合。Gamma-arg 支路
（`Dev/GammaArg*`，docs/940/941/942）是 **redundant sibling**，只给出
`Re[Gamma(1+i/2)^4]>=0`，非 canonical gate 所需。真正剩余（非 Lean-assembly leaf）：
RH 等价 Source-criterion；Gate-3U infinite carrier 与 Burnol 属于独立支线。

`finite-S` sign, Burnol's identity, and RH stay open.

**【Source model status corrected (2026-08-12)】** The former theorem saying
`SourceWeilFormData concreteTestAlgebra` was empty described the old global
reverse-exact-support model. The S2 per-common refactor replaced that model;
`ConcreteP1SupportProbe.concreteWeilForm` now constructs the exact type
axiom-clean, and `CCM25SourceDataGuards` archives the old negation. Historical
docs 812/813/830/831 and the closure audit are superseded by docs/proofs/835 for
this point.

The remaining source-data root is different:
`normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot` requires all-pairs
finite-prime certificates plus `scopedArchimedeanContributionBalance`. The
healthy source algebra fixes the former additive-convolution defect, while
`WellFormHealthyRepoint.healthyWeilForm` supplies only per-common `{2}` support.
Neither is an all-pairs/all-prime producer, and neither closes the RH criterion.

`finite-S` sign, Burnol's identity, and RH stay open.

**【850，sign 判定（2026-08-07）】** “847/848 的 canonical Weil≤0 在 concrete 被反证”只在
additive `convolutionSquare` 模型（`weilLocalSum = -polePairing`，`M(conv²g)=2·M g` 线性，
`{0,1/2,1}` 不约束 `±i/2` 处 Mellin，可自由设 -1）下成立，是模型伪问题——该模型连
`NormalizedCC20MellinConvolutionLaw` 都违背（2=1，`CC20YoshidaConstruction:2727`）。真正载体
`CompactLogTest` 已把正半定做成定理：`convolutionSquare(0)=∫‖g‖²≥0`，HS detector `F†F` 二次型
`⟨u,F†Fu⟩=‖Fu‖²≥0`（A3 `detector_diagonal_re_nonneg`）（2026-08-07 已编译通过、axiom-clean：quadratic form 用 mathlib `apply_norm_sq_eq_inner_adjoint_right` 的 .symm 得 re⟨u,detector u⟩=‖Fu‖^2 再 sq_nonneg；同文件 hsGate_selfAdjoint / hsGate_traceClass / nonzero_hsGate_witness 均无 sorry、无项目 axiom，WSL 绿并同步回 Windows）。正确的 sign 重建 = re-type endpoint/
Weil 判定到 CompactLog 载体，不重选 sign。RH 不声明，非 milestone。见 `docs/proofs/850`。

**【859，sign slot 模型墙（2026-08-07，numeric verdict）】** 一号高斯线路的诚实结论：对自然光滑实值测试（Gaussian `e^-t^2`、`e^-t`、sech），临界点 Mellin `∫ t^(i/2-1)f` 在 `t=0` 处 `~t^-1` 发散，`(M g i/2)` 不定义（即 858c 的可积前提 `Integrable (logWeight (i/2) g)` 不成立），故 `Re[(M g i/2)⁴]≥0` 语焉不祥。而在 t=0 消光的测试上 sign **不一致**（`t^a e^-t`：a=.4 → −1.99，.55 → −1.21，.9 → +0.16，1.0 → +0.26）——通用 sign 为假，具体 sign 需选消光 band 测试并做重积分下界（A0/零算子类）。`MellinSignAssembly` 本身带可导前提，无 bug；待办 = 把 `Integrable(logWeight(i/2) g)` 编为定义域谓词。见 `docs/proofs/859`。
   剩余 open：Re[Gamma(a+i/2)^4] >= 0 之相位上界（需具体化 Stirling/积分余项证明），未证。 【888（2026-08-08）：】`|arg Gamma(1+i/2)| <= pi/8` 已在 analytic 层用元素级级数夹逼闭合：arg = -gamma/2 - arctan(1/2) + S，S = Sum_n>=1 [1/(2n) - arctan(1/(2(n+1)))] 落在 `[3.8218e-1, 5.0842e-1]`（80 位 mpmath 已验），故 `Re[Gamma(1+i/2)^4] >= 0`。Lean 内闭合需在本仓库实现 real-analysis Stirling/积分余项 bound（axiom-clean、不依赖外部），除了需构造的真实解析证明（docs/888, 886 rev2）；勿在缺该证明时伪证此 leaf（A0）。 【888-wiring（2026-08-08，WSL-verified）】arch 槽已接 data-bearing `Nonempty HilbertSignArchCorrected.HilbertArchSignDatum` 并整链绿（3193 jobs，#print axioms 全 [propext, Classical.choice, Quot.sound]，无 sorryAx）。 [ArctanCert M1 done(2026-08-08,WSL-verified)] ConnesWeilRH/Dev/ArctanCert.lean gives x/(1+x*x)<=atan x<=x, 2/5<=atan(1/2)<=1/2, 4/17<=atan(1/4)<=1/4, 6/37<=atan(1/6)<=1/6, 8/65<=atan(1/8)<=1/8; 2636 jobs green, axioms [propext Classical.choice Quot.sound], 0 sorry. [SSandwich brick2 (2026-08-08,WSL-green)] ConnesWeilRH/Dev/SSeriesSandwich.lean proves axiom-clean the elementary S-series content: a=p+u split, x-x^3 <= x/(1+x^2) <= atan x, u>=0 p>=0, u<=1/(8(n+2)^3), and the telescope sum_range_p=1/2-1/(2(N+1)).  The cleaner sandwich S=1/2+U gives 1/2 <= S <= 1/2+1/32 (supersedes docs/888 tighter-but-unneeded 0.382..0.509), inside the gate [0.3596,1.14].  brick 2+2b CLOSED (2026-08-08, WSL green, axiom-clean): lift to tsum done, hasSum_p, tsum_u_le_32 (1/32 via c-telescope), S_eq S=1/2+tsum u, S_ge_half 1/2<=S, S_le_half_plus S<=1/2+1/32; axioms [propext, Classical.choice, Quot.sound], 0 sorry. OPEN next: wire gamma/atan(1/2)/pi decimals into |arg Gamma(1+i/2)|<=pi/8 (859/Mellin-cell Stirling residue). RH not claimed.

** PhaseGateSandwich (2026-08-08, WSL green, axiom-clean) **: `ConnesWeilRH/Dev/PhaseGateSandwich.lean` closes the analytic phase shift D = S - gamma/2 - atan(1/2) with -pi/8 < D < pi/8 (D_lower / D_upper / D_abs_lt_pi_eighth), built on SSeriesSandwich.S (1/2 <= S <= 1/2+1/32), mathlib gamma bounds (0.5<gamma<2/3) and pi>3, and ArctanCert.arctan_half. Axioms = [propext, Classical.choice, Quot.sound], 0 sorry. This is the tail of the real-phase gate |arg Gamma(1+I/2)|<=pi/8; the Gamma magnitude identity arg=-gamma/2-atan+S remains an open analytic step. RH not claimed. +937-route-ruling (2026-08-10, docs/937): the naive large-band sign Re[Gamma(a+i/2)^4]>=0 extracted at a=3,5,10 equals -3.7/-2.9e5/-3.4e21. Stirling gives arg Gamma(a+i/2) ~ (1/2) ln a rather than a limit of zero, so Re = |w|^4 cos(4 arg) changes sign infinitely often. The 859 section 6 eventual-positivity conjecture is refuted. The band test t^a e^{-t} cannot be the finite-S sign producer; Step-3 sign stays on CompactLog HS/A3 positivity (`healthy_strict_positive_diagonal`). Only the isolated a=1 leaf has positive sampled value (+0.26).


**Wall-A 1.4 hI leaf — PROVABLE closure via large-plateau bump (2026-08-10, docs/970).** The sole surviving
scalar `arch(witness^2)!=0` (healthy-carrier Wall-A refutation, docs/965/969) now has a Lean-realizable
analytic route that needs NO opaque mathlib-bump analysis: choose a test with a plateau `f=1` on `[-b,b]`
(`ContDiffBump rIn=9/10 rOut=1`), rely on `F(y)>=max(0,2b-y)`, `0<=F<=A`, exact tail `2A ln tanh(R/2)`, and
the near-removable limit `tendsto_archimedeanIntegrand_nhdsGT`; conservative `arch >= +3.34` for `b=0.9`.
Re-point `witnessTest` to that bump, prove the 6 block pieces, assemble into the unchanged
`archimedeanTerm_ne_zero_of_lead_pos_and_integral_bound` sufficiency (docs/965 layers). Lean build remains.
RH NOT claimed.
**`|F'|<=1` near-band structural reduction CLOSED (2026-08-11, Dev/Wall14PlateauFDeriv.lean, axiom-clean).**
The derivative of the explicit bump conv-square now reduces to the folded band: `bumpFderiv x` -> (support) ->
`int_{u in -2..2} bb x` -> `bb_two_band` splits to the two survivors
`int_{u in -1..-9/10} + int_{u in 9/10..1}` of `bb x u := bumpReal(x-u)*bd u`, with `bd := deriv bumpReal`
(pointwise zero on |u|<9/10 and |u|>1, odd `bd_neg`, continuous `bd_continuous`). New Leans: `bd_plateau_zero`,
`bd_outer_zero`, `bumpFderiv_eq_integral`, `bumpFderiv_custom_sub`, `interval_integral_eq_zero_of_Ioo` (integral
0 when zero on the open interval, via NoAtoms `Ioo_ae_eq_Ioc`), `bb_support_subset`, `bb_outer_left_interval` /
**`|F'|<=1` now CLOSED axiom-clean (2026-08-11).** Folded survivor via `u ↦ -u` (`pair_cvt` = `integral_comp_neg`.symm + `bb_neg_piece` + `integral_add`)
**`|bumpA - bumpF y| <= y` CLOSED axiom-clean (2026-08-11).** (two-sided MVT on `[0,y]` from `|bumpF'|<=1`, premise `bumpF 0 = bumpA`).
**hI closure at `bumpPlateauOwner` CLOSED axiom-clean (2026-08-11, Dev/Wall14PlateauBumpHI.lean).** Near <=11/4 (`bump_near_integral_le`), tail <=(4/3)A (`bump_tail_feas`/`bump_tail_integral_le` via exp decay), split, all <=11/4+(4/3)A, `bump_hi` (|Re int_(0,inf) archimedeanIntegrand| < (log(4pi)+gamma)*A), then `bumpArchimedeanTerm_ne_zero` (owner.archimedeanTerm != 0) via `archimedeanTerm_ne_zero_of_lead_pos_and_integral_bound`; C-gate`archCoeff_gt` (29/10<log(4pi)+gamma) intact; audits `[propext, Classical.choice, Quot.sound]`, 0 sorry. RH NOT claimed.
  Also `bumpArchimedeanTerm_re_pos : 0 < Re(bumpPlateauOwner.archimedeanTerm)` and its compact-log lift are axiom-clean. The former C1 four-fold wiring defect is fixed in `Dev/C1HealthyTestSpace.lean`: `weilLocalSum` reads its argument and the generic criterion applies `starConvolution` exactly once. The separate four-fold Wall14 estimates in docs/972/973 remain historical optional analysis, not a C1 requirement. RH NOT claimed.
**Gate-3U 外通道 {2}-族条件性推导（2026-08-11，docs/998）：** 纸面坐标计算提出：
metric coframe `D=(T†T)∘J∘G⁻¹` 在带状 `(logλ−log p, logλ)` 上精确等于 `−p^{−1/2}·x(t+log p)`，故
窗口非零质量应推出 `‖(I−R)∘D‖>0`。但该 strip identity 和 implication 尚无 Lean theorem；
`OuterTwoNonzeroObligation.lean` 只定义 `twoFamily` 与开放 `Prop`
`twoOuterNonzeroObligation`。下一步必须先形式化坐标桥，再构造 Sonin 窗口 witness。
关闭该支线只会否定当前 infinite-carrier Gate-3U cancellation route，不会推出 RH。

**Diagnostic PSP branch (2026-08-12, branch `feat/paley-wiener-psp`, docs/paley_wiener/).** The finite-prime `{2}` diagnostic gate asks for a Sonin-carrier element with nonzero `L2` restriction to the log-2 window. The quotient-invariant contract is `archimedeanSonin_window_mass`, implemented through `soninWindowRestriction`; it replaces the invalid test of a representative function at one point. `Dev/PaleyWindowProbe.lean` closes the ambient radial indicator and its nonzero restricted norm, while `Dev/PaleyHTAssembly.lean` and `Dev/PaleyWindowAnalysis.lean` close the HT and support reductions. These are axiom-clean assembly results, not a carrier witness.

The live analytic statement is the nontriviality of the scattering Toeplitz kernel `archimedeanScatteringToeplitzKernel_nontrivial`: find nonzero `psi : H+` with `P+(m * psi) = 0`, where `m(xi) = Gamma_R(1/2 - i*2*pi*xi) / Gamma_R(1/2 + i*2*pi*xi)`. The prior factorization route `m = Q/P`, `psi = P` is retracted: an a.e.-unimodular `P` is not in `L2(R)`, and a Wiener--Hopf factorization alone does not establish a nonzero Toeplitz kernel. The remaining viable candidate is a genuine prolate/Sonin `L2` eigenfunction, followed by transport to `sourceSoninCarrier` and a proof of nonzero window restriction. Closing this branch would prove nonzero outer leakage for `{2}` and reject the current infinite-carrier Gate-3U cancellation route; it would not prove RH.

## 3. Execution Cadence

Work top-down from the active route consumer. A substantial milestone must
change the route judgment (producer rejected by named guards, consumer switches
to a stronger data-bearing API, old weak path inactive, dependency reaches a
bottom, target proved RH-equivalent or false by counterexample).

Normal rounds attack 10–20 black boxes/branches/dependency layers. Default
build cadence: do **not** `lake build` or audit after each helper; continue to a
substantial milestone, then build/audit when Peter asks or the milestone needs
formal evidence.

Per-change memory record: every non-trivial file change logs one brief line in
`MEMORY.md` under a dated heading, format
`<date> <file> : <what + why, 1-2 lines>`. Keep it to a single line per change,
imperative-free prose, and collapse several related edits into one entry. These
lines live atop `MEMORY.md` and rot out on the next route-milestone merit scan.
Full narrative goes in `docs/proofs/` only when a proof judgment changes. Do not
re-narrate helper-by-helper chronology; log the change, not the journey.

## 3b. Standing Authorization (procedures run without asking)

Unless Peter says otherwise, the agent executes the normal engineering
procedures below **directly, without pausing to ask for permission**. Asking is
reserved for genuine ambiguities with real consequences, not for routine steps.

Granted (no confirmation needed):
- Running WSL-side builds and axiom audits (the established cadence in §3/§8),
  including `flock`-guarded `lake build`, focused `#print axioms`, and the
  numbered verification ladder.
- Editing existing Lean/`.md` files in this repo to advance the active route.
- Adding new `.lean` source modules under `ConnesWeilRH/`.
- Deleting **only** broken/stale artifacts the agent itself just wrote (never
  user or committed work without a separate check).
- Extending or reaping the route's Lean and docs (e.g. a new probe, a new
  seam, a route judgment that updates `MEMORY.md`/`docs/proofs/`).
- Recording the per-change memory line in `MEMORY.md` and updating `AGENTS.MD`
  per the stub rules.
- Treat **new mathematics / new analysis / self-created theory** (anything that
  would otherwise be labeled "open analytic bottom", "needs genuinely new
  analysis", or "not a Lean-assembly leaf") as a **standard attackable target**,
  attack it **directly**, and do **not** stop, ask permission, or wait for
  consent to work on it. Absence of a known theorem is a license to construct
  one, not a blocker to escalate to Peter.

**Broad change authorization (2026-08-09):** the agent may execute **any**
substantial or architecture-level change — new modules, module/package
boundary changes, new claims pushed into the route, new seams, dependency or
carrier changes — **directly, without asking Peter for consent**. Peter will
not be consulted for every large change. "Ask before every architecture or big
change" (project-local instruction overrides the global AGENTS default). Do
not stop to request a green light.

**New mathematics is not a blocker (2026-08-10):** whenever a step requires new
mathematics, new analysis, or a self-created theory rather than assembling
existing theorems, treat it as a standing attackable target and attack it
directly — no reporting to Peter, no asking for consent. Only the hard guards
below (sorry/axiom, RH-only claims, destructive/git/share-infra actions) still
stop the agent. "open analytic bottom" is work to be done in place, not news
that needs to be surfaced first.

**No-stop rule (2026-08-10, Peter):** unless a path has been **conclusively
judged dead** — meaning named guards/definitions actively forbid or contradict
it, a verified counterexample or model-artifact negation exists, or a route
decision (docs/proofs) already rules it unviable — do **not** stop, defer,
gold-plate, or decline it for any reason (missing theorem, "needs new math",
effort, uncertainty, desire to avoid a build, or current-route estimates).
Treat every such path as live work: advance it with the strongest available
reasoning/analysis, and either (a) push it to a closable result, or (b) produce
a precise **conclusive-dead verdict** (named guard / counterexample / docs
ruling) — the only thing that ends work on that path. Waiting-for-consent or
"let me surface this first" is a stop pattern to avoid. The never-granted hard
guards below (sorry/axiom, RH-only claims, destructive/git/share infra) still
override this rule and always require Peter.

Still requires Peter (decision with consequence / irreversibility):
- Any `git commit` / `push` / remote operation (authorized per execution, §14).
- Letting unwanted shared infra, damaging shared files, dropping/adding
  dependencies at the `lean-toolchain`/CI level, or making any public GitHub
  payload (PR/issue/comment).
- ANY step that would non-consensually violate the integrity/RH guards below
  (§6 `sorry`/`axiom`, §11 RH-only claims) — those are never granted.

Rule: when a step is on the "run directly" or broad-authorization list, do it;
do not ask "shall I proceed". If a step falls to the "requires Peter" or the
never-granted list, stop and surface it.

## 4. Single-Agent Rule

Automatic subagents and worker fan-out are paused; use one coordinating agent
unless Peter restores them. Peter may run several independent AI sessions
manually; those sessions own disjoint semantic lanes and must not edit the same
declaration, route consumer, old weak path, or plan document. On session start
and handoff, record owner/cwd/lane/files/build/audit/expected output (handoff
also records status, files, declarations, blockers, next safe action). A later
session that discovers overlap must stop editing and go read-only. Another
session's dirty diff is evidence, not accepted progress — the main worktree plus
an import-facing WSL build and axiom audit decides acceptance.

## 5. File Ownership And Safety

The Windows repository is the only source of truth. Edit, stage, commit, fetch,
merge, and push only from the Windows repository. Sync source **one way**
Windows → WSL ext4 mirror. Never treat a WSL branch/commit/dirty diff/artifact
as authoritative. If WSL experimentation changes source, reproduce the exact
semantic edit on Windows and re-verify the Windows snapshot. Do not copy a whole
WSL worktree back over Windows; port reviewed file-level edits.

## 6. Lean Integrity Standard

Do not introduce or hide gaps through `sorry`, `admit`, `axiom`, opaque
placeholders, unsafe shortcuts, `True`/`Set.univ` producer fields, or stored
conclusions disguised as source data. An axiom-free proof of a weak statement
does not count — the theorem must remove a real active dependency.

Prefer data-bearing owners when several facts must refer to the same object.
Separate propositions can silently mix different witnesses. Required-same-object
pairs include: route test and convolution square; operator and Schwartz kernel;
kernel and Hilbert-Schmidt norm; positive trace and support-square trace; source
Weil-form and evaluation data; canonical atoms and package certificate data;
restricted/global masses with one evaluation object.

## 7. Lean Failure Modes (known hazards, abbreviated)

- **Row-record destructuring**: don't flatten an existential/conjunction whose
  final item is a structure; keep `⟨r, hmatch⟩` structured.
- **Type/Prop universes**: respect the target universe when doing this.
- **Import artifact freshness**: a single-module build can pass while a clean
  dependency build fails; rebuild the owning module's artifacts, don't widen to
  full build unless narrow repair fails.
- **Axiom audits do not detect theorem premises**: `#print axioms` only shows
  what a declaration depends on; it cannot catch a wrong-stated premise.
- Keep guards naming files as rejected-route record for future reference.
- **`R` vs `R0` vs `S` naming landmine (Gate-3U outer/band channels)**: the CONPUTABLE  band projection is `radialSupportProjection` = `R` in docs/815/884/997 but `R0` in docs/995's private naming; the UNREACHABLE archimedean `sourceSoninProjection` is `R0` in docs/815 but `S`/`P` in docs/872/995. `OuterChannel = (I-R_radial).o.D` (docs/815) is the computable one and is what 824/884 measure (~0.62); `(I-Sonin)D=J-D` is a DIFFERENT operator that requires the exact Sonin intersection. Never equate the probe's `(I-R)D` with `(I-Sonin)D`, and always pin which projection a doc's `R`/`S` means.
- **`simp` does NOT expand `‖s • d0‖²` on an L² carrier**: on `cc20GlobalLogCrossingL2` (= `Lp ℂ 2 (volume : Measure ℝ)`) the scalar-multiple norm lemma `norm_smul` is not a default-simp lemma, so bare `simp` leaves `‖s•d0‖²` stuck ("made no progress"). Fix: `rw [norm_smul, mul_pow]` first → `(‖s‖·‖d0‖)² = ‖s‖²·‖d0‖²`, then BARE `simp` closes the scalar residual `‖(s:ℂ)‖² = |s|² = s²` for ANY real `s` — **no `0 ≤ s` hypothesis needed**. (Observed 2026-08-22, C1Stage3WindowedTraceP3a P4 build.)
- **Explicit section variable `(x : A)` becomes a LEADING EXPLICIT parameter of every later declaration**: an explicit local declared with parens — `variable {ν} [Countable ν] (globalBasis : HilbertBasis ν ℂ H)` — is prefixed as the first argument of every later declaration whose *type* depends on it (used-or-not), even when you call one from WITHIN that same section. Basis-theorems and structures depend on it → pass `globalBasis` first (`p4_healthyCriterionState globalBasis F …`, `(p3aPairData globalBasis)`, `frontierHS_summable globalBasis n g`). Carrier-only defs whose type never mentions the basis are used **bare** — no leading arg: `TmapCLM (globalBasis i)` and `frontierWindowFactor n g u` (here `(globalBasis i)` is the input vector, not a prefix). Omitting a required prefix shifts every later argument one slot left → "Application type mismatch: … expected `HilbertBasis ?m.N ℂ ↥H` but got `<the next arg>`"; the stuck metavariable also poisons the axiom probe with a spurious `sorryAx`. When unsure which form, mirror how existing green code calls each name. (Observed 2026-08-22, P5 producer build + C1Stage3FrontierStatus.)

- **Lambda body swallows a top-level `∧` in a theorem header**: `Summable fun i => ‖x‖² ∧ P` parses as `Summable (fun i => (‖x‖²) ∧ P)` — the `=>` body extends right past the conjunction, so Lean tries to build an instance out of a Prop-valued function ("failed to synthesize `AddCommMonoid Prop`", "HPow ℝ ℕ Prop"; at the tactic stage, "target is not an inductive datatype ⊢ sorry"). Fix: parenthesize the first conjunct — `(Summable fun i => ‖x‖²) ∧ P`. (Observed 2026-08-22, `C1Stage3FrontierStatus.frontierStatus_satisfiableAt_gV`.)

- **A carrier type is NOT transitively re-exported by a module that merely uses it**: the name `cc20GlobalLogCrossingL2` lives in `CC20Concrete.GlobalLogCrossing`; importing a brick that *uses* it (e.g. `C1Stage3FrontierHS`) does not bring the bare name into scope. To write it bare you must `import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing` **and** `open CC20Concrete`. Otherwise "Unknown identifier cc20GlobalLogCrossingL2" — which then cascades: the section variable's type fails → `globalBasis : sorry` → every basis-binder inference in the file breaks (a wall of ~15 downstream errors from one missing import). (Observed 2026-08-22, `C1Stage3FrontierStatus`.)

- **The integral binder `∫ t, body` swallows everything to its right** — including a trailing subtraction: source text `volume.real W * ∫ t, ‖…‖² − c` parses as `vol * (∫t (‖…‖² − c))`, NOT `(vol · ∫t ‖…‖²) − c`. Symptom when you meant the latter: `ring_nf` leaves the goal unchanged because two mass subterms are not equal ring-atoms, or a spurious "No goals to be solved" on an inner `rfl` because §B's rewrite already closed it. Fix: name the mass as an **atomic identifier** (`let mfun n := vol · ∫t ‖…‖²`) and reference that bare name in both positions — no parsing ambiguity with a plain identifier, so `ring` closes `X − (X − c) = c`. When reusing §B's closed form to set up such an equality, assign the lemma **directly** (`have hT : LHS = mfun n := frontierPlainWindowTrace_eq_volumeTimesMass …`) rather than via a by-block that ends in `rfl` — its RHS is definitionally `mfun n`, so the rewrite closes it and a trailing `rfl` errors. (Observed 2026-08-22, §C bulk-witness build, `C1Stage3FrontierStatus`.)

- **`norm_num at h` can pre-close a `False` goal**: when the current goal is `False` (e.g. inside proving `a ≠ b`) and you simplify a hypothesis into an absurdity — `intro h; rw [h] at hd0; norm_num at hd0` turns `hd0 : 0 < ‖d0‖²` into `hd0 : 0 < 0` — the *tactic* `norm_num at hd0` discharges that contradiction and leaves **no goals**. A trailing `exact lt_irrefl _ hd0` then errors with "No goals to be solved". Fix: make exactly one tactic the sole closer. Use `nlinarith` (it normalizes `0² = 0`, sees `hd0 : 0 < 0`, and closes `False`) after a hypothesis-only rewrite (`rw [h] at hd0` never touches the main goal): `intro h; rw [h] at hd0; nlinarith`. (Observed 2026-08-23, Program P step-2 build, `C1Stage3WindowedTraceP3a.rankOneCorrection_HS_mass_eq_qw`.)

- **`field_simp` on a norm-power divisor needs the *base* nonzero, not just its square**: to cancel `(qw g / ‖d0‖⁴) · ‖d0‖⁴ = qw g`, `field_simp [ne_of_gt (hd0 : 0 < ‖d0‖²)]` only cancels three of the four factors and leaves the residual goal `qw g * ‖d0‖ / ‖d0‖ = qw g` — it cannot derive the first-power base fact `‖d0‖ ≠ 0` from the squared one `‖d0‖² ≠ 0`. Fix: derive and feed the base explicitly, `have hd0n : ‖d0‖ ≠ 0 := by intro h; rw [h] at hd0; nlinarith`, then `field_simp [hd0n]` cancels fully. (Observed 2026-08-23, same build, final calc step of `rankOneCorrection_HS_mass_eq_qw`.)

- **A section variable referenced only in a proof BODY is NOT auto-lifted into a new declaration's parameters**: Lean promotes an explicit `variable {ν} [Countable ν] (globalBasis : …)` into a later theorem's leading parameter ONLY when that theorem's *type signature* mentions it. If the type does not reference `globalBasis` but the proof body does (`:= by exact … globalBasis …`), the variable is **not** lifted → "Unknown identifier `globalBasis`" plus an unsolved goal whose context is missing both `globalBasis` and `[Countable ν]`. Fix: name `globalBasis` as an explicit leading parameter of that specific theorem — its type `HilbertBasis ν ℂ …` drags `{ν}` + `[Countable ν]` into scope so they lift with it. (Observed 2026-08-23, §D end-to-end closure build, `C1Stage3FrontierStatus.frontierStatus_healthyCriterionState_of_rankOneCorrection`. Refines the preceding explicit-section-variable bullet: body-only use is NOT enough.)

- **A module's file PATH name ≠ its internal namespace — and for the Stage-3 crux files they differ**: `ConnesWeilRH/Dev/C1Stage3FrontierCrux.lean` declares `namespace ConnesWeilRH.Source.C1Stage3FrontierCrux`, so the *module* (what `lake build <target>` resolves to a source file) is named by its **path** — `ConnesWeilRH.Dev.C1Stage3FrontierCrux` — while every theorem's fully-qualified name uses the **internal namespace**, e.g. `ConnesWeilRH.Source.C1Stage3FrontierCrux.frontierCrux_powerSpectrum_eq_weilValue`. Building by the namespace FQN (`lake build ConnesWeilRH.Source.C1Stage3FrontierCrux`) fails with "no such file or directory … `.Source/C1Stage3FrontierCrux.lean`" because no file exists at that path; `#print axioms` / cross-references use the `.Source.` name instead. Same split for `C1Stage3BareHSObstruction` (Dev path, Source namespace). Rule: **build/import by PATH, reference declarations by their declared-namespace FQN.** (Observed 2026-08-24, step② axiom probe.)

- **A pointwise Lp product zeroes via `@[simp] Lp.zero_smul`, NOT algebraic `zero_smul`**: for `(0 : Lp 𝕜 ⊤ μ) • f` (the Fourier-multiplier `cc20FourierMultiplier h u = (𝓕h).toLp ⊤ • u`), the zeroing simp lemma is Mathlib's `MeasureTheory.Function.Holder.Lp.zero_smul`. An unqualified `rw [zero_smul]` looks for the generic `[SMulWithZero]` form and fails "did not find an occurrence of pattern `0 • ?m`" because this product is a **pointwise Lp** operation, not scalar-field smul. Fix: after rewriting the multiplier to its zero (`rw [hmult]`), close with plain `simp` (or `simp [ContinuousLinearMap.map_zero]`) so `Lp.zero_smul` + `LinearMap.zero_apply` reduce both sides to the L² zero. (Observed 2026-08-24, `C1Stage3BareHSObstruction.stage3FamilyFactor_zero_of_test_zero`.)

- **A final `rw [hlhs, hrhs]` that reduces both sides to one literal can close the goal itself — do NOT add a trailing `rfl`**: with `hlhs : LHS = 0` and `hrhs : RHS = 0`, the last `rw [hlhs, hrhs]` rewrites the target to `0 = 0`, which this toolchain's `rw` closes automatically; an extra `rfl` then errors "No goals to be solved". (Same family as the earlier norm_num / by-block-rfl pre-close hazards: after a final rewrite, check whether it already discharged a definitionally-true goal before adding another closer.) (Observed 2026-08-24, main theorem of `C1Stage3BareHSObstruction`.)

- **Fast axiom probe without rebuilding the audit module**: `lake env lean --run <scratch.lean>` elaborates a tiny script against the already-built oleans and prints `#print axioms …` — far faster than building `UnifiedRemainingGapsRouteAudit`. Two gotchas: (a) it still loads all transitive oleans from `/mnt/c`, so allow several minutes; (b) import by **PATH** name, and a script with no `main` exits 1 with "(interpreter) unknown declaration 'main'" *after* printing the axiom lists — that exit-1 is harmless. (Observed 2026-08-24.)

- **Unicode minus sign `−` (U+2212) is NOT Lean's subtraction operator — use ASCII `-`**: typing `a − b` with the typographic minus parses `−` as an *identifier*, not an infix op → "expected token" at that column, which cascades to "Unknown constant `<theorem>`" for the whole declaration (the body never elaborates) plus a spurious entry in any downstream `#print axioms`. Docstrings/comments may keep `−` in prose; only **expression positions** need ASCII `-`. Symptom fingerprint: two "expected token" errors at exactly the columns where you wrote an infix minus, followed by "Unknown constant" on every later reference. (Observed 2026-08-24, both new lemmas of `C1Stage3WindowedTraceP2` first build.)

- **Uniqueness of limits is `Filter.tendsto_nhds_unique`, NOT a bare `tendsto_unique`**: the "same function tending to two points forces them equal" lemma is `tendsto_nhds_unique [T2Space X] {f : Y → X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : a = b` (mathlib `Topology/Separation/Hausdorff.lean`). There is no unqualified `tendsto_unique`; guessing that name gives "Unknown identifier". For ℝ targets both `[T2Space ℝ]` and `[NeBot atTop]` auto-resolve, so after rewriting the hypothesis to a constant-zero sequence you close with `exact tendsto_nhds_unique hReadback (tendsto_const_nhds)`. (Observed 2026-08-24, `C1Stage3WindowedTraceP2.p2_renormReadback_forces_qw_zero`.)


- **`mul_zero` vs `zero_mul`: after a gap-rewrite substitutes the difference with 0, check which side the zero lands on.** In `spectralTerm_convolutionSquare_pair_re_sum_uncond`, rewriting the multiplicity-gap to 0 leaves a LEFT-multiple residual `0 * (laplaceAt …).re`; that closes by `zero_mul : 0*a = 0`, NOT `mul_zero : a*0 = 0` — using the latter fails "Did not find an occurrence of the pattern `?a * 0`". Always read the goal after the gap-rewrite: zero on the LEFT → `zero_mul`; zero on the RIGHT → `mul_zero`. (Observed 2026-08-25, W4a wiring; cost Build #14's only failure at line 181.)
- **A hard-failing `have` subproof tags the WHOLE enclosing declaration with `sorryAx`:** if a local `have h : T := by …` fails to close, Lean records an "error" term carrying `sorryAx`, and that axiom INHERITS into every theorem whose proof references it — so one broken tactic line deep in a subproof surfaces as `sorryAx` on the TOP-LEVEL theorem's `#print axioms`. When auditing, do not trust "the top lemma is clean"; grep the whole build log for `sorryAx` and locate the deepest failing bullet. (Observed 2026-08-25 — Build #14 showed `pair_re_sum_uncond` with sorryAx from a single-line tactic bug.)
- **A Nat equality does not directly `simpa` an ℝ-subtraction goal:** to prove `(a : ℝ) − (b : ℝ) = 0` from the Nat fact `(a : ℕ) = b`, do NOT try `simpa using H` — the target is real subtraction, a different syntactic shape. Rewrite the natural-number equality in first (`rw [hEq]`) so both casts are of one Nat value, then let `ring` clear the cast arithmetic to 0. (Observed 2026-08-25, W4a multiplicity-gap computation.)
- **Through `/mnt/c`, match source edits by SHORT substrings and verify in one process:** reading/writing Lean source across the cross-OS WSL 9P mount can mangle LONG multi-space string literals while short fragments survive intact, so a whole-line `old_string` may fail to match even when it "looks" identical. Robust pattern: anchor on a unique SHORT substring, capture surrounding indent, and do read + rewrite + re-read inside ONE python process with an assert on the occurrence count; keep any single Edit's literal short (compact one-liners survived fine this session). (Observed 2026-08-25.)
- **Confirm a declaration's EXACT on-disk spelling before referencing it — a one-syllable typo is `Unknown identifier`:** the W4a wiring theorem resolves only as `xiMultiplicity_hermitianPartner_eq`; a mistyped variant (e.g. swapping an `-ier`/`-icity` suffix) gives "Unknown identifier", and because that reference sits inside a failing subproof it also poisons the enclosing axiom set with sorryAx (see preceding bullet). Confirm the exact name by having a prior `#print axioms <name>` print cleanly, or grep the definition. (Observed 2026-08-25.)

- **SetOf/inter membership does not auto-unfold for `rw` or `linarith`:** after `refine ⟨_, ?_⟩` splits an `a ∈ s ∩ {rho | p rho}` goal, the remaining goal is displayed as `a ∈ {rho | p rho}` — `rw` then reports "did not find an occurrence of the pattern" (the pattern lives under the un-unfolded membership), and `linarith` cannot use a membership hypothesis. Fix with `show (p a)` (defeq through `Set.mem_setOf_eq`) before the rewrite, and lift comparisons with `have hp : 0 < X := h.2` before `linarith`. (Observed 2026-08-25, W4b-pairing halves lemmas.)

- **`rw [Set.indicator_apply, if_neg h]` fails on Decidable synthesis:** instantiating `Set.indicator_apply` leaves the `ite` instance as a metavariable, and `if_neg` then triggers instance synthesis for `Decidable (a ∈ s)` on a def-defined set — fails. Do NOT fight instances: prove the zero case as its own `have e : s.indicator f a = 0 := by simp [h_not_mem]` and `rw [e]`; `simp` resolves the classical instance. (Observed 2026-08-25.)

- **Parenthesize `.mp` inside application arguments:** `h (iff_lemma x).mp hpl` parses as applying `h` to the PARTIALLY applied `.mp`; the intended `h ((iff_lemma x).mp hpl)` needs the outer parentheses. Symptom: "Application type mismatch: the argument has type ... → ... but is expected to have type <the goal prop>". (Observed 2026-08-25.)

- **Check the ext4 mirror for stale sources BEFORE building on it:** `/home/peter/rh` had pre-wiring W4a files (missing the multiplicity-transport theorems) while oleans looked healthy; a build there would have verified the wrong sources. Cheap guard: `diff <(tr -d '\r' < windows-file) <(tr -d '\r' < mirror-file)` for the modules under edit, or `rsync` the source tree first and let lake rebuild the touched bricks. (Observed 2026-08-25.)

- **`tsum_congr` yields an EQUALITY, not a `<=` — never feed it straight into `.trans` on a `le` goal** (Observed 2026-08-25, C1SpectralQwAssembly): the type mismatch is reported at the `.trans` site AND elaboration silently inserts `sorry` downstream — the module still reaches the `#print axioms` stage, so the failure mode is `sorryAx` in the audit block, not a red error. Guard: build `have h : lhs = rhs := tsum_congr fun x => _` with an explicit type ascription (which also folds any un-unfolded `def` such as `offLineNormMass`), then compose `(norm_tsum_le_tsum_norm habs).trans h.le`. Related: `norm_tsum_le_tsum_norm` is an inequality and cannot be `rw`'d at all.

- **`rw` may leave a residual goal that differs only by an un-unfolded local `def`** (Observed 2026-08-25): after `rw [thm_with_tsum_rhs]` the auto-`rfl` can leave `tsum-expr = myDef g` where `myDef g` *is* that tsum by definition. Append an explicit `rfl` (whnf closes it); do not chase the difference with more rewrites.

- **WSL python for probes has NO scipy system-wide; run via uv** (Observed 2026-08-25): neither `/usr/bin/python3.12` user-site nor the two `~/.*venv*` carry numpy+scipy. Working invocation: `/home/peter/.local/bin/uv run --with numpy --with scipy python <probe>.py` from the probe directory (ephemeral env, no system pollution). This is how 1041/1042 run.


## 8. WSL Verification

WSL2 is a **verification environment, not a source workspace**. Author/manage
git only in Windows, then copy the Windows snapshot into an ext4 mirror. Never
run Lake through Windows Lean or from a Windows-mounted source path.

**Hard rule (2026-08-24): 严禁用 `/mnt/c` — build natively on WSL ext4.** The live native copy is `/home/peter/rh` (ext4, ~8 GB with a warm `.lake`). **Canonical-copy adjudication (2026-08-24, Peter-approved): the Windows git tree `C:\Projects\Connes-Weil-RH-Proof` is the single source of truth; `/home/peter/rh` is a BUILD-ONLY copy with NO `.git`** (its old `.git` — 46 stashes, ~30 campaign branches, 4 tags from the 2026-07 multi-AI era — was archived to `/home/peter/rh-git-archive-2026-08-24.tar.gz` (17 MB, verified readable) and then deleted; restore with `tar xzf` if ever needed). Never point `lake build` at the Windows tree via `/mnt/c/…`: drvfs costs ~7 min/heavy brick while native ext4 is ≈5× faster. Workflow: edit in the git tree (`C:\Projects\Connes-Weil-RH-Proof`) → sync changed files to `/home/peter/rh` → build natively there. The old "mirror must be its own git toplevel" sync check is obsolete — the mirror has no `.git` by design; `git rev-parse` there must now FAIL.

Preferred persistent mirror: `<ext4-mirror>/Connes-Weil-RH-Proof`.

Rules:
- Before syncing, run `git rev-parse --show-toplevel`; it must return the mirror
  itself. If it returns the user's home directory or any other path, **do not sync over the
  directory**; create a fresh ext4 verification directory, seed `.lake` from the
  compatible persistent cache, and copy current sources excluding `.git`/`.lake`.
- **Do not overwrite a dirty mirror.** Record divergence and use an isolated
  ext4 verification directory.
- **Never commit or push from either mirror.** A successful WSL build accepts the
  tested Windows snapshot only; it does not transfer source ownership to WSL.
- All Lake commands take the lock:
  `flock -w 1800 "$TMPDIR/connes-weil-rh-lake.lock" lake build <target>`,
  **and must run with the mirror as cwd** (`cd <ext4-mirror>/<mirror> && flock ...`).
  Without the `cd`, lake resolves the Windows project root from the caller's
  cwd and writes olean into the Windows `.lake/build` (observed 2026-08-15:
  a `flock ... lake build` without `cd` compiled Source files from
  a Windows-mounted source path and polluted the Windows build tree; kill, delete the
  same-day `*.olean/*.ilean/*.c/*.hash/*.json` under the Windows
  `.lake/build`, and rerun inside the mirror).
- `.lake/build` metadata is path-sensitive: seed package caches only, then
  recreate the project build directory; verify Lean input/output stay under the
  ext4 mirror. If a dirty mirror makes `git diff HEAD --exit-code` block on
  captured stdout, use `GIT_EXTERNAL_DIFF=true` for that one command only (suppress
  the payload, not the check).
- Verification order: (1) direct Lean check during implementation, (2) smallest
  owning module build, (3) import-facing `#check`/`#print`, (4) focused
  `#print axioms`, (5) route/Dev build after local target passes, (6) full build
  only for a final milestone/explicit request, (7) shortcut scan and
  `git diff --check`.
- Accepted focused axiom output may contain Mathlib foundations
  `[propext, Classical.choice, Quot.sound]`; it must not contain `sorryAx` or new
  project axioms outside explicitly audited roots.
- **Whitespace-linter tail trap**: mathlib's `style.whitespace` linter reports
  `'' starts on column N` on the LAST line of a file that lacks a trailing
  blank line after `end ConnesWeilRH` (the EOF implicit command lands
  off-column). End every `.lean` file with `end ConnesWeilRH` + one blank line.
- **Incrementality lies**: `lake build` re-runs nothing on unchanged files —
  a "no errors/warnings" pass can mean "not rebuilt". Force acceptance
  verification by re-copying (or `touch`) the file on the mirror first.
- **Root-cause discipline**: capture lake output WITHOUT head/tail line caps —
  the FIRST `error:` is the root cause; later `Unknown identifier` cascades
  are noise. Use `grep -B3 -A10 error:` or `grep -E "^error:"`.
- **WSL variable assignment is unreliable** in `wsl.exe -- bash -lc 'X=...; ...'`
  (observed empty expansions); write full paths inline instead of `$VAR`. The Bash tool layer
  additionally strips single quotes / pre-expands `$VAR` inside for-loop bodies, so a loop's own
  variables arrive empty — use fully-literal paths and avoid loops in `wsl -d ... -- bash -lc '...'`. Only a BARE `$?` survives (even `${PIPESTATUS[0]}` is lost); to capture lake's exit, run `cmd > log 2>&1; echo EXIT=$?` with NO pipe.
  **But do not trust even that:** observed twice this session — a build whose log ends "Lean exited with code 1 / build failed" still read back `EXIT=0`. The ground truth is the LOG, not any exit code: grep for real `error:` lines (see above) and the terminal "Build completed successfully (N jobs)" footer.
- **Distro name for `wsl -d`:** the installed distro is `Ubuntu-24.04`, not bare `Ubuntu` —
  `wsl -d Ubuntu` fails with `WSL_E_DISTRO_NOT_FOUND`. List with `wsl -l -v` if unsure.
- **Where mathlib oleans actually live:** modern Lake keeps each package's compiled artifacts at
  `.lake/packages/mathlib/.lake/build`, NOT in the project tree; an empty count under the project
  `.lake/build` does not mean a cold cache — check the per-package build dir before assuming a rebuild.
- **Where THIS project's oleans live:** `.lake/build/lib/lean/ConnesWeilRH/<Path>.olean`, keyed by FILE PATH — so `Dev` modules are under `…/lib/lean/ConnesWeilRH/Dev/<module>.olean`, NOT under `lib/ConnesWeilRH`. Checking the wrong dir makes a built module look absent.
- **`cp -a` preserves mtime, so an old-looking olean does not prove a skip:** trust the log's `Built <module>` line over file mtimes. To *prove* an edited source re-elaborated, delete its `.olean` first, then build and expect a real `Built` (refines "Incrementality lies" above).
- **Cold vs warm aggregate build exit differs on lint warnings:** v4.30 Lake treats the ~4187 pre-existing lint warnings as errors ON freshly-elaborated modules, so a cold `lake build ConnesWeilRH` can print "Build completed successfully" yet still EXIT 1 — while a warm (all-Replayed) rebuild of the SAME tree exits 0. The true regression signal is the count of `error:` lines (= 0), not the exit code.
- **`CompactLogTest.laplaceAt` is namespaced in CC20YoshidaConvolution, not with the structure:** the structure `CompactLogTest` lives in `CCM25Concrete.CompactLogConvolution` (`Source/CCM25Concrete/CompactLogConvolution.lean:29`), but `laplaceAt` is defined inside `namespace CompactLogTest` in `Source/CC20YoshidaConvolution.lean:55`. Resolving `CompactLogTest.laplaceAt` therefore needs BOTH `open CCM25Concrete.CompactLogConvolution` (the type) AND `open CC20YoshidaConvolution` (the alias the dot-notation resolves through). Missing the second gives "Unknown constant …CompactLogConvolution.CompactLogTest.laplaceAt". (Observed 2026-08-24, W1 module.)
- **`star` vs `(starRingEnd ℂ)` — simp crosses the gap, `rw` does not:** `Complex.normSq_eq_conj_mul_self` is stated with `(starRingEnd ℂ) z * z`, while the Hermitian square law produces `Star.star z * z`; `rw [← Complex.normSq_eq_conj_mul_self]` FAILS (heads do not match syntactically), but `simp [Complex.mul_re, Complex.normSq]` proves `(star L * L).re = Complex.normSq L` by computing both sides. Probe which tactic crosses a star/conj mismatch before committing to `rw`. (Observed 2026-08-24, W1 module.)
- **For a sign goal `0 ≤ (↑m * X).re` with X a star-product, prove X equals a real-cast FIRST:** `have hprod : star L * L = ((Complex.normSq L : ℝ) : ℂ)` via `apply Complex.ext <;> simp [...] <;> first | ring | simp`, then one `rw [hprod, Complex.mul_re]` + cast cleanup (`Complex.natCast_re`, `Complex.natCast_im`, `Complex.ofReal_re`, `Complex.ofReal_im`, root-namespace `zero_mul`, `sub_zero`). Decomposing `.re`/`.im` separately starves later rewrites — `Complex.mul_im` fires on the pattern a later `rw` still needs. Also: `zero_mul` is root-namespace, NOT `Complex.zero_mul`. (Observed 2026-08-24, W1 module.)
- **W3 summand owner must match the square:** `spectralTerm_convolutionSquare_nonneg_of_onLine` proves a term for `g.convolutionSquare`, not for the root `g`.  When splitting a square series by indicators, parameterize the split by the root `g` and use `spectralTerm g.convolutionSquare`; otherwise Lean reports a type mismatch that can look like a bad positivity proof.
- **For absolutely summable indicator splits, use `Summable.indicator` and merge `HasSum`s:** the generic `tsum_add` identifier is not available in this toolchain.  Given `h₁ : Summable f` and `h₂ : Summable g`, use `(h₁.hasSum.add h₂.hasSum).tsum_eq`; parenthesize the summand under `∑'` when it contains a binary `+`, or the second binder can escape scope.
- **Do not identify `oneSubXiZero` with the Hermitian conjugate partner:** `centeredXiCoordinate (oneSubXiZero rho) = -centeredXiCoordinate rho`, while the square law uses `-star (centeredXiCoordinate rho)`.  A conjugate-zero transport theorem is a separate obligation; the W3 complement split must not claim the missing `2 * Re` pairing.

## 8a. Canonical Incremental Build Strategy

Use one persistent WSL2 ext4 mirror for the current Windows snapshot and keep
the build ladder narrow until a coherent milestone is ready:

```text
edit a leaf
   -> owning module
   -> import-facing probe / #print axioms
   -> route or aggregate target (only when the local target is green)
   -> ConnesWeilRH root (milestone/final gate)
```

The three cache layers are different and must not be conflated:

```text
.lake/packages  = dependency/package cache (Mathlib and package sources)
.lake/build     = this project's path-sensitive .olean/.ilean artifacts
source mirror   = the Windows snapshot being verified
```

Daily commands run from the ext4 mirror and take the shared lock:

```bash
cd <ext4-mirror>/<current-mirror>
flock -w 1800 "$TMPDIR/connes-weil-rh-lake.lock" \
  lake build ConnesWeilRH.Dev.<OwningModule>
flock -w 1800 "$TMPDIR/connes-weil-rh-lake.lock" \
  lake build ConnesWeilRH.Dev.<ImportFacingProbe>
```

Run `lake build ConnesWeilRH` only after a related batch is coherent or when
the milestone explicitly requires root evidence. Do not build the root after
each helper, and do not import a `Dev` probe into `ConnesWeilRH.lean` merely to
make that probe part of the root build; direct target builds are the intended
audit boundary.

Reuse the same mirror's `.lake/build` for the owning-module/probe loop. If the
mirror is dirty or on a different lineage, create one isolated ext4 mirror for
that batch, seed `.lake/packages` once, and keep its project `.lake/build`
private to that mirror. Never recreate a fresh probe directory per edit, and
never copy a path-sensitive project `.lake/build` from another checkout unless
the source path and exact source snapshot are identical. Package caches may be
shared read-only; project artifacts may not be treated as a portable cache.
Historical setup helpers such as `a1setup.sh` may create an isolated cold
probe, but they are not part of the daily loop and must not be used to reset
the persistent mirror after every edit.

Interpret Lake output correctly: `jobs` is dependency-graph work, not elapsed
seconds. `Built` entries indicate recompilation; `Replayed` entries indicate
cache reuse. A wide rebuild after an upstream dependency change is legal, while
an unchanged target should become a short replay in the same mirror. Record
target, job count, elapsed time, and whether the run was cold or warm in the
verification note.

The accepted verification ladder is therefore:

```text
owning module -> import-facing probe -> focused #print axioms
             -> route/aggregate target -> root build at milestone
```

## 8b. Cold-VS-Warm Lake Rebuilds (CacheReuse diagnostics)

2026-08-06 lesson: a leaf edit (Probe + Audit `Dev` files) triggered a ~7 hour,
~130-module cold tail that looked like the cache had been thrown away. It had
**not** been. `lake` reuses a hot cache; what it recompiled were modules whose
transitive deps changed since their last `.olean`.

How to tell reuse-vs-rebuild (Windows path `/c/Projects/Connes-Weil-RH-Proof`):
- `find .lake/build/lib/lean/ConnesWeilRH -name "*.olean"` and inspect mtimes.
  Old-but-present files (`2026-06-30`, `2026-07-07`) prove the cache is shared.
  A total discard would remove those too.
- Grep the build log for `^✔ \[n/N\]` progress lines and the `n/N` total; the
  per-module `(NNNs)` is seconds, not a healthy/normal indicator.
- When the build hitches (no new `✔` / `.trace` for 10+ min but `ps` shows lake
  alive), the module is just huge (440s+ is normal here), not stalled.

**Root cause of a wide legal rebuild**: module-mtime deps changed since the last
build. In this repo the usual trigger is `proof717`-series commits touching
`CCM24FiniteSCombinedCoframeGuard` / `CCM24FiniteSEndpointContractionGuard`, which
dirty the downstream chain below them even though the probe files themselves are
late leaves.

**Do NOT** conclude cache-dropped and kill the build. A kill mid-tail burns the
hours already spent and gets no verification. Let a warm, error-free build run to
completion; only abort on a real error or an explicit Peter request.

**Dirty vendored package warning** (`mathlib/plausible/LeanSearchClient has local
changes`) is a red herring for import invalidation: all 40 modified mathlib files
are under `scripts/` (bench/dev tooling), not `.lean` mathlib sources — it does
not dirty the module graph. `plausible`/`LeanSearchClient` were clean. Check the
`git -C .lake/packages/<p> status --porcelain` path before assuming vendor dirt
is the cause.

**Foreground `sleep` SIGTERM trap**: a foreground Bash command that is mostly
`sleep 180`+check can be killed when the tool call exceeds its default 2-min
timeout (exit 143, no log output persists). Prefer: run the build itself as a
blocking command with an explicit long `timeout` (e.g. 400000ms) and `| tail`,
OR run the `wsl.exe -e` build with a high `timeout:` param and wait on the task.
Standalone `sleep N; ...` in the foreground is fragile; a killed parent also
kills a `nohup` child whose log was in the same killed tree.
Use the full path `/c/Windows/System32/wsl.exe` — bare `wsl` may not be on
PATH in this bash.

**Namespace-close pitfall**: adding a new theorem in leaf `Dev` files can leave
an outer `namespace` unclosed at EOF; the error only surfaces on the final build
(`Invalid name after end: Expected <leafnamespace>, but found ...`). Always
confirm each `namespace` opened at the top of a file has a matching `end` after
the last declaration, before launching a long build.

**Identifier/universe pitfall (2026-08-22)**: Lean treats ASCII identifiers and
their visually similar Unicode forms as different names (`nu` versus `ν`).  In a
declaration with `relaxedAutoImplicit = false`, mixing them can silently create
an extra single-letter implicit type and later report stuck universe constraints.
Use one spelling consistently in binder headers and result types, then rerun the
owning target before diagnosing the mathematics.

**Namespace visibility pitfall (2026-08-22)**: a transitive import makes a Lean
declaration available to elaboration but does not open its namespace.  The Stage-3
arithmetic bridge therefore needs `open C1CrossingEulerLogReadback` before using
`canonicalPrimePowerTerms` or `canonicalCrossingLengthSet`; an `Unknown identifier`
at those names is a visibility error, not a missing theorem.

## 8c. Numeric probe hygiene on the metric wall (`docs/proofs/*probe.py`)

2026-08-06 lesson (Gate-3U / Proof-717): probing `(I−R)∘T†∘R` in numpy, and then
the full-metric endpoint, hit two artifacts that must be guarded:

- **Naive `G⁻¹` blows up.** The metric coframe `D = finiteEulerMetricCoframe =
  `H·J·G⁻¹` with `G=H` restricted Gram; pinv of the full-grid `G` yields
  `~3×10¹⁴` because off-carrier columns make it near-singular. `G` must be
  restricted to the carrier rank *before* inversion, else the probe reports
  "unbounded" where the analytic operator restricts to an isometry.
- **The uniform-grid proxy `I−R` annihilates `D` by construction.** The real
  `sourceBandProjection = E − R₀` (E − source Sonin projection) does NOT vanish
  on the metric coframe; the grid's `I−R` does, so `‖(I−R)∘D‖=0` is a proxy bug,
  not a fact. Faithful numeric cancellation tests need the actual R₀ band, which
  a uniform log-t grid does not realize. Off-piste numeric verdicts on this wall
  are therefore only decisive for the outer branch in isolation (`‖(I−R)∘T†∘R‖`),
  not for the three-branch cancellation.

**Lesson**: a numeric probe that "decides" Gate-3U must build the exact operator
products and inverse Gram with the same metric restriction the proof uses; grid
proxies of projections are a trap. Scope any probe result accordingly (branch
in isolation vs full cancellation) in the docstring and in any commit.

**Fidelity guard (proven-identity first)**: before trusting any norm/leak number
on the metric wall, the probe MUST first reproduce a Lean-proven identity. For
the metric coframe that identity is `J†∘D = id` (CoframeResponse:52). In 816 the
small well-conditioned grid reproduces it to `1.0000` exactly; only then are the
`(I−R)∘D` numbers trusted. Doing this separates a real fact (outer channel stays
>1 on 2+ primes) from the two 814 traps (naive `G⁻¹`→3e14, grid `I−R`→0). The
correct ambient Gram is `T†T`, not `T·T†` (T non-normal), and `G`/`G⁻¹` must be
restricted to the carrier span before inverting.

**Probe universality / carrier realism (817)**: a numeric verdict on the metric
wall is only as honest as its carrier. If the escape hypothesis names a
"prolate / exact-Sonin carrier", that must be approximated by the *exact*
band-limited family (Slepian sequences via `scipy.signal.windows.dpss`), not by
smooth bumps (816's Gaussian-sinc). Slepian dpss columns cut to radial support
do **not** make the outer leak `(I−R)∘D` decay: it stays 0.28–0.46 as the band
narrows. Lean grounding: the repo defines the Sonin space only by abstract
star-projections over the spatial half-line (`GlobalLogSoninProjection.lean:153-
163`, `cc20PositiveHalfLine = Set.Ici 0`); there are **no explicit PSWF**
objects. So an "exact prolate" carrier is not a reachable Lean object today —
state that the Slepian probe uses the mathematically-correct object the escape
names, not a repo-owned basis.

**Do not discretize the Sonin projection (818)**: the exact `R0` (Sonin =
`range(radial) ∩ range(HT†·R·HT)`, a *continuous* infinite-dim intersection,
`CCM24HardyTitchmarsh.lean:376-380`) CANNOT be "reached" numerically by von
Neumann alternating projection on a finite grid: `span(R)` and `span(HT†RHT)`
are near-transversal there, so the numerical intersection is rank 0 (or fails
idempotence).  Any second/band-channel number built on that degenerate R0 is a
proxy artifact and must be explicitly discounted (818).  The only channels a
grid probe can trust are ones free of R0/Q0 — i.e. the OUTER channel
`(I−R)∘D`.  To measure the inner (second/band) gate channel you need the actual
archimedean scattering phase `archFactor/conj(archFactor)` and its transported
Sonin/prolate frame — an analytic object, not a grid intersection.

**(819): even the TRUE archimedean phase does not converge.** The real
`m = archFactor/archFactor(−xi)` (Gamma-ratio, `CCM24HardyTitchmarsh:43-45,
74,104-106`) rescues the *dimension* (rank 0→8 at λ=0) but NOT the
*projection*: idempotence never →0 under iteration (profile 3.04e-1…2.55e-1).
Root cause: `range(R)` and `range(HT†R·HT)` are almost-parallel (thin Sonin
band), so alternating projection has no angle lower bound ⇒ no finite-grid
convergence. Do NOT spend time re-cutting R0 by iteration.

**(820): no Sobolev/decay mechanism for the outer channel (route-1 ruling).**
The outer leak of D on a radial probe is FLAT in both metric resolution (x1..x8:
0.278→0.279 / 0.374→0.375 / 0.344→0.396) and radial-cutoff depth (0..-1.5).
No threshold/mollifier scale makes `(I−R)∘D` vanish. A Lean route-1 "Sobolev/
decay" lemma has no numerical basis. Probes on this wall: keep them R0/Q0-free
(outer channel) else they inherit the 818/819 degeneracy; the outer channel is
non-zero at every analytic scale tested (815 simple, 816 band, 817 exact-Slepian,
819 real-phase dim, 820 Sobolev-scale).

**(821) verify a "0" against box growth**: a leak that prints `0.000` for a large
prime (e.g. `{101}`) is usually a box-truncation artifact — `log(101)=4.61` > box
`Lt=4`, the transport shift leaves the grid, `D` acts trivially. Always
re-check by growing `Lt` (small primes are box-stable, so the contrast is real);
the honest `{101}` leak is 0.098, not 0. Route "real primes escape to 0" is a
box trap.

**(822) build the transported-Sonin frame, don't intersect subspaces**: use the
proven `maps_sonin_intersection` (`CCM24FiniteEulerSoninTransport:69-77`): the
correct gate frame is `T·(exact Slepian radial)`. Measuring `(I−R)∘D` on it gave
the LARGEST leak of the whole family (0.38–0.56, log-stable), so the transported
frame is where the outer leaks most, not where it vanishes. Neither 821 (real
arithmetic) nor 822 (transported-Sonin) rescues the outer channel; the live
routes are RH-scale analytic, beyond a finite grid.

**(824) a non-zero leak must be checked for plateau vs decay**: a single-grid
non-zero (like 822's 0.38–0.56 at n=600) only proves "non-zero at one
resolution". To promote it to a real lower bound (or dismiss it as an artifact),
sweep resolution AND interval. On the transported-Sonin frame the outer leak is
resolution-robust: n:200→6000 and L:4→32 keep it pinned at ≈0.62 (single-family
floor ≥0.369), so it PLATEAUS to a positive constant — the 822 leak is real, the
transported-Sonin outer channel cannot vanish. A leak that decays to 0 as
`n,L→∞` would instead be a grid artifact and should be discarded. (See 824.)

**(P3-0, 2026-08-21) FFT legs need an origin check; closed-form tails need the right antiderivative.** Two bugs in
the `qw(bumpPlateauTest)` probe (`p3_probe_qw_plateau.py`) would each have flipped the Fork A/B verdict:
(1) circular convolution of a signal centered at index N/2 lands near `2·(N/2) mod N = 0` — the FFT origin must sit
at position 0 so the support [−1,1] straddles index 0 (wrap-around is safe only when support width < period); always
cross-check an FFT leg against direct quadrature at probe points before trusting it. (2) `np.expm1(y)` is e^y − 1,
NOT e^y: the archimedean denominator is `e^y − e^{−y} = 2 sinh y` (`SelectedWeilFormula.lean:103`), and writing
`expm1(y) − exp(−y)` makes it tend to −1 (false pole at asinh(½)). (3) The tail `∫_a^∞ dy/(2sinh y)` is
`atanh(e^{−a}) = Σ_k e^{−(2k+1)a}/(2k+1)`, NOT `-ln(1−e^{−a})` (that integrates 1/(e^y−1)); they differ by ~0.0093
at a=2, i.e. +0.035 on the archimedean term. Final probe: three independent legs (trapz double-resolution, FFT grid,
Gauss–Legendre direct) agree to ~2e-9; `qw g₀ = −0.421583` → Fork B.

**(P3-a·0, 2026-08-21) at narrow width w, do NOT assume the archimedean main integral is relatively ~w.** In
`p3_probe_qw_narrow.py` (qw of `narrowArchRoot`, w ≈ 1.8e-8), the pre-estimate claimed I_main[0,2w] contributes only
O(w·F(0)) — off by an O(1) factor of ~9. Root cause: when ∫g dx = 0 exactly (zero-mean test; here all three spectral-integral
moments vanish because bumpEx is flat at ±1 AND vanishes there, so int Bₖ = 0 ∀k), the identity
∫₀²[Φ(u)+Φ(−u)]du = 0 cancels I_main's leading piece and leaves `I_main = w·K''` with K'' := ∫₀²(E(u)−Φ(0))/u du an O(Φ(0))
constant ⇒ |I_main|/F(0) → |K''|/Φ(0) ≈ 8.9, i.e. O(1), NOT ~w. Rule: for any narrow-support archimedean integral, FIRST check
the zero-mean identity; and verify the dimensionless ratio (here I_main/F(0)) is resolution-stable before calling a term
"negligible". Minor companion lesson: `np.polynomial.legendre.leggauss` nodes already live on [−1,1] — remapping them into
[0,1] silently computes a half-integral for even integrands (the tell is exactly a factor 2).

## 9. CC20 Operator/Trace Rule

The current normalized core does not implement operator theory
(`positiveTrace`, `traceClass`, `cyclicLegal`, `hilbertSchmidtGate` are not
analytic closure). A valid CC20 trace producer must tie one route test to:
half-density convolution square, theta-smoothed compressed operator, measurable
Schwartz kernel, square-integrability, Hilbert-Schmidt norm, adjoint/composition
kernel, ordinary positive trace, per-move cyclicity witnesses, source-normalized
trace identity with explicit remainder, and the rank/pole corrections that
identity requires.

Keep the regularized Connes trace separate from the ordinary positive trace of
`A*A`; do not write `Tr(A*A)=QW_lambda`. Contract M3 must prove or reject control
of the nonzero remainder `D_S`. Keep the CCM25 support parameter (`lambda_qw`)
and operator cutoff (`Lambda_op`) separate.

`ordinaryTraceAlong` (CC20Concrete/PositiveTrace.lean) is the diagonal-series
trace in a named Hilbert basis; `ordinaryTraceAlong_neg` needs no trace witness.
A legal cyclic trace move requires two Hilbert-Schmidt factors or one
trace-class times one bounded factor; bounded-times-HS alone is not trace-class.

## 10. CCM25 Canonical Owner Rule

Preserve one source owner through source Weil-form, evaluation data, visible
arithmetic, canonical atom normalization, package certificate data, and
restricted/global masses. Do not lower the route by moving among equivalent
wrapper spellings unless a named theorem proves otherwise. Support data plus
visible arithmetic is insufficient when atoms can come from another source;
  package-atom alignment and same-owner transport are mandatory. The old
  globally quantified support model was uninhabited, but S2 replaced it with
  `PerCommonSourceFinitePrimeSupport`; the current concrete
  `SourceWeilFormData` is constructible (`ConcreteP1SupportProbe.concreteWeilForm`).
  Do not reuse the archived pre-S2 emptiness guard against the current type.

## 11. RH-Level Guards

Detector-only coverage is not a lower producer after detector existence is
available. Do not use `SourceRH` or no-off-line source-zero as closure for the
route.

`hilbertSchmidtGate` in the concrete CC20 model (`Test=SchwartzMap`,
`Window=(0,0)` single-point, `window-gated supportValue`) needs BOTH
`suppCarrier f` and `suppCarrier (𝓕 f)` inside the same single-point window;
only the zero test satisfies both, and a `{0}`-only trace model is an empty
producer (AGENTS §6). Do not obtain HS-gate by λ-scaling — `windowCarrier ⊆
lambdaCarrier` is passive containment that does not enlarge the window. A
  non-single-point window architecture with nonzero tests (or a new band-limited
  HS model) is required to resolve that archived A0 lane. It is not the current
  RH theorem root.

**A0 实证收窄 (2026-08-04, Dev/A0WindowGateGuard.lean**): build-reduced the
RUNNING skeleton (`#reduce normalizedCoreSourcePkg.cc20Trace...hilbertSchmidtGate`):
`traceClass g = SupportWindowData.supportInWindow g I`, `cyclicLegal g =
fourierSupportInWindow g I` over `defaultWindow=(0,0)`,
`hilbertSchmidtGate g = traceClass g ∧ cyclicLegal g` (rfl).  The concrete
single-point carrier is now PROVEN (axiom-clean, `Dev/A0WindowGateGuard.lean`):
`pointInConcreteWindow (0,0) x ↔ x.1=0 ∧ x.2=0`.  So the windowed Fourier side
(`cyclicLegal`) forces `(𝓕 g)` to be supported only at coordinate `{0}` — a
Schwartz function with Fourier support ⊆ a point is a (zero) polynomial, so
only the zero test can satisfy the gate over this window: **empty producer,
AGENTS §6**.  Statements were provable all along; the obstruction is the
carrier's zero-only satisfiability.  The skeleton statements
(`trace_class_template_statement`:462, `trace_square_statement`:481,
`ordinary_trace_support_square_statement`:487) are provable for this seed
without any window.  To clear A0 requires a genuinely non-single-point window
with a nonzero test carrying an HS trace-class witness (windowed machine
`windowedBoundaryDetector = A†A`, `CompactLogTest`), i.e. a change of the
carrier/`traceClass`/`cyclicLegal` concrete interpretation — NOT a change of the
`hilbertSchmidtGate` signature.
Both probes (supplier + statement) are axiom-clean.  A1 (Seam B) bridge
(`Dev/A1SeamBOperatorCarrierProbe.lean`) is closed axiom-clean: `0 ≤ Tr(A†A)`
via `ordinaryTrace_positiveComposition_re_nonnegative` and concrete
`HilbertBasis` of `cc20GlobalLogCrossingL2` exist.  The sign chain bottoms out
at `cc20Trace.sourceHilbertSchmidtGate sourceTraceTest`
(UnconditionalSkeleton.lean:5205), a structural gate on one test — so A0's
remaining open item is the existence of a **nonzero** `CompactLogTest` test
satisfying the HS gate, not the downstream positive-trace machinery (that
segment is now fully proved).  A2 (`Dev/A2CompactLogCarrierProbe.lean`) shows
this cannot be a localized carrier swap: `SourceTestAlgebra` forces a full
`legacy : LegacyTestEquiv Test` bijection (Test ⇌ TestFunction), and
`CompactLogTest` is only a compact-support subset of `TestFunction`, so no
`LegacyTestEquiv CompactLogTest` exists.  **Seam B double-block verdict
(2026-08-04)**: BOTH repair conduits die at the concrete carrier layer and are
structurally rejected.  (ii) an operator/trace-class gate cannot be spliced
either: `concreteTestAlgebra` carries `Test := ConcreteTest := TestFunction`
(`AnalyticCoreBase.lean:3094,3119`, `legacy = concreteLegacyTestEquiv`,
encode/decode `= id`), while the HS-sandwich machine
(`windowedBoundaryDetector` = `A†A`, `windowedRootFactor`) lives on the
`CompactLogTest` domain — so the operator gate and the concrete carrier do not
type-match.  **A0 emptiness is the Heisenberg/band-time conflict in the gate's
own semantics, not a `(0,0)`-window artifact**: `supportInWindow g I =
supportCarrier g ⊆ windowCarrier I` (AnalyticCoreBase.lean:1441) and
`fourierSupportInWindow g I = fourierSupportCarrier g ⊆ windowCarrier I` (:1495),
so the single-point-window empty-producer result actually holds for **any bounded
window** (compact time-support ⇒ entire `𝓕g` (Paley–Wiener), an entire function
with compact real-axis Fourier support is zero).  Hence (i) the compact-support
equality carrier shell is **mathematically dead too**, not merely type-blocked.
Resolving A0 needs **the operator/trace-class gate**, whose only movable seam is
`SourceFourierSupportInvolutionGeometryData.fourierSupportInWindow`
(AnalyticCore.lean:678-681, a seed-supplied structure field), reinterpreted as an
`A†A`-operator predicate; it is a genuinely new band-limited operator estimate,
not a signature rewrite.

**Gate-3U 右能量对 inverse-Gram 界（2026-08-04，CCM25Concrete）**: 在
`canonicalRealGate3UAt` 正向上，`canonicalRealGate3UAt_of_completedKernelRightEnergy`
（`CCM24FiniteSCanonicalAdjointEnergyGate.lean:375`）把 Gate 归约到单一 premise
`hright : sourcePhysicalCoframeCompletedKernelRightEnergy ≤ fixedMajorant`。该右能量 =
`∑‖pair.right∘leak(basis i)‖²`，经 `tsum_normSq_precomp_le` 收紧为
`‖leak‖²·(右边 fixed majorant)`；唯一真新量是 `‖finiteEulerMetricCoframe‖`（未归一
Gram 逆，内含 `finiteEulerGramInv`）。scalar seam 给出 `‖metric coframe‖ ≤ 1/
suffixEulerSchurMarkovScalar(canonical)`,且该 scalar ≤1。因 consumer 只就固定
canonical family 求右能量，对**固定 owner** 这是**有限**（可能大于 majorant）的单算子
界, 不族统一 → 需具体计算核对 `1/suffix(canonical)` 因子系数 vs `fixedMajorant`，
    是该历史 Gate-3U lane 的 analytic bottom (condition-number 类, 防发散; 【859b/859c 推进（2026-08-08）：】定义域谓词 `MellinCriticalDefined.criticalDefined g := Integrable (logWeight (I/2) g)` 已建（axiom-clean）；`MellinBandGamma` 证得 band 测试 `t^a e^{-t}` 临界点 Mellin = `Complex.Gamma(a+i/2)` 且非零（`mellin_band_eq_Gamma` / `mellin_band_ne_zero`，axiom-clean）——sign 槽不再是空/零生产者。剩余 open：`Re[Gamma(a+i/2)^4] >= 0` 之相位上界（需 Gamma 渐近/Stirling，mathlib 尚缺），未证。

## 12. Coding And Review

Follow existing namespaces, naming, imports, and theorem layout. Make local,
reversible changes; extract helpers only to remove duplication or preserve a
same-object invariant. For a nontrivial change: state old weak path, add lower
data/API, prove projection/compatibility theorems, rewire the real consumer,
prove the old path is inactive, add negative guards for the removed shortcut.
Comments explain math ownership or a Lean elaboration hazard, not obvious code.

## 13. Documentation

`AGENTS.md` stores stable working rules; `MEMORY.md` stores the current route
snapshot and milestone evidence; plan docs store executable dependency trees.
Keep root docs concise; git history owns superseded chronology. Every plan must
state scope/non-goals, code evidence (file+line), source evidence (URL/manuscript
line), exact data-bearing APIs, consumer rewiring path, rejection guards,
smallest build and focused axiom audit, and success/partial/blocked/rejection
criteria.

For GitHub-rendered Markdown, use `$$` display blocks for LaTeX. Wrap a
multiline equation in `\begin{aligned} ... \end{aligned}` when it contains an
equals-sign continuation: GitHub can otherwise parse the preceding line as a
heading. Avoid `\operatorname`; the repository renderer rejects it. Verify
edited display math in the repository UI, not only through `/markdown`.

## 14. Git And Public Hygiene

Imperative commit subjects ≤72 chars; commit/push only coherent milestones and
only when requested/authorized. Before commit/push:
`git status --short`, `git diff --check`, `git diff --cached --name-status`,
`git diff --cached --check`; inspect staged file ownership; scan for local
paths/private workflow artifacts. Do not stage private workflow files
(`AGENTS.md`, `MEMORY.md`, `RUNBOOK.md`, `HANDOFF.md`, `CONTEXT.md`, `WORKLOG.md`,
`.codex/`) unless the repo owns them. Public GitHub text must not contain Windows
or WSL absolute paths, temp verification dir names, private artifact names, JSON
escapes, or mojibake. After posting/editing public text, read back the rendered

**Default delivery lane (2026-08-08):** all routine work lands on main -- commit on main, push origin main. Do not spin up or keep extra local/remote branches for routine milestones; only branch for a genuinely isolated experiment that must not pollute main, and clean it up when done. When an internal convening asks to consolidate, ff-only into main and push, then remove the now-dead local branch. A GitHub-PR workflow is a separate, explicitly-requested exception, not the norm.
upstream body.

## 15. Handoff Standard

A milestone handoff must answer: result (good/partial/blocked/rejected); RH
status (unconditional or conditional); files changed; declarations added/changed;
active root removed/lowered; old weak path inactive evidence; build target and
result; import-facing audit result; focused axioms; remaining mathematical
bottom; next safe action. Do not claim "proved RH" from a successful build; that
requires plan 016 Phase 8 (`#print axioms unconditional_rh_skeleton` with no
project roots / `sorryAx`) plus the full repository verification gate.

## 16. Stable API / Build Facts

- Whole-line Schwartz convolution owner: `CC20Concrete/GlobalLogConvolution.lean`.
  Accepted build: `lake build ConnesWeilRH.Source.CC20Concrete
  ConnesWeilRH.Dev.GlobalLogConvolution`.
- Crossing owner: `CC20Concrete/GlobalConvolutionCrossing.lean`
  (`C_h† C_h` positive, `C_h† C_h J_b` crossing); keep separate from compact
  `pairData`. Accepted build: `... GlobalConvolutionCrossingAudit`.
- Legal HS cyclicity: `ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint`
  (`Tr_H(A†B)=Tr_G(BA†)`, absolutely summable two-basis expansion).
- Raw Gate 3U readout contract: `CCM24FiniteSCausalMarkovRawSourceOwnerTrace.lean`.
- Physical renewal support split (Proof 807):
  `CCM24FiniteSCausalMarkovRawRenewalSupportSplit.lean` +
  `Dev/CCM24FiniteSCausalMarkovRawRenewalSupportSplitAudit.lean`.
- Tail trace-bound contract (Direction A):
  `CCM24FiniteSCausalMarkovRawRenewalTailBound.lean` +
  `Dev/CCM24FiniteSCausalMarkovRawRenewalTailBoundAudit.lean`; builds clean,
  axioms `[propext, Classical.choice, Quot.sound]`. Holds the support+tail trace
  split, the abs gate = sum of piece bounds, the `canonicalRealGate3UAt_of_tailNormBound`
  closure, **and** the whole-tail operator-norm bound with its exponential decay
  chain (`norm_inverseLowerFactorPhysicalRenewalTailResponse_le_const`,
  `_le_const_exp`, `rawRenewalTailNormConstant`, `rawRenewalTailWeightDoubleSum_reassoc`).
- Brick G (CLOSED 2026-08-14, `Dev/C1XiGlobalZeroSum.lean`): global regularized
  zero sum `Σ (1/(s-ρ)+1/ρ)` — `regularizedZeroSummable` +
  `regularizedZeroTail_norm_shellSum_le` + consumer form
  `regularizedZeroTerm_norm_shell_le`. Route: docs/proofs/1012 §3, 1013.
- H-A0 (CLOSED 2026-08-14, `Dev/C1XiGlobalWeightedZeroSum.lean`):
  `weightedRegularizedZeroSummable` for
  `algebraMap ℝ ℂ (xiMultiplicity rho : Real) * regularizedZeroTerm s rho`.
  Norm-cast fact: `norm_algebraMap` + `Real.norm_eq_abs` — ℂ has NO
  `norm_ofReal` lemma; write the def with `algebraMap` literal.
  Route: docs/proofs/1013 (queue), next H-A1 = analyticity of the weighted
  sum via `Mathlib/Analysis/Calculus/SmoothSeries.lean`
  (`hasDerivAt_tsum_of_isPreconnected`).
- Center-2 Gamma_R readback (CLOSED 2026-08-17,
  `Dev/C1XiCenterTwoGamma.lean`): the paired-profile Fubini bridge
  `summable_integralOn_norm_gammaRArchProfileTerm`,
  `integralOn_tsum_gammaRArchProfileTerm`, and
  `integralOn_archimedeanIntegrand_eq_tsum` combines with the per-term
  Fourier/resolvent identity
  `integral_gammaRReciprocalTerm_eq_neg_four_pi_I_mul_archProfile`.
  The normalized series theorem
  `normalized_tsum_integral_gammaRReciprocalTerm_eq_neg_archimedeanIntegral`
  and `normalized_gammaR_centerTwo_re_eq_archimedeanTerm` then supply
  `centerTwoGammaReadbackContract_of_halfAnchorGauss`.
  The two summands of `gammaRArchProfileTerm` diverge separately: never
  dominate, integrate, or sum them separately. Keep the pair intact; use the
  compact-support Lipschitz `n^-2` head and exponential tail before
  `MeasureTheory.integral_tsum_of_summable_integral_norm`.
  This closes the Gamma_R archimedean factor. Its center-`2` contract is
  consumed by `C1XiCenterTwoArithmeticAssembly` to close Gate 2; it does not
  close the positive-trace bridge or RH. Accepted owner-plus-probe build:
  `lake build ConnesWeilRH.Dev.C1XiCenterTwoGamma
  ConnesWeilRH.Dev.C1XiCenterTwoGammaProbe`.
- Center-2 Gate 2 assembly (CLOSED 2026-08-17,
  `Dev/C1XiCenterTwoArithmeticAssembly.lean`):
  `centerTwo_arithmetic_eq_spectral` supplies
  `C1SameOwnerWeil.psi F = C1SpectralWeil.spectralWeilValue F` for every
  `CompactLogTest F`, and `gate2ExplicitFormula_centerTwo` packages it with
  the unconditional spectral summability theorem. The assembly consumes the
  proved `centerTwoGammaReadbackContract_of_halfAnchorGauss`; its owner-plus-
  probe build reports only `[propext, Classical.choice, Quot.sound]`. This
  closes Gate 2 only, not the positive-trace bridge, finite-vanishing
  criterion, Yoshida transport, or RH.
- Center-2 criterion bridge (CLOSED 2026-08-17,
  `Dev/C1CenterTwoCriterionBridge.lean`):
  `qw_eq_spectralWeilValue_centerTwo` transports the Gate 2 readback through
  one convolution square, and
  `healthyCriterionState_iff_all_vanishing_spectral_nonnegative` rewrites the
  healthy finite-vanishing criterion as spectral nonnegativity on every
  vanishing square. The spectral nonnegativity/positive-trace premise is still
  open; this module does not assert it. Its owner-plus-probe build is
  axiom-clean with `[propext, Classical.choice, Quot.sound]`.
- Center-2 healthy RH exit (CLOSED as a ledger statement 2026-08-17,
  `Dev/C1CenterTwoRHExit.lean`):
  `healthy_spectral_nonneg_sourceRH_of_yoshida_detector` composes the bridge
  with the generic `cc20_proposition_c1_from_yoshida_detector` at
  `C1.healthyCC20TestSpace`, discharging the triple admissibility and
  disjointness rows by the closed theorems. The distance to `SourceRH` on the
  generic all-zero healthy owner is exactly two explicit premises: Yoshida
  detector existence on that owner (constructive transport, open) and
  nonnegativity of `spectralWeilValue g.convolutionSquare` on vanishing
  squares (Lane R).  The later right-oriented construction removes the first
  premise only after choosing the functional-equation representative on the
  right of the critical line.
  Owner-plus-probe build (3603 jobs) axiom-clean with
  `[propext, Classical.choice, Quot.sound]`. RH is NOT claimed.
- Healthy Yoshida detector scaffold (2026-08-17,
  `Dev/C1HealthyYoshidaDetector.lean`): the healthy square is the genuine
  Hermitian square `laplaceAt (g.convolutionSquare) s =
  conj (laplaceAt g (-conj s)) * laplaceAt g s`, so a triple-vanishing test
  has ZERO pole term on its square and `qw g = -(archimedeanTerm +
  finitePrimeSum)` on vanishing tests. `HealthyYoshidaDetectorData rho g`
  (nondegeneracy + unconditional `0 < weilLocalSum (starConvolution g)`)
  refines detector existence into finite data, and
  `healthy_sourceRH_of_healthyDetectorData_and_spectral_nonneg` is the refined
  two-premise capstone. Build axiom-clean (3605 jobs). The generic all-zero
  detector producer remains open; the later right-oriented producer closes
  the direction needed for the spectral-sign contradiction. The Lane R sign
  stays untouched. RH NOT claimed.
- Right-oriented healthy detector and conditional RH exit (CLOSED 2026-08-18,
  `Dev/C1HealthyYoshidaSpectralNegativity.lean`): for every source xi zero
  strictly to the right of the critical line,
  `exists_healthyDetectorData_of_sourceNontrivialZero_right` builds genuine
  `HealthyYoshidaDetectorData` on one selected half-density-shifted owner. It
  keeps the finite interpolation prefix and fourth-order spectral tail on that
  same square, then proves its `spectralWeilValue` is strictly negative.
  `healthy_sourceRH_of_global_spectral_nonneg` chooses a right-side
  functional-equation representative for any hypothetical off-line zero and
  contradicts the explicit global nonnegativity premise. This is conditional:
  it does not prove global spectral nonnegativity or RH. Do not reflect a
  right detector back to a left zero without a new owner-preserving theorem;
  the reflection has not been proved to preserve the same Hermitian-square
  spectral sign. The owner-plus-probe WSL2 build (3633 jobs) is axiom-clean
 with `[propext, Classical.choice, Quot.sound]`.
- Remainder-aware positive-trace consumer (CLOSED 2026-08-18,
  `Dev/C1PositiveTraceLimitBridge.lean` and
  `Dev/C1PositiveTraceLimitBridgeExit.lean`):
  `PositiveTraceLimitFamily` keeps one Hilbert basis, trace-data sequence,
  real remainder, vanishing remainder limit, and same-owner readback in one
  structure. `positiveTrace_sub_remainder_lower_bound` uses only the ordinary
  `A^* A` trace positivity; the two limit consumers then derive
  `qw >= 0`, spectral nonnegativity, and the conditional `SourceRH` exit.
  The corrected trace identity in `docs/proofs/016_corrected_trace_identity.md`
  requires `PositiveTrace = QW + D` on vanishing tests, so `D` is kept as a
  genuine remainder and is never defined to be zero. The finite-window
  operator construction and its trace-class witness are now closed by the
  companion producer below. A fixed-carrier cutoff schedule adapter now binds
  the expanding windows to one whole-line basis; its remainder estimate and
  same-owner analytic readback remain open. The owner-plus-probe WSL2 build
  (3636 jobs) is axiom-clean with
  `[propext, Classical.choice, Quot.sound]`; `Tendsto` requires `open Filter`
  and the `𝓝` notation requires `open scoped Topology`.
- Finite-window positive-trace producer (CLOSED 2026-08-18,
  `Dev/C1PositiveTraceWindowProducer.lean` and its probe):
  `fullBoundaryPositivePairData` keeps the same whole-line `globalBasis` on
  both copies of `fullBoundaryRootFactor : H -> G`, proving the genuine
  rectangular `F†F` trace is trace-class and has nonnegative real part.
  `fullBoundaryOutputZeroExtension` maps the output interval back into the
  common carrier, and its proved identity `E†E = id` yields the square owner
  `fullBoundaryPositiveBasisData.positiveComposition =
  windowedBoundaryDetector`. The square trace-class, detector readback, and
  nonnegativity declarations all audit to `[propext, Classical.choice,
  Quot.sound]`; WSL2 ext4 owner-plus-probe verification completed `3693`
  jobs. This is a fixed-window result only: it does not construct the
  `PositiveTracePairLimitFamily`, prove a cutoff remainder tends to zero,
  identify the limit with `C1SameOwnerWeil.qw`, or prove RH. The local import
  `open CCM25Concrete.SelectedCrossingOperatorBridge` is required because
  namespace openings are not transitive across files.
- Fixed-carrier cutoff adapter (CLOSED 2026-08-18,
  `Dev/C1PositiveTraceCutoffAdapter.lean` and its probe):
  `cutoffRadius g n = supportRadius g + n + 1` gives an expanding symmetric
  window containing `Function.support g.test`; `cutoffPositiveBasisData` uses
  fresh local interval bases only for Hilbert--Schmidt summability while every
  ordinary trace stays on one caller-supplied `globalBasis`. The proved
  `positiveComposition = windowedBoundaryDetector` readback and nonnegative
  trace are packaged into `CutoffLimitContracts`, whose two fields are exactly
  `remainder_tendsto_zero` and the same-owner corrected-trace readback. The
  adapter constructs `PositiveTraceLimitFamily` from those fields but does not
  prove either field. WSL2 ext4 `lake build
  ConnesWeilRH.Dev.C1PositiveTraceCutoffAdapter
  ConnesWeilRH.Dev.C1PositiveTraceCutoffAdapterProbe` completed successfully
  (`3694` jobs); the probe audit reports only `[propext, Classical.choice,
  Quot.sound]`, with no `sorryAx` or RH root axiom.
- Dominated-diagonal cutoff adapter (CLOSED 2026-08-18,
  `Dev/C1PositiveTraceTraceContinuity.lean` and the extended cutoff probe):
  `tendsto_ordinaryTraceAlong_re_of_dominated_diagonal` applies Tannery
  convergence on the fixed `globalBasis` under an explicit summable diagonal
  majorant. `CutoffDominatedTraceWitness` records that majorant, the candidate
  limit operator, diagonal convergence/dominance, and the same-owner limit
  trace identity. `cutoffLimitContractsOfDominatedWitness` then combines this
  trace limit with a separately supplied `remainder -> 0`; it does not produce
  the majorant, remainder estimate, or analytic same-owner identity. WSL2
  ext4 verification completed the owner and probe build at `3696` jobs with
  only `[propext, Classical.choice, Quot.sound]`.
- Cutoff compression obstruction (CLOSED 2026-08-18,
  `Dev/C1PositiveTraceCutoffCompression.lean` and
  `Dev/C1PositiveTraceCutoffObstruction.lean`): each finite-window detector is
  exactly `C† * P_window * C`, while the natural uncompressed candidate is
  `C† * C`; the projection cannot be removed before a trace-limit theorem.
  `positiveComposition_trace_re_le_tsum_bound` proves that any summable
  diagonal majorant gives one uniform upper bound for all cutoff real traces,
  and `not_exists_cutoffDominatedTraceWitness_of_trace_re_unbounded` excludes
  the current dominated-diagonal witness if a separate lower-growth theorem
  proves those traces unbounded. The lower-growth theorem is now CLOSED by
  `Dev/C1PositiveTraceCutoffGrowth.lean` (exact trace = window length times
  `L2` mass, hence unbounded). Direct WSL2 `lake env lean` checks of the
  owner and probe pass; the audited declarations use only
  `[propext, Classical.choice, Quot.sound]`.
- Plain-window trace family verdict (DEAD for `qw` readback, 2026-08-18,
  `Dev/C1PositiveTraceCutoffVerdict.lean`, docs/proofs/1016):
  `not_nonempty_cutoffLimitContracts_of_test_ne_zero` proves
  `IsEmpty (CutoffLimitContracts g globalBasis)` for every nonzero
  compact-log root. The two contract fields force the raw cutoff trace to
  converge to the finite `C1SameOwnerWeil.qw g`, while the exact
  window-length formula plus `cutoffPositiveBasisData_trace_re_monotone`
  forces monotone linear divergence. The plain-window detector trace is the
  pure window bulk mass with no arithmetic content; do NOT re-attack this
  family with sharper estimates. A productive positive-trace limit needs a
  different detector family (Hilbert-transform/Mellin-conjugated window) so
  the bulk cancels. Owner and probe are WSL2 axiom-clean
  `[propext, Classical.choice, Quot.sound]`; RH NOT claimed.
- Lane R prime-free numeric verdict (POSITIVE, 2026-08-18,
  docs/proofs/1017 + probe script): sampled triple-vanishing prime-free
  roots satisfy `archimedeanTerm (g^2) < 0` strictly with margin 0.77..1.24
  at unit norm (qw = -arch > 0), across four windows; the arch quadratic
  form looks negative DEFINITE on the vanishing subspace. Detector roots at
  fake off-line points keep arch < 0 (the Lean sign flip needs a REAL
  off-line zero). Identified next Lean targets: concrete-root leaf
  `arch(root^2) <= 0` via the plateau template, then the general subspace
  negativity via the C1XiCenterTwoGamma Gamma_R paired-profile machinery.
  The prime-free instance carries no prime arithmetic; full prime-inclusive
  Lane R remains the RH-level gap. RH NOT claimed.
- Lane R prime-free spectrum scan (NUMERICAL, 2026-08-18,
  docs/proofs/1020 + probe script): a deterministic archimedean quadratic
  form scan on the three-moment nullspace remains negative through square
  support radius `0.690 < log 2`, polynomial-envelope bases through `K = 32`,
  and an independent sine basis through `K = 48`.  At the widest sine case
  the top eigenvalue is about `-0.8535` and grid convergence is stable.  The
  Gamma_R paired-profile declarations in `C1XiCenterTwoGamma` are an exact
  readback only; they do not supply this sign inequality.  Do not transfer
  numerical eigenvalues into Lean.  This is evidence for the prime-free
  subfamily, not universal Lane R, detector positivity, or RH.
- Gamma_R profile-term sign screen (REJECTED, 2026-08-18,
  docs/proofs/1021 + probe script): the individual paired-profile quadratic
  forms are nonpositive at small indices but develop positive directions on
  the same three-moment prime-free subspace (at `n = 400` in the
  analytically de-singularized Gauss-Legendre screen).  Do not pursue a theorem of the form
  `forall n, profileTerm n <= 0`; the total arch sign requires the constant
  term and cross-index cancellation.  The exact Gamma_R readback remains
  valid, but it is not a sign producer.
- Summed Gamma_R prefix/tail owner (2026-08-18, docs/proofs/1022):
  `Dev/C1XiCenterTwoGammaSummedKernel.lean` exposes the exact decomposition
  `archimedeanTerm = constant + sum (range N) profileIntegral + shiftedTail`
  and proves the shifted tail tends to zero.  The 1022 sine-nullspace screen
  finds the first all-negative finite prefix at Lean length `N = 4`, with the
  3201-term reference top eigenvalue about `-0.8643`; small positive directions
  remain in high finite tails.  The next valid target is a finite constrained
  kernel bound plus a tail norm bound, not a tail sign lemma.  Owner/probe
  audit is `[propext, Classical.choice, Quot.sound]`; numerical spectra are
  not transported into Lean and RH remains open.
- Summed Gamma_R tail magnitude estimate (CLOSED 2026-08-18,
  `Dev/C1XiCenterTwoGammaTailEstimate.lean`):
  `exists_gammaRArchProfileIntegral_norm_bound` gives each paired profile
  integral an explicit `n^-2` head plus exponential tail bound.  The public
  `gammaRArchProfileTailNorm_le_explicit_majorant` then bounds the shifted
  absolute tail by a real `tsum` whose two components are respectively a
  summable p-series and a summable geometric series.  This is a magnitude
  interface for the coupled finite-prefix estimate.  The follow-up
  `gammaRArchProfileTailNorm_le_explicit_rate` closes the rate
  `L / (2*N) + 2*||F.test 0||*exp(-(2*N+1)*(supportRadius F+1)) /
  (1-exp(-2*(supportRadius F+1)))` for `N > 0`, with existential `L >= 0`.
  This remains a magnitude interface only: it supplies neither a tail sign
  nor the finite constrained-prefix inequality.  Owner/probe WSL2 build
  completed at 3540 jobs, with audited declarations using only
  `[propext, Classical.choice, Quot.sound]`; RH remains open.
- Summed Gamma_R prefix/tail sign consumer (CLOSED 2026-08-18,
  `Dev/C1XiCenterTwoGammaPrefixTailConsumer.lean`):
  `archimedeanTerm_nonpos_of_profilePrefix_bound_and_tailNorm_bound` consumes
  the exact constant-plus-prefix-plus-tail decomposition, bounds the tail real
  part by `Complex.re_le_norm` and `norm_gammaRArchProfileTail_le_tailNorm`,
  and concludes `archimedeanTerm F <= 0` from a matching prefix budget and
  absolute tail budget.  The strict companion retains a positive `delta`
  prefix margin.  This is an order-theoretic consumer only; it does not
  produce the finite constrained-kernel inequality or a tail sign.  The
  owner/probe build completed at 3541 jobs with only
  `[propext, Classical.choice, Quot.sound]`; RH remains open.
- Lane R prefix/tail absolute-budget screen (NUMERICAL, 2026-08-18,
  docs/proofs/1025): the finite `N=4` prefix is negative in the tested sine
  nullspaces, but the same-vector finite tail sum
  `sum_(N <= n < 801) |profile_n|` is roughly `6x` to `12x` its prefix margin.
  At `N=21`, the corresponding sampled ratios are `0.083` to `0.719` over
  radii `0.20..0.34` and basis sizes `16,24`.  These are finite numerical
  screens only; they reject the naive `N=4` absolute-budget choice for the
  samples and select `N=21` as the next formal target.  Do not treat them as
  an infinite-tail or universal constrained-kernel theorem.
- Lane R mass-relative tail bridge (CONDITIONAL CLOSED, 2026-08-18,
  docs/proofs/1026): `C1XiCenterTwoGammaTailEstimate` now exposes
  `gammaRArchProfileTailNorm_le_explicit_rate_of_pointwise_majorant`, so a
  later owner can supply an explicit profile constant instead of unpacking an
  existential `L`.  `C1XiCenterTwoGammaMassRelativeTail` rewrites the norm of
  a convolution-square zero value to its nonnegative real mass and assembles a
  budget with `L = C * mass`.  The local mass-scaled profile estimate remains
  a premise: `convolutionSquare_norm_le_mass` controls values, not the
  derivative/Lipschitz constant behind the `n^-2` bound.  Do not infer that
  premise from Cauchy-Schwarz, and do not call this bridge a Lane R or RH
  proof.  Owner/probe WSL2 verification is axiom-clean.
- Mass-relative Lipschitz stress screen (NUMERICAL, 2026-08-18,
  docs/proofs/1027): normalized D3 roots retain three-point Laplace residuals
  below `4e-12`, while the interior-grid lower bound for the convolution-square
  derivative grows from `72.7` at frequency `0` to `256.5` at frequency `256`
  at unit mass.  This is evidence against assuming a small frequency-uniform
  mass-only coefficient for the Gamma_R `n^-2` head.  It is not a proof against
  a finite-band or owner-specific bound; use a derivative-energy certificate
  or a coupled quadratic tail instead.  Do not import these floating-point
  values into Lean.
- Mass-relative Lipschitz tail adapter (CONDITIONAL CLOSED, 2026-08-19,
  docs/proofs/1028): `C1XiCenterTwoGamma` now exposes
  `gammaRArchProfileTerm_norm_le_of_support_lipschitz` with an explicit
  nonnegative `Lip`.  `C1XiCenterTwoGammaMassRelativeTail` converts a supplied
  certificate `Lip = C_L * squareMass` into the head coefficient
  `(2 * C_L + 1) * squareMass` and feeds it to
  `gammaRArchProfileTailNorm_le_mass_scaled_rate_of_support_lipschitz`.
  The certificate and the finite constrained-prefix inequality remain open;
  this is an adapter only.  Owner/probe WSL2 verification completed at
  `3541`/`3542` jobs with `[propext, Classical.choice, Quot.sound]`.
  Do not infer a universal `C_L`, Lane R, global spectral nonnegativity, or RH.
- Derivative-energy Gamma_R tail producer (MAGNITUDE CLOSED, 2026-08-19,
  docs/proofs/1029): `C1XiCenterTwoGammaDerivativeEnergy.lean` defines the
  compact-log derivative energy and proves the genuine convolution-square
  derivative bound
  `||deriv (g^* * g).test x|| <=
  sqrt(squareMass(g)) * sqrt(derivativeEnergy(g))`.
  Reflection/translation invariance gives the support-local Lipschitz
  certificate, and `gammaRArchProfileTailNorm_le_derivativeEnergy_rate`
  supplies the existing explicit shifted-tail rate.  This is an unconditional
  absolute-magnitude producer only; it does not supply a tail sign, the finite
  constrained-prefix inequality, universal Lane R, or RH.  Owner/probe WSL2
  verification completed at `3542`/`3543` jobs with only
  `[propext, Classical.choice, Quot.sound]`.
- Constrained Gamma_R prefix owner (INTERFACE CLOSED, 2026-08-19,
  docs/proofs/1030): `C1XiCenterTwoGammaConstrainedPrefix.lean` names the
  numerical `N = 21` prefix, exposes its real profile-integral readback, and
  proves the exact same-owner decomposition into that prefix plus the shifted
  tail.  It also names the triple-vanishing and prime-free predicates and
  transports the D3 root into them.  Since the shifted tail tends to zero,
  `exists_gammaRArchFinitePrefixValue_lt_zero_of_archimedeanTerm_neg` proves
  existence of some negative finite prefix whenever the complete archimedean
  value is strictly negative.  The witness length is test-dependent: this
  does not prove the uniform `N = 21` sign target
  `laneRConstrainedPrefixSignTarget`, a tail sign, universal Lane R, or RH.
  Owner/probe WSL2 verification completed at `3607`/`3608` jobs with only
  `[propext, Classical.choice, Quot.sound]`.
- Smooth constrained-prefix screen (NUMERICAL, 2026-08-19,
  docs/proofs/1031): the fixed `N = 21` paired Gamma_R prefix is negative on
  smooth bump-times-Legendre finite nullspaces up to square support
  `0.6928 < log 2`.  The sampled unconstrained matrices have one positive
  eigenvalue, while all three Laplace constraints give a stable negative
  maximum near `-0.8`.  A stronger sampled candidate is
  `P_21(g) <= |L(g,0)|^2 + |L(g,1/2)|^2 + |L(g,1)|^2`: with penalty
  coefficient `1`, the full-basis corrected maximum stays negative, and the
  sampled critical coefficient is about `0.707`--`0.736` at the boundary.
  This suggests a finite-rank kernel-certificate route.
  The Lean owner names `laneRLaplacePenalty` and
  `laneRConstrainedPrefixPenaltyCertificate`; its implication theorem reduces
  that stronger certificate to `laneRConstrainedPrefixSignTarget`, but does
  not produce the certificate.  It is not an operator-index theorem, a
  continuous-space sign proof, a tail sign, universal Lane R, or RH.  Do not
  import floating-point eigenvalues into Lean or replace the required
  analytic certificate with another magnitude-only adapter.
- One-sided penalty translation failure (VERDICT, 2026-08-19,
  `docs/proofs/1032`): the candidate
  `P_21 <= |L(0)|^2 + |L(1/2)|^2 + |L(1)|^2` is not compatible with the
  un-gauged owner.  `laplaceAt_translate` multiplies each node by `exp(s*a)`
  while the convolution-square prefix is translation invariant; a stable
  positive sampled direction appears at center `-1` (`+0.292...` at `K=48`)
  while the centered row is negative.  Do not revive this fixed one-sided
  penalty without an explicit translation gauge.
- Translation-invariant paired penalty (INTERFACE CLOSED / NUMERICAL SCREEN,
  2026-08-19, `docs/proofs/1033`):
  `laneRTranslationInvariantLaplacePenalty` uses
  `|L(0)|^2 + |L(-1/2)L(1/2)| + |L(-1)L(1)|`.
  `laneRTranslationInvariantLaplaceProduct_translate` and
  `laneRTranslationInvariantLaplacePenalty_translate` prove the algebraic
  translation invariance, and the paired penalty is zero on the three-node
  vanishing owner.  The finite sine screen remains negative through the
  prime-free boundary, but the continuous certificate producer is still open.
  The positive unrestricted sign-sector eigenvalues are diagnostics only;
  they are not a proof of the absolute-value inequality.
- Complex Lane R owner split (INTERFACE CLOSED, 2026-08-19,
  `docs/proofs/1034`): `C1XiCenterTwoGammaComplexSplit.lean` constructs the
  real and imaginary compact-log component tests and carries the exact split
  through Laplace values, triple vanishing, the real part of the Hermitian
  convolution square, the complete archimedean term, Gamma_R profile
  integrals, and the fixed `N = 21` prefix.  Do not infer component-level
  prime-free support from narrow support of the complex square: cross
  convolution cancellation can invalidate that implication.  A separate
  root-support hypothesis is required.  The owner/probe are axiom-clean with
  `[propext, Classical.choice, Quot.sound]`; no finite-prefix sign, global
  Lane R, or RH theorem is claimed.
- Conditional real-owner reduction (INTERFACE CLOSED, 2026-08-19,
  `docs/proofs/1035`): `C1XiCenterTwoGammaComplexSplitReduction.lean` defines
  real-valued component tests and reduces the complex `N = 21` prefix sign to
  a real-valued sign producer when both component squares are separately
  prime-free.  It also provides `primeFreeSquare_of_support_Icc` and the D3
  adapter that safely derive component prime-freeness from narrow support of
  the original root.  Keep `componentPrimeFreeSquare` explicit when the only
  available premise is `laneRPrimeFreeSquare g`: cross-convolution terms can
  cancel, so square support does not transfer componentwise.  This closes no
  sign producer, universal Lane R statement, or RH theorem; owner/probe axioms
  remain `[propext, Classical.choice, Quot.sound]`.
- Name ownership for the zero-sum lane (`open` is NOT transitive; every
  consumer imports and `open`s each namespace itself):
  `sourceNontrivialZeroSet`, `dyadicShellIndex`, `lt_two_pow_succ_dyadicShellIndex`
  → `Source/CC20YoshidaNearZeros.lean`; `spectralMultiplicityConstant`,
  `spectralHeightMultiplicity_geometric_bound` → `Dev/C1SpectralSummability.lean`;
  `xiMultiplicity`, `spectralHeightShell(_partition/_finite)` → `Dev/C1SpectralWeil.lean`.
- Split-brain `CompactLogTest` namespace: the STRUCTURE lives in
  `CCM25Concrete.CompactLogConvolution`, but `laplaceAt`, `laplaceAt_convolution`,
  and `laplaceAt_involution` live in `CC20YoshidaConvolution.CompactLogTest`.
  Open BOTH namespaces and use the `CompactLogTest.` prefix on the law names
  (bare law names do not resolve). Also: the elaborator normalizes
  neg-of-cast terms (`((-(x:ℝ)):ℂ)` becomes `-↑x`), so compound rw patterns
  like `-↑(-(1/2))` silently re-parse and miss; peel with `Complex.ofReal_neg`
  and `neg_neg` instead of hand-written show-casts.



- Healthy Yoshida finite-node interpolation (CLOSED 2026-08-17,
  `Dev/C1HealthyYoshidaInterpolation.lean`):
  `compactLogTestOfWindow` transports the existing linear Mellin
  interpolation through its exact Laplace/Mellin coordinate contract. At the
  fixed window `(1/2, 2)`, every off-line source zero has a healthy compact-log
  test with values `0` at `0, 1/2, 1` and `-1` at `rho, +i/2, -i/2`.
  `HealthyExpandedLaplaceRealizes` consequently supplies compact smoothness,
  triple vanishing, and nonzero detection at `rho`; it does not claim a sign
  for the Hermitian square. The endpoint
  `healthyCC20YoshidaDetectorExists_of_healthyExpandedLaplaceRealizes_and_spectral_neg`
  reduces healthy detector existence exactly to strict negativity of
  `spectralWeilValue g.convolutionSquare` for those fully constructed roots.
  The companion capstone combines that local negative condition with the
  separately guarded global nonnegativity premise to obtain `SourceRH`.
  Owner-plus-probe WSL2 build (3606 jobs) is axiom-clean with
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or project axiom.
  This does not prove either strict local negativity or global spectral
  nonnegativity, and RH is NOT claimed.

- Healthy Yoshida minimal-node and prime-free guard (2026-08-17): the healthy
  `YoshidaDetector` consumes exactly the three values at `0`, `1/2`, `1` and
  nonzero detection at `rho`. The legacy `plus/minus I/2` targets belong only
  to the rejected normalized additive-doubling owner; do not require or use
  them when constructing a healthy positive direction. The axiom-clean module
  `Dev/C1HealthyYoshidaMinimalInterpolation.lean` realizes those four nodes in
  the `(3/4, 5/4)` positive window, where its Hermitian square has support
  strictly inside `(-log 2, log 2)`. Thus
  `finitePrimeSum_eq_zero_of_support_subset_open_log_two` removes every
  visible prime-power term, and triple vanishing removes the pole term:
  `0 < weilLocalSum (starConvolution g)` is equivalent to
  `0 < archimedeanTerm g.convolutionSquare`. This is a reduction of the local
  sign construction, not an archimedean positivity theorem, detector
  existence theorem, spectral sign producer, or RH proof.

- Healthy narrow plateau archimedean positivity (CLOSED 2026-08-17,
  `Dev/C1HealthyNarrowPlateau.lean`): `primeFreePlateau` is the same-owner
  `wideTest` at width `1 / 3`. Its convolution square has support strictly
  inside `(-log 2, log 2)`, square mass in `[3/5, 2/3]`, and the explicit
  archimedean integral estimate is at most `(257 / 270) * bumpA`, while the
  leading term is greater than `(29 / 30) * bumpA`. Therefore
  `primeFreePlateau_archimedeanTerm_pos` proves strict positivity of the
  ordinary `archimedeanTerm` for this concrete witness. The owner-plus-probe
  WSL2 build (3496 jobs) reports only `[propext, Classical.choice,
  Quot.sound]`; no `sorryAx` or project axiom was introduced. This is a
  local archimedean positivity producer only: it does not construct a
  `YoshidaDetector`, prove global spectral nonnegativity, close the finite-
  vanishing criterion, or prove RH.

- Narrow plateau analysis uses the root-level Mathlib declarations
  `integral_inv` and `integral_one_div` from
  `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`; the cached WSL2
  environment does not expose the attempted
  `intervalIntegral.integral_inv_of_pos` spelling. Keep the selected
  `SelectedWeilSquareOwner` throughout the estimate so the proof never mixes
  a directly constructed function with a different owner carrying its
  support and archimedean data.

- Lane R D3-root archimedean sign leaf (CLOSED 2026-08-18,
  `Dev/C1LaneRD3Root.lean` + `Dev/C1LaneRNarrowArch.lean`):
  `D3 = (d/dt)(d/dt + 1/2)(d/dt + 1)` gives exact Laplace vanishing at
  `0`, `1/2`, and `1`.  The explicit root
  `narrowArchRoot = tripleVanishingRoot (wideTest (R/4))`, with
  `R = exp(-4*(log(4*pi)+gamma+1))`, has square support in `(-R,R)`.
  The near/middle/tail integral split proves
  `narrowArchRoot_archimedeanTerm_nonpos`, and the prime-free readback then
  proves `narrowArchRoot_qw_nonneg`.  The owner and probe build axiom-clean
  with `[propext, Classical.choice, Quot.sound]`.  This is one non-strict
  concrete witness only: it is not universal Lane R, does not establish a
  strict Yoshida detector sign, and does not prove RH.  The `qw = -arch`
  bridge still requires the separate `(-log 2, log 2)` support theorem; a
  narrower support proof alone does not match that API.

- Lane R D3-root strict sign (CLOSED 2026-08-18,
  `Dev/C1LaneRStrictness.lean`): the base `wideTest` has a strictly positive
  real Laplace value at `s = 2`, so the exact D3 transform law proves
  `narrowArchRoot.test != 0`.  The exposed budget estimate
  `archimedeanTerm_le_narrow_budget`, together with the strict scalar budget
  `narrowArchRadius_budget_lt` and positive square mass, then proves
  `narrowArchRoot_archimedeanTerm_neg` and
  `narrowArchRoot_qw_pos`.  The owner-plus-probe WSL2 build (3619 jobs) is
  axiom-clean with `[propext, Classical.choice, Quot.sound]`.  This is a
  strict positive `qw` witness for Lane R only; it is not detector positivity,
  universal Lane R, or RH.  Keep the detector-side sign distinction explicit:
  prime-free detector data would require a positive archimedean term.
  The same module also proves the family theorems
  `tripleVanishingRoot_qw_nonneg_of_narrow_base` and
  `tripleVanishingRoot_qw_pos_of_narrow_base_of_laplaceAt_two_ne_zero` for
  every D3 root whose base support lies in `[-R/4,R/4]`; treat this as a
  universal D3/narrow subfamily only, not as Lane R coverage.

## 17. RH Axiom Guard (from 887 review, updated 2026-08-12)

Read `UnconditionalSkeleton.lean` before classifying its axioms. Two of them are
**RH-equivalent**, NOT "removable on a healthy carrier":
- `normalizedCoreCC20PropositionC1SourceCriterionRoot` (line 1564): its proposition is
  `<-> _root_.RiemannHypothesis` (lines 1555-1559).
- `normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreRoot` (line 5896): likewise
  `<-> RiemannHypothesis` (lines 5890-5894).
- `normalizedSelectedFinalRouteDetectorCriterionCoverageRoot` is the active root
  of `unconditional_rh_skeleton`; `CC20RouteRealization` proves its proposition
  equivalent to `SourceRH` under the existing detector theorem.

Discharging either **IS proving RH**; you cannot swap in a healthy-carrier datum and claim
the axiom is "removed". Do not list C1-sign or Yoshida polarity under "provable lane".
Full inventory + four-lane classification (R / A / B / C): `docs/proofs/887_rh_axiom_ledger.md`.
`#print axioms` hook for the skeleton output (when built): a module + `#print axioms` on
`rhDefinitionBridgeToMathlibFromTheorems`; expected output still lists the `...Root` axioms.
