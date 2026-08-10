# 936 — To-RH re-type seam: concrete source-core onto the healthy CompactLog HS carrier

Date: 2026-08-10. Status: seam captured; architectural re-type OPEN.
RH NOT claimed. This file pinpoints exactly what a re-type must do and the
verified artifacts it can rely on, so the next session can attack the skeleton
layer without re-deriving the walls.

## 1. Goal (what "re-type" means)
The RH exit discharges a C1 criterion / Weil positivity on a concrete source
model. The concrete model is BROKEN (below); the healthy model lives on the
CompactLog HS carrier. Re-type = route the C1 input through that healthy
carrier so the strict positive diagonal (already proven) is exactly what
`fullWeilPositivity` reads.

## 2. The collected (proven, axiom-clean) healthy content to pull from
- `ConnesWeilRH/Dev/Wall1GlobalConvNonzero.lean` (commits 25e0864, 3372aa4):
  * `cc20GlobalLogConvolution_ne_zero h hne` : `G h != 0` (nonzero kernel,
    nonzero global log-convolution operator on the log carrier).
  * `cc20GlobalLogConvolution_strict h hne` : `exists u, 0 < ||G h u||`.
  * `cc20GlobalConvolutionPositive_strict_diagonal h hne` :
        `exists u, 0 < real <u, (G h)† ∘ (G h) u>` (strict inner diagonal of
        the PSD square operator).
- `ConnesWeilRH/Dev/Wall1HealthyPositive.lean` (commit bdb730c):
  * `healthy_strict_positive_diagonal` : the above with `h = nonzeroTest.test`
    (the concrete nonzero A3 Fourier-core bump). The non-empty producer is
    VERIFIED on the healthy log carrier.
- `ConnesWeilRH/Source/CC20Concrete/GlobalLogConvolution.lean` and
  `GlobalConvolutionCrossing.lean`:
  * `cc20GlobalConvolutionPositive h = (cc20GlobalLogConvolution h)† ∘
    cc20GlobalLogConvolution h` and the inner-to-norm-square identity
    `Re〈u, Pos h u〉 = ‖G h u‖^2` (the nonnegative half of the diagonal).
- `ConnesWeilRH/Dev/MellinProductCarrier.lean` (commit 9b74c64):
  `mellinConvolutionProductLaw`, `mellin(f⋆g) = mellin f · mellin g` on the
  healthy CompactLog carrier. This is the multiplicative-Mellin law that the
  broken additive model violates.
- `CompactRootHalfLinePair` (build green): true Schwartz convolution, and
  `globalConvolutionPositive_eq_convolutionSquare`.

## 3. The broken concrete model (must be replaced / re-routed)
- `Source/AnalyticCoreBase.lean` ~line 3121: the concrete algebra
  `concreteTestAlgebra : SourceTestAlgebra` with
    `Test := ConcreteTest`  (= `TestFunction`, ~line 3094)
    `convolutionStar := fun f g => f + g`      (ADDITIVE; not Mellin)
    `involution := fun f => Fourier f`
    `convolutionSquare := fun g => g + g`
  This violates Mellin: `M(f + g) = M f + M g` is additive with no product law,
  so the `qwLambda`-style (multiplicative) identities break.  It is not
  Mellin/multiplicative on the healthy carrier.
- `SourceWeilFormData` / `weilForm` concrete evaluation: the finite-prime
  `exactSupport` forces `sourceFinitePrimeTerm` to 0, yet evaluation reads a
  positive `Λ(2)·|v|/pointValue` contribution; the concrete source data model
  is internally inconsistent (see MEMORY 2026-08-05 and the closure-audit
  notes in `docs/proofs/`).

## 4. Why a naive "just switch Test" does not work
A `SourceTestAlgebra` requires a `LegacyTestEquiv Test` — a full bijection with
`TestFunction`. `CompactLogTest.test` is injective (the test determines the
`CompactLogTest`), but NOT surjective onto all of `TestFunction` (only those
Schwartz maps with compact support). So `Test := CompactLogTest` cannot give a
`LegacyTestEquiv` today. Re-type must either:
  (a) widen the healthy test type to a superset of `TestFunction` while keeping
      the structural laws, or
  (b) change `TestFunction`'s convolution law (replace the additive unfolding)
      and re-export the CompactLog crossing product as the canonical
      `convolutionStar`, or
  (c) re-define the concrete base layer's `weilForm` / `exactSupport` /
      finite-prime fields so they are consistent on the healthy carrier
      instead of forced to 0.
Then rebuild `Source.AnalyticCore` and the skeleton reference in
`Dev/UnconditionalSkeleton.lean` against it.


## 6. DONE (renumbered: was step-1) — Step 1 (2026-08-10): healthy SourceTestAlgebra on TestFunction, axiom-clean
- `Dev/HealthySourceMellinAlgebra.lean` builds a `SourceTestAlgebra` on `Test = TestFunction`
  (= `ConcreteTest` = `SchwartzMap ℝ ℂ`) with the SAME identity `LegacyTestEquiv` as the broken
  `concreteTestAlgebra`, but with
    `convolutionStar f g = SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) f g`
    `involution := fun f => 𝓕 f`
    `convolutionSquare := fun g => convolutionStar g g`
  This fixes the additive `f + g` defect on the *same* carrier — so it drops into the skeleton
  consumer without a type change, and sidesteps the `CompactLogTest`-bijection wall (A2 probe:
  `decode : TestFunction -> CompactLogTest` would force compact support on all Schwartz maps).
- Axiom-clean: WSL build green (2936 jobs); `#print axioms` for
  `healthyMellinSourceTestAlgebra` / `healthyFourierConvolutionMul` / `healthyLegacyTestEquiv` /
  `healthyConvolutionStar` = `[propext, Classical.choice, Quot.sound]`, 0 sorry, 0 new project axiom.
- `healthyFourierConvolutionMul` records the multiplicative-Mellin Fourier law:
  `𝓕 (f *̃ g x) = pairing (mul) (𝓕 f) (𝓕 g)` via `SchwartzMap.fourier_convolution`.
- This replaces the concrete algebra's broken ADDITIVE product with the Mellin one. Next: re-point
  `qwLambda`/`fullWeilPositivity` consumers onto `healthyMellinSourceTestAlgebra`.



## 7. DONE — concrete non-empty C1 / Weil input (2026-08-10)
- `Dev/WeilC1NonEmptyProducer.lean` proves the "non-empty C1 input (Weil state)" brick needed by
  the skeleton `normalizedCoreCC20PropositionC1SourceCriterionRoot` (per-input
  `CC20PropositionC1InputData ... input` with `input.fullWeilPositivity`).  It builds a concrete
  `WeilPositivityInput` on the healthy CompactLog HS carrier whose `fullWeilPositivity` Sort is
  `WeilPositiveState` (= strictly positive crossing vectors of `cc20GlobalConvolutionPositive`
  `nonzeroTest.test`), and proves `Nonempty ...` from `healthy_strict_positive_diagonal`.
- Axiom-clean: WSL build green (3180 jobs); `#print axioms` = [propext, Classical.choice,
  Quot.sound], 0 sorry.  This supplies the non-empty producer; the finite-S sign discharge of every
  such input (step 3 / fullWeilPositivity re-point + RH exit) stays open.  RH not claimed.

## 5. Next steps (ordered, all buildable against the green base above)
1. Define the healthy `SourceTestAlgebra` whose convolution is the CompactLog
   Mellin product (`CompactRootHalfLinePair`), proving `convolutionSquare_eq`.
2. Re-point the concrete core identity (`legacy` ad apper) so `qwLambda` reads
   the multiplicative `mellinConvolutionProductLaw` (Item 2).
3. Re-point the concrete `fullWeilPositivity` witness to the strict positive
   diagonal of `Wall1HealthyPositive`.
4. Rebuild + axiom audit the skeleton consumer.



## 8. DONE — concrete C1 input DATA at the standard bridge (2026-08-10, step-1 of exit)
- `Dev/WeilC1NonEmptyProducer.lean` now also builds a REAL `Source.CC20PropositionC1InputData`
  `RHDefinitionBridge.standard cc20TripleFiniteVanishingSet concreteWeilInput` and its route
  refinement `concreteC1RouteInputData` (RouteInput variant).
- Fields: finiteSetIsTriple (`cc20_triple_finite_set_is_triple`), finiteSetDisjointFromNontrivialZeros
  (`cc20_triple_disjoint_from_standard_source_nontrivial_zeros`, the zeta-half nonvanishing row,
  ZetaHalfNonvanishing.lean), tripleVanishing (`concreteWeilInput_triple`: True), and
  fullWeilPositivity (`Classical.choice weilStateNonempty` = a `WellPositiveState` witness).
- WSL build green (3593 jobs); #print axioms for both = [propext, Classical.choice, Quot.sound],
  0 sorry, 0 new project axiom.  This gives the skeleton's exit-1 a concrete nonempty producer.
  RH not claimed: this fills the C1 input data, not the finite-S sign discharge.

## 9. OPEN — step 2 (healthy-Mellin re-type + skeleton cold build) and step 3 (finite-S sign)
- step-2: re-point the skeleton source consumer (`convolutionStar`/`qw`, and the `WellFormData` ON
  the healthy Mellin algebra `healthyMellinSourceTestAlgebra`) to the strict positive (the
  `WellPositiveState` non-diagonal is already wired as `concreteWeilInput.fullWeilPositivity`).  The
  remaining large item = build `SourceWellFormData healthyMellinSourceTestAlgebra` (incl. the
  per-common finite-prime support on the Mellin carrier) and swap `concreteTestAlgebra` out, then a
  full `UnconditionalSkeleton` cold build + `#print axioms`.
- step-3: the finite-S Weil sign discharge of every such input (the only open analytic bottom).

RH is NOT claimed. This seam fixes the exact re-type boundary; the re-type is
the next open, large, attackable target.

## 10. DONE (2026-08-10): healthy-carrier `SourceWeilFormData` brick (step-2 first leaf)
- `Dev/WellFormHealthyRepoint.lean` now proves the healthy-Mellin per-common finite-prime
  support and lifts to a real, axiom-clean `SourceWeilFormData healthyMellinSourceTestAlgebra`
  (`healthyWeilForm`), on the SAME `TestFunction` carrier with `{2}` exact support, using
  `commonBump`/`forward_mem`/`term_two_pos` transferred word-for-word from
  `ConcreteP1SupportProbe` via `healthyEval_sourceFinitePrimeTerm_eq_concrete` (both carriers
  identity-encode `valueAt := ||encode F x||`, so `sourceFinitePrimeTerm` is algebra-invariant).
- WSL build green (2949 jobs); `#print axioms healthyWeilForm = [propext, Classical.choice, Quot.sound]`, 0 sorry, 0 new project axiom.
- This is the healthy substitute for the L137 `normalizedCoreSourceWeilFormDataRoot` axiom ON the
  healthy Mellin algebra (the concrete one was inconsistent); it does NOT yet route the skeleton
  consumer, and the finite-S Weil sign stays open.
## 11. Verified exit-audit baseline (2026-08-10): axiom set is exactly Step 3's gap
- `lake env lean` audit at the current mirror (HEAD, no skeleton source change):
  * healthyWeilForm / healthyPerCommonSupport / concreteC1InputData /
    normalizedCoreSourceWeilFormDataFromTheorems : axioms = [propext, Classical.choice, Quot.sound], 0 sorry.
  * `UnconditionalSkeleton` focused build green (3500 jobs).
- `#print axioms normalizedCoreCC20PropositionC1SourceCriterionRoot` returns AX SET =
  [propext, Classical.choice, Quot.sound, Dev.UnconditionalSkeleton.normalizedCoreCC20...Root]:
  i.e. the RH exit axiom self-depends exactly on itself.  That self-dependency is the
  finite-S Weil sign (Step 3) - the single open object that still blocks RH.  Nothing in the
  current C1/Weil data layer (Step 1 + healthy Weil form) touches it.