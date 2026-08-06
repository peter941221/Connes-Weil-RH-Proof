# Next-step design consensus: parallel source model (Route-A re-type)

Date: 2026-08-06 · Status: **design / blocked-by-two-new-walls** · Owner lane:
Route-A re-type (parallel source model)

## Why this exists

The closure audit (`docs/proofs/closure-audit-skeleton-source-consistency.md`)
found Route-A blocks because `SourceWeilFormData` is empty on the concrete
algebra and `convolutionStar` fails the Mellin law.  The agreed fix direction is
a **parallel source model** that re-uses the already-proved CC20 Yoshida
detector ladder instead of re-typing the broken skeleton core.

## Decisive facts established this session

1. **Route-1 off-line half is already axiom-clean.** `normalizedCC20YoshidaDetectorExists`
   (`CC20YoshidaConstruction.lean:2717`) is a theorem (non-axiom), grounded in
   `weighted_mellin_kernel_log_line_independence` (:942).  It does **not** depend
   on the empty `SourceWeilFormData`.  So the "off-line contradiction" half of
   the sign lane is already dead.

2. **断点2 is not a bug, it is a proven non-law.** `NormalizedCC20MellinConvolutionLaw`
   (`CC20ConcreteTestSpace.lean:167`) requires `mellin(f✳g)=mellin(f)·mellin(g)`.
   The concrete `convolutionStar = f+g` (pointwise) and
   `normalizedCC20TestSpace_is_additive_pole_model` (:175) make the law provably
   false (`not_normalizedCC20MellinConvolutionLaw` :2727).  A separate, real
   convolution carrier is required for the multiply semantics.

3. **CompactLog carrier traps (new, not previously noted):** the obvious
   "wrap `CompactLogTest` as a `SourceTestAlgebra`" route hits two fresh walls:
   - `LegacyTestEquiv` needs `decode : TestFunction → Test` total; `CompactLogTest`
     is a compact-support subtype of `TestFunction`, so a total decode is
     structurally impossible (same wall as the A2/Seam-B rejection).
   - `CompactLogConvolution.lean` contains **no Mellin identities**; the
     Mellin-product relation for log-additive convolution is not yet in the
     library.

## Recommended configuration (lowest blast radius, no LegacyTestEquiv wall)

Do **not** wrap `CompactLogTest` as a full `SourceTestAlgebra`.  Instead build a
**standalone carrier** that:

- carries the (non-surjective) encode `Test → TestFunction` only — no
  `LegacyTestEquiv`, so no decode wall;
- supplies a **true Mellin convolution** (log-coordinate additive convolution
  whose Mellin product is `mellin(f·g)`), to be proved as new identities;
- reuses `CC20YoshidaDetectorExists` / `CC20PropositionC1` for the sign lane.

## Open sub-decisions

1. Whether to prove the Mellin-product identity for CompactLog/Log convolutions
   from scratch (new analytic work) or to vendor an existing Mellin-law proof.
2. Whether the parallel model still feeds the `SourceWeilFormData` interface (a
   type) or is a free-standing model wired to a narrower exit.

## Judgment

This is a **new analytic construction**, not a Lean reassembly: the empty
`SourceWeilFormData` is a model bug needing a genuinely-convolution-equipped
carrier, and the Mellin code is not yet present in the CompactLog world.

## Decisive addendum (2026-08-06): current additive model cannot bypass 断点2

"审查当前模型能否绕开" was tried and the answer is **no**, on two confirmed,
evidence-closed grounds:

1. **The sign lane needs `CC20FiniteVanishingWeilCriterion C F` as `hcriterion`**
   (`CC20PropositionC1.cc20_proposition_c1_from_yoshida_detector`,
   `CC20YoshidaCriterion.lean:221`).
2. **That criterion is provably FALSE on the concrete additive model**:
   `not_normalizedCC20FiniteVanishingWeilCriterion`
   (`CC20YoshidaConstruction.lean:2475`), via the counterexample
   `exists_normalizedCC20_halfDensityPoleSum_counterexample` — a test `g`
   vanishing at all three critical points whose half-density pole-pairing
   (`polePairing (convolutionSquare g)`) is negative.

So both roads through `cc20_proposition_c1_*` (Route-1 sign lane) are blocked:
the detector ladder is proved (`:2717`) but the finite-vanishing Weil criterion
itself is false here.  A **new convolution carrier** (with a real Mellin product)
is forced; there is no in-model reassembly that yields it.  This closes the
"bypass in current model" option.

## Corrected handoff

- RH status: Route-A blocked (model-level); Route-1 off-line half dead
  (detector) but online sign needs a carrier with a true Mellin product.
- Next real step (any chosen direction): construct a **new Mellin-product
  convolution** (new analytic identity) on a carrier that does not require the
  total `LegacyTestEquiv.decode`.  No current-model reassembly unblocks it.