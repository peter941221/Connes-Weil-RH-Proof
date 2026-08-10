# 960 - C1-RH criterion: honest current status (input data done; criterion open)

Date: 2026-08-10.  Status: source audit (definitions read; not a new proof).  RH not claimed.
See docs/955 (C1 = RH-equivalent discharge), AGENTS tags on the two-lane verdict.

## What exists

- C1 input DATA is already instantiated, axiom-clean: Dev/WeilC1NonEmptyProducer
  gives concreteWeilInput (tripleVanishing=True, fullWeilPositivity = the inhabited
  healthy HS `Weil-positive diagonal`), plus concreteC1InputData / concreteC1RouteInputData
  on RHDefinitionBridge.standard (Necessary.FiniteSetDisjointousnontrivialZeros from
  cc20_triple_disjoint..., fullWeilPositive from healthy_strict_positive_diagonal).

## What the C1 exit actually needs

The route to `_root_.RiemannHypothesis` runs through
`cc20_proposition_c1_from_yoshida_detector` (CC20YoshidaCriterion.lean:213):

    CC20YoshidaDetectorExists C F  ->  CC20FiniteVanishingWeilCriterion C F
        ->  RHDefinitionBridge.standard.SourceRH

where CC20FiniteVanishingWeilCriterion :=
    forall g, compactSupportSmooth g -> vanishesOn(C F) g -> weilLocalSum(starConvolution g) <= 0.

## The honest status: the criterion is NOT dischargeable on the concrete carrier

- On the normalized concrete test `normalizedCC20TestSpace` the criterion is
  REFUTED, axiom-clean: CC20YoshidaConstruction.lean:2474 has
  `not_normalizedCC20FiniteVanishingWeilCriterion : `notCC20FiniteVanishingWeilCriterion
    normalizedCC20TestSpace cc20TripleFiniteVanishingSet` (built from the
  `concreteYoshidaMomentData_* ` counterexample chain at :2283-2474).
- So the C1 lane cannot run on `normalizedCC20`.  Whether that negation is a real
  number-theoretic fact or an artifact of the known additive-normalization bug
  (`convolution-square` fails the multiplicative Mellin law there) is NOT resolved:
  the counterexample uses `normalizedCC20` (the model already flagged in docs/850).
- The live candidate is the healthy CompactLog HS carrier; there `fullWeilPositivity`
  is inhabited (WeilC1NonEmptyProducer) but `CC20FiniteVanishingWeilCriterion` is NOT
  yet proven there.

## Verdict

Switching to the C1 lane does NOT give a cheap RH discharge.  It is the same
qualitative wall as Wall-A 1.4: the genuine finite-S / Weil-positivity criterion must
be established on the healthy CompactLog HS carrier (a real archimedean/HS analytic
step), and the normalized concrete carrier is a proven dead end for it.  The
difference is only the carrier, not the effort.  RH NOT claimed.

## Recommendation

- Do NOT spend a heat build proving C1 against the normalized concrete model (it is
  refuted).  The lever is the healthy HS carrier version of the criterion plus the
  detector, i.e. the same re-framing the Wall-A arch already points at.

## Upgrade (same date): the `normalizedCC20` "refutation" is an additive-model artifact

Reading the source of the negation chain (CC20YoshidaConstruction.lean) more
carefully, the counterexample is CONDITIONAL and lives inside the broken
additive model:

- `concreteYoshidaMomentData_weilLocalSum_positive` assumes
  `ConcreteYoshidaMomentData rho g` (an off-line nontrivial-zero datum) with
  Mellin values set to -1 at +/-I/2, and routes the sign through the additive
  normalized `polePairing_eq_mellin_convolutionSquare_half_sum`.
- `concreteYoshidaMomentData_halfDensityPoleSum_negative` then reads the
  double convolution-square at +/-I/2 -> negative, using TWO applications of the
  additive `convolutionSquare` (g convolved twice).

So `not_normalizedCC20FiniteVanishingWeilCriterion` is NOT a genuine
falsification of the C1 criterion.  It lives in the same additive normalized
model where the known `M(conv^2)=2*M(g)` linearization bug (docs/850, AGENTS
lines) forces the +/-I/2 sign to be negative when it is flat/free.  The proper
multiplicative+HS CompactLog carrier (where the sign is closed, docs/942, 850)
is exactly the carrier on which this artifact disappears.

Therefore the C1 lane is OPEN on the healthy CompactLog HS carrier (the
criterion is neither proved nor truly refuted).  The `not_normalized...`
negation is a *model artifact*, not a mathematical falsification.  This
re-aligns docs/960's earlier "REFUTED" phrasing: the honest status is "open on
the healthy carrier; additive carrier's negation is an artifact."
