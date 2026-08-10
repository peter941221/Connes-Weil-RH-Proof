# 946 — Task-2 verified seam: strict diagonal CLOSED, re-type seam assembled, RH wall precisely located

Date: 2026-08-10. Status: verification + decomposition note on the healthy CompactLog/HS re-type
front. RH NOT claimed. Builds below ran on the isolated ext4 mirror `cwr-lanb-archlift` (warm seed,
Windows sources).

## 1. What this corrects vs. earlier reads

Earlier (934) read the "strict diagonal / injection" step as OPEN. It is in fact CLOSED
axiom-clean now:

  * `Dev/Wall1GlobalConvNonzero.lean`
      - `cc20GlobalLogConvolution_ne_zero h hne`: a nonzero Schwartz kernel h gives a nonzero
        global log-convolution operator (Fourier-multiplier injectivity).
      - `cc20GlobalLogConvolution_strict h hne`: `∃ u, 0 < ‖cc20GlobalLogConvolution h u‖`.
      - `cc20GlobalConvolutionPositive_strict_diagonal h hne`: `∃ u, 0 < Re⟨u, (G h)†∘(G h) u⟩`.
  * `Dev/Wall1HealthyPositive.lean`: instantiates at the concrete nonzero test
    (`healthy_strict_positive_diagonal`). #print axioms = [propext, Classical.choice, Quot.sound],
    0 sorry (re-verified 3177/3179 jobs on the isolated mirror).

## 2. The re-type seam built (this session)

`Dev/Wall1StrictWeilInput.lean` packages the healthy strict positive Hilbert diagonal as a
`WeilPositivityInput.fullWeilPositivity : Sort 1` witness:

  `healthyFullWeilPositivity : Sort 1`   = {u // 0 < Re⟨u, cc20GlobalConvolutionPositive nonzeroTest.test u⟩}
  `healthyFullWeil_positivity_nonempty`   : Nonempty healthyFullWeilPositivity     (axiom-clean)
  `healthyWeilInput : WeilPositivityInput` with fullWeilPositivity := healthyFullWeilPositivity

`#print axioms healthyFullWeil_positivity_nonempty` = [propext, Classical.choice, Quot.sound], 0 sorry.
Full Dev-touched chain (CompactLogArchimedeanLift, CompactSCealBalance, A3NonzeroCompactLogGateProbe,
Wall1StrictWeilInput) builds together: 2 programs, 0 errors (3180-3182 jobs).

## 3. Assembly status vs 912

`CC24DoorBCarrierAssemblyProbe912` shows `CC20PropositionC1InputData` has four fields, three
of which are CLOSED axiom-clean for the CC20 triple:
  finiteSetIsTriple, finiteSetDisjointFromNontrivialZeros, tripleVanishingMatchesMellin
and `c1InputData_of_positivity_witness` assembles them from ANY provided `input.fullWeilPositivity`.
The healthy side now provides genuine strict positivity at the `Sort 1` witness level (946 §2).

## 4. The honest remaining wall (this is the RH-equivalent bottom, not a leaf)

Two genuinely-open route steps separate the healthy strict positivity from `unconditional RH`:
  (a) **re-type equality**: the healthy Hilbert-space witness `healthyFullWeilPositivity`
      (on `cc20GlobalLogCrossingL2`) is NOT automatically the skeleton's
      `CC20C1InputData.fullWeilPositivity`, whose semantic is the localized Weil quadratic
      functional ≥ 0 on the finite vanishing set. Bridging the crossing-space operator
      PSD to the Weil-functional statement is the re-type seam skeleton layer (936), OPEN.
  (b) **the RH-equivalent C1 discharge**: even with the re-typed witness, feeding it to the
      RH-equivalent `NormalizeKinCC20PropositionC1SourceCriterion` and applying the bridge
      `standard_source_rh_iff_mathlib` is a *real RH proof*, never a leaf. RH NOT claimed.

So routing/verify progress: strict diagonal CLOSED + re-type seam witness BUILT + full-chain
axiom-clean — but lane B arch/pole half and the RH discharge stay open.

RH NOT claimed.
