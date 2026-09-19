# 1697 — map 047: the whole program compresses to the committed two-premise exit; premise 1 (detector transport on the genuine carrier) priced into three concrete sub-obligations; premise 2 is the RH core with no carrier (map 046 confirmed); the skeleton's only axiom socket rides a toy model and is not load-bearing; laws F67/F68

Date: 2026-09-19.

Status: audit record (paper level; no new Lean brick — the exit spine is
already committed and machine-checked).  All objects pinned file:line.

## 1. The committed two-premise exit

`Dev/C1CenterTwoRHExit.lean:67-79`
(`healthy_spectral_nonneg_sourceRH_of_yoshida_detector`, composing
`:51-61` + the committed bridge
`healthyCriterionState_iff_all_vanishing_spectral_nonnegative`,
`C1CenterTwoCriterionBridge.lean:36`) states, entirely machine-checked:

```text
  SourceRH  ⟸  [premise 1]  CC20YoshidaDetectorExists healthyCC20TestSpace
                              cc20TripleFiniteVanishingSet
              [premise 2]  ∀ g triple-vanishing,
                             0 ≤ spectralWeilValue g.convolutionSquare
```

The exit module's own header (lines 20-37) says it verbatim: "the complete
distance to `SourceRH` on the healthy compact-log owner as exactly two
explicit premises … Discharging premise `2` is RH-equivalent; it must never
be replaced by a carrier datum swap."

Context that makes this the whole program: `qw = spectralWeilValue ∘
convolutionSquare` is the committed center-`2` Gate-2 readback
(`qw_eq_spectralWeilValue_centerTwo`, `C1CenterTwoCriterionBridge.lean:28`);
`healthyCC20TestSpace` is the GENUINE carrier — real convolution square,
`weilLocalSum = −qw` (`C1HealthyTestSpace.lean:44-88`); the detector's sign
field on this carrier reads, on the prime-free `log 2 / 2` window class,
exactly as strict positivity of the explicit archimedean term
(`weilSquareSumPositive_iff_archimedeanTerm_pos_of_vanishesOn_cc20Triple`,
`C1HealthyYoshidaDetector.lean:204-216`) — because on that class `qw =
−archimedeanTerm` (`:145-159`).

## 2. Premise 1 (detector transport) — priced into three sub-obligations

`CC20YoshidaDetectorExists C F` unpacks (`CC20YoshidaCriterion.lean:35-41`)
to: for every off-critical source zero ρ, a test g with
{compactSupportSmooth, vanishing at F = {0, 1/2, 1}, `ĝ(ρ) ≠ 0`,
`qw(g) < 0` conditional on ρ off-line}.  The healthy packing is committed
(`nonempty_yoshidaDetector_of_healthyDetectorData :220`,
`healthyCC20YoshidaDetectorExists_of_healthyDetectorData :235`).  What is
OPEN is the construction itself, in three named pieces:

1. **Interpolation**: a genuine `CompactLogTest` with prescribed bilateral
   Laplace vanishings at {0, 1/2, 1} and nonvanishing at ρ.  In the log
   coordinate, Mellin vanishing at s is the moment condition
   `∫ g(x) x^{−s} dx = 0`; the differential-operator orbit
   `(x d/dx − c)` multiplies the Mellin transform by an affine factor of s,
   so finite interpolation is an explicit compactly-supported
   construction (classical; the tree's Mellin machinery is committed).
2. **Domination**: the test must concentrate so that, GIVEN ρ off-line,
   the ρ-pair of spectral terms dominates the rest of the explicit formula
   and forces `qw(g) < 0`.  This is the Weil/Yoshida negative-test
   argument (classical); its honest content is the phase asymmetry of
   `spectralTerm` off the line — `spectralTerm F ρ = mult(ρ)·F̂(ρ − 1/2)`
   (`C1SpectralWeil.lean:112-115`) is a modulus square only ON the line.
3. **Window confinement (optional but powerful)**: confining supp g to
   `[−log 2/2, log 2/2]` makes the sign field read through the EXPLICIT
   archimedean term alone (`:204-216`), turning the domination question
   into a concrete integral-inequality construction on a compact window —
   rig-able with synthetic off-line ρ (validate the machinery numerically
   by computing `qw(g)` from the explicit formula with a synthetic zero).

The Toy contrast: the unconditional "detector existence" committed in the
normalized route lives on `normalizedCC20TestSpace`, whose
`starConvolution` is ADDITIVE (`legacy.encode (starConvolution g) =
encode g + encode g`, `CC20ConcreteTestSpace.lean:174-183`, with the
`NormalizedCC20MellinConvolutionLaw` contract explicitly parked so toy
carriers "can be rejected") — there the sign field is arrangeable because
`weilLocalSum = −polePairing` has no analytic content.  That theorem is a
model artefact, not premise 1.

## 3. Premise 2 (the spectral sign) — the RH core, carrier-free

Premise 2 is `healthyCriterionState {0,1/2,1}` in spectral form.  Map 046
(1695/1696) already established that no single positive trace of the
committed vocabulary can carry this sign, and 1695's readback socket was
precisely a "carrier datum swap" attempt — the exit header's warning,
instantiated and killed.  RH ⟹ premise 2 (Weil positivity on RH), and
premise 2 + premise 1 ⟹ RH, so premise 2 is RH-equivalent in the presence
of premise 1: **this premise is where genuine analytic progress IS
progress on RH**.  The only committed lever is the spectral side itself:
`spectralWeilValue = Re Σ_ρ mult(ρ) F̂(ρ − 1/2)`, on which the line/off-line
dichotomy (modulus squares on the line, phases off it) is the sole
structural input.

## 4. The skeleton's axiom socket is not load-bearing

`UnconditionalSkeleton.lean:5885`
(`normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreRoot`) asserts
the pole-pairing realizer ON THE TOY MODEL
(`NormalizedRouteBackedSourceZeroYoshidaDetectorPolePairingNonnegativeRealizer`,
`CC20RouteRealization.lean:1709`, quantified over `YoshidaDetector
normalizedCC20TestSpace …`).  Since that carrier's operations are additive
(§2), the axiom is a stub: it can be discharged trivially inside the toy
world and equally fails to transport.  The genuine exit does not consume
it — `C1CenterTwoRHExit` runs on `healthyCC20TestSpace` and asks for the
two real premises.  Map bookkeeping: the "single axiom socket" of the
skeleton is therefore NOT the remaining RH object; the remaining objects
are premises 1 and 2.

## 5. Laws

- **F67 (no carrier datum swap)**: a criterion premise must never be
  discharged by an object whose committed positivity engine forces the
  premise's sign unconditionally — such a socket is vacuous (1695/1696 is
  the instance; `C1CenterTwoRHExit.lean:36-37` is the law's positive
  form).  Before consuming any "premise producer", check whether it
  implies the premise at tests where the premise's negation is
  consistent.
- **F68 (model fidelity)**: an axiom/realizer riding a test space that
  violates the Mellin convolution law (`NormalizedCC20MellinConvolutionLaw`)
  is a model stub, not RH content; RH ledger objects must live on the
  genuine convolution carrier (`healthyCC20TestSpace`).

## 6. Next

1. **1698 (premise 1, paper)**: write the Weil/Yoshida negative-test
   construction on the log-coordinate carrier — interpolation piece first
   (explicit `CompactLogTest` with Mellin zeros at {0, 1/2, 1}, nonzero at
   ρ), then the domination lemma, then window confinement.
2. **1699 (premise 1, rig)**: validate the construction numerically at a
   synthetic off-line ρ (compute `qw(g)` from the explicit formula with a
   synthetic zero inserted; the domination should read negative).
3. Premise 2 stays the RH core: any candidate carrier must first pass the
   F67 sign check at detector tests.
