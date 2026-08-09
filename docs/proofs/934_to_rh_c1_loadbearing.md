# 934 - To RH: the exit is C1 fullWeilPositivity, and it is inhab(i)table on the CompactLog HS carrier

Date: 2026-08-10. Type: route-root strategy / new seam. No sorry, no claims of RH.

## 0. The RH exit is NOT Gate 3U.

Lean final RH exit = discharging EITHER of two RH-equivalent axioms in
UnconditionalSkeleton.lean:

- normalizedCoreCC20PropositionC1SourceCriterionRoot (must be inhabited for all
  CC20PropositionC1InputData inputs)  ~ line 1555; wired to _root_.RiemannHypothesis
  at lines 1536-1543 via standard_source_rh_iff_mathlib.
- normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreRoot  ~ line 5896.

AGENTS 6/13: discharging either of these IS proving RH. They cannot be classified
as "provable lane" out of reach, and no finite-patent / health-carrier swap alone
rights them.

## The exit object

Basic.lean:421-430:

    structure WeilPositivityInput where
      tripleVanishing : Prop
      fullWeilPositivity : Sort 1
    structure FiniteVanishingCriterionPackage where
      finiteSetAdmissible : Prop
      criterion : forall i, i.tripleVanishing -> i.fullWeilPositivity -> RH

So "to RH" reduces to producing i : WeilPositivityInput with
  i.tripleVanishing  (constructible) and  fullWeilPositivity : Sort 1  INHABITED
  by a proof of the real finite-S Weil positivity, then applying criterion.

## Why the healthy CompactLog HS carrier is the right home for it
The broken additive concrete model cannot hold it: not_normalizedCC20MellinConvolutionLaw
(CC20YoshidaConstruction:2727) proves 2 = 1 on it. On the healthy carrier, built and
axiom-clean at HEAD (fresh-cache mirror):
- MellinProductCarrier.mellinConvolutionProductLaw  - Mellin product law (Build green).
- CompactRootHalfLinePair and CompactLogConvolution - genuine Schwartz convolution.
- A3GeneralizedCompactLogDetector.detector_isPositive_any / detector_re_inner_nonneg_any:
  F dagger F is PSD for EVERY compact-log test (windowedBoundaryDetector g a c), with
  Re<u,det u> >= 0 on cc20GlobalLogCrossingL2.  This IS the positivity seed that can
  inhabit fullWeilPositivity (869: the Gamma-phase/Stirling route is NON-canonical in
  the CompactLog carrier; the sign is a theorem there).

## What the honest "打穿" is
Not a Gale-phase. It is an assembly + re-type seam plus one real positivity theorem:
1. Re-type / define a concrete WeilPositivityInput on the CompactLog HS carrier whose
   fullWeilPositivity is the Prop "the localized Weil quadratic form is >= 0
   (finite vanishing set), witnessed by the A3 PSD"/the well-selected normal form."
2. Inhabit that Prop from detector_isPositive_any (an actual proof, not an axiom).
3. Feed it to FiniteVanishingCriterion / the C1 theorem (cc20_proposition_c1_...)
   and close through the RH bridge.

Status: foundation bricks verified green (2704/3154/3153 jobs, axiom-clean).
This memo records the pivot; the re-type + inhabit blck is the active load-bearing task.
RH NOT claimed.