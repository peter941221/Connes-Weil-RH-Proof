# 942 - Step-3 finite-S sign is CLOSED axiom-clean (canonical CompactLog/A3)

Date: 2026-08-10. Status: route-verdict update. RH NOT claimed.

## 1. Claim

On the canonical CompactLog/A3 carrier, the Step-3 finite-S sign (the nonempty
Weil / A3 positive state that feeds the C1 input) is CLOSED axiom-clean, i.e.
`#print axioms = [propext, Classical.choice, Quot.sound]`, 0 sorry:

  * `Dev/A3NonzeroCompactLogGateProbe.lean`
      - `detector_diagonal_re_nonneg (a c u)` :
        0 <= Re<a u, windowedBoundaryDetector nonzeroTest a c u> (the quadratic
        form is the real square `||fullBoundaryRootFactor u||^2` via the
        adjoint-norm square identity);
      - `detector_isPositive (a c)` : the windowed HS detector at the nonzero
        test is `IsPositive` (PSD as an operator);
      - `detector_re_inner_nonneg (a c u)` : operator-level PSD corollary.
  * `Dev/Wall1HealthyPositive.lean` :
      `healthy_strict_positive_diagonal` :
      exists u, 0 < Re(u, cc20GlobalConvolutionPositive nonzeroTest.test u).
  * `Dev/WeilC1NonEmptyProducer.lean` :
      `weilStateNonempty`, `concrete_c1_input_nonempty_exists`, and
      `concreteC1InputData` (the concrete nonempty C1/Weil input), all axiom-clean.

A spot-audit of these five declarations reports only mathlib foundations.
So the "finite-S sign is nonnegative / the C1 input is inhabited" step is closed.
The Gamma-argument route (docs/940/941, Dev/GammaArg*) is a redundant sibling: it
gives `Re[Gamma(1+i/2)^4]>=0` (finite-S arch sign) but is NOT needed for the
canonical finite gate.

## 2. What is NOT closed (the actual RH bottom)

Closing the finite-S sign does not reach RH. The two-sheeted exit stays:
the `SourceRH` bridge consumes `CC20PropositionC1InputData ... fullWeilPositivity`
via the RH-equivalent criterion `normalizedCoreCC20PropositionC1SourceCriterion`
(UnconditionalSkeleton). That criterion is the C1-`SourceRH` equivalence; proving
it on any concrete carrier is the actual RH result, not a Lean-assembly leaf.
The finite gate we close only supplies the nonempty producer. Hence:

  finite-S sign CLOSED  =>  C1 input NONEMPTY (axiom-clean)
  C1 input nonempty     =>  SourceRH ONLY via RH-equivalent criterion (stays open)

## 3. Route verdict

Final-S sign: CLOSED (canonical CompactLog/A3, axiom-clean).
Gamma-argument route (Dev/GammaArg*, docs/940/941): redundant sibling, already
committed; not needed for the canonical gate.
Remaining open (not a Lean-assembly leaf): the RH-equivalent source criterion.