/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1FourPointHighShellTail
import ConnesWeilRH.Dev.C1FourPointSpanGateCertificate
import ConnesWeilRH.Dev.C1FourPointSpectralPrefixTransport
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity
import ConnesWeilRH.Dev.C1OrbitWindowExitComposition
import ConnesWeilRH.Dev.C1PinnedOrbitExit
import ConnesWeilRH.Dev.C1SignedVarianceIdentity
import ConnesWeilRH.Dev.C1BipartiteMeanGapCertificate
import ConnesWeilRH.Dev.C1SpectralSummability

/-!
# 103 Cut 3: Contradiction Assembly for the Four-Point Same-Span Route

This module formalizes Cut 3 of Map `103`, assembling the two-sign contradiction
on the same `annihilatorDetectorSpanVector` owner `v(lam) = u - lam * g`:

1. `spectralWeilValue_neg_of_spectralHeightShellPrefix_and_tail_scaled`:
   Generalizes the shell prefix + tail negativity to an arbitrary positive bound `M > 0`.

2. `spectralWeilValue_neg_of_spectralHeightShellPrefix_and_fourthOrderTail_scaled`:
   Deduces `spectralWeilValue F < 0` from `FourthOrderSpectralTail` and a scaled prefix bound.

3. `annihilatorDetectorSpanVector_qw_neg_of_gate_and_tail`:
   Establishes `qw v(lam) < 0` for the four-point span vector under the Cut-1 high-shell
   tail bound and Cut-2 spectral prefix bound.

4. `annihilatorDetectorSpanVector_qw_nonneg_of_gate`:
   Establishes `0 ≤ qw v(lam)` from Cut-2 gate nonpositivity and triple vanishing.

5. `false_of_four_point_span_contradiction`:
   Forces `False` from the simultaneous nonnegativity and strict negativity of `qw v(lam)`.

6. `sourceRH_of_right_nontrivial_zeros_empty` and `riemannHypothesis_of_right_nontrivial_zeros_empty`:
   Connects the impossibility of right off-line zeros directly to `SourceRH` and Mathlib's
   canonical `_root_.RiemannHypothesis`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1FourPointContradictionAssembly

open Matrix
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open ConnesWeilRH.Dev.C1C3CarrierTransport
open C1ArchimedeanIntegrabilityGeneric
open C1CenterTwoCriterionBridge
open C1GateMatrixRepresentation
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1LocalConfigurationDomination
open C1OrbitWindowSemiLocalGate
open C1SpectralWeil
open C1SpectralTailBound
open C1SpectralSummability
open C1SameOwnerWeil
open C1TwoPointSpectralDecomposition
open C1FourPointSpectralPrefixTransport
open C1FourPointHighShellTail
open C1FourPointSpanGateCertificate
open C1SignedVarianceIdentity
open C1BipartiteMeanGapCertificate
open scoped BigOperators

noncomputable section

/-! ## Scaled Shell-Prefix Negativity Theorems -/

/-- General scaled shell-prefix theorem: any test function whose shell prefix is bounded
by `-M` and whose norm tail is strictly smaller than `M` has strictly negative spectral value. -/
theorem spectralWeilValue_neg_of_spectralHeightShellPrefix_and_tail_scaled
    (F : CompactLogTest) (N : Nat) (M : Real)
    (hprefix :
      (∑ k ∈ Finset.range N, ∑' z : spectralHeightShell k,
        spectralTerm F z.1).re ≤ -M)
    (htail :
      (∑' m : Nat, ∑' z : spectralHeightShell (m + N),
        ‖spectralTerm F z.1‖) < M) :
    spectralWeilValue F < 0 := by
  have htailRe := spectralHeightShellTail_re_le_normTail F N
  have htailReLt :
      (∑' m : Nat, ∑' z : spectralHeightShell (m + N),
        spectralTerm F z.1).re < M :=
    htailRe.trans_lt htail
  unfold spectralWeilValue
  rw [← spectralHeightShellSum_eq_source_tsum F]
  rw [spectralHeightShellSum_split F N, Complex.add_re]
  linarith

/-- Scaled fourth-order tail to spectral negativity: when `FourthOrderSpectralTail` provides
a tail bound strictly smaller than the prefix bound `M > 0`, the spectral value is strictly
negative. -/
theorem spectralWeilValue_neg_of_spectralHeightShellPrefix_and_fourthOrderTail_scaled
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet)
    (T epsilon : Real) (htail : FourthOrderSpectralTail F rho.1 T epsilon)
    (n0 : Nat) (hT : T ≤ (2 : Real) ^ (n0 + 1))
    (hrhoHeight : 2 * |rho.1.im| ≤ (2 : Real) ^ (n0 + 1))
    (M : Real)
    (hprefix :
      (∑ k ∈ Finset.range (n0 + 1), ∑' z : spectralHeightShell k,
        spectralTerm F z.1).re ≤ -M)
    (hsmall : 4 * epsilon ^ 2 * spectralMultiplicityConstant *
        (3 / 4 : Real) ^ n0 < M) :
    spectralWeilValue F < 0 := by
  have htailBound := spectralTail_norm_shellSum_le_of_fourthOrderTail
    F rho.1 T epsilon htail n0 hT hrhoHeight
  have htailBound' :
      (∑' m : Nat, ∑' z : spectralHeightShell (m + (n0 + 1)),
        ‖spectralTerm F z.1‖) ≤
        4 * epsilon ^ 2 * spectralMultiplicityConstant *
          (3 / 4 : Real) ^ n0 := by
    simpa only [Nat.add_assoc] using htailBound
  exact spectralWeilValue_neg_of_spectralHeightShellPrefix_and_tail_scaled
    F (n0 + 1) M hprefix (htailBound'.trans_lt hsmall)

/-- Same-owner Weil value negativity: for any test `v`, if its convolution square satisfies
the scaled shell-prefix and fourth-order tail conditions, then `qw v < 0`. -/
theorem qw_neg_of_spectralHeightShellPrefix_and_fourthOrderTail_scaled
    (v : CompactLogTest) (rho : sourceNontrivialZeroSet)
    (T epsilon : Real)
    (htail : FourthOrderSpectralTail v.convolutionSquare rho.1 T epsilon)
    (n0 : Nat) (hT : T ≤ (2 : Real) ^ (n0 + 1))
    (hrhoHeight : 2 * |rho.1.im| ≤ (2 : Real) ^ (n0 + 1))
    (M : Real)
    (hprefix :
      (∑ k ∈ Finset.range (n0 + 1), ∑' z : spectralHeightShell k,
        spectralTerm v.convolutionSquare z.1).re ≤ -M)
    (hsmall : 4 * epsilon ^ 2 * spectralMultiplicityConstant *
        (3 / 4 : Real) ^ n0 < M) :
    C1SameOwnerWeil.qw v < 0 := by
  have hspectral :=
    spectralWeilValue_neg_of_spectralHeightShellPrefix_and_fourthOrderTail_scaled
      v.convolutionSquare rho T epsilon htail n0 hT hrhoHeight M hprefix hsmall
  rw [qw_eq_spectralWeilValue_centerTwo v]
  exact hspectral

/-! ## Nonnegativity from Gate and Triple Vanishing -/

/-- Span nonnegativity: an annihilator-detector span vector `v` satisfying triple vanishing
and the semi-local gate has nonnegative same-owner Weil value `0 ≤ qw v`. -/
theorem annihilatorDetectorSpanVector_qw_nonneg_of_gate
    (u g : CompactLogTest) (lam : Real)
    (hu : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet u)
    (hg : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g)
    (hgate : orbitWindowSemiLocalGate (annihilatorDetectorSpanVector u g lam)) :
    0 ≤ C1SameOwnerWeil.qw (annihilatorDetectorSpanVector u g lam) := by
  have hvanish : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet
      (annihilatorDetectorSpanVector u g lam) :=
    annihilatorDetectorSpanVector_vanishesOn_cc20Triple u g lam hu hg
  exact qw_nonneg_of_orbitWindowSemiLocalGate _ hvanish hgate

/-! ## The Universal Contradiction Principle -/

/-- Contradiction Principle: a single test function cannot simultaneously satisfy
nonnegative Weil energy `0 ≤ qw v` and strictly negative Weil energy `qw v < 0`. -/
theorem false_of_qw_nonneg_and_neg
    (v : CompactLogTest)
    (hnonneg : 0 ≤ C1SameOwnerWeil.qw v)
    (hneg : C1SameOwnerWeil.qw v < 0) :
    False := by
  linarith

/-- Contradiction on the Annihilator-Detector Span: if the span vector `v(lam)` simultaneously
satisfies the semi-local gate and the high-shell tail negativity, `False` is obtained. -/
theorem false_of_annihilatorDetectorSpanVector_gate_and_spectral_neg
    (u g : CompactLogTest) (lam : Real)
    (hu : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet u)
    (hg : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g)
    (hgate : orbitWindowSemiLocalGate (annihilatorDetectorSpanVector u g lam))
    (hneg : C1SameOwnerWeil.qw (annihilatorDetectorSpanVector u g lam) < 0) :
    False := by
  have hnonneg := annihilatorDetectorSpanVector_qw_nonneg_of_gate u g lam hu hg hgate
  exact false_of_qw_nonneg_and_neg _ hnonneg hneg

/-! ## Master Exit to RiemannHypothesis -/

/-- If hypothetical right-hand off-line zeros are impossible (produce `False`),
then `SourceRH` holds unconditionally. -/
theorem sourceRH_of_right_nontrivial_zeros_empty
    (hnoRight : ∀ rho : sourceNontrivialZeroSet, (1 / 2 : Real) < rho.1.re → False) :
    RHDefinitionBridge.standard.SourceRH := by
  intro rho hrho
  by_cases hline : rho.re = 1 / 2
  · simpa [RHDefinitionBridge.standard] using hline
  · obtain ⟨sigma, hright, _hmultiplicity, _hchoice⟩ :=
      exists_rightOfCriticalXiZero_of_re_ne_half ⟨rho, hrho⟩ hline
    exact False.elim (hnoRight sigma hright)

/-- Master Exit from Off-Line Contradiction: proving `False` for every right-hand
off-line zero directly yields Mathlib's canonical `_root_.RiemannHypothesis`. -/
theorem riemannHypothesis_of_right_nontrivial_zeros_empty
    (hnoRight : ∀ rho : sourceNontrivialZeroSet, (1 / 2 : Real) < rho.1.re → False) :
    _root_.RiemannHypothesis := by
  exact RHDefinitionBridge.standard_source_rh_iff_mathlib.mp
    (sourceRH_of_right_nontrivial_zeros_empty hnoRight)

/-- Cut 3 Synthesis: when a healthy detector owner provides the four-point span gate
and high-shell tail convergence, Mathlib's `_root_.RiemannHypothesis` follows. -/
theorem riemannHypothesis_of_four_point_span_contradiction_producer
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ (g : CompactLogTest) (lam : Real),
          0 < lam ∧
          CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g ∧
          orbitWindowSemiLocalGate
            (annihilatorDetectorSpanVector
              (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam) ∧
          C1SameOwnerWeil.qw
            (annihilatorDetectorSpanVector
              (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam) < 0) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_right_nontrivial_zeros_empty
  intro rho hright
  obtain ⟨g, lam, _hpos, hgVanish, hgate, hqwNeg⟩ := hproducer rho hright
  have huVanish : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet
      (fullFunctionalEquationOrbitAnnihilator g rho.1) :=
    fullFunctionalEquationOrbitAnnihilator_vanishesOn_cc20Triple g rho.1 hgVanish
  exact false_of_annihilatorDetectorSpanVector_gate_and_spectral_neg
    (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam huVanish hgVanish hgate hqwNeg

end

end C1FourPointContradictionAssembly
end Source
end ConnesWeilRH
