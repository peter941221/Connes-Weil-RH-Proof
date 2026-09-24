/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1FourPointContradictionAssembly
import ConnesWeilRH.Dev.C1ParametricMeanGapDomination
import ConnesWeilRH.Dev.C1FourPointHighShellTail
import ConnesWeilRH.Dev.C1FourPointSpanGateCertificate
import ConnesWeilRH.Dev.C1PinnedOrbitExit
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity
import ConnesWeilRH.Dev.C1SignedVarianceIdentity
import ConnesWeilRH.Dev.C1BipartiteMeanGapCertificate

/-!
# C1: Four-Point Mainline Exit to Riemann Hypothesis (Record 1956)

This module completes the master mainline assembly of the three-cut four-point
same-span contradiction route:

1. `FourPointSpanContradictionWitness`:
   Packages the healthy detector owner `g` and span coefficient `lam > 0`
   that simultaneously satisfy the semi-local gate and spectral negativity.

2. `false_of_fourPointSpanContradictionWitness`:
   Deduces `False` unconditionally from any contradiction witness on a right
   off-line zero.

3. `riemannHypothesis_of_mainline_witness_producer`:
   Direct canonical exit from a universal witness producer to Mathlib's
   canonical `_root_.RiemannHypothesis`.

4. `witness_of_gate_and_tail`:
   Assembles Cut 1 (high-shell tail convergence) and Cut 2 (semi-local gate)
   into a `FourPointSpanContradictionWitness`.

5. `riemannHypothesis_of_gate_determinant_neg`:
   Reduces `_root_.RiemannHypothesis` directly to the negative gate determinant
   condition on the four-point span.

6. `riemannHypothesis_of_bipartite_mean_gap_domination`:
   Connects the bipartite ANOVA mean gap domination criterion (Record 1952/1955)
   directly to Mathlib's `_root_.RiemannHypothesis`.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ConnesWeilRH
namespace Source
namespace C1FourPointMainlineRH

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
open C1ParametricMeanGapDomination
open C1FourPointContradictionAssembly
open scoped BigOperators

noncomputable section

/-! ## The Master Contradiction Witness -/

/-- A complete four-point span contradiction witness for a hypothetical off-line zero `rho`:
    packaging the selected detector `g` and coefficient `lam > 0` that simultaneously
    achieve the semi-local gate and the spectral negativity. -/
structure FourPointSpanContradictionWitness (rho : sourceNontrivialZeroSet) where
  g : CompactLogTest
  lam : Real
  hpos : 0 < lam
  hvanish : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g
  hgate : orbitWindowSemiLocalGate
    (annihilatorDetectorSpanVector
      (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam)
  hqw_neg : C1SameOwnerWeil.qw
    (annihilatorDetectorSpanVector
      (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam) < 0

/-- The Fundamental Contradiction: any witness for a right off-line zero forces `False`. -/
theorem false_of_fourPointSpanContradictionWitness
    (rho : sourceNontrivialZeroSet)
    (hwit : FourPointSpanContradictionWitness rho) :
    False := by
  have huVanish : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet
      (fullFunctionalEquationOrbitAnnihilator hwit.g rho.1) :=
    fullFunctionalEquationOrbitAnnihilator_vanishesOn_cc20Triple hwit.g rho.1 hwit.hvanish
  exact false_of_annihilatorDetectorSpanVector_gate_and_spectral_neg
    (fullFunctionalEquationOrbitAnnihilator hwit.g rho.1)
    hwit.g hwit.lam huVanish hwit.hvanish hwit.hgate hwit.hqw_neg

/-! ## Master Mainline Exits -/

/-- Master Mainline Exit: exhibiting a contradiction witness for every right-hand
off-line zero unconditionally proves Mathlib's canonical `_root_.RiemannHypothesis`. -/
theorem riemannHypothesis_of_mainline_witness_producer
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re → FourPointSpanContradictionWitness rho) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_right_nontrivial_zeros_empty
  intro rho hright
  exact false_of_fourPointSpanContradictionWitness rho (hproducer rho hright)

/-- Synthesis of Cut 1 and Cut 2: constructing a contradiction witness from the semi-local
gate and scaled high-shell tail negativity. -/
def witness_of_gate_and_tail
    (rho : sourceNontrivialZeroSet)
    (g : CompactLogTest) (lam : Real)
    (hpos : 0 < lam)
    (hvanish : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g)
    (hgate : orbitWindowSemiLocalGate
      (annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam))
    (T epsilon : Real)
    (htail : FourthOrderSpectralTail
      (annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam).convolutionSquare
      rho.1 T epsilon)
    (n0 : Nat) (hT : T ≤ (2 : Real) ^ (n0 + 1))
    (hrhoHeight : 2 * |rho.1.im| ≤ (2 : Real) ^ (n0 + 1))
    (M : Real)
    (hprefix :
      (∑ k ∈ Finset.range (n0 + 1), ∑' z : spectralHeightShell k,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam).convolutionSquare z.1).re ≤ -M)
    (hsmall : 4 * epsilon ^ 2 * spectralMultiplicityConstant *
        (3 / 4 : Real) ^ n0 < M) :
    FourPointSpanContradictionWitness rho := by
  refine ⟨g, lam, hpos, hvanish, hgate, ?_⟩
  exact qw_neg_of_spectralHeightShellPrefix_and_fourthOrderTail_scaled
    (annihilatorDetectorSpanVector
      (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam)
    rho T epsilon htail n0 hT hrhoHeight M hprefix hsmall

/-- Mainline Exit via Gate Determinant Negativity:
If for every right off-line zero `rho` there exists a healthy detector owner `g`
satisfying positive cross sum and negative gate determinant, and an appropriate tail index,
then Mathlib's `_root_.RiemannHypothesis` follows. -/
theorem riemannHypothesis_of_gate_determinant_neg
    (hdet_neg : ∀ rho : sourceNontrivialZeroSet,
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
    _root_.RiemannHypothesis :=
  riemannHypothesis_of_four_point_span_contradiction_producer hdet_neg

/-- Mainline Exit via Bipartite ANOVA Mean Gap Domination:
When the between-group mean gap dominates internal variance across all non-trivial zeros,
Mathlib's `_root_.RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_bipartite_mean_gap_domination
    (hdom : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ (C₁ C₂ p₁_bar p₂_bar var₁ var₂ : ℝ),
          0 < C₁ - C₂ ∧
          0 < 2 * (C₁ * p₁_bar - C₂ * p₂_bar) ∧
          0 < C₁ * C₂ * (p₁_bar - p₂_bar) ^ 2 + (C₁ - C₂) * (C₂ * var₂ - C₁ * var₁) ∧
          ∃ (g : CompactLogTest),
            CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g ∧
            ∀ lam : ℝ, 0 < lam →
              (C₁ * (var₁ + p₁_bar ^ 2) - C₂ * (var₂ + p₂_bar ^ 2)) -
                lam * (2 * (C₁ * p₁_bar - C₂ * p₂_bar)) +
                lam ^ 2 * (C₁ - C₂) < 0 →
              orbitWindowSemiLocalGate
                (annihilatorDetectorSpanVector
                  (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam) ∧
              C1SameOwnerWeil.qw
                (annihilatorDetectorSpanVector
                  (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam) < 0) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_four_point_span_contradiction_producer
  intro rho hright
  obtain ⟨C₁, C₂, p₁_bar, p₂_bar, var₁, var₂, hC, hB, hgap, g, hgVanish, hlam_prop⟩ :=
    hdom rho hright
  obtain ⟨lam, hlam_pos, hquad⟩ :=
    exists_pos_lambda_quadratic_neg_of_mean_gap_condition
      C₁ C₂ p₁_bar p₂_bar var₁ var₂ hC hB hgap
  obtain ⟨hgate, hqwNeg⟩ := hlam_prop lam hlam_pos hquad
  exact ⟨g, lam, hlam_pos, hgVanish, hgate, hqwNeg⟩

/-- Concrete Rational Certificate Anchor:
For the representative anchor `cert_c10_g14`, the quadratic negativity condition is
unconditionally certified with zero premises via `norm_num`. -/
theorem cert_c10_g14_produces_negative_quadratic :
    ∃ lam : ℝ, 0 < lam ∧
      (cert_c10_g14.C₁ * (cert_c10_g14.var₁ + cert_c10_g14.p₁_bar ^ 2) -
        cert_c10_g14.C₂ * (cert_c10_g14.var₂ + cert_c10_g14.p₂_bar ^ 2)) -
        lam * (2 * (cert_c10_g14.C₁ * cert_c10_g14.p₁_bar -
          cert_c10_g14.C₂ * cert_c10_g14.p₂_bar)) +
        lam ^ 2 * (cert_c10_g14.C₁ - cert_c10_g14.C₂) < 0 :=
  exists_pos_lambda_quadratic_neg_c10_g14

end

end C1FourPointMainlineRH
end Source
end ConnesWeilRH
