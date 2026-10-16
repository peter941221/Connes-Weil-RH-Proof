/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1FourPointContradictionAssembly

/-!
# Record 2721 wired four-point row-B contradiction at pinned constants

The record-2720/2718/2721 numeric certificates are absorbed into the
four-point contradiction chain at explicit pinned decimals (proxy-tie
discipline, records 2257/2311): every numeric constant enters as a
named `def` rounded UP from the artifact render, and the residual
obligations of the reopen motion appear as the exact hypothesis list of
one theorem.

Row B is (gamma_2 = 21.0220..., N = 5, n = 3): the row where record
2720's certified PAIR lane closes the tail constraint at its own stored
index and record 2718 certifies both gate signs (branch `all`).  The
pinned constants:

  q   = 26 / 10^17      (>= 2720 q*(64)  = 2.525e-16)
  C4  = 61000000        (>= 2720 C4*     = 6.052e+07)
  C2  = 29000000        (>= 2720 C2*     = 2.816e+07)
  T   = 64 = 2^(5+1),   span coefficient lambda = 24, epsilon = 1,
  mult cap 515 (>= spectralMultiplicityConstant proxy, record 2354),
  rho caps: ‖rho‖ <= 22, |Im rho| <= 421/20.

The scalar acceptance margins at these pins (exact rational, checked by
the artifact-side checker `scripts/check_four_point_wired_2721.py`):
tail budget 2.3e-37 < 1 (margin 4.3e+36), eta budget 13905/16384 < 1.

Nothing here is a producer GO or an RH claim: the hypotheses that
remain (the three strip envelopes, the g-construction obligations, the
gate corner at lambda = 24, and the shell-prefix bound) are exactly the
named residual obligations of the map-103 reopen motion.
-/

namespace ConnesWeilRH
namespace Source
namespace C1FourPointRowBWired2721

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
open C1FourPointContradictionAssembly
open scoped BigOperators

noncomputable section

/-- Base contraction pin: dominates the record-2720 certified
contraction `q*(64) = 2.525e-16` at row B (21.0220, N = 5). -/
def wiredQRowB2721 : Real := 26 / 10 ^ 17

/-- Base quartic strip constant pin: dominates the record-2720
`C4* = 6.052e+07` at row B. -/
def wiredC4RowB2721 : Real := 61000000

/-- Correction quadratic strip constant pin: dominates the
record-2720 `C2* = 2.816e+07` at row B. -/
def wiredC2RowB2721 : Real := 29000000

/-- Norm cap for the selected zero: `|gamma_2| = 21.0220...` gives
`‖rho‖ <= 21.1 < 22`. -/
def wiredRhoNormCapRowB2721 : Real := 22

/-- Imaginary-height cap for the selected zero:
`|Im rho| <= 421 / 20 = 21.05`. -/
def wiredRhoImCapRowB2721 : Real := 421 / 20

/-- Spectral multiplicity proxy cap (record-2354 proxy-tie:
`spectralMultiplicityConstant` stays a def, bounded by hypothesis). -/
def wiredMultCapRowB2721 : Real := 515

private theorem wiredPiBound2721 : Real.pi < 22 / 7 := by
  calc
    Real.pi < 3.1416 := Real.pi_lt_d4
    _ < 22 / 7 := by norm_num

private theorem wiredTwoPiPowTwelve2721 :
    (2 * Real.pi) ^ 12 ≤ 4 * 10 ^ 9 := by
  have h2pi : (2 * Real.pi) < 44 / 7 := by
    nlinarith [wiredPiBound2721, Real.pi_pos]
  have hpow : (2 * Real.pi) ^ 12 < (44 / 7 : Real) ^ 12 :=
    pow_lt_pow_left₀ h2pi (by positivity) (by norm_num)
  exact le_of_lt (lt_trans hpow (by norm_num))

/-- The record-2721 tail scalar acceptance at the pinned row-B
constants, uniform in the zero norm below the cap: the
`selectedOwner_fullOrbit_span_fourthOrderSpectralTail_of_q` budget at
`epsilon = 1`, `lambda = 24`, `n = 3`.  Exact rational margin at the
pins: `2.3e-37 < 1` (4.3e+36 headroom). -/
theorem wiredHsmallTailRowB2721 {rn : Real} (hrn0 : 0 ≤ rn) (hrn : rn ≤ 22) :
    (3 + rn) ^ 4 * ((3 + rn) ^ 4 + |(24 : Real)|) ^ 2 * (2 * Real.pi) ^ 12 *
      ((wiredQRowB2721 ^ 3 * (wiredC4RowB2721 * wiredC2RowB2721)) ^ 2) <
      (1 : Real) ^ 2 := by
  have hA : (3 + rn) ^ 4 ≤ (25 : Real) ^ 4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hB : ((3 + rn) ^ 4 + |(24 : Real)|) ^ 2 ≤ ((25 : Real) ^ 4 + 24) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    exact add_le_add hA (by norm_num)
  have h1 : (3 + rn) ^ 4 * ((3 + rn) ^ 4 + |(24 : Real)|) ^ 2 ≤
      (25 : Real) ^ 4 * ((25 : Real) ^ 4 + 24) ^ 2 :=
    mul_le_mul hA hB (by positivity) (by positivity)
  have h2 : ((3 + rn) ^ 4 * ((3 + rn) ^ 4 + |(24 : Real)|) ^ 2) *
      (2 * Real.pi) ^ 12 ≤
      ((25 : Real) ^ 4 * ((25 : Real) ^ 4 + 24) ^ 2) * (4 * 10 ^ 9) :=
    mul_le_mul h1 wiredTwoPiPowTwelve2721 (by positivity) (by positivity)
  have h3 :
      (((3 + rn) ^ 4 * ((3 + rn) ^ 4 + |(24 : Real)|) ^ 2) *
          (2 * Real.pi) ^ 12) *
        ((wiredQRowB2721 ^ 3 * (wiredC4RowB2721 * wiredC2RowB2721)) ^ 2) ≤
      (((25 : Real) ^ 4 * ((25 : Real) ^ 4 + 24) ^ 2) * (4 * 10 ^ 9)) *
        ((wiredQRowB2721 ^ 3 * (wiredC4RowB2721 * wiredC2RowB2721)) ^ 2) :=
    mul_le_mul h2 (le_refl _) (by positivity) (by positivity)
  refine lt_of_le_of_lt h3 ?_
  norm_num [wiredQRowB2721, wiredC4RowB2721, wiredC2RowB2721]

/-- The coefficient-scaled eta budget at the pinned constants:
`4 * (1 / 24)^2 * spectralMultiplicityConstant * (3/4)^5 < 1`
(exact value at the cap: `13905 / 16384`). -/
theorem wiredEtaBudgetRowB2721
    (hmult : spectralMultiplicityConstant ≤ wiredMultCapRowB2721) :
    4 * ((1 : Real) / 24) ^ 2 * spectralMultiplicityConstant *
      (3 / 4 : Real) ^ 5 < 1 := by
  have hstep : 4 * ((1 : Real) / 24) ^ 2 * spectralMultiplicityConstant *
      (3 / 4 : Real) ^ 5 ≤
      4 * ((1 : Real) / 24) ^ 2 * wiredMultCapRowB2721 * (3 / 4 : Real) ^ 5 := by
    calc 4 * ((1 : Real) / 24) ^ 2 * spectralMultiplicityConstant *
            (3 / 4 : Real) ^ 5 =
        (4 * ((1 : Real) / 24) ^ 2 * spectralMultiplicityConstant) *
          (3 / 4 : Real) ^ 5 := rfl
      _ ≤ (4 * ((1 : Real) / 24) ^ 2 * wiredMultCapRowB2721) *
            (3 / 4 : Real) ^ 5 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmult (by positivity)) (by positivity)
      _ = 4 * ((1 : Real) / 24) ^ 2 * wiredMultCapRowB2721 *
            (3 / 4 : Real) ^ 5 := rfl
  refine hstep.trans_lt ?_
  norm_num [wiredMultCapRowB2721]

/-- The record-2721 wired row-B contradiction: at the pinned constants,
the four-point span contradiction closes, with every numeric premise an
explicit hypothesis.  Residual obligations (the map-103 reopen-motion
list):

  * `hNorm`/`hIm` — zero interval pins (record-2719-grade enclosing
    intervals for `gamma_2`);
  * `hmult` — the spectral-multiplicity proxy tie (record 2354);
  * `hvanish`/`hsupport` — the `g`-construction obligations for
    `(selectedOwner base correction 3).sourceTest`;
  * `hcontract`/`hquartic`/`hquadratic` — the three strip envelopes at
    the record-2720 certified constants (P3, artifact grade);
  * `hgate24` — the record-2718/2721 gate corner at the pinned span
    coefficient `lambda = 24` (branch `all` certifies the parabola at
    every positive coefficient);
  * `hprefix` — the shell-prefix bound (P2 numeric residual). -/
theorem fourPointContradictionRowBWired2721
    (base correction : CompactLogTest) (rho : sourceNontrivialZeroSet)
    {B : Real}
    (hNorm : ‖rho.1‖ ≤ wiredRhoNormCapRowB2721)
    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721)
    (hmult : spectralMultiplicityConstant ≤ wiredMultCapRowB2721)
    (hvanish : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet (selectedOwner base correction 3).sourceTest)
    (hsupport : Function.support
      (selectedOwner base correction 3).sourceTest.test ⊆ Set.Ioo (-B) B)
    (hcontract : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      64 ≤ |t| →
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredQRowB2721)
    (hquartic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 4 *
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredC4RowB2721)
    (hquadratic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredC2RowB2721)
    (hgate24 : ICgate
        ((fullFunctionalEquationOrbitAnnihilator
          (selectedOwner base correction 3).sourceTest rho.1).convolutionSquare) -
      24 * (ICgate ((fullFunctionalEquationOrbitAnnihilator
          (selectedOwner base correction 3).sourceTest rho.1).involution.convolution
            (selectedOwner base correction 3).sourceTest) +
        ICgate (((selectedOwner base correction 3).sourceTest).involution.convolution
          (fullFunctionalEquationOrbitAnnihilator
            (selectedOwner base correction 3).sourceTest rho.1))) +
      24 ^ 2 * ICgate
        (((selectedOwner base correction 3).sourceTest).convolutionSquare) ≤ 0)
    (hprefix : (∑ k ∈ Finset.range 6, ∑' z : spectralHeightShell k,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator
              (selectedOwner base correction 3).sourceTest rho.1)
            (selectedOwner base correction 3).sourceTest 24).convolutionSquare
          z.1).re ≤
      -((xiMultiplicity rho : Real) * 24 ^ 2)) :
    False := by
  have hsupp_g : Function.support
      (selectedOwner base correction 3).sourceTest.test ⊆ Set.Icc (-B) B :=
    hsupport.trans Set.Ioo_subset_Icc_self
  have hsupp_u : Function.support
      (fullFunctionalEquationOrbitAnnihilator
        (selectedOwner base correction 3).sourceTest rho.1).test ⊆
      Set.Icc (-B) B :=
    fullFunctionalEquationOrbitAnnihilator_support_subset_Icc
      (selectedOwner base correction 3).sourceTest rho.1 hsupp_g
  have hw : ∀ i, Function.support
      ((![fullFunctionalEquationOrbitAnnihilator
          (selectedOwner base correction 3).sourceTest rho.1,
        (selectedOwner base correction 3).sourceTest] :
        Fin 2 → CompactLogTest) i).test ⊆
      Set.Ioo (-(B + 1)) (B + 1) := by
    intro i
    fin_cases i
    · intro x hx
      have hx' := hsupp_u hx
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
    · intro x hx
      have hx' := hsupp_g hx
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  have hgate : orbitWindowSemiLocalGate
      (annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator
          (selectedOwner base correction 3).sourceTest rho.1)
        (selectedOwner base correction 3).sourceTest 24) := by
    rw [orbitWindowSemiLocalGate_iff,
      annihilator_span_gate_eq_parabola
        (fullFunctionalEquationOrbitAnnihilator
          (selectedOwner base correction 3).sourceTest rho.1)
        (selectedOwner base correction 3).sourceTest 24 hw]
    exact hgate24
  have hnonneg : 0 ≤ C1SameOwnerWeil.qw
      (annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator
          (selectedOwner base correction 3).sourceTest rho.1)
        (selectedOwner base correction 3).sourceTest 24) := by
    have huVanish : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet
        (fullFunctionalEquationOrbitAnnihilator
          (selectedOwner base correction 3).sourceTest rho.1) :=
      fullFunctionalEquationOrbitAnnihilator_vanishesOn_cc20Triple
        (selectedOwner base correction 3).sourceTest rho.1 hvanish
    exact annihilatorDetectorSpanVector_qw_nonneg_of_gate
      (fullFunctionalEquationOrbitAnnihilator
        (selectedOwner base correction 3).sourceTest rho.1)
      (selectedOwner base correction 3).sourceTest 24 huVanish hvanish hgate
  have htailOne : FourthOrderSpectralTail
      (annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator
          (selectedOwner base correction 3).sourceTest rho.1)
        (selectedOwner base correction 3).sourceTest 24).convolutionSquare
      rho.1 64 1 := by
    have hsmall := wiredHsmallTailRowB2721 (norm_nonneg rho.1) hNorm
    exact selectedOwner_fullOrbit_span_fourthOrderSpectralTail_of_q
      base correction rho.1 24 wiredC4RowB2721 wiredC2RowB2721 64 wiredQRowB2721 1 3
      (by norm_num [wiredQRowB2721])
      (by norm_num [wiredC4RowB2721])
      (by norm_num [wiredC2RowB2721])
      hcontract hquartic hquadratic hsmall
  have hneg : C1SameOwnerWeil.qw
      (annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator
          (selectedOwner base correction 3).sourceTest rho.1)
        (selectedOwner base correction 3).sourceTest 24) < 0 := by
    refine qw_neg_of_spectralHeightShellPrefix_and_coefficient_scaled_tail
      (annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator
          (selectedOwner base correction 3).sourceTest rho.1)
        (selectedOwner base correction 3).sourceTest 24)
      rho 64 (1 / 24) 24 ?_ 5 ?_ ?_ (by norm_num)
      (by simpa only [neg_mul] using hprefix) ?_
    · have hlam : (24 : Real) * (1 / 24) = 1 := by
        rw [mul_one_div, div_self (by norm_num)]
      rw [hlam]
      exact htailOne
    · norm_num
    · have h64 : ((2 : Real) ^ (5 + 1)) = 64 := by norm_num
      rw [h64]
      have himle : |rho.1.im| ≤ 421 / 20 := hIm
      have h2 := mul_le_mul_of_nonneg_left himle (by norm_num : (0 : Real) ≤ 2)
      linarith
    · have h0nat : 0 < xiMultiplicity rho := xiMultiplicity_pos rho
      have h1le : (1 : ℕ) ≤ xiMultiplicity rho := by omega
      have hx : (1 : Real) ≤ (xiMultiplicity rho : Real) := by
        exact_mod_cast h1le
      have hb := wiredEtaBudgetRowB2721 hmult
      linarith [hb, hx]
  exact false_of_qw_nonneg_and_neg
    (annihilatorDetectorSpanVector
      (fullFunctionalEquationOrbitAnnihilator
        (selectedOwner base correction 3).sourceTest rho.1)
      (selectedOwner base correction 3).sourceTest 24)
    hnonneg hneg

end

end C1FourPointRowBWired2721
end Source
end ConnesWeilRH
