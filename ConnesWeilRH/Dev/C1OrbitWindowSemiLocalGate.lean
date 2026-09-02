/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity
import ConnesWeilRH.Dev.C1SameOwnerWeil

/-!
# C1: the orbit-window semi-local gate (record 1089)

Record 1087 closed the ROOT-window attack lines, and its prescribed re-anchor
grows the ROOT-local CC20 endpoint certificate OUTWARD to the detector orbit
window.  This module makes the surviving C3 target a SINGLE Prop on the SAME
explicit object, exactly as record 1085 did for the root gate:

* `orbitWindowSemiLocalGate g` is the orbit analogue of the record-1080 scalar
  gate: `arch(F_g) + finitePrimeSum(F_g) <= 0`, which is equivalent to
  `0 <= qw g` for every triple-vanishing test (one-line bridge below).
* The visible prime-power readback: a prime power `q` visible to a test whose
  support lies in `(-B, B)` satisfies `log q < B`, hence `q < exp B`.  For the
  orbit square of the committed fixed-window D1 construction the window is
  `Ioo (-(n+2)) (n+2)`, so the square's visible set is bounded by
  `q < exp (2*(n+2))`.
* `exists_pinnedOrbitDetector_with_window_and_visiblePrimes` packages the
  formal detector data (`HealthyYoshidaDetectorData`) with its orbit support
  bound and the visible-set bound on ONE object.

This module proves no sign.  The gate itself is the open P2 obligation (map
`004`); the candidate routes are designed in the record-1089 design document.
RH unclaimed; GATE 1 mainline untouched.
-/

namespace ConnesWeilRH
namespace Source
namespace C1OrbitWindowSemiLocalGate

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaDetector
open C1HealthyYoshidaUnscaledOrbit
open C1HealthyYoshidaClosedPrefix
open C1SpectralSummability
open C1SpectralTailBound
open C1SpectralWeil
open C1HealthyYoshidaSpectralNegativity
open C1SameOwnerWeil
open scoped BigOperators

/-- The orbit-window semi-local gate: the archimedean term and the finite
visible prime-power sum of the Hermitian square sum to at most zero.  On the
ROOT window the prime sum vanishes and this reduces to the record-1080 scalar
archimedean gate; at orbit support the arithmetic term is part of the sign. -/
def orbitWindowSemiLocalGate (g : CompactLogTest) : Prop :=
  C1SameOwnerWeil.archimedeanTerm g.convolutionSquare +
      C1SameOwnerWeil.finitePrimeSum g.convolutionSquare <= 0

/-- One-line bridge: the orbit gate gives the nonnegative same-owner Weil value
consumed by `healthy_sourceRH_of_right_detector_specific_qw_nonneg`. -/
theorem qw_nonneg_of_orbitWindowSemiLocalGate
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hgate : orbitWindowSemiLocalGate g) :
    0 <= C1SameOwnerWeil.qw g := by
  rw [qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple
    g hvanishes]
  unfold orbitWindowSemiLocalGate at hgate
  linarith

/-- Pointwise visible-prime readback: a test supported in the open symmetric
window `(-B, B)` sees no visible prime power at or beyond `exp B`, because
prime terms evaluate the test at `Real.log q` and at `-Real.log q`. -/
theorem log_lt_of_mem_globalPrimeIndexSet_of_support_subset
    (F : CompactLogTest) {B : Real}
    (hsupport : Function.support F.test ⊆ Set.Ioo (-B) B)
    {q : Nat} (hq : q ∈ C1SameOwnerWeil.globalPrimeIndexSet F) :
    Real.log q < B := by
  obtain ⟨_hprime, hterm⟩ :=
    C1SameOwnerWeil.mem_globalPrimeIndexSet_iff F q |>.mp hq
  have hsum : F.test (Real.log q) + F.test (-Real.log q) ≠ 0 := by
    intro hzero
    apply hterm
    simp [C1SameOwnerWeil.finitePrimeTermComplex, hzero]
  have hpoint :
      F.test (Real.log q) ≠ 0 ∨ F.test (-Real.log q) ≠ 0 := by
    by_cases h1 : F.test (Real.log q) = 0
    · refine Or.inr fun hcon => hsum ?_
      rw [h1, hcon, add_zero]
    · exact Or.inl h1
  rcases hpoint with hleft | hright
  · exact (hsupport (Function.mem_support.mpr hleft)).2
  · have hinside := hsupport (Function.mem_support.mpr hright)
    linarith [hinside.1]

/-- Orbit-square version: if the root's support lies in the symmetric open
window `Ioo (-a) a`, every visible prime power of the Hermitian square is
below `exp (2*a)`.  This is the orbit-window replacement of the ROOT
prime-free vanishing lemma. -/
theorem mem_globalPrimeIndexSet_convolutionSquare_lt_exp
    (g : CompactLogTest) {a : Real}
    (hsupport : Function.support g.test ⊆ Set.Ioo (-a) a)
    {q : Nat}
    (hq : q ∈ C1SameOwnerWeil.globalPrimeIndexSet g.convolutionSquare) :
    (q : Real) < Real.exp (2 * a) := by
  have hsq := CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo
    g (fun x hx => Set.Ioo_subset_Icc_self (hsupport hx))
  have hbound := log_lt_of_mem_globalPrimeIndexSet_of_support_subset
    g.convolutionSquare (B := 2 * a) hsq hq
  have hqpos : (0 : Real) < q := by
    obtain ⟨hprime, _⟩ := C1SameOwnerWeil.mem_globalPrimeIndexSet_iff
      g.convolutionSquare q |>.mp hq
    have h2 : (1 : Real) < (q : Real) := by exact_mod_cast hprime.one_lt
    linarith
  calc (q : Real) = Real.exp (Real.log q) := (Real.exp_log hqpos).symm
    _ < Real.exp (2 * a) := Real.exp_lt_exp.mpr hbound

/-- The committed fixed-window D1 construction, exported as ONE pinned object:
healthy detector data, the orbit-window support bound, and the visible
prime-power bound all hold for the same test.  This is the explicit carrier of
the record-1089 semi-local gate; the gate itself remains the open P2
obligation. -/
theorem exists_pinnedOrbitDetector_with_window_and_visiblePrimes
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re) :
    ∃ g : CompactLogTest, ∃ n : Nat,
      HealthyYoshidaDetectorData rho.1 g ∧
      Function.support g.test ⊆
        Set.Ioo (-((n + 2 : ℕ) : Real)) (((n + 2 : ℕ) : Real)) ∧
      ∀ q ∈ C1SameOwnerWeil.globalPrimeIndexSet g.convolutionSquare,
        (q : Real) < Real.exp (2 * ((n + 2 : ℕ) : Real)) := by
  obtain ⟨base, T, _hbaseSupport, _hT, hconstruction⟩ :=
    exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets
      rho.1 rho.2 hoff ∅
      (baseLower := -(1 : Real)) (baseUpper := 1)
      (lower := -(1 : Real)) (upper := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (1 : Real) (by norm_num)
  obtain ⟨n0, hT, hrhoHeight, hsmall⟩ :=
    exists_dyadic_tail_start_with_budget_lt_xiMultiplicity T (1 : Real) rho
  let R : Real := (2 : Real) ^ (n0 + 1) + 2 + dist (2 : Complex) rho.1
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  obtain ⟨correction, _C, n, _hcorrectionSupport, hselectedSupport,
      htargetValues, _hminimal, _horbitSum, hsquareZeros, _hC,
      _hcenteredTail, hsquareTail⟩ :=
    hconstruction R hR
  have himLt : |rho.1.im| < (2 : Real) ^ (n0 + 1) := by
    have hpow : 0 < (2 : Real) ^ (n0 + 1) := by positivity
    have himNonneg : 0 ≤ |rho.1.im| := abs_nonneg _
    nlinarith
  have hrhoShell : dyadicShellIndex |rho.1.im| < n0 + 1 := by
    have hminimal := Nat.find_min'
      (exists_lt_two_pow_succ |rho.1.im|) himLt
    rw [← dyadicShellIndex] at hminimal
    omega
  have hsquareZeros' :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              ((2 : Real) ^ (n0 + 1) + 2 + dist (2 : Complex) rho.1) ∪
                (∅ : Finset Complex)),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt (selectedOwner base correction n).convolutionSquare
            (w.1 - 1 / 2) = 0 := by
    simpa only [R] using hsquareZeros
  have hwindow : Function.support
      (selectedOwner base correction n).sourceTest.test ⊆
      Set.Ioo (-((n + 1 + 1 : ℕ) : Real)) (((n + 1 + 1 : ℕ) : Real)) := by
    have hwL :
      ((n + 1 : ℕ) : Real) * (-(1 : Real)) + (-(1 : Real)) =
        (-((n + 1 + 1 : ℕ) : Real)) := by
      push_cast
      ring
    have hwR :
      ((n + 1 : ℕ) : Real) * (1 : Real) + (1 : Real) =
        ((n + 1 + 1 : ℕ) : Real) := by
      push_cast
      ring
    rw [hwL, hwR] at hselectedSupport
    exact hselectedSupport
  have hnat : (n + 1 + 1 : ℕ) = n + 2 := by omega
  rw [hnat] at hwindow
  refine ⟨(selectedOwner base correction n).sourceTest, n,
    selectedOwner_healthyDetectorData_of_closedBall_square_zero_control_and_fourthOrderTail
      base correction n rho hoff hright T (1 : Real) hsquareTail n0 hT
      hrhoHeight hrhoShell (∅ : Finset Complex) htargetValues
      hsquareZeros' hsmall, hwindow, ?_⟩
  intro q hq
  exact mem_globalPrimeIndexSet_convolutionSquare_lt_exp
    (selectedOwner base correction n).sourceTest hwindow hq

end C1OrbitWindowSemiLocalGate
end Source
end ConnesWeilRH
