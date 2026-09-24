/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1P2BilateralProfile
import ConnesWeilRH.Dev.C1P2OrbitPhysicalProfileReadback
import ConnesWeilRH.Dev.C1P2OrbitPhysicalKernelIntegrandBounds
import ConnesWeilRH.Dev.C1P2DirectSupportOverlapDecoupling
import ConnesWeilRH.Dev.C1P2DirectChebyshevDecoupling

/-!
# Owner-preserving prime-prefix reduction for the four-point gate

This leaf does not assert that the first prime power is visible for the
selected owner.  It isolates that obligation exactly: visibility of `n = 2`
permits an exact prefix-plus-remainder decomposition, while non-visibility
forces the corresponding real prime term to vanish.

Consumer: the signed physical-kernel / four-point same-owner budget in map
103.  The finite remainder is always the actual owner's visible set; no
ambient bump or replacement detector is introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace C1FourPointPrimePrefixReduction

open C1SameOwnerWeil
open C1P2BilateralProfile
open C1P2OrbitPhysicalProfileReadback
open C1P2OrbitPhysicalKernelIntegrandBounds
open C1P2DirectSupportOverlapDecoupling
open C1P2DirectChebyshevDecoupling
open C1P2SignedBudget
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1G8R0OrbitGeometry
open scoped BigOperators

theorem orbitG8_range_bound_two
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    2 < Nat.ceil
        (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1 := by
  have hnat : 1 ≤ geometry.orbitIndex + 2 := by omega
  have hreal : (1 : Real) ≤ ((geometry.orbitIndex + 2 : Nat) : Real) := by
    exact_mod_cast hnat
  have harg : (1 : Real) ≤
      2 * ((geometry.orbitIndex + 2 : Nat) : Real) := by
    nlinarith
  have hexp : (2 : Real) ≤
      Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real)) := by
    calc
      (2 : Real) = 1 + 1 := by norm_num
      _ ≤ Real.exp 1 := Real.add_one_le_exp 1
      _ ≤ Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real)) :=
        Real.exp_le_exp.mpr harg
  have hceil : (2 : Real) ≤
      (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) : Real) :=
    hexp.trans (Nat.le_ceil _)
  have hceilNat : 2 ≤
      Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) := by
    exact_mod_cast hceil
  omega

theorem finitePrimeSum_eq_term_add_erase_of_mem
    (F : CompactLogTest) {n : Nat}
    (hn : n ∈ globalPrimeIndexSet F) :
    finitePrimeSum F =
      finitePrimeTerm F n +
        ∑ k ∈ (globalPrimeIndexSet F).erase n, finitePrimeTerm F k := by
  unfold finitePrimeSum
  rw [← Finset.sum_erase_add _ _ hn, add_comm]

theorem finitePrimeTerm_eq_zero_of_not_mem_globalPrimeIndexSet
    (F : CompactLogTest) {n : Nat}
    (hn : n ∉ globalPrimeIndexSet F) :
    finitePrimeTerm F n = 0 := by
  have hzero : finitePrimeTermComplex F n = 0 := by
    by_contra hne
    exact hn ((mem_globalPrimeIndexSet_iff F n).mpr
      ⟨finitePrimeTermComplex_nonzero_primePower F hne, hne⟩)
  unfold finitePrimeTerm
  rw [hzero]
  rfl

theorem finitePrimeSum_eq_two_prefix_add_remainder
    {F : CompactLogTest}
    (h2 : 2 ∈ globalPrimeIndexSet F) :
    finitePrimeSum F =
      finitePrimeTerm F 2 +
        ∑ k ∈ (globalPrimeIndexSet F).erase 2, finitePrimeTerm F k :=
  finitePrimeSum_eq_term_add_erase_of_mem F h2

theorem finitePrimeTerm_two_eq_zero_of_not_visible
    {F : CompactLogTest}
    (h2 : 2 ∉ globalPrimeIndexSet F) :
    finitePrimeTerm F 2 = 0 :=
  finitePrimeTerm_eq_zero_of_not_mem_globalPrimeIndexSet F h2

theorem finitePrimeTerm_two_eq_log_two_profile
    (F : CompactLogTest) :
    finitePrimeTerm F 2 =
      Real.log 2 * (1 / Real.sqrt (2 : Real)) *
        (bilateralProfile F (Real.log 2)).re := by
  rw [finitePrimeTerm_eq_realCoefficient_mul_bilateralProfile_re]
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

theorem finitePrimeTerm_two_neg_iff_profile_at_log_two_neg
    (F : CompactLogTest) :
    finitePrimeTerm F 2 < 0 ↔
      (bilateralProfile F (Real.log 2)).re < 0 := by
  rw [finitePrimeTerm_two_eq_log_two_profile]
  have hcoef : 0 < Real.log 2 * (1 / Real.sqrt (2 : Real)) := by
    exact mul_pos (Real.log_pos (by norm_num)) (by positivity)
  constructor
  · intro hterm
    by_contra hnot
    have hprofile : 0 ≤ (bilateralProfile F (Real.log 2)).re := le_of_not_gt hnot
    exact (not_lt_of_ge (mul_nonneg (le_of_lt hcoef) hprofile)) hterm
  · intro hprofile
    exact mul_neg_of_pos_of_neg hcoef hprofile

theorem finitePrimeTerm_two_eq_orbitPhysicalKernel_re
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeTerm g.convolutionSquare 2 =
      ArithmeticFunction.vonMangoldt 2 * (1 / Real.sqrt (2 : Real)) *
        (2 * (orbitPhysicalKernel geometry (Real.log 2)).re) := by
  exact finitePrimeTerm_eq_orbitPhysicalKernel_re geometry 2

theorem finitePrimeTerm_two_neg_iff_orbitPhysicalKernel_re_neg
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeTerm g.convolutionSquare 2 < 0 ↔
      (orbitPhysicalKernel geometry (Real.log 2)).re < 0 := by
  rw [finitePrimeTerm_two_eq_orbitPhysicalKernel_re geometry]
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hshape : Real.log 2 * (1 / Real.sqrt (2 : Real)) *
      (2 * (orbitPhysicalKernel geometry (Real.log 2)).re) =
      (Real.log 2 * (1 / Real.sqrt (2 : Real)) * 2) *
        (orbitPhysicalKernel geometry (Real.log 2)).re := by ring
  change (Real.log (2 : Real) * (1 / Real.sqrt (2 : Real)) *
      (2 * (orbitPhysicalKernel geometry (Real.log (2 : Real))).re)) < 0 ↔
    (orbitPhysicalKernel geometry (Real.log (2 : Real))).re < 0
  rw [hshape]
  have hcoef : 0 < Real.log 2 * (1 / Real.sqrt (2 : Real)) * 2 := by
    positivity
  constructor
  · intro hterm
    by_contra hnot
    have hkernel : 0 ≤ (orbitPhysicalKernel geometry (Real.log 2)).re :=
      le_of_not_gt hnot
    exact (not_lt_of_ge (mul_nonneg (le_of_lt hcoef) hkernel)) hterm
  · intro hkernel
    exact mul_neg_of_pos_of_neg hcoef hkernel

theorem finitePrimeSum_eq_two_term_add_orbit_range_remainder
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hbound : 2 <
      Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1) :
    finitePrimeSum g.convolutionSquare =
      finitePrimeTerm g.convolutionSquare 2 +
        ∑ k ∈ (Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)).erase 2,
          finitePrimeTerm g.convolutionSquare k := by
  rw [finitePrimeSum_eq_sum_range_of_orbitG8Geometry geometry]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr hbound), add_comm]

theorem finitePrimeSum_eq_two_term_add_orbit_range_remainder_unconditional
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare =
      finitePrimeTerm g.convolutionSquare 2 +
        ∑ k ∈ (Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)).erase 2,
          finitePrimeTerm g.convolutionSquare k :=
  finitePrimeSum_eq_two_term_add_orbit_range_remainder geometry
    (orbitG8_range_bound_two geometry)

theorem finitePrimeSum_le_two_prefix_plus_overlap_remainder
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare ≤
      finitePrimeTerm g.convolutionSquare 2 +
        ∑ k ∈ (Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)).erase 2,
          2 * Real.exp (rawFactorSupportRadius geometry) *
            (rawFactorSeminorm geometry) ^ 2 *
            (ArithmeticFunction.vonMangoldt k / (k : Real)) := by
  rw [finitePrimeSum_eq_two_term_add_orbit_range_remainder_unconditional geometry]
  have hsum :
      (∑ k ∈ (Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)).erase 2,
          finitePrimeTerm g.convolutionSquare k) ≤
        ∑ k ∈ (Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)).erase 2,
          2 * Real.exp (rawFactorSupportRadius geometry) *
            (rawFactorSeminorm geometry) ^ 2 *
            (ArithmeticFunction.vonMangoldt k / (k : Real)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hterm := orbitPhysicalKernel_nodeTerm_le_overlap geometry k
    have heq : finitePrimeTerm g.convolutionSquare k =
        ArithmeticFunction.vonMangoldt k * (1 / Real.sqrt (k : Real)) *
          (orbitPhysicalKernel geometry (Real.log (k : Real)) +
            orbitPhysicalKernel geometry (-Real.log (k : Real))).re := by
      rw [finitePrimeTerm_eq_orbitPhysicalKernel_re geometry k]
      rw [orbitPhysicalKernel_add_neg_re_eq_two_mul geometry (Real.log (k : Real))]
    rw [heq]
    exact hterm
  calc
    finitePrimeTerm g.convolutionSquare 2 +
        ∑ k ∈ (Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)).erase 2,
          finitePrimeTerm g.convolutionSquare k =
      (∑ k ∈ (Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)).erase 2,
          finitePrimeTerm g.convolutionSquare k) +
        finitePrimeTerm g.convolutionSquare 2 := by ring
    _ ≤
      (∑ k ∈ (Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)).erase 2,
          2 * Real.exp (rawFactorSupportRadius geometry) *
            (rawFactorSeminorm geometry) ^ 2 *
        (ArithmeticFunction.vonMangoldt k / (k : Real))) +
        finitePrimeTerm g.convolutionSquare 2 :=
      by linarith
    _ = finitePrimeTerm g.convolutionSquare 2 +
        ∑ k ∈ (Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)).erase 2,
          2 * Real.exp (rawFactorSupportRadius geometry) *
            (rawFactorSeminorm geometry) ^ 2 *
            (ArithmeticFunction.vonMangoldt k / (k : Real)) := by ring

theorem finitePrimeSum_le_two_prefix_plus_overlap_minus_two_majorant
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare ≤
      finitePrimeTerm g.convolutionSquare 2 +
        orbitSupportOverlapBound geometry -
          2 * Real.exp (rawFactorSupportRadius geometry) *
            (rawFactorSeminorm geometry) ^ 2 *
            (ArithmeticFunction.vonMangoldt 2 / (2 : Real)) := by
  have hprefix := finitePrimeSum_le_two_prefix_plus_overlap_remainder geometry
  let R : Finset Nat := Finset.range
    (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)
  let A : Real := 2 * Real.exp (rawFactorSupportRadius geometry) *
    (rawFactorSeminorm geometry) ^ 2
  let f : Nat → Real := fun k => ArithmeticFunction.vonMangoldt k / (k : Real)
  have h2 : 2 ∈ R := by
    dsimp [R]
    exact Finset.mem_range.mpr (orbitG8_range_bound_two geometry)
  have hsum :
      (∑ k ∈ R.erase 2, A * f k) =
        A * (∑ k ∈ R, f k) - A * f 2 := by
    rw [← Finset.mul_sum]
    rw [← Finset.sum_erase_add _ _ h2]
    ring
  have hrewrite :
      orbitSupportOverlapBound geometry = A * (∑ k ∈ R, f k) := by
    simp only [orbitSupportOverlapBound, visibleHarmonicChebyshevSum,
      orbitVisiblePrimeRange, R, A, f]
  have hprefix' :
      finitePrimeSum g.convolutionSquare ≤
        finitePrimeTerm g.convolutionSquare 2 +
          (∑ k ∈ R.erase 2, A * f k) := by
    simpa [R, A, f] using hprefix
  rw [hsum, ← hrewrite] at hprefix'
  calc
    finitePrimeSum g.convolutionSquare ≤
        finitePrimeTerm g.convolutionSquare 2 +
          (orbitSupportOverlapBound geometry -
            2 * Real.exp (rawFactorSupportRadius geometry) *
              (rawFactorSeminorm geometry) ^ 2 *
              (ArithmeticFunction.vonMangoldt 2 / (2 : Real))) := by
      simpa [A, f] using hprefix'
    _ = finitePrimeTerm g.convolutionSquare 2 +
        orbitSupportOverlapBound geometry -
          2 * Real.exp (rawFactorSupportRadius geometry) *
            (rawFactorSeminorm geometry) ^ 2 *
            (ArithmeticFunction.vonMangoldt 2 / (2 : Real)) := by ring

theorem finitePrimeSum_eq_two_term_add_erased_signed_physical_remainder
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare =
      finitePrimeTerm g.convolutionSquare 2 +
        ∑ k ∈ (Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)).erase 2,
          ArithmeticFunction.vonMangoldt k * (1 / Real.sqrt (k : Real)) *
            (2 * ((∫ t, orbitPositiveIntegrandMajorant geometry k t) -
              ∫ t, orbitNegativeIntegrandMajorant geometry k t)) := by
  rw [finitePrimeSum_eq_two_term_add_orbit_range_remainder_unconditional geometry]
  apply congrArg (fun x => finitePrimeTerm g.convolutionSquare 2 + x)
  apply Finset.sum_congr rfl
  intro k hk
  rw [finitePrimeTerm_eq_orbitPhysicalKernel_re geometry k]
  have hnode := orbitPhysicalKernel_nodeTerm_eq_positive_sub_negative geometry k
  rw [orbitPhysicalKernel_add_neg_re_eq_two_mul geometry (Real.log (k : Real))] at hnode
  exact hnode

end C1FourPointPrimePrefixReduction
end Source
end ConnesWeilRH
