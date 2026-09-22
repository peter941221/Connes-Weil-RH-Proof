/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1P2DefectControl
import ConnesWeilRH.Dev.C1P2BaseSeminormBound

/-!
# G8 R0: raw orbit geometry for the selected healthy-owner chain

This leaf packages the lower-data output of the existing right-oriented
off-line-zero orbit construction.  The package records the selected-owner
factorization, raw interpolation values, centered orbit identity, zero and
tail controls, and the support/visible-prime cutoff.  It deliberately does
not contain `HealthyYoshidaDetectorData` or any Weil-sign field.

Consumer: the G8 same-owner readback for the detector selected against the
same hypothetical right-hand off-line zero.  This is an R0 compatibility
package only; it proves no trace limit, semi-local sign, or RH conclusion.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8R0OrbitGeometry

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaDetector
open C1HealthyYoshidaMinimalInterpolation
open C1HealthyYoshidaUnscaledOrbit
open C1HealthyYoshidaSpectralNegativity
open C1P2DefectControl
open C1P2BaseSeminormBound
open C1SameOwnerWeil
open C1SpectralSummability
open C1SpectralTailBound
open C1SpectralWeil
open scoped BigOperators

/-! The fields are exactly the raw construction witnesses consumed by later
same-owner G8 work.  No field mentions the health/sign package. -/

/-- Raw orbit-construction geometry for one selected healthy-owner test.

The selected test is retained together with its unscaled orbit factors and
the finite analytic certificates from which it was built.  The radius and
prime cutoff are attached to this exact test and its genuine convolution
square. -/
structure OrbitG8Geometry
    (rho : sourceNontrivialZeroSet) (g : CompactLogTest) where
  base : CompactLogTest
  base_support : Function.support base.test ⊆ Set.Ioo (-1 : Real) 1
  correction : CompactLogTest
  correction_support : Function.support correction.test ⊆
    Set.Ioo (-1 : Real) 1
  orbitIndex : Nat
  selected_owner_test :
    g = (selectedOwner base correction orbitIndex).sourceTest
  tailThreshold : Real
  tailAccuracy : Real
  tailStart : Nat
  threshold_le_dyadic : tailThreshold ≤ (2 : Real) ^ (tailStart + 1)
  zero_height_le_dyadic :
    2 * |rho.1.im| ≤ (2 : Real) ^ (tailStart + 1)
  zero_shell_before_tail : dyadicShellIndex |rho.1.im| < tailStart + 1
  tail_budget_below_multiplicity :
    4 * tailAccuracy ^ 2 * spectralMultiplicityConstant *
        (3 / 4 : Real) ^ tailStart < (xiMultiplicity rho : Real)
  raw_square_tail : FourthOrderSpectralTail
    (selectedOwner base correction orbitIndex).convolutionSquare
      rho.1 tailThreshold tailAccuracy
  raw_target_values :
    ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
      laplaceAt ((convolutionIterate base orbitIndex).convolution correction)
        w.1 = healthyUnscaledTargetValue rho.1 w
  minimal_interpolation :
    HealthyMinimalLaplaceRealizes rho.1
      (selectedOwner base correction orbitIndex).sourceTest
  centered_orbit_sum :
    (∑ u ∈ centeredFunctionalEquationOrbit rho.1,
      laplaceAt (selectedOwner base correction orbitIndex).convolutionSquare u)
        = -2
  square_zero_control :
    ∀ w : FiniteMellinNode
        (sourceNontrivialZerosInClosedBallFinset rho.1
          ((2 : Real) ^ (tailStart + 1) + 2 + dist (2 : Complex) rho.1) ∪
          (∅ : Finset Complex)),
      w.1 ∉ healthyUnscaledTargetNodes rho.1 →
        laplaceAt (selectedOwner base correction orbitIndex).convolutionSquare
          (w.1 - 1 / 2) = 0
  support_bound : Function.support g.test ⊆
    Set.Ioo (-((orbitIndex + 2 : Nat) : Real))
      (((orbitIndex + 2 : Nat) : Real))
  visible_prime_cutoff :
    ∀ q ∈ globalPrimeIndexSet g.convolutionSquare,
      (q : Real) < Real.exp (2 * ((orbitIndex + 2 : Nat) : Real))

/-! ### The finite owner in executable range form -/

/-- The support-derived visible-prime cutoff is an actual finite-range
owner, not only a real inequality.  This is the form consumed by finite
prime-power sums in the semi-local sign branch. -/
theorem visiblePrimeSet_subset_range_of_orbitG8Geometry
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    globalPrimeIndexSet g.convolutionSquare ⊆
      Finset.range
        (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1) := by
  intro q hq
  have hqexp := geometry.visible_prime_cutoff q hq
  have hceil :
      Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real)) ≤
        (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) : Real) :=
    Nat.le_ceil _
  have hqceil :
      (q : Real) <
        (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) : Real) :=
    hqexp.trans_le hceil
  have hqnat :
      q < Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) := by
    exact_mod_cast hqceil
  exact Finset.mem_range.mpr (by omega)

/-- The same owner can be used to rewrite the finite prime contribution over
the explicit range supplied by the orbit geometry. -/
theorem finitePrimeSum_eq_sum_range_of_orbitG8Geometry
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
  finitePrimeSum g.convolutionSquare =
      ∑ n ∈ Finset.range
        (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1),
        finitePrimeTerm g.convolutionSquare n := by
  unfold finitePrimeSum
  apply Finset.sum_subset
    (visiblePrimeSet_subset_range_of_orbitG8Geometry geometry)
  intro n _hnRange hnNotMem
  by_contra hterm
  apply hnNotMem
  have hcomplex : finitePrimeTermComplex g.convolutionSquare n ≠ 0 := by
    intro hzero
    apply hterm
    change (finitePrimeTermComplex g.convolutionSquare n).re = 0
    rw [hzero]
    simp
  exact (mem_globalPrimeIndexSet_iff g.convolutionSquare n).mpr
    ⟨finitePrimeTermComplex_nonzero_primePower
        g.convolutionSquare hcomplex, hcomplex⟩

/-! Package an already indexed raw construction.  The index is an input to
this constructor; all interpolation and tail data therefore remain attached
to the same selected owner. -/
theorem orbitG8Geometry_of_indexed_raw_construction
    (rho : sourceNontrivialZeroSet)
    (base correction : CompactLogTest) (orbitIndex : Nat)
    (tailThreshold tailAccuracy : Real) (tailStart : Nat)
    (hbaseSupport : Function.support base.test ⊆ Set.Ioo (-1 : Real) 1)
    (hcorrectionSupport : Function.support correction.test ⊆
      Set.Ioo (-1 : Real) 1)
    (hselectedSupport : Function.support
        (selectedOwner base correction orbitIndex).sourceTest.test ⊆
      Set.Ioo (-((orbitIndex + 2 : Nat) : Real))
        (((orbitIndex + 2 : Nat) : Real)))
    (hthreshold : tailThreshold ≤ (2 : Real) ^ (tailStart + 1))
    (hzeroHeight : 2 * |rho.1.im| ≤ (2 : Real) ^ (tailStart + 1))
    (htailBudget :
      4 * tailAccuracy ^ 2 * spectralMultiplicityConstant *
          (3 / 4 : Real) ^ tailStart < (xiMultiplicity rho : Real))
    (hrawSquareTail : FourthOrderSpectralTail
      (selectedOwner base correction orbitIndex).convolutionSquare
        rho.1 tailThreshold tailAccuracy)
    (hrawTargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt ((convolutionIterate base orbitIndex).convolution correction)
          w.1 = healthyUnscaledTargetValue rho.1 w)
    (hminimal : HealthyMinimalLaplaceRealizes rho.1
      (selectedOwner base correction orbitIndex).sourceTest)
    (horbitSum :
      (∑ u ∈ centeredFunctionalEquationOrbit rho.1,
        laplaceAt (selectedOwner base correction orbitIndex).convolutionSquare u)
        = -2)
    (hsquareZeros :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              ((2 : Real) ^ (tailStart + 1) + 2 + dist (2 : Complex) rho.1) ∪
            (∅ : Finset Complex)),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt (selectedOwner base correction orbitIndex).convolutionSquare
            (w.1 - 1 / 2) = 0) :
    Nonempty (OrbitG8Geometry rho
      (selectedOwner base correction orbitIndex).sourceTest) := by
  have himLt : |rho.1.im| < (2 : Real) ^ (tailStart + 1) := by
    have hpow : 0 < (2 : Real) ^ (tailStart + 1) := by positivity
    have himNonneg : 0 ≤ |rho.1.im| := abs_nonneg _
    nlinarith
  have hrhoShell : dyadicShellIndex |rho.1.im| < tailStart + 1 := by
    have hminimal := Nat.find_min'
      (exists_lt_two_pow_succ |rho.1.im|) himLt
    rw [← dyadicShellIndex] at hminimal
    omega
  let g : CompactLogTest :=
    (selectedOwner base correction orbitIndex).sourceTest
  have hprimeCutoff :
      ∀ q ∈ globalPrimeIndexSet g.convolutionSquare,
        (q : Real) < Real.exp (2 * ((orbitIndex + 2 : Nat) : Real)) := by
    intro q hq
    exact pinned_visiblePrimeCutoff_of_support g orbitIndex hselectedSupport hq
  refine ⟨?_⟩
  exact
    { base := base
      base_support := hbaseSupport
      correction := correction
      correction_support := hcorrectionSupport
      orbitIndex := orbitIndex
      selected_owner_test := rfl
      tailThreshold := tailThreshold
      tailAccuracy := tailAccuracy
      tailStart := tailStart
      threshold_le_dyadic := hthreshold
      zero_height_le_dyadic := hzeroHeight
      zero_shell_before_tail := hrhoShell
      tail_budget_below_multiplicity := htailBudget
      raw_square_tail := hrawSquareTail
      raw_target_values := hrawTargetValues
      minimal_interpolation := hminimal
      centered_orbit_sum := horbitSum
      square_zero_control := hsquareZeros
      support_bound := hselectedSupport
      visible_prime_cutoff := hprimeCutoff }

/-- The pinned orbit construction exports the raw G8 geometry package.

The proof uses only the unscaled orbit interpolation, the fourth-order tail,
and the support-derived prime cutoff.  It does not call the theorem that
constructs `HealthyYoshidaDetectorData`; in particular, no Weil sign is an
input to this package producer. -/
theorem exists_orbitG8Geometry_of_sourceNontrivialZero_right
    (rho : sourceNontrivialZeroSet)
    (hoff : rho.1.re ≠ 1 / 2)
    (_hright : (1 / 2 : Real) < rho.1.re) :
    ∃ g : CompactLogTest, Nonempty (OrbitG8Geometry rho g) := by
  obtain ⟨base, T, hbaseSupport, _hT, hconstruction⟩ :=
    exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets
      rho.1 rho.2 hoff ∅
      (baseLower := -(1 : Real)) (baseUpper := 1)
      (lower := -(1 : Real)) (upper := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (1 : Real) (by norm_num)
  obtain ⟨tailStart, hT, hrhoHeight, hsmall⟩ :=
    exists_dyadic_tail_start_with_budget_lt_xiMultiplicity T (1 : Real) rho
  let R : Real :=
    (2 : Real) ^ (tailStart + 1) + 2 + dist (2 : Complex) rho.1
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  obtain ⟨correction, _C, orbitIndex, hcorrectionSupport,
      hselectedSupport, htargetValues, hminimal, horbitSum, hsquareZeros,
      _hC, _hcenteredTail, hsquareTail⟩ := hconstruction R hR
  have hsquareZeros' :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              ((2 : Real) ^ (tailStart + 1) + 2 + dist (2 : Complex) rho.1) ∪
            (∅ : Finset Complex)),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt (selectedOwner base correction orbitIndex).convolutionSquare
            (w.1 - 1 / 2) = 0 := by
    simpa only [R] using hsquareZeros
  have hsupport : Function.support
      (selectedOwner base correction orbitIndex).sourceTest.test ⊆
        Set.Ioo (-((orbitIndex + 2 : Nat) : Real))
          (((orbitIndex + 2 : Nat) : Real)) := by
    intro x hx
    have h := hselectedSupport hx
    rcases h with ⟨hl, hu⟩
    constructor
    · norm_num [Nat.cast_add, Nat.cast_one] at hl ⊢
      linarith
    · norm_num [Nat.cast_add, Nat.cast_one] at hu ⊢
      linarith
  let g : CompactLogTest :=
    (selectedOwner base correction orbitIndex).sourceTest
  refine ⟨g, ?_⟩
  exact orbitG8Geometry_of_indexed_raw_construction
    rho base correction orbitIndex T 1 tailStart
    hbaseSupport hcorrectionSupport hsupport hT hrhoHeight
    (by simpa using hsmall) hsquareTail htargetValues hminimal horbitSum
    hsquareZeros'

/-! The all-index healthy assembly can now feed the indexed geometry package
directly.  The correction and its tail constant are fixed before the caller
chooses an orbit count; only the explicit remote-tail condition remains on n. -/
theorem exists_indexed_orbitG8Geometry_of_sourceNontrivialZero_right
    (rho : sourceNontrivialZeroSet)
    (hoff : rho.1.re ≠ 1 / 2)
    (_hright : (1 / 2 : Real) < rho.1.re) :
    ∃ base : CompactLogTest, ∃ T : Real,
      Function.support base.test ⊆ Set.Ioo (-1 : Real) 1 ∧
      0 ≤ T ∧
      ∃ correction : CompactLogTest, ∃ C : Real,
        Function.support correction.test ⊆ Set.Ioo (-1 : Real) 1 ∧
        0 ≤ C ∧
        ∀ orbitIndex : Nat,
          (6 * Real.pi) ^ 2 * ((1 / 2 : Real) ^ (orbitIndex + 1) * C) < 1 →
          ∃ g : CompactLogTest, Nonempty (OrbitG8Geometry rho g) := by
  obtain ⟨base, hbaseSupport, hbaseTargets, baseC, hbaseC, hbaseDecay⟩ :=
    exists_affine_base_with_unit_targets_and_quadratic_decay
      (healthyUnscaledTargetNodes rho.1)
      (lower := -(1 : Real)) (upper := 1) (by norm_num) (by norm_num)
  obtain ⟨T, hT, hbase⟩ :=
    exists_laplaceAt_vertical_half_contraction_of_quadratic_bound
      base baseC hbaseC hbaseDecay
  have hconstruction :=
    exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets_all_indices_of_base_data
      rho.1 rho.2 hoff ∅
      (baseLower := -(1 : Real)) (baseUpper := 1)
      (lower := -(1 : Real)) (upper := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (1 : Real) (by norm_num)
      base T hbaseSupport hbaseTargets hbase
  obtain ⟨tailStart, hTailThreshold, hrhoHeight, hTailBudget⟩ :=
    exists_dyadic_tail_start_with_budget_lt_xiMultiplicity T (1 : Real) rho
  let R : Real :=
    (2 : Real) ^ (tailStart + 1) + 2 + dist (2 : Complex) rho.1
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  obtain ⟨correction, C, hcorrectionSupport, hC, halln⟩ :=
    hconstruction R hR
  refine ⟨base, T, hbaseSupport, hT, correction, C,
    hcorrectionSupport, hC, ?_⟩
  intro orbitIndex hTail
  obtain ⟨hselectedSupport, htargetValues, hminimal, horbitSum, hrawZeros,
      htailSource, htailSquare⟩ := halln orbitIndex hTail
  have hsupport : Function.support
      (selectedOwner base correction orbitIndex).sourceTest.test ⊆
        Set.Ioo (-((orbitIndex + 2 : Nat) : Real))
          (((orbitIndex + 2 : Nat) : Real)) := by
    intro x hx
    have h := hselectedSupport hx
    rcases h with ⟨hl, hu⟩
    constructor
    · norm_num [Nat.cast_add, Nat.cast_one] at hl ⊢
      linarith
    · norm_num [Nat.cast_add, Nat.cast_one] at hu ⊢
      linarith
  have hsquareZeros :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              ((2 : Real) ^ (tailStart + 1) + 2 + dist (2 : Complex) rho.1) ∪
            (∅ : Finset Complex)),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt (selectedOwner base correction orbitIndex).convolutionSquare
            (w.1 - 1 / 2) = 0 := by
    simpa only [R] using hrawZeros
  have hsquareTail : FourthOrderSpectralTail
      (selectedOwner base correction orbitIndex).convolutionSquare
        rho.1 T 1 := htailSquare
  let g : CompactLogTest :=
    (selectedOwner base correction orbitIndex).sourceTest
  refine ⟨g, ?_⟩
  exact orbitG8Geometry_of_indexed_raw_construction
    rho base correction orbitIndex T 1 tailStart
    hbaseSupport hcorrectionSupport hsupport hTailThreshold hrhoHeight
    (by simpa using hTailBudget) hsquareTail htargetValues hminimal horbitSum
    hsquareZeros

/-- The raw orbit geometry and the strict healthy-detector package can be
    attached to the same selected owner.  This removes the possible mismatch
    between two separate existential constructions; it still supplies no
    semi-local sign. -/
theorem healthyDetectorData_of_orbitG8Geometry
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re) :
    HealthyYoshidaDetectorData rho.1 g := by
  rw [geometry.selected_owner_test]
  apply selectedOwner_healthyDetectorData_of_closedBall_square_zero_control_and_fourthOrderTail
    geometry.base geometry.correction geometry.orbitIndex rho hoff hright
    geometry.tailThreshold geometry.tailAccuracy geometry.raw_square_tail
    geometry.tailStart geometry.threshold_le_dyadic geometry.zero_height_le_dyadic
    geometry.zero_shell_before_tail (∅ : Finset Complex)
    geometry.raw_target_values
  · intro w hw
    simpa using geometry.square_zero_control w hw
  · exact geometry.tail_budget_below_multiplicity

theorem exists_healthyOrbitG8Geometry_of_sourceNontrivialZero_right
    (rho : sourceNontrivialZeroSet)
    (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re) :
    ∃ g : CompactLogTest, ∃ geometry : OrbitG8Geometry rho g,
      HealthyYoshidaDetectorData rho.1 g := by
  obtain ⟨g, ⟨geometry⟩⟩ :=
    exists_orbitG8Geometry_of_sourceNontrivialZero_right rho hoff hright
  refine ⟨g, geometry, ?_⟩
  exact healthyDetectorData_of_orbitG8Geometry geometry hoff hright

end C1G8R0OrbitGeometry
end Source
end ConnesWeilRH
