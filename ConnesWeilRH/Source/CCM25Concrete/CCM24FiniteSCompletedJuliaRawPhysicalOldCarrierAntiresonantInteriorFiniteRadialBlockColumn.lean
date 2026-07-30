/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryReadout
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A uniform finite radial-block column

Proof 612 recovers each radial boundary block separately from the raw Bone 1
column.  The geometric readout later sums those blocks in the ambient carrier.
This module retains the first `N` Euler-weighted blocks in the orthogonal
`PiLp 2` carrier before any summation:

```text
raw antiresonant column
  -> (q^(n+1) B_n)_(n < N)
  -> (q^(n+1) C V^n newFrame)_(n < N).
```

The complete column readout has norm at most `32`, uniformly in the visible
prime and in `N`.  Thus later compact-window producers may address all needed
radial cells at once without paying either a cardinality factor or the raw
`q^(-1/2)` loss of an unweighted block.  This controls only the radial block
column; it does not identify the second-support/prolate branch with it.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteRadialBlockColumn

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryReadout
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Orthogonal finite columns -/

/-- The first `N` Euler-weighted radial readouts, retained as orthogonal
coordinates. -/
noncomputable def finitePrimeEulerRadialGeometricReadoutColumn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (N : ℕ) :
    finiteSCarrier →L[ℂ]
      PiLp 2 (fun _ : Fin N => finiteSCarrier) :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin N => finiteSCarrier)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i : Fin N =>
      primeEulerRadialGeometricReadoutTerm lambda p i)

@[simp]
theorem finitePrimeEulerRadialGeometricReadoutColumn_apply
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (N : ℕ)
    (x : finiteSCarrier) (i : Fin N) :
    finitePrimeEulerRadialGeometricReadoutColumn lambda p N x i =
      primeEulerRadialGeometricReadoutTerm lambda p i x := by
  rfl

/-- The matching first `N` Euler-weighted physical boundary blocks on one
actual suffix frame. -/
noncomputable def finitePrimeEulerRadialGeometricBoundaryColumn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : ℕ) :
    sourceSoninCarrier lambda →L[ℂ]
      PiLp 2 (fun _ : Fin N => finiteSCarrier) :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin N => finiteSCarrier)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i : Fin N =>
      primeEulerRadialGeometricBoundaryTerm lambda p i ∘L
        newSuffixFrame lambda S)

@[simp]
theorem finitePrimeEulerRadialGeometricBoundaryColumn_apply
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : ℕ)
    (x : sourceSoninCarrier lambda) (i : Fin N) :
    finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N x i =
      primeEulerRadialGeometricBoundaryTerm lambda p i
        (newSuffixFrame lambda S x) := by
  rfl

/-! ## Exact readout -/

/-- All first `N` weighted radial cells are read from the same raw
antiresonant column.  Equality is proved coordinatewise before taking a norm. -/
theorem finiteRadialGeometricReadoutColumn_comp_ambientLossColumn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : ℕ) :
    finitePrimeEulerRadialGeometricReadoutColumn lambda p N ∘L
        newFrameAntiresonantColumn lambda p S =
      finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  have hblock := DFunLike.congr_fun
    (newFrameAntiresonantRadialBlockReadout_comp_column
      lambda p S i) x
  simp only [finitePrimeEulerRadialGeometricReadoutColumn_apply,
    finitePrimeEulerRadialGeometricBoundaryColumn_apply,
    primeEulerRadialGeometricReadoutTerm,
    primeEulerRadialGeometricBoundaryTerm,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
  exact congrArg
    (fun y : finiteSCarrier =>
      ((ccm24PrimeEulerCoefficient p : ℂ) ^ ((i : ℕ) + 1)) • y) hblock

/-! ## A block-count-independent norm bound -/

/-- The `PiLp 2` norm square is the sum of the individual weighted block
energies. -/
theorem norm_sq_finitePrimeEulerRadialGeometricReadoutColumn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (N : ℕ)
    (x : finiteSCarrier) :
    ‖finitePrimeEulerRadialGeometricReadoutColumn lambda p N x‖ ^ 2 =
      ∑ i : Fin N,
        ‖primeEulerRadialGeometricReadoutTerm lambda p i x‖ ^ 2 := by
  change ‖WithLp.toLp 2
      (fun i : Fin N =>
        finitePrimeEulerRadialGeometricReadoutColumn lambda p N x i)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [finitePrimeEulerRadialGeometricReadoutColumn_apply]

/-- The finite sum of the universal coordinate majorants never exceeds the
already computed infinite geometric sum `32`. -/
theorem sum_finiteRadialGeometricMajorant_le_thirtyTwo (N : ℕ) :
    (∑ i : Fin N,
        2 * ((((i : ℕ) + 1 : ℕ) : ℝ) *
          (3 / 4 : ℝ) ^ (i : ℕ))) ≤ 32 := by
  let sequence : ℕ → ℝ := fun n =>
    2 * (((n + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ n)
  have hsummable : Summable sequence :=
    summable_linear_three_quarters.mul_left 2
  calc
    (∑ i : Fin N,
        2 * ((((i : ℕ) + 1 : ℕ) : ℝ) *
          (3 / 4 : ℝ) ^ (i : ℕ))) =
        ∑ n ∈ Finset.range N, sequence n := by
      simpa only [sequence] using
        (Fin.sum_univ_eq_sum_range sequence N)
    _ ≤ ∑' n : ℕ, sequence n :=
      hsummable.sum_le_tsum (Finset.range N) (fun n hn => by positivity)
    _ = 2 * (∑' n : ℕ,
        ((n + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ n) := by
      dsimp only [sequence]
      rw [tsum_mul_left]
    _ = 32 := by rw [tsum_linear_three_quarters]; norm_num

/-- The finite orthogonal readout has pointwise norm cost at most `32`, with
no dependence on the prime or on the number of retained blocks. -/
theorem norm_finitePrimeEulerRadialGeometricReadoutColumn_apply_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (N : ℕ)
    (x : finiteSCarrier) :
    ‖finitePrimeEulerRadialGeometricReadoutColumn lambda p N x‖ ≤
      32 * ‖x‖ := by
  let majorant : Fin N → ℝ := fun i =>
    2 * ((((i : ℕ) + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ (i : ℕ))
  have hmajorant_nonneg : ∀ i : Fin N, 0 ≤ majorant i := by
    intro i
    dsimp only [majorant]
    positivity
  have hcoord : ∀ i : Fin N,
      ‖primeEulerRadialGeometricReadoutTerm lambda p i x‖ ≤
        majorant i * ‖x‖ := by
    intro i
    calc
      ‖primeEulerRadialGeometricReadoutTerm lambda p i x‖ ≤
          ‖primeEulerRadialGeometricReadoutTerm lambda p i‖ * ‖x‖ :=
        (primeEulerRadialGeometricReadoutTerm lambda p i).le_opNorm x
      _ ≤ majorant i * ‖x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
        simpa only [majorant, mul_assoc] using
          norm_primeEulerRadialGeometricReadoutTerm_le lambda p i
  have hsum : (∑ i : Fin N, majorant i) ≤ 32 := by
    simpa only [majorant] using
      sum_finiteRadialGeometricMajorant_le_thirtyTwo N
  have hsum_scaled :
      (∑ i : Fin N, majorant i * ‖x‖) ≤ 32 * ‖x‖ := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hsum (norm_nonneg x)
  have henergy :
      ‖finitePrimeEulerRadialGeometricReadoutColumn lambda p N x‖ ^ 2 ≤
        (32 * ‖x‖) ^ 2 := by
    rw [norm_sq_finitePrimeEulerRadialGeometricReadoutColumn]
    calc
      (∑ i : Fin N,
          ‖primeEulerRadialGeometricReadoutTerm lambda p i x‖ ^ 2) ≤
          ∑ i : Fin N, (majorant i * ‖x‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (hmajorant_nonneg i) (norm_nonneg x))).2 (hcoord i)
      _ ≤ (∑ i : Fin N, majorant i * ‖x‖) ^ 2 := by
        exact Finset.sum_sq_le_sq_sum_of_nonneg
          (s := Finset.univ)
          (f := fun i : Fin N => majorant i * ‖x‖)
          (fun i hi => mul_nonneg (hmajorant_nonneg i) (norm_nonneg x))
      _ ≤ (32 * ‖x‖) ^ 2 :=
        (sq_le_sq₀
          (Finset.sum_nonneg fun i hi =>
            mul_nonneg (hmajorant_nonneg i) (norm_nonneg x))
          (mul_nonneg (by norm_num) (norm_nonneg x))).2 hsum_scaled
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by norm_num) (norm_nonneg x))).1 henergy

/-- Operator-norm form of the uniform finite-column estimate. -/
theorem norm_finitePrimeEulerRadialGeometricReadoutColumn_le_thirtyTwo
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (N : ℕ) :
    ‖finitePrimeEulerRadialGeometricReadoutColumn lambda p N‖ ≤ 32 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [mul_comm] using
    norm_finitePrimeEulerRadialGeometricReadoutColumn_apply_le lambda p N x

/-- Consequently the complete first-`N` physical boundary column is bounded
by the same raw right-co-defect column, uniformly in `(p,S,N)`. -/
theorem norm_finitePrimeEulerRadialGeometricBoundaryColumn_apply_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : ℕ)
    (x : sourceSoninCarrier lambda) :
    ‖finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N x‖ ≤
      32 * ‖newFrameAntiresonantColumn lambda p S x‖ := by
  have hfactor := DFunLike.congr_fun
    (finiteRadialGeometricReadoutColumn_comp_ambientLossColumn
      lambda p S N) x
  rw [← hfactor]
  exact
    norm_finitePrimeEulerRadialGeometricReadoutColumn_apply_le lambda p N
      (newFrameAntiresonantColumn lambda p S x)

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteRadialBlockColumn
end CCM25Concrete
end Source
end ConnesWeilRH
