/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Julia defect-row Bessel calculus

This module assembles pointwise Julia colligation steps into one defect row.
It proves the exact survivor/defect energy telescope and the weighted Bessel
bound for the Gram-normalized range-sine outputs.  The theorem is generic: it
does not assume or manufacture the still-missing finite-S detector dual row.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSJuliaBessel

open scoped BigOperators InnerProduct InnerProductSpace
open RCLike

variable {H G : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- One pulled-back Julia step on a fixed source carrier.

`pythagorean` is the transfer/defect colligation identity.  The range-sine
field is kept separate: its weighted square is bounded by the same defect
slot, which is the post-Gram prime-square gain from Proof 350. -/
structure JuliaDefectStep (H G : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] where
  transfer : H →L[ℂ] H
  defect : H →L[ℂ] H
  rangeSine : H →L[ℂ] G
  weight : ℝ
  weight_nonneg : 0 ≤ weight
  pythagorean : ∀ x : H,
    ‖transfer x‖ ^ 2 + ‖defect x‖ ^ 2 = ‖x‖ ^ 2
  rangeSine_weighted_le_defect : ∀ x : H,
    weight * ‖rangeSine x‖ ^ 2 ≤ ‖defect x‖ ^ 2

/-!
The defect is not an arbitrary auxiliary row.  For a genuine contractive
transfer `F`, its canonical Julia defect is

```text
D_F = (I - F† F)^(1/2).
```

The continuous functional calculus supplies the square root on the actual
Hilbert carrier.  This constructor is deliberately placed below the generic
row structure: source code must still prove the range-sine inequality, but it
can no longer satisfy the Pythagorean field with an unrelated bookkeeping
map.
-/
noncomputable def canonicalJuliaDefect
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (transfer : H →L[ℂ] H)
    (hcontract : transfer† ∘L transfer ≤ ContinuousLinearMap.id ℂ H) :
    H →L[ℂ] H :=
  CFC.sqrt (ContinuousLinearMap.id ℂ H - transfer† ∘L transfer)

theorem canonicalJuliaDefect_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (transfer : H →L[ℂ] H)
    (hcontract : transfer† ∘L transfer ≤ ContinuousLinearMap.id ℂ H) :
    canonicalJuliaDefect transfer hcontract ∘L
        canonicalJuliaDefect transfer hcontract =
      ContinuousLinearMap.id ℂ H - transfer† ∘L transfer := by
  rw [canonicalJuliaDefect, ← ContinuousLinearMap.mul_def]
  exact CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hcontract)

theorem adjoint_comp_self_le_id_of_norm_le_one
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (transfer : H →L[ℂ] K) (htransfer : ‖transfer‖ ≤ 1) :
    transfer† ∘L transfer ≤ ContinuousLinearMap.id ℂ H := by
  have hgram_nonneg :
      (0 : H →L[ℂ] H) ≤ transfer† ∘L transfer :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self transfer)
  have hgram_norm : ‖transfer† ∘L transfer‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_adjoint_comp_self]
    nlinarith [htransfer, norm_nonneg transfer]
  have hgram_le_one : transfer† ∘L transfer ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg
      (transfer† ∘L transfer) hgram_nonneg).mp hgram_norm
  simpa only [ContinuousLinearMap.one_def] using hgram_le_one

theorem norm_le_one_of_adjoint_comp_self_le_id
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (transfer : H →L[ℂ] H)
    (hcontract : transfer† ∘L transfer ≤ ContinuousLinearMap.id ℂ H) :
    ‖transfer‖ ≤ 1 := by
  have hgram_nonneg :
      (0 : H →L[ℂ] H) ≤ transfer† ∘L transfer :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self transfer)
  have hgram_norm : ‖transfer† ∘L transfer‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg
      (transfer† ∘L transfer) hgram_nonneg).mpr hcontract
  rw [ContinuousLinearMap.norm_adjoint_comp_self] at hgram_norm
  apply (sq_le_sq₀ (norm_nonneg transfer) (by norm_num)).mp
  nlinarith [hgram_norm]

theorem canonicalJuliaDefect_adjoint_comp_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (transfer : H →L[ℂ] H)
    (hcontract : transfer† ∘L transfer ≤ ContinuousLinearMap.id ℂ H) :
    (canonicalJuliaDefect transfer hcontract)† ∘L
        canonicalJuliaDefect transfer hcontract =
      ContinuousLinearMap.id ℂ H - transfer† ∘L transfer := by
  have hnonneg :
      (0 : H →L[ℂ] H) ≤ canonicalJuliaDefect transfer hcontract :=
    CFC.sqrt_nonneg _
  have hself : IsSelfAdjoint (canonicalJuliaDefect transfer hcontract) :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mp hnonneg |>.isSelfAdjoint
  rw [hself.adjoint_eq]
  exact canonicalJuliaDefect_sq transfer hcontract

theorem canonicalJuliaDefect_isSelfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (transfer : H →L[ℂ] H)
    (hcontract : transfer† ∘L transfer ≤ ContinuousLinearMap.id ℂ H) :
    IsSelfAdjoint (canonicalJuliaDefect transfer hcontract) := by
  have hnonneg :
      (0 : H →L[ℂ] H) ≤ canonicalJuliaDefect transfer hcontract :=
    CFC.sqrt_nonneg _
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp hnonneg |>.isSelfAdjoint

theorem canonicalJuliaDefect_pythagorean
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (transfer : H →L[ℂ] H)
    (hcontract : transfer† ∘L transfer ≤ ContinuousLinearMap.id ℂ H)
    (x : H) :
    ‖transfer x‖ ^ 2 +
        ‖canonicalJuliaDefect transfer hcontract x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hgram := canonicalJuliaDefect_adjoint_comp_self transfer hcontract
  have hsum :
      transfer† ∘L transfer +
          (canonicalJuliaDefect transfer hcontract)† ∘L
            canonicalJuliaDefect transfer hcontract =
        ContinuousLinearMap.id ℂ H := by
    rw [hgram]
    apply ContinuousLinearMap.ext
    intro y
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply]
    abel
  calc
    ‖transfer x‖ ^ 2 +
        ‖canonicalJuliaDefect transfer hcontract x‖ ^ 2 =
      re ⟪(transfer† ∘L transfer) x, x⟫_ℂ +
        re ⟪((canonicalJuliaDefect transfer hcontract)† ∘L
          canonicalJuliaDefect transfer hcontract) x, x⟫_ℂ := by
            rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left,
              ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
    _ = re ⟪(transfer† ∘L transfer +
          (canonicalJuliaDefect transfer hcontract)† ∘L
            canonicalJuliaDefect transfer hcontract) x, x⟫_ℂ := by
          simp only [ContinuousLinearMap.add_apply, inner_add_left, map_add,
            map_add, Complex.add_re]
    _ = re ⟪x, x⟫_ℂ := by rw [hsum]; rfl
    _ = ‖x‖ ^ 2 := inner_self_eq_norm_sq x

/-!
This is the source-facing constructor for one real Julia step.  The only
remaining analytic input is the range-sine estimate.  In particular, the
defect and its exact energy identity are generated from the transfer
contraction rather than supplied as independent witnesses.
-/
structure CanonicalJuliaStepData (H G : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] where
  transfer : H →L[ℂ] H
  rangeSine : H →L[ℂ] G
  weight : ℝ
  weight_nonneg : 0 ≤ weight
  transfer_contract : transfer† ∘L transfer ≤ ContinuousLinearMap.id ℂ H
  rangeSine_weighted_le : ∀ x : H,
    weight * ‖rangeSine x‖ ^ 2 ≤
      ‖canonicalJuliaDefect transfer transfer_contract x‖ ^ 2

noncomputable def CanonicalJuliaStepData.toJuliaDefectStep
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : CanonicalJuliaStepData H G) : JuliaDefectStep H G :=
  { transfer := data.transfer
    defect := canonicalJuliaDefect data.transfer data.transfer_contract
    rangeSine := data.rangeSine
    weight := data.weight
    weight_nonneg := data.weight_nonneg
    pythagorean := canonicalJuliaDefect_pythagorean data.transfer
      data.transfer_contract
    rangeSine_weighted_le_defect := data.rangeSine_weighted_le }

@[simp]
theorem CanonicalJuliaStepData.toJuliaDefectStep_transfer
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : CanonicalJuliaStepData H G) :
    data.toJuliaDefectStep.transfer = data.transfer :=
  rfl

@[simp]
theorem CanonicalJuliaStepData.toJuliaDefectStep_rangeSine
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : CanonicalJuliaStepData H G) :
    data.toJuliaDefectStep.rangeSine = data.rangeSine :=
  rfl

/-!
The adjoint transfer carries the left co-defect.  If `F` is contractive, then
the canonical Julia defect of `F†` is

```text
  (I - F F†)^(1/2),
```

which is the left, or co-, defect of `F`.  The range-sine row is set to zero
because this adapter is used only to expose the co-defect history; the
physical detector readout is supplied later as a separate bounded map.
-/
noncomputable def CanonicalJuliaStepData.toAdjointCoDefectStep
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : CanonicalJuliaStepData H G) : JuliaDefectStep H H := by
  have hnorm : ‖data.transfer‖ ≤ 1 :=
    norm_le_one_of_adjoint_comp_self_le_id data.transfer
      data.transfer_contract
  have hadjoint_norm : ‖data.transfer†‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hnorm
  let transferContract :=
    adjoint_comp_self_le_id_of_norm_le_one ((data.transfer)†) hadjoint_norm
  exact
    { transfer := (data.transfer)†
      defect := canonicalJuliaDefect ((data.transfer)†) transferContract
      rangeSine := 0
      weight := 0
      weight_nonneg := by norm_num
      pythagorean := canonicalJuliaDefect_pythagorean ((data.transfer)†)
        transferContract
      rangeSine_weighted_le_defect := by
        intro x
        simp }

@[simp]
theorem CanonicalJuliaStepData.toAdjointCoDefectStep_transfer
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : CanonicalJuliaStepData H G) :
    data.toAdjointCoDefectStep.transfer = data.transfer† := by
  simp [CanonicalJuliaStepData.toAdjointCoDefectStep]

/-- The survivor transfer after all Julia steps, in chronological order. -/
def juliaSurvivor :
    List (JuliaDefectStep H G) → H →L[ℂ] H
  | [] => ContinuousLinearMap.id ℂ H
  | step :: steps => juliaSurvivor steps ∘L step.transfer

/-- Sum of the squared defect outputs along the pulled-back transfer path. -/
def juliaDefectEnergy :
    List (JuliaDefectStep H G) → H → ℝ
  | [], _ => 0
  | step :: steps, x =>
      ‖step.defect x‖ ^ 2 +
        juliaDefectEnergy steps (step.transfer x)

/-- Weighted sum of the squared Gram-normalized range-sine outputs. -/
def juliaRangeEnergy :
    List (JuliaDefectStep H G) → H → ℝ
  | [], _ => 0
  | step :: steps, x =>
      step.weight * ‖step.rangeSine x‖ ^ 2 +
        juliaRangeEnergy steps (step.transfer x)

/-!
The scalar square-root is part of the column, rather than part of a later
estimate.  This is the finite-dimensional `L²` realization of the weighted
range-sine row.
-/
noncomputable def juliaRangeStepMap
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (step : JuliaDefectStep H G) : H →L[ℂ] G :=
  (Real.sqrt step.weight : ℂ) • step.rangeSine

/-!
`juliaRangeMaps steps` is the actual finite column before it is packed into a
`PiLp`.  The tail maps are precomposed by the transfer of the current step,
so coordinate `n` is evaluated on exactly the survivor entering that step.
-/
noncomputable def juliaRangeMaps
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] :
    List (JuliaDefectStep H G) → List (H →L[ℂ] G)
  | [] => []
  | step :: steps =>
      juliaRangeStepMap step ::
        (juliaRangeMaps steps).map (fun f => f ∘L step.transfer)

theorem juliaRangeMaps_length
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) :
    (juliaRangeMaps steps).length = steps.length := by
  induction steps with
  | nil => rfl
  | cons step steps ih => simp [juliaRangeMaps, ih]

/-!
The carrier is `PiLp 2`, not the ordinary product norm.  This is important:
the norm square of the column is the sum of the weighted coordinates, which
is the exact Julia energy rather than a cardinality-dependent sup-norm bound.
-/
noncomputable def juliaRangeColumn
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) :
    H →L[ℂ] PiLp 2 (fun _ : Fin steps.length => G) :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin steps.length => G)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i =>
      (juliaRangeMaps steps).get
        ⟨i, by
          rw [juliaRangeMaps_length]
          exact i.isLt⟩)

@[simp]
theorem juliaRangeColumn_apply
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) (x : H)
    (i : Fin steps.length) :
    juliaRangeColumn steps x i =
      (juliaRangeMaps steps).get
        ⟨i, by
          rw [juliaRangeMaps_length]
          exact i.isLt⟩ x := by
  rfl

/-!
The co-defect row is the left-hand column in the Schur intertwinement
telescope.  It is different from the weighted range-sine column: no
source-specific visibility statement is needed to form it, and its squared
`PiLp` norm is exactly `juliaDefectEnergy`.
-/
noncomputable def juliaDefectMaps
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] :
    List (JuliaDefectStep H G) → List (H →L[ℂ] H)
  | [] => []
  | step :: steps =>
      step.defect ::
        (juliaDefectMaps steps).map (fun f => f ∘L step.transfer)

theorem juliaDefectMaps_length
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) :
    (juliaDefectMaps steps).length = steps.length := by
  induction steps with
  | nil => rfl
  | cons step steps ih => simp [juliaDefectMaps, ih]

/-!
The finite direct-sum carrier for the complete co-defect history.  Tail
coordinates are precomposed by the current transfer, exactly as in the
survivor recursion.
-/
noncomputable def juliaDefectColumn
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) :
    H →L[ℂ] PiLp 2 (fun _ : Fin steps.length => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin steps.length => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i =>
      (juliaDefectMaps steps).get
        ⟨i, by
          rw [juliaDefectMaps_length]
          exact i.isLt⟩)

@[simp]
theorem juliaDefectColumn_apply
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) (x : H)
    (i : Fin steps.length) :
    juliaDefectColumn steps x i =
      (juliaDefectMaps steps).get
        ⟨i, by
          rw [juliaDefectMaps_length]
          exact i.isLt⟩ x := by
  rfl

theorem juliaDefectMaps_normSq_sum_eq
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) (x : H) :
    ((juliaDefectMaps steps).map (fun f => ‖f x‖ ^ 2)).sum =
      juliaDefectEnergy steps x := by
  induction steps generalizing x with
  | nil => simp [juliaDefectMaps, juliaDefectEnergy]
  | cons step steps ih =>
      simp only [juliaDefectMaps, juliaDefectEnergy, List.map_cons,
        List.sum_cons]
      have hmap :
          List.map (fun f => ‖f x‖ ^ 2)
              (List.map (fun f => f ∘L step.transfer)
                (juliaDefectMaps steps)) =
            List.map (fun f => ‖f (step.transfer x)‖ ^ 2)
              (juliaDefectMaps steps) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro f hf
        simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
      rw [hmap, ih]

theorem juliaDefectColumn_normSq_eq
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) (x : H) :
    ‖juliaDefectColumn steps x‖ ^ 2 = juliaDefectEnergy steps x := by
  change ‖WithLp.toLp 2
      (fun i : Fin steps.length => juliaDefectColumn steps x i)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [juliaDefectColumn_apply, List.get_eq_getElem]
  let hlen := juliaDefectMaps_length steps
  have hsum :
      ∑ i : Fin steps.length,
          ‖(juliaDefectMaps steps).get
            ⟨i, by
              rw [hlen]
              exact i.isLt⟩ x‖ ^ 2 =
        ((juliaDefectMaps steps).map (fun f => ‖f x‖ ^ 2)).sum := by
    calc
      ∑ i : Fin steps.length,
          ‖(juliaDefectMaps steps).get
            ⟨i, by
              rw [hlen]
              exact i.isLt⟩ x‖ ^ 2 =
          ∑ i : Fin (juliaDefectMaps steps).length,
            ‖(juliaDefectMaps steps).get i x‖ ^ 2 := by
        simpa [hlen] using
          (Equiv.sum_comp (finCongr hlen.symm)
            (fun i : Fin (juliaDefectMaps steps).length =>
              ‖(juliaDefectMaps steps).get i x‖ ^ 2))
      _ = ((juliaDefectMaps steps).map (fun f => ‖f x‖ ^ 2)).sum := by
        simpa only [List.get_eq_getElem] using
          (Fin.sum_univ_fun_getElem (juliaDefectMaps steps)
            (fun f : H →L[ℂ] H => ‖f x‖ ^ 2))
  calc
    ∑ i : Fin steps.length,
        ‖(juliaDefectMaps steps).get
          ⟨i, by
            rw [juliaDefectMaps_length]
            exact i.isLt⟩ x‖ ^ 2 =
        ((juliaDefectMaps steps).map (fun f => ‖f x‖ ^ 2)).sum := hsum
    _ = juliaDefectEnergy steps x := juliaDefectMaps_normSq_sum_eq steps x

theorem juliaRangeStepMap_normSq
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (step : JuliaDefectStep H G) (x : H) :
    ‖juliaRangeStepMap step x‖ ^ 2 =
      step.weight * ‖step.rangeSine x‖ ^ 2 := by
  calc
    ‖juliaRangeStepMap step x‖ ^ 2 =
        ‖(Real.sqrt step.weight : ℂ)‖ ^ 2 *
          ‖step.rangeSine x‖ ^ 2 := by
      rw [juliaRangeStepMap, ContinuousLinearMap.smul_apply, norm_smul,
        mul_pow]
    _ = step.weight * ‖step.rangeSine x‖ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt step.weight_nonneg]

theorem juliaRangeMaps_normSq_sum_eq
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) (x : H) :
    ((juliaRangeMaps steps).map (fun f => ‖f x‖ ^ 2)).sum =
      juliaRangeEnergy steps x := by
  induction steps generalizing x with
  | nil => simp [juliaRangeMaps, juliaRangeEnergy]
  | cons step steps ih =>
      simp only [juliaRangeMaps, juliaRangeEnergy, List.map_cons,
        List.sum_cons]
      have hmap :
          List.map (fun f => ‖f x‖ ^ 2)
              (List.map (fun f => f ∘L step.transfer)
                (juliaRangeMaps steps)) =
            List.map (fun f => ‖f (step.transfer x)‖ ^ 2)
              (juliaRangeMaps steps) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro f hf
        simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
      rw [juliaRangeStepMap_normSq, hmap, ih]

theorem juliaRangeColumn_normSq_eq
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) (x : H) :
    ‖juliaRangeColumn steps x‖ ^ 2 = juliaRangeEnergy steps x := by
  change ‖WithLp.toLp 2
      (fun i : Fin steps.length => juliaRangeColumn steps x i)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [juliaRangeColumn_apply, List.get_eq_getElem]
  let hlen := juliaRangeMaps_length steps
  have hsum :
      ∑ i : Fin steps.length,
          ‖(juliaRangeMaps steps).get
            ⟨i, by
              rw [hlen]
              exact i.isLt⟩ x‖ ^ 2 =
        ((juliaRangeMaps steps).map (fun f => ‖f x‖ ^ 2)).sum := by
    calc
      ∑ i : Fin steps.length,
          ‖(juliaRangeMaps steps).get
            ⟨i, by
              rw [hlen]
              exact i.isLt⟩ x‖ ^ 2 =
          ∑ i : Fin (juliaRangeMaps steps).length,
            ‖(juliaRangeMaps steps).get i x‖ ^ 2 := by
        simpa [hlen] using
          (Equiv.sum_comp (finCongr hlen.symm)
            (fun i : Fin (juliaRangeMaps steps).length =>
              ‖(juliaRangeMaps steps).get i x‖ ^ 2))
      _ = ((juliaRangeMaps steps).map (fun f => ‖f x‖ ^ 2)).sum := by
        simpa only [List.get_eq_getElem] using
          (Fin.sum_univ_fun_getElem (juliaRangeMaps steps)
            (fun f : H →L[ℂ] G => ‖f x‖ ^ 2))
  calc
    ∑ i : Fin steps.length,
        ‖(juliaRangeMaps steps).get
          ⟨i, by
            rw [juliaRangeMaps_length]
            exact i.isLt⟩ x‖ ^ 2 =
        ((juliaRangeMaps steps).map (fun f => ‖f x‖ ^ 2)).sum := hsum
    _ = juliaRangeEnergy steps x := juliaRangeMaps_normSq_sum_eq steps x

theorem juliaDefectEnergy_nonneg
    (steps : List (JuliaDefectStep H G)) (x : H) :
    0 ≤ juliaDefectEnergy steps x := by
  induction steps generalizing x with
  | nil => simp [juliaDefectEnergy]
  | cons step steps ih =>
      simp only [juliaDefectEnergy]
      exact add_nonneg (sq_nonneg ‖step.defect x‖)
        (ih (step.transfer x))

theorem juliaRangeEnergy_nonneg
    (steps : List (JuliaDefectStep H G)) (x : H) :
    0 ≤ juliaRangeEnergy steps x := by
  induction steps generalizing x with
  | nil => simp [juliaRangeEnergy]
  | cons step steps ih =>
      simp only [juliaRangeEnergy]
      exact add_nonneg
        (mul_nonneg step.weight_nonneg (sq_nonneg ‖step.rangeSine x‖))
        (ih (step.transfer x))

/-- Exact Pythagorean telescope: every Julia defect slot plus the final
survivor has the source norm square. -/
theorem juliaDefectEnergy_add_survivor_normSq
    (steps : List (JuliaDefectStep H G)) (x : H) :
    juliaDefectEnergy steps x + ‖juliaSurvivor steps x‖ ^ 2 = ‖x‖ ^ 2 := by
  induction steps generalizing x with
  | nil => simp [juliaDefectEnergy, juliaSurvivor]
  | cons step steps ih =>
      simp only [juliaDefectEnergy, juliaSurvivor,
        ContinuousLinearMap.comp_apply]
      calc
        ‖step.defect x‖ ^ 2 + juliaDefectEnergy steps (step.transfer x) +
            ‖juliaSurvivor steps (step.transfer x)‖ ^ 2 =
          ‖step.defect x‖ ^ 2 +
            (juliaDefectEnergy steps (step.transfer x) +
              ‖juliaSurvivor steps (step.transfer x)‖ ^ 2) := by
                rw [add_assoc]
        _ = ‖step.defect x‖ ^ 2 + ‖step.transfer x‖ ^ 2 := by
              rw [ih (step.transfer x)]
        _ = ‖x‖ ^ 2 := by
              simpa only [add_comm] using step.pythagorean x

theorem juliaDefectEnergy_le_normSq
    (steps : List (JuliaDefectStep H G)) (x : H) :
    juliaDefectEnergy steps x ≤ ‖x‖ ^ 2 := by
  rw [← juliaDefectEnergy_add_survivor_normSq steps x]
  exact le_add_of_nonneg_right (sq_nonneg ‖juliaSurvivor steps x‖)

theorem juliaDefectColumn_normSq_le_normSq
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) (x : H) :
    ‖juliaDefectColumn steps x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [juliaDefectColumn_normSq_eq]
  exact juliaDefectEnergy_le_normSq steps x

theorem tsum_juliaDefectColumn_normSq_le
    {ι K H G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (basis : HilbertBasis ι ℂ K)
    (steps : List (JuliaDefectStep H G)) (operator : K →L[ℂ] H)
    (hoperator : Summable fun i => ‖operator (basis i)‖ ^ 2) :
    ∑' i, ‖juliaDefectColumn steps (operator (basis i))‖ ^ 2 ≤
      ∑' i, ‖operator (basis i)‖ ^ 2 := by
  have henergy : Summable (fun i => juliaDefectEnergy steps
      (operator (basis i))) :=
    Summable.of_nonneg_of_le
      (fun i => juliaDefectEnergy_nonneg steps (operator (basis i)))
      (fun i => juliaDefectEnergy_le_normSq steps (operator (basis i)))
      hoperator
  simpa only [juliaDefectColumn_normSq_eq] using
    henergy.tsum_le_tsum
      (fun i => juliaDefectEnergy_le_normSq steps (operator (basis i)))
      hoperator

/-- The weighted range-sine row is dominated stepwise by the exact Julia
defect row before any summation or absolute value. -/
theorem juliaRangeEnergy_le_defectEnergy
    (steps : List (JuliaDefectStep H G)) (x : H) :
    juliaRangeEnergy steps x ≤ juliaDefectEnergy steps x := by
  induction steps generalizing x with
  | nil => simp [juliaRangeEnergy, juliaDefectEnergy]
  | cons step steps ih =>
      simp only [juliaRangeEnergy, juliaDefectEnergy]
      exact add_le_add (step.rangeSine_weighted_le_defect x)
        (ih (step.transfer x))

/-- Constant-one weighted Bessel bound for the complete pulled-back range
row. -/
theorem juliaRangeEnergy_le_normSq
    (steps : List (JuliaDefectStep H G)) (x : H) :
    juliaRangeEnergy steps x ≤ ‖x‖ ^ 2 :=
  (juliaRangeEnergy_le_defectEnergy steps x).trans
    (juliaDefectEnergy_le_normSq steps x)

/-- The Bessel estimate amplifies over any summable family of source vectors.
This is the basis-level form used for Hilbert--Schmidt inputs. -/
theorem summable_juliaRangeEnergy
    {ι : Type*} (steps : List (JuliaDefectStep H G)) (vectors : ι → H)
    (hvectors : Summable fun i => ‖vectors i‖ ^ 2) :
    Summable fun i => juliaRangeEnergy steps (vectors i) := by
  exact Summable.of_nonneg_of_le
    (fun i => juliaRangeEnergy_nonneg steps (vectors i))
    (fun i => juliaRangeEnergy_le_normSq steps (vectors i))
    hvectors

/-- The total weighted range energy is no larger than the source square sum. -/
theorem tsum_juliaRangeEnergy_le
    {ι : Type*} (steps : List (JuliaDefectStep H G)) (vectors : ι → H)
    (hvectors : Summable fun i => ‖vectors i‖ ^ 2) :
    ∑' i, juliaRangeEnergy steps (vectors i) ≤
      ∑' i, ‖vectors i‖ ^ 2 := by
  exact (summable_juliaRangeEnergy steps vectors hvectors).tsum_le_tsum
    (fun i => juliaRangeEnergy_le_normSq steps (vectors i))
    hvectors

theorem juliaRangeColumn_normSq_le_normSq
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) (x : H) :
    ‖juliaRangeColumn steps x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [juliaRangeColumn_normSq_eq]
  exact juliaRangeEnergy_le_normSq steps x

theorem tsum_juliaRangeColumn_normSq_le
    {ι K H G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (basis : HilbertBasis ι ℂ K)
    (steps : List (JuliaDefectStep H G)) (operator : K →L[ℂ] H)
    (hoperator : Summable fun i => ‖operator (basis i)‖ ^ 2) :
    ∑' i, ‖juliaRangeColumn steps (operator (basis i))‖ ^ 2 ≤
      ∑' i, ‖operator (basis i)‖ ^ 2 := by
  simpa only [juliaRangeColumn_normSq_eq] using
    (tsum_juliaRangeEnergy_le steps
      (fun i => operator (basis i)) hoperator)

/-- Named-basis Hilbert--Schmidt amplification of the Julia Bessel row. -/
theorem summable_juliaRangeEnergy_comp
    {ι K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (basis : HilbertBasis ι ℂ K)
    (steps : List (JuliaDefectStep H G)) (operator : K →L[ℂ] H)
    (hoperator : Summable fun i => ‖operator (basis i)‖ ^ 2) :
    Summable fun i => juliaRangeEnergy steps (operator (basis i)) :=
  summable_juliaRangeEnergy steps (fun i => operator (basis i)) hoperator

/-! The final finite direct-sum consumer is kept separate from the still-open
detector producer.  A route owner may instantiate `left` with the weighted
Julia range row and `right` with completed detector innovations only after the
same-object endpoint identity has been proved. -/

theorem finite_dual_pairing_norm_le
    {ι : Type*} [Fintype ι]
    (left right : ι → H) :
    ‖∑ i, ⟪left i, right i⟫_ℂ‖ ≤
      Real.sqrt (∑ i, ‖left i‖ ^ 2) *
        Real.sqrt (∑ i, ‖right i‖ ^ 2) := by
  calc
    ‖∑ i, ⟪left i, right i⟫_ℂ‖ ≤
        ∑ i, ‖⟪left i, right i⟫_ℂ‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖left i‖ * ‖right i‖ := by
      exact Finset.sum_le_sum (fun i _ => norm_inner_le_norm _ _)
    _ ≤ Real.sqrt (∑ i, ‖left i‖ ^ 2) *
          Real.sqrt (∑ i, ‖right i‖ ^ 2) := by
      simpa using
        (Real.sum_mul_le_sqrt_mul_sqrt (s := Finset.univ)
          (f := fun i => ‖left i‖) (g := fun i => ‖right i‖))

end CCM24FiniteSJuliaBessel
end CCM25Concrete
end Source
end ConnesWeilRH
