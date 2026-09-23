/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.RHDefinition
import ConnesWeilRH.Source.CC20YoshidaNearZeros
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
import ConnesWeilRH.Dev.C1G8R3AnnularMassConsumer
import ConnesWeilRH.Dev.C1G8R3AnnularKernelDiagonalBessel
import ConnesWeilRH.Dev.C1G8R3AnnularPointwiseReadback
import ConnesWeilRH.Dev.C1G8R3AnnularTailDecay
import ConnesWeilRH.Dev.C1G8R3AnnularTwoIBP
import ConnesWeilRH.Dev.C1G8MasterExit
import ConnesWeilRH.Dev.C1G8AdjointShearGram
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1SameOwnerWeil
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Concrete Annular Wing Majorant for S3 Survivor Core

This module instantiates the concrete annular wing majorant function:
`concreteWingMajorant N C t = if N < |t| then C / t^2 else 0`

Key Properties:
1. `concreteWingMajorant_measurable`: `concreteWingMajorant N C` is Borel measurable;
2. `concreteWingMajorant_nonneg`: For `0 ≤ C`, `concreteWingMajorant N C t ≥ 0` pointwise;
3. `concreteWingMajorant_eq_zero_of_mem_Icc`: Vanishes identically on `[-N, N]`;
4. `concreteWingMajorant_neg`: Even function `g(-t) = g(t)`;
5. `lintegral_Ici_concreteWingMajorant_le`: Finite integral on `[N, ∞)` bounded by `C / N`;
6. `lintegral_Iic_concreteWingMajorant_le`: Finite integral on `(-∞, -N]` bounded by `C / N`;
7. `sourceCompressedRoot_squareSum_of_concreteWingMajorant`: Discharges all structural
   integrability and support premises of `sourceCompressedRoot_squareSum_of_annular_wing_majorant`,
   leaving only the pointwise kernel diagonal estimate;
8. `riemannHypothesis_of_right_concrete_wing_majorant_and_aggregateEq`: Connects the concrete
   majorant directly to Mathlib's canonical `_root_.RiemannHypothesis`.

Axioms: strictly standard `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ConnesWeilRH
namespace Dev

open MeasureTheory Filter Topology
open ConnesWeilRH.Source
open Source.CC20Concrete
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSParameterizedEulerProduct
open Source.CCM25Concrete.SelectedWeilSquare
open Source.CC20YoshidaNearZeros
open Source.C1G8AdjointShearGram
open Source.C1G8MasterExit
open Source.C1HealthyYoshidaDetector
open Source.C1SameOwnerWeil

/-- The concrete annular wing majorant function: decays as `C / t^2` on the outer wings
    `|t| > N` and vanishes identically on the inner window `|t| ≤ N`. -/
noncomputable def concreteWingMajorant (N C : ℝ) (t : ℝ) : ℝ :=
  if N < |t| then C / t ^ 2 else 0

/-- Borel measurability of the concrete annular wing majorant. -/
theorem concreteWingMajorant_measurable (N C : ℝ) :
    Measurable (concreteWingMajorant N C) := by
  have hset : MeasurableSet {t : ℝ | N < |t|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hfun : Measurable (fun t : ℝ => C / t ^ 2) :=
    measurable_const.div (measurable_id.pow_const 2)
  exact Measurable.piecewise hset hfun measurable_const

/-- Pointwise nonnegativity of the concrete wing majorant for `0 ≤ C`. -/
theorem concreteWingMajorant_nonneg (N C : ℝ) (hC : 0 ≤ C) (t : ℝ) :
    0 ≤ concreteWingMajorant N C t := by
  unfold concreteWingMajorant
  split_ifs with h
  · exact div_nonneg hC (sq_nonneg t)
  · exact le_rfl

/-- The concrete wing majorant vanishes identically on the closed inner window `[-N, N]`. -/
theorem concreteWingMajorant_eq_zero_of_mem_Icc (N C : ℝ) (t : ℝ)
    (hlower : -N ≤ t) (hupper : t ≤ N) :
    concreteWingMajorant N C t = 0 := by
  unfold concreteWingMajorant
  have habs : |t| ≤ N := abs_le.mpr ⟨hlower, hupper⟩
  have hnot : ¬ (N < |t|) := not_lt.mpr habs
  rw [if_neg hnot]

/-- Reflection symmetry: `concreteWingMajorant` is an even function. -/
theorem concreteWingMajorant_neg (N C : ℝ) (t : ℝ) :
    concreteWingMajorant N C (-t) = concreteWingMajorant N C t := by
  unfold concreteWingMajorant
  rw [abs_neg, neg_sq]

/-- Pointwise domination of the concrete wing majorant by the power function `C * t^(-2)`
    on the half-line `[N, ∞)`. -/
theorem concreteWingMajorant_le_rpow_neg_two (N C : ℝ) (hC : 0 ≤ C)
    (t : ℝ) (ht : N ≤ t) (hN : 0 < N) :
    concreteWingMajorant N C t ≤ C * t ^ (-2 : ℝ) := by
  unfold concreteWingMajorant
  split_ifs with h
  · have ht0 : 0 ≤ t := hN.le.trans ht
    have hrpow : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      have h1 : t ^ (-2 : ℝ) = (t ^ (2 : ℝ))⁻¹ := Real.rpow_neg ht0 2
      have h2 : (t ^ (2 : ℝ))⁻¹ = (t ^ 2)⁻¹ := congrArg Inv.inv (Real.rpow_natCast t 2)
      exact h1.trans h2
    rw [div_eq_mul_inv, hrpow]
  · have ht0 : 0 ≤ t := hN.le.trans ht
    have hrpow_pos : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht0 (-2)
    have hprod : 0 ≤ C * t ^ (-2 : ℝ) := mul_nonneg hC hrpow_pos
    exact hprod

/-- The elementary power-tail integral `∫_[X, ∞) C · s⁻² = C / X`. -/
private theorem real_integral_Ici_const_rpow_neg_two (X C : ℝ) (hX : 0 < X) :
    (∫ s : ℝ in Set.Ici X, C * s ^ (-2 : ℝ)) = C / X := by
  rw [integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_Ioi_rpow_of_lt (a := -2) (by norm_num) hX]
  have h1 : (-2 : ℝ) + 1 = -1 := by norm_num
  rw [h1, Real.rpow_neg_one X]
  ring

/-- Finite Lebesgue integral on the right outer wing `[N, ∞)`:
    `∫⁻ t in [N, ∞), g(t) ≤ C / N`. -/
theorem lintegral_Ici_concreteWingMajorant_le (N C : ℝ) (hN : 0 < N) (hC : 0 ≤ C) :
    (∫⁻ t in Set.Ici N, ENNReal.ofReal (concreteWingMajorant N C t))
      ≤ ENNReal.ofReal (C / N) := by
  have hint : Integrable (fun s : ℝ => C * s ^ (-2 : ℝ))
      (volume.restrict (Set.Ici N)) := by
    have hsub : Set.Ici N ⊆ Set.Ioi (N / 2) := Set.Ici_subset_Ioi.mpr (by linarith)
    have h1 : Integrable (fun s : ℝ => C * s ^ (-2 : ℝ))
        (volume.restrict (Set.Ioi (N / 2))) :=
      (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num)
        (by linarith : (0 : ℝ) < N / 2)).const_mul C
    exact h1.mono_measure (Measure.restrict_mono_set volume hsub)
  have hpoint : ∀ s : ℝ, N ≤ s →
      ENNReal.ofReal (concreteWingMajorant N C s) ≤
        ENNReal.ofReal (C * s ^ (-2 : ℝ)) := by
    intro s hs
    exact ENNReal.ofReal_le_ofReal (concreteWingMajorant_le_rpow_neg_two N C hC s hs hN)
  calc (∫⁻ t in Set.Ici N, ENNReal.ofReal (concreteWingMajorant N C t))
      ≤ (∫⁻ t in Set.Ici N, ENNReal.ofReal (C * t ^ (-2 : ℝ))) :=
        setLIntegral_mono (by measurability) hpoint
    _ = ENNReal.ofReal (∫ s : ℝ in Set.Ici N, C * s ^ (-2 : ℝ)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          ((ae_restrict_mem measurableSet_Ici).mono fun s hs => by
            have hs0 : 0 ≤ s := hN.le.trans (Set.mem_Ici.mp hs)
            exact mul_nonneg hC (Real.rpow_nonneg hs0 (-2)))).symm
    _ = ENNReal.ofReal (C / N) :=
        congrArg ENNReal.ofReal (real_integral_Ici_const_rpow_neg_two N C hN)

/-- Finite Lebesgue integral on the left outer wing `(-∞, -N]`:
    `∫⁻ t in (-∞, -N], g(t) ≤ C / N`. -/
theorem lintegral_Iic_concreteWingMajorant_le (N C : ℝ) (hN : 0 < N) (hC : 0 ≤ C) :
    (∫⁻ t in Set.Iic (-N), ENNReal.ofReal (concreteWingMajorant N C t))
      ≤ ENNReal.ofReal (C / N) := by
  have hmp : MeasurePreserving (fun (x : ℝ) => -x) (volume : Measure ℝ) (volume : Measure ℝ) :=
    Measure.measurePreserving_neg (volume : Measure ℝ)
  have hpre : (fun (x : ℝ) => -x) ⁻¹' (Set.Iic (-N)) = Set.Ici N := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
    constructor <;> intro h <;> linarith
  have hmeas : Measurable (fun (t : ℝ) => ENNReal.ofReal (concreteWingMajorant N C t)) :=
    ENNReal.measurable_ofReal.comp (concreteWingMajorant_measurable N C)
  have hsubst := hmp.setLIntegral_comp_preimage (s := Set.Iic (-N))
    (measurableSet_Iic (a := -N)) hmeas
  rw [hpre] at hsubst
  have heven : (fun (a : ℝ) => ENNReal.ofReal (concreteWingMajorant N C (-a))) =
      fun (a : ℝ) => ENNReal.ofReal (concreteWingMajorant N C a) := by
    funext a
    rw [concreteWingMajorant_neg]
  rw [heven] at hsubst
  rw [← hsubst]
  exact lintegral_Ici_concreteWingMajorant_le N C hN hC

/-- Concrete S3 Survivor Core Consumer:
    Under pointwise domination by `concreteWingMajorant (N : ℝ) C`, the source-compressed
    root square-sum is finite. All integral and support hypotheses are discharged. -/
theorem sourceCompressedRoot_squareSum_of_concreteWingMajorant
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    (hNpos : 0 < (N : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hpoint : ∀ n, N ≤ n → ∀ t, ∑' i, ENNReal.ofReal
        (‖(sourceRootAnnularOutputWindow owner lambda N n
          (sourceBasis i) : ℝ → ℂ) t‖) ^ (2 : ℕ) ≤
        ENNReal.ofReal (concreteWingMajorant (N : ℝ) C t)) :
    Summable fun i => ‖sourceCompressedRoot owner lambda
      (sourceBasis i)‖ ^ 2 := by
  refine sourceCompressedRoot_squareSum_of_annular_wing_majorant
    owner lambda sourceBasis N hN
    (hg := concreteWingMajorant_measurable (N : ℝ) C)
    (hgnonneg := concreteWingMajorant_nonneg (N : ℝ) C hC)
    (hB₁ := div_nonneg hC hNpos.le)
    (hB₂ := div_nonneg hC hNpos.le)
    hNpos
    (hzero := fun t hlower hupper =>
      concreteWingMajorant_eq_zero_of_mem_Icc (N : ℝ) C t hlower hupper)
    hpoint
    (hleft := lintegral_Iic_concreteWingMajorant_le (N : ℝ) C hNpos hC)
    (hright := lintegral_Ici_concreteWingMajorant_le (N : ℝ) C hNpos hC)

/-- Master Exit to Mathlib RiemannHypothesis via Concrete Wing Majorant:
    Exhibiting pointwise domination by `concreteWingMajorant` and the aggregate trace
    equality for every hypothetical off-line zero proves Mathlib's `_root_.RiemannHypothesis`. -/
theorem riemannHypothesis_of_right_concrete_wing_majorant_and_aggregateEq
    (hconcrete : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ (owner : SelectedWeilSquareOwner)
          (lambda : CCM24SoninScale)
          (family : FinitePrimePowerFamily)
          (ν : Type*)
          (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
          (ι : Type*)
          (_hcount : Countable ι)
          (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
          (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
          (hNpos : 0 < (N : ℝ))
          (C : ℝ) (hC : 0 ≤ C),
          HealthyYoshidaDetectorData rho.1 owner.sourceTest ∧
          (∀ n, N ≤ n → ∀ t, ∑' i, ENNReal.ofReal
            (‖(sourceRootAnnularOutputWindow owner lambda N n
              (sourceBasis i) : ℝ → ℂ) t‖) ^ (2 : ℕ) ≤
            ENNReal.ofReal (concreteWingMajorant (N : ℝ) C t)) ∧
          ((ordinaryTraceAlong sourceBasis
            (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
            = qw owner.sourceTest)) :
    _root_.RiemannHypothesis := by
  apply Source.C1G8MasterExit.riemannHypothesis_of_right_annular_wing_majorant_and_aggregateEq
  intro rho hright
  obtain ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, N, hN, hNpos, C, hC,
    hdata, hpoint, heq⟩ := hconcrete rho hright
  refine ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, N, hN,
    concreteWingMajorant (N : ℝ) C, C / (N : ℝ), C / (N : ℝ),
    hdata,
    concreteWingMajorant_measurable (N : ℝ) C,
    concreteWingMajorant_nonneg (N : ℝ) C hC,
    div_nonneg hC hNpos.le,
    div_nonneg hC hNpos.le,
    hNpos,
    fun t hl hu => concreteWingMajorant_eq_zero_of_mem_Icc (N : ℝ) C t hl hu,
    hpoint,
    lintegral_Iic_concreteWingMajorant_le (N : ℝ) C hNpos hC,
    lintegral_Ici_concreteWingMajorant_le (N : ℝ) C hNpos hC,
    heq⟩

end Dev
end ConnesWeilRH
