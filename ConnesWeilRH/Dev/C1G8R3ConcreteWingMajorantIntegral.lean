/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.RHDefinition
import ConnesWeilRH.Source.CC20YoshidaNearZeros
import ConnesWeilRH.Dev.C1G8MasterExit
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.C1G8AdjointShearGram
import ConnesWeilRH.Dev.C1G8R3ConcreteWingMajorant
import ConnesWeilRH.Dev.C1G8R3AnnularKernelDiagonalMass

/-!
# Total Integral Bound for the Concrete Annular Wing Majorant

This module proves that the total Lebesgue integral of the concrete annular wing
majorant `concreteWingMajorant N C` over the entire real line `ℝ` is bounded by
`2 * C / N`.

Key Theorems:
1. `lintegral_concreteWingMajorant_eq_wings`: The full-line integral splits as the sum
   of the left wing `(-∞, -N]` and right wing `[N, ∞)`, since `concreteWingMajorant`
   vanishes identically on `[-N, N]`.
2. `lintegral_concreteWingMajorant_le`:
   `∫⁻ t, ENNReal.ofReal (concreteWingMajorant N C t) ≤ ENNReal.ofReal (2 * C / N)`.
3. `sourceCompressedRoot_squareSum_of_lintegral_concreteWingMajorant`:
   Directly deduces S3 survivor core square-summability whenever the annular output
   window column energy integral is bounded by `2 * C / N`.

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
open Source.CCM25Concrete.SelectedWeilSquare
open Source.CC20YoshidaNearZeros
open Source.C1HealthyYoshidaDetector
open Source.C1SameOwnerWeil
open Source.C1G8AdjointShearGram
open Source.C1G8MasterExit

/-- The middle integral on `(-N, N)` vanishes identically because `concreteWingMajorant`
    vanishes on `[-N, N]`. -/
theorem lintegral_Ioo_concreteWingMajorant_eq_zero (N C : ℝ) :
    ∫⁻ t in Set.Ioo (-N) N, ENNReal.ofReal (concreteWingMajorant N C t) = 0 := by
  have hg := concreteWingMajorant_measurable N C
  rw [lintegral_eq_zero_iff (f := fun t => ENNReal.ofReal (concreteWingMajorant N C t))
    (ENNReal.measurable_ofReal.comp hg),
    MeasureTheory.ae_restrict_eq measurableSet_Ioo]
  change Filter.Eventually (fun x => ENNReal.ofReal (concreteWingMajorant N C x) = (0 : ℝ → ENNReal) x)
    (MeasureTheory.ae volume ⊓ Filter.principal (Set.Ioo (-N) N))
  rw [Filter.eventually_inf_principal]
  refine Filter.Eventually.of_forall fun t ht => ?_
  rw [concreteWingMajorant_eq_zero_of_mem_Icc N C t (Set.mem_Ioo.1 ht).1.le (Set.mem_Ioo.1 ht).2.le]
  simp

/-- Full-line integral of `concreteWingMajorant` equals the sum of its two wings. -/
theorem lintegral_concreteWingMajorant_eq_wings (N C : ℝ) (hN : 0 < N) :
    ∫⁻ t, ENNReal.ofReal (concreteWingMajorant N C t) =
      (∫⁻ t in Set.Iic (-N), ENNReal.ofReal (concreteWingMajorant N C t)) +
      (∫⁻ t in Set.Ici N, ENNReal.ofReal (concreteWingMajorant N C t)) := by
  have hg := concreteWingMajorant_measurable N C
  have hmid := lintegral_Ioo_concreteWingMajorant_eq_zero N C
  have hdisj : Disjoint (Set.Ioo (-N) N) (Set.Ici N) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    have hioo : -N < t ∧ t < N := Set.mem_Ioo.1 h1
    exact absurd (le_antisymm hioo.2.le (Set.mem_Ici.1 h2)) hioo.2.ne
  have hsplit : ∫⁻ t in Set.Ioi (-N), ENNReal.ofReal (concreteWingMajorant N C t) =
      (∫⁻ t in Set.Ioo (-N) N, ENNReal.ofReal (concreteWingMajorant N C t)) +
      (∫⁻ t in Set.Ici N, ENNReal.ofReal (concreteWingMajorant N C t)) := by
    have hunion : Set.Ioo (-N) N ∪ Set.Ici N = Set.Ioi (-N) := by
      ext t
      constructor
      · rintro (h | h)
        · exact Set.mem_Ioi.2 (Set.mem_Ioo.1 h).1
        · exact Set.mem_Ioi.2 (lt_of_lt_of_le (show -N < N from by linarith) h)
      · intro h
        rcases lt_trichotomy t N with hlt | heq | hgt
        · exact Or.inl (Set.mem_Ioo.2 ⟨h, hlt⟩)
        · exact Or.inr (Set.mem_Ici.2 heq.ge)
        · exact Or.inr (Set.mem_Ici.2 hgt.le)
    rw [← hunion]
    exact lintegral_union (f := fun t => ENNReal.ofReal (concreteWingMajorant N C t))
      (μ := volume) measurableSet_Ici hdisj
  have step1 : ∫⁻ t, ENNReal.ofReal (concreteWingMajorant N C t) =
      (∫⁻ t in Set.Iic (-N), ENNReal.ofReal (concreteWingMajorant N C t)) +
      (∫⁻ t in Set.Ioi (-N), ENNReal.ofReal (concreteWingMajorant N C t)) := by
    rw [← Set.compl_Iic,
      lintegral_add_compl (A := Set.Iic (-N))
        (fun t => ENNReal.ofReal (concreteWingMajorant N C t))
        measurableSet_Iic]
  rw [step1, hsplit, hmid, zero_add]

/-- The total Lebesgue integral of `concreteWingMajorant` over the entire real line
    is bounded by `2 * C / N`. -/
theorem lintegral_concreteWingMajorant_le (N C : ℝ) (hN : 0 < N) (hC : 0 ≤ C) :
    ∫⁻ t, ENNReal.ofReal (concreteWingMajorant N C t) ≤
      ENNReal.ofReal (2 * C / N) := by
  rw [lintegral_concreteWingMajorant_eq_wings N C hN]
  have hleft := lintegral_Iic_concreteWingMajorant_le N C hN hC
  have hright := lintegral_Ici_concreteWingMajorant_le N C hN hC
  have hdiv : 0 ≤ C / N := div_nonneg hC hN.le
  calc (∫⁻ t in Set.Iic (-N), ENNReal.ofReal (concreteWingMajorant N C t)) +
        (∫⁻ t in Set.Ici N, ENNReal.ofReal (concreteWingMajorant N C t))
      ≤ ENNReal.ofReal (C / N) + ENNReal.ofReal (C / N) := add_le_add hleft hright
    _ = ENNReal.ofReal (C / N + C / N) := (ENNReal.ofReal_add hdiv hdiv).symm
    _ = ENNReal.ofReal (2 * C / N) := by
        congr 1
        ring

/-- S3 Survivor Core square-summability deduced directly from the total integral bound. -/
theorem sourceCompressedRoot_squareSum_of_lintegral_concreteWingMajorant
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    (hNpos : 0 < (N : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hint : ∀ n, N ≤ n →
      ∫⁻ t, ∑' i, ‖(sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i) : ℝ → ℂ) t‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (2 * C / (N : ℝ))) :
    Summable fun i => ‖sourceCompressedRoot owner lambda (sourceBasis i)‖ ^ 2 := by
  have hB : 0 ≤ 2 * C / (N : ℝ) := div_nonneg (mul_nonneg zero_le_two hC) hNpos.le
  exact sourceCompressedRoot_squareSum_of_kernelDiagonal_lintegral_bound
    owner lambda sourceBasis N hN (B := 2 * C / (N : ℝ)) hB hint

/-- Integrating the almost-everywhere pointwise bound over `ℝ` yields the total integral
    bound bounded by `2 * C / N`. -/
theorem lintegral_annular_output_le_of_ae_pointwise
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (hNpos : 0 < (N : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hpoint : ∀ n, N ≤ n → ∀ᵐ t ∂volume,
      ∑' i, ‖(sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i) : ℝ → ℂ) t‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (concreteWingMajorant (N : ℝ) C t)) :
    ∀ n, N ≤ n →
      ∫⁻ t, ∑' i, ‖(sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i) : ℝ → ℂ) t‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (2 * C / (N : ℝ)) := by
  intro n hn
  calc ∫⁻ t, ∑' i, ‖(sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i) : ℝ → ℂ) t‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ t, ENNReal.ofReal (concreteWingMajorant (N : ℝ) C t) :=
        lintegral_mono_ae (hpoint n hn)
    _ ≤ ENNReal.ofReal (2 * C / (N : ℝ)) :=
        lintegral_concreteWingMajorant_le (N : ℝ) C hNpos hC

/-- S3 Survivor Core square-summability deduced from the almost-everywhere pointwise bound. -/
theorem sourceCompressedRoot_squareSum_of_ae_pointwise_concreteWingMajorant
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    (hNpos : 0 < (N : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hpoint : ∀ n, N ≤ n → ∀ᵐ t ∂volume,
      ∑' i, ‖(sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i) : ℝ → ℂ) t‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (concreteWingMajorant (N : ℝ) C t)) :
    Summable fun i => ‖sourceCompressedRoot owner lambda (sourceBasis i)‖ ^ 2 := by
  apply sourceCompressedRoot_squareSum_of_lintegral_concreteWingMajorant
    owner lambda sourceBasis N hN hNpos hC
  exact lintegral_annular_output_le_of_ae_pointwise owner lambda sourceBasis N hNpos hC hpoint

/-- Master Exit to Mathlib RiemannHypothesis from the almost-everywhere pointwise concrete
    wing majorant and aggregate trace limit equality. -/
theorem riemannHypothesis_of_right_ae_pointwise_concrete_wing_majorant_and_aggregateEq
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
          (∀ n, N ≤ n → ∀ᵐ t ∂volume, ∑' i,
            ‖(sourceRootAnnularOutputWindow owner lambda N n
              (sourceBasis i) : ℝ → ℂ) t‖ₑ ^ (2 : ℝ) ≤
            ENNReal.ofReal (concreteWingMajorant (N : ℝ) C t)) ∧
          ((ordinaryTraceAlong sourceBasis
            (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
            = qw owner.sourceTest)) :
    _root_.RiemannHypothesis := by
  apply Source.C1G8MasterExit.riemannHypothesis_of_right_survivorCore_and_aggregateEq
  intro rho hright
  obtain ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, N, hN, hNpos, C, hC,
    hdata, hpoint, heq⟩ := hconcrete rho hright
  have hsum := sourceCompressedRoot_squareSum_of_ae_pointwise_concreteWingMajorant
    owner lambda sourceBasis N hN hNpos hC hpoint
  exact ⟨owner, lambda, family, ν, ι, globalBasis, sourceBasis, hdata, hsum, heq⟩

end Dev
end ConnesWeilRH
