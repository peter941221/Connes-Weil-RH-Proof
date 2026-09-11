/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8P1ColumnEnergyAlignment

/-!
# G8 P1 quantitative column-energy alignment

Record 1327 aligned the two P1 boundary channels *summability-wise*: both
eat the same full-carrier column-energy premise.  This record upgrades the
alignment to a *quantitative energy inequality* between the two channels
at the same input.

The engine is the classical Hilbert-Schmidt norm adjoint invariance:

```text
∑_j ‖T b_j‖²  =  ∑_i ‖T† u_i‖²
```

along any pair of Hilbert bases, proved here by routing both Parseval
identities through one nonnegative real coefficient matrix and comparing
finite partial sums in both index directions (`Real.tsum_le_of_sum_le`
twice, antisymmetry).  From it:

* precomposition with a contraction *costs* `‖pull‖²` in energy:
  `∑_j ‖(C∘pull) b_j‖² ≤ ‖pull‖² ∑_i ‖C u_i‖²`;
* instantiating `pull := oldFrame` (contractive) and
  `C := antiresonantColumn ∘L newFrame†` gives the metric boundary
  energy bound `E_metric ≤ ‖oldFrame‖² · E_col`, hence
  `E_metric ≤ E_col`;
* the two-channel P1 ledger: radial + metric boundary energy is bounded
  by `(1 + (32 ‖q_p⁻¹‖)²) ‖oldFrame‖² E_col` — both channels from the
  single named analytic input.

The full-carrier column-energy premise is NOT proved here.  No
vanishing, no sign, and no RH-facing claim is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1ColumnEnergyQuantitativeAlignment

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryColumnBridge
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryColumnFullCarrierExtension
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryCauchyPairProducer
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryCauchyDefect
open CCM25Concrete.AntiresonantFrameLossRadialBoundarySplit
open CCM25Concrete.AntiresonantFrameLossCommutator
open CCM25Concrete.CCM24FiniteSActualSchurCascade
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM25Concrete.CCM24FiniteSFrameGramCalculus
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSFixedSourcePolar
open CCM25Concrete.CCM24FiniteSJuliaCausal
open CCM25Concrete.CCM24UnitScaleProlateAlignment
open C1G8P1SchurBoundaryAntiresonantFactorization
open C1G8P1RadialCommutatorChannelLedger
open C1G8P1ColumnEnergyAlignment

/-- Local copy of the source-carrier completeness instance (the Schur
cascade declares it `local`, so it is not exported). -/
noncomputable local instance sourceSoninCarrierCompleteSpaceQuantAlign
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Real-valued Parseval along a Hilbert basis -/

/-- Parseval's identity in real norm-square form along any Hilbert basis
of a complex inner product space. -/
theorem realParseval
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ι ℂ H) (x : H) :
    (‖x‖ ^ 2 : ℝ) = ∑' i, ‖inner ℂ (b i) x‖ ^ 2 := by
  classical
  have hpi : ∀ i : ι,
      (inner ℂ x (b i) * inner ℂ (b i) x : ℂ) =
        ((‖inner ℂ (b i) x‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    have hsym : inner ℂ x (b i) = (starRingEnd ℂ) (inner ℂ (b i) x) :=
      (inner_conj_symm x (b i)).symm
    rw [hsym, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsum : Summable fun i => (inner ℂ x (b i) * inner ℂ (b i) x : ℂ) := by
    refine Summable.of_norm_bounded (b.orthonormal.inner_products_summable x) ?_
    intro i
    rw [norm_mul, norm_inner_symm]
    rw [sq]
  have hc := b.tsum_inner_mul_inner x x
  calc ‖x‖ ^ 2 = Complex.re (inner ℂ x x) :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm
    _ = Complex.re (∑' i, (inner ℂ x (b i) * inner ℂ (b i) x : ℂ)) := by
        rw [← hc]
    _ = ∑' i, Complex.re (inner ℂ x (b i) * inner ℂ (b i) x) :=
        Complex.reCLM.map_tsum hsum
    _ = ∑' i, (‖inner ℂ (b i) x‖ ^ 2 : ℝ) := by
        exact tsum_congr (fun i => by rw [hpi i, Complex.ofReal_re])

/-! ## Hilbert-Schmidt norm adjoint invariance -/

/-- The Hilbert-Schmidt basis energy of an operator equals that of its
adjoint, read along arbitrary Hilbert bases of domain and codomain.  Both
sides are routed through one nonnegative real coefficient matrix; the
cross-index comparison uses finite partial sums in the two directions. -/
theorem hsNormSq_adjoint_invariance
    {ι κ H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (sourceBasis : HilbertBasis κ ℂ H₁) (carrierBasis : HilbertBasis ι ℂ H₂)
    (operator : H₁ →L[ℂ] H₂)
    (hsrc : Summable fun j => ‖operator (sourceBasis j)‖ ^ 2)
    (hadj : Summable fun i => ‖operator.adjoint (carrierBasis i)‖ ^ 2) :
    (∑' j, ‖operator (sourceBasis j)‖ ^ 2)
      = ∑' i, ‖operator.adjoint (carrierBasis i)‖ ^ 2 := by
  classical
  -- the shared nonnegative coefficient matrix, in the exact shape of
  -- `Orthonormal.inner_products_summable` for the carrier basis
  have hcol : ∀ j : κ, Summable fun i =>
      ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2 :=
    fun j => carrierBasis.orthonormal.inner_products_summable
      (operator (sourceBasis j))
  have hrow : ∀ i : ι, Summable fun j =>
      ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2 :=
    fun i => (sourceBasis.orthonormal.inner_products_summable
      (operator.adjoint (carrierBasis i))).congr (fun j => by
        rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm])
  -- Parseval links (real form) on both sides
  have perJ : ∀ j : κ, ‖operator (sourceBasis j)‖ ^ 2
      = ∑' i, ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2 :=
    fun j => realParseval carrierBasis (operator (sourceBasis j))
  have perI : ∀ i : ι, ‖operator.adjoint (carrierBasis i)‖ ^ 2
      = ∑' j, ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2 := by
    intro i
    rw [realParseval sourceBasis (operator.adjoint (carrierBasis i))]
    exact tsum_congr (fun j => by
      rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm])
  -- the outer real series are summable, from the hypotheses
  have houtJ : Summable fun j =>
      ∑' i, ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2 :=
    hsrc.congr (fun j => perJ j)
  have houtI : Summable fun i =>
      ∑' j, ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2 :=
    hadj.congr (fun i => perI i)
  -- partial-sum bound in the source direction
  have hle1 : (∑' j, ‖operator (sourceBasis j)‖ ^ 2)
      ≤ ∑' i, ‖operator.adjoint (carrierBasis i)‖ ^ 2 := by
    refine Real.tsum_le_of_sum_le (fun j => sq_nonneg _) ?_
    intro u
    have hexch : (∑ j ∈ u, ∑' i,
        ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2)
        = ∑' i, (∑ j ∈ u,
          ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2) :=
      (Summable.tsum_finsetSum (fun j _ => hcol j)).symm
    have hminor : Summable fun i => ∑ j ∈ u,
        ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2 :=
      Summable.of_nonneg_of_le
        (fun i => Finset.sum_nonneg (fun j _ => sq_nonneg _))
        (fun i => (hrow i).sum_le_tsum u (fun j _ => sq_nonneg _)) houtI
    calc (∑ j ∈ u, ‖operator (sourceBasis j)‖ ^ 2)
        = ∑ j ∈ u, ∑' i,
            ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2 :=
          Finset.sum_congr rfl (fun j _ => perJ j)
      _ = ∑' i, ∑ j ∈ u,
            ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2 := hexch
      _ ≤ ∑' i, ∑' j,
            ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2 :=
          hminor.tsum_le_tsum
            (fun i => (hrow i).sum_le_tsum u (fun j _ => sq_nonneg _)) houtI
      _ = ∑' i, ‖operator.adjoint (carrierBasis i)‖ ^ 2 :=
          tsum_congr (fun i => (perI i).symm)
  -- partial-sum bound in the carrier direction (symmetric)
  have hle2 : (∑' i, ‖operator.adjoint (carrierBasis i)‖ ^ 2)
      ≤ ∑' j, ‖operator (sourceBasis j)‖ ^ 2 := by
    refine Real.tsum_le_of_sum_le (fun i => sq_nonneg _) ?_
    intro v
    have hexch : (∑ i ∈ v, ∑' j,
        ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2)
        = ∑' j, (∑ i ∈ v,
          ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2) :=
      (Summable.tsum_finsetSum (fun i _ => hrow i)).symm
    have hminor : Summable fun j => ∑ i ∈ v,
        ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2 :=
      Summable.of_nonneg_of_le
        (fun j => Finset.sum_nonneg (fun i _ => sq_nonneg _))
        (fun j => (hcol j).sum_le_tsum v (fun i _ => sq_nonneg _)) houtJ
    calc (∑ i ∈ v, ‖operator.adjoint (carrierBasis i)‖ ^ 2)
        = ∑ i ∈ v, ∑' j,
            ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2 :=
          Finset.sum_congr rfl (fun i _ => perI i)
      _ = ∑' j, ∑ i ∈ v,
            ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2 := hexch
      _ ≤ ∑' j, ∑' i,
            ‖inner ℂ (carrierBasis i) (operator (sourceBasis j))‖ ^ 2 :=
          hminor.tsum_le_tsum
            (fun j => (hcol j).sum_le_tsum v (fun i _ => sq_nonneg _)) houtJ
      _ = ∑' j, ‖operator (sourceBasis j)‖ ^ 2 :=
          tsum_congr (fun j => (perJ j).symm)
  exact le_antisymm hle1 hle2

/-! ## Quantitative contraction cost -/

/-- Precomposition with a contraction costs at most `‖pull‖²` in
Hilbert-Schmidt basis energy. -/
theorem comp_normSq_le_of_contractive_pull
    {ι κ H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (sourceBasis : HilbertBasis κ ℂ H₁) (carrierBasis : HilbertBasis ι ℂ H₂)
    (pull : H₁ →L[ℂ] H₂) (hpull : ‖pull‖ ≤ 1)
    (column : H₂ →L[ℂ] H₂)
    (hcolumn : Summable fun i => ‖column (carrierBasis i)‖ ^ 2) :
    (∑' j, ‖(column ∘L pull) (sourceBasis j)‖ ^ 2)
      ≤ ‖pull‖ ^ 2 * ∑' i, ‖column (carrierBasis i)‖ ^ 2 := by
  classical
  have hcomp := summable_comp_normSq_of_contractive_pull sourceBasis
    carrierBasis pull hpull column hcolumn
  have hadjComp : Summable fun i =>
      ‖(column ∘L pull).adjoint (carrierBasis i)‖ ^ 2 :=
    BasisHilbertSchmidtPairData.summable_adjoint_normSq sourceBasis
      carrierBasis (column ∘L pull) hcomp
  have hadjC : Summable fun i => ‖column.adjoint (carrierBasis i)‖ ^ 2 :=
    BasisHilbertSchmidtPairData.summable_adjoint_normSq carrierBasis
      carrierBasis column hcolumn
  rw [hsNormSq_adjoint_invariance sourceBasis carrierBasis
      (column ∘L pull) hcomp hadjComp,
    hsNormSq_adjoint_invariance carrierBasis carrierBasis column
      hcolumn hadjC]
  refine le_trans (hadjComp.tsum_le_tsum (fun i => ?_)
    (Summable.mul_left (‖pull‖ ^ 2) hadjC)) (le_of_eq tsum_mul_left)
  have h1 : ‖(column ∘L pull).adjoint (carrierBasis i)‖
      ≤ ‖pull‖ * ‖column.adjoint (carrierBasis i)‖ := by
    rw [ContinuousLinearMap.adjoint_comp]
    simp only [ContinuousLinearMap.comp_apply]
    refine le_trans (ContinuousLinearMap.le_opNorm pull.adjoint
      (column.adjoint (carrierBasis i))) ?_
    rw [ContinuousLinearMap.adjoint.norm_map]
  calc ‖(column ∘L pull).adjoint (carrierBasis i)‖ ^ 2
      ≤ (‖pull‖ * ‖column.adjoint (carrierBasis i)‖) ^ 2 := by
        nlinarith [norm_nonneg ((column ∘L pull).adjoint (carrierBasis i)),
          norm_nonneg pull,
          norm_nonneg (column.adjoint (carrierBasis i)), h1]
    _ = ‖pull‖ ^ 2 * ‖column.adjoint (carrierBasis i)‖ ^ 2 := by
        ring

/-! ## The metric boundary channel costs at most the column energy -/

/-- The metric boundary composite
`antiresonantColumn ∘L newFrame† ∘L oldFrame` carries at most `‖oldFrame‖²`
times the full-carrier column energy — the quantitative form of the 1327
alignment; with `oldFrame` contractive this is `E_metric ≤ E_col`. -/
theorem metricBoundaryComposite_normSq_le_fullCarrierColumnEnergy
    {ι κ : Type*}
    (sourceBasis : HilbertBasis κ ℂ (sourceSoninCarrier unitSoninScale))
    (carrierBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcolumn : Summable fun i =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (carrierBasis i))‖ ^ 2) :
    (∑' j, ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ ^ 2)
      ≤ ‖oldSuffixFrame unitSoninScale p S‖ ^ 2 *
        ∑' i, ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
            (carrierBasis i))‖ ^ 2 :=
  comp_normSq_le_of_contractive_pull sourceBasis carrierBasis
    (oldSuffixFrame unitSoninScale p S) (norm_oldSuffixFrame_le_one p S)
    (newFrameAntiresonantColumn unitSoninScale p S ∘L
      ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S))
    hcolumn

/-- Contractive old frame: the metric boundary energy is bounded by the
full-carrier column energy itself. -/
theorem metricBoundaryComposite_normSq_le_fullCarrierColumnEnergyContractive
    {ι κ : Type*}
    (sourceBasis : HilbertBasis κ ℂ (sourceSoninCarrier unitSoninScale))
    (carrierBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcolumn : Summable fun i =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (carrierBasis i))‖ ^ 2) :
    (∑' j, ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ ^ 2)
      ≤ ∑' i, ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (carrierBasis i))‖ ^ 2 := by
  classical
  refine le_trans
    (metricBoundaryComposite_normSq_le_fullCarrierColumnEnergy
      sourceBasis carrierBasis p S hcolumn) ?_
  have hnormsq : ‖oldSuffixFrame unitSoninScale p S‖ ^ 2 ≤ 1 := by
    have h1 := norm_oldSuffixFrame_le_one p S
    have h0 : (0 : ℝ) ≤ ‖oldSuffixFrame unitSoninScale p S‖ := norm_nonneg _
    nlinarith
  exact mul_le_of_le_one_left
    (tsum_nonneg (fun i => sq_nonneg _)) hnormsq

/-! ## The two-channel P1 energy ledger -/

/-- Both P1 boundary channels together — the radial crossing after the
old frame plus the metric boundary composite — are bounded by a single
closed constant times `‖oldFrame‖²` times the one full-carrier column
energy.  This is the quantitative one-gate packaging of P1. -/
theorem p1BoundaryEnergyLedger_of_fullCarrierColumnEnergy
    {ι κ : Type*}
    (sourceBasis : HilbertBasis κ ℂ (sourceSoninCarrier unitSoninScale))
    (carrierBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcolumn : Summable fun i =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (carrierBasis i))‖ ^ 2) :
    (∑' j, ‖radialSoninBoundaryCrossing p S
          (oldSuffixFrame unitSoninScale p S (sourceBasis j))‖ ^ 2
      + ∑' j, ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ ^ 2)
      ≤ ((1 : ℝ) + (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2) *
        ‖oldSuffixFrame unitSoninScale p S‖ ^ 2 *
        ∑' i, ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
            (carrierBasis i))‖ ^ 2 := by
  classical
  have hmet := metricBoundaryComposite_normSq_le_fullCarrierColumnEnergy
    sourceBasis carrierBasis p S hcolumn
  have hsumMet : Summable fun j =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ ^ 2 :=
    summable_metricBoundaryComposite_normSq_of_fullCarrierColumnEnergy
      sourceBasis carrierBasis p S hcolumn
  have hrad : (∑' j, ‖radialSoninBoundaryCrossing p S
      (oldSuffixFrame unitSoninScale p S (sourceBasis j))‖ ^ 2)
      ≤ (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2 *
        ∑' j, ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
            (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ ^ 2 := by
    have hradsum := summable_radialCrossingAfterOldFrame_normSq_of_fullCarrierColumnEnergy
      sourceBasis carrierBasis p S hcolumn
    have hmaj := Summable.mul_left
      ((32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2) hsumMet
    refine le_trans (hradsum.tsum_le_tsum (fun j => ?_) hmaj)
      (le_of_eq tsum_mul_left)
    have h := norm_radialSoninBoundaryCrossing_apply_oldSuffixFrame_le p S
      (sourceBasis j)
    have hA : 0 ≤ ‖radialSoninBoundaryCrossing p S
        (oldSuffixFrame unitSoninScale p S (sourceBasis j))‖ :=
      norm_nonneg _
    have hB : 0 ≤ (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) *
        ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
            (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ :=
      mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _)
    calc ‖radialSoninBoundaryCrossing p S
          (oldSuffixFrame unitSoninScale p S (sourceBasis j))‖ ^ 2
        ≤ ((32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) *
            ‖newFrameAntiresonantColumn unitSoninScale p S
              (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
                (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖) ^ 2 :=
          sq_le_sq' (by linarith) h
      _ = (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2 *
          ‖newFrameAntiresonantColumn unitSoninScale p S
            (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
              (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ ^ 2 := by
          ring
  have hMetNonneg : 0 ≤ ∑' j, ‖newFrameAntiresonantColumn unitSoninScale p S
      (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
        (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ ^ 2 :=
    tsum_nonneg (fun j => sq_nonneg _)
  have hConstNonneg : (0 : ℝ) ≤
      (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2 + 1 := by
    positivity
  calc (∑' j, ‖radialSoninBoundaryCrossing p S
        (oldSuffixFrame unitSoninScale p S (sourceBasis j))‖ ^ 2
      + ∑' j, ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ ^ 2)
    ≤ (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2 *
        ∑' j, ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
            (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ ^ 2
      + ∑' j, ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ ^ 2 :=
      add_le_add hrad le_rfl
  _ = ((32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2 + 1) *
      ∑' j, ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (oldSuffixFrame unitSoninScale p S (sourceBasis j)))‖ ^ 2 := by
      ring
  _ ≤ ((32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2 + 1) *
      (‖oldSuffixFrame unitSoninScale p S‖ ^ 2 *
        ∑' i, ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
            (carrierBasis i))‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmet hConstNonneg
  _ = ((1 : ℝ) + (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2) *
      ‖oldSuffixFrame unitSoninScale p S‖ ^ 2 *
      ∑' i, ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (carrierBasis i))‖ ^ 2 := by
      ring

end C1G8P1ColumnEnergyQuantitativeAlignment
end Source
end ConnesWeilRH
