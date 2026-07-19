/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTwoSidedRootRecombination
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientFirstJet
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSInverseMetric
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJuliaBessel
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSDouglasFactor
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal

/-!
# One common pair owner for the fixed source boundary ledger

The outer, reflected second-support, and prolate constructions originally
produce separate `A^dagger B` owners.  This module places their output carriers
in orthogonal `L2` products and combines the signed operators before the
source coframe is attached.  It closes the common fixed-source pair layer; it
does not claim the uniform unnormalised coframe estimate required by Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCommonBoundaryPair

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24RadialBoundaryPairTransport
open CCM24SourceProlateTrace
open CCM24FiniteSTwoSidedRootRecombination
open CCM24FiniteSFixedQuotientFirstJet
open CCM24FiniteSInverseMetric
open CCM24FiniteSJuliaBessel
open CCM24ReflectedCompactRoot

noncomputable local instance sourceSoninSubmoduleCompleteSpace
    (lambda : CCM24SoninScale) :
    CompleteSpace ((ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable local instance sourceSoninIntersectionCompleteSpace
    (lambda : CCM24SoninScale) :
    CompleteSpace
      (↥(((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule) ⊓
        ((ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule))) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable abbrev commonBoundaryCarrier (a c : ℝ) :=
  WithLp 2
    (WithLp 2
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) ×
        Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))) ×
      WithLp 2
        ((WithLp 2
            (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))) ×
              Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))))) ×
          WithLp 2 (finiteSCarrier × finiteSCarrier)))

noncomputable abbrev radialBoundaryCarrier (a c : ℝ) :=
  WithLp 2
    (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) ×
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)))

noncomputable abbrev correctedBoundaryCarrier (a c : ℝ) :=
  WithLp 2
    (commonBoundaryCarrier a c ×
      WithLp 2 (radialBoundaryCarrier a c × radialBoundaryCarrier a c))

/-!
The common-root producer is the exact interface still missing from the Gate 3U
route.  Both Hilbert--Schmidt legs factor through one boundary-localized root;
the Julia range row is allowed to control the right leg only through its
pointwise energy inequality.  No route-specific producer is assumed here.
-/
structure CommonRootS2Producer
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ H) where
  root : H →L[ℂ] K
  leftFactor : K →L[ℂ] G
  rightFactor : K →L[ℂ] G
  steps : List (JuliaDefectStep K G)
  root_summable_normSq : Summable fun i => ‖root (sourceBasis i)‖ ^ 2
  right_energy_le : ∀ i,
    ‖rightFactor (root (sourceBasis i))‖ ^ 2 ≤
      juliaRangeEnergy steps (root (sourceBasis i))
  response : H →L[ℂ] H
  response_eq :
    (leftFactor ∘L root).adjoint ∘L (rightFactor ∘L root) = response

/-!
The ordinary pair owner above only knows a scalar Julia-energy majorant.  That
majorant is sufficient for fixed-S summability, but it does not say that the
physical right column is visible to the actual Julia range column.  The
following refinement stores precisely that missing source-specific datum.

`rangeColumn` is the genuine pulled-back Julia range column.  `factor` is its
Douglas readout.  Thus `factorization` is the operator form of

```text
physicalColumn = Z * JuliaColumn,
```

and `rangeColumn_energy_eq` prevents an arbitrary small column from being
called a Julia column.  The kernel visibility consequence is proved below,
not assumed informally.
-/
structure DouglasAlignedCommonRootS2Producer
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ H) where
  base : CommonRootS2Producer (K := K) (G := G) sourceBasis
  rangeColumn : H →L[ℂ]
    PiLp 2 (fun _ : Fin base.steps.length => G)
  rangeColumn_energy_eq : ∀ x,
    ‖rangeColumn x‖ ^ 2 =
      juliaRangeEnergy base.steps (base.root x)
  factor : PiLp 2 (fun _ : Fin base.steps.length => G) →L[ℂ] G
  factorBound : ℝ
  factorBound_nonneg : 0 ≤ factorBound
  factor_norm_le : ‖factor‖ ≤ factorBound
  factorization : base.rightFactor ∘L base.root =
    factor ∘L rangeColumn

/-!
This constructor fixes the carrier of the Douglas column.  The factorization
is still an explicit source-side premise: the finite Julia column is now
genuine, while the theorem refuses to infer physical visibility from the
scalar Bessel inequality alone.
-/
noncomputable def douglasAlignedCommonRootS2ProducerOfJuliaRangeColumn
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : CommonRootS2Producer (K := K) (G := G) sourceBasis)
    (factor : PiLp 2 (fun _ : Fin base.steps.length => G) →L[ℂ] G)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (factorization : base.rightFactor ∘L base.root =
      factor ∘L ((juliaRangeColumn (H := K) (G := G) base.steps) ∘L
        base.root)) :
    DouglasAlignedCommonRootS2Producer (K := K) (G := G) sourceBasis :=
  { base := base
    rangeColumn :=
      (juliaRangeColumn (H := K) (G := G) base.steps) ∘L base.root
    rangeColumn_energy_eq := fun x =>
      juliaRangeColumn_normSq_eq base.steps (base.root x)
    factor := factor
    factorBound := factorBound
    factorBound_nonneg := factorBound_nonneg
    factor_norm_le := factor_norm_le
    factorization := factorization }

theorem DouglasAlignedCommonRootS2Producer.rightColumn_eq_zero_of_rangeColumn_eq_zero
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : DouglasAlignedCommonRootS2Producer (K := K) (G := G) sourceBasis)
    {x : H} (hx : producer.rangeColumn x = 0) :
    producer.base.rightFactor (producer.base.root x) = 0 := by
  have h := congrArg (fun f => f x) producer.factorization
  simpa only [ContinuousLinearMap.comp_apply, hx, map_zero] using h

theorem DouglasAlignedCommonRootS2Producer.rightColumn_normSq_le
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : DouglasAlignedCommonRootS2Producer (K := K) (G := G) sourceBasis)
    (x : H) :
    ‖producer.base.rightFactor (producer.base.root x)‖ ^ 2 ≤
      producer.factorBound ^ 2 * ‖producer.base.root x‖ ^ 2 := by
  have hfactorization := congrArg (fun f => f x) producer.factorization
  have hfactorBound_nonneg : 0 ≤ producer.factorBound :=
    producer.factorBound_nonneg
  rw [show producer.base.rightFactor (producer.base.root x) =
      producer.factor (producer.rangeColumn x) by
        simpa only [ContinuousLinearMap.comp_apply] using hfactorization]
  calc
    ‖producer.factor (producer.rangeColumn x)‖ ^ 2 ≤
        (‖producer.factor‖ * ‖producer.rangeColumn x‖) ^ 2 := by
      gcongr
      exact producer.factor.le_opNorm _
    _ ≤ (producer.factorBound * ‖producer.rangeColumn x‖) ^ 2 := by
      gcongr
      exact producer.factor_norm_le
    _ = producer.factorBound ^ 2 * ‖producer.rangeColumn x‖ ^ 2 := by
      ring
    _ = producer.factorBound ^ 2 *
        juliaRangeEnergy producer.base.steps (producer.base.root x) := by
      rw [producer.rangeColumn_energy_eq]
    _ ≤ producer.factorBound ^ 2 * ‖producer.base.root x‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (juliaRangeEnergy_le_normSq producer.base.steps
          (producer.base.root x))
        (sq_nonneg _)

/-!
Moved before the Douglas-aligned constructor so the pair-data owner is
available without a forward reference.  The following two-copy construction
is an exact carrier factorization for an
already available Hilbert--Schmidt pair.  It is useful for attaching the
physical pair owner to the common-root consumer without inventing a Douglas
factorization.  The single Julia step below is only a bookkeeping Bessel row:
it proves the projection onto the second copy is contractive.  It is therefore
not the source-specific Julia/Schur alignment needed for Gate 3U.
-/
noncomputable def commonRootSecondCoordinate
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] :
    WithLp 2 (G × G) →L[ℂ] WithLp 2 (G × G) :=
  let E := WithLp.prodContinuousLinearEquiv 2 ℂ G G
  E.symm.toContinuousLinearMap ∘L
    ((ContinuousLinearMap.snd ℂ G G).prod
      (0 : (G × G) →L[ℂ] G)) ∘L
    E.toContinuousLinearMap

theorem commonRootSecondCoordinate_apply
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (x : WithLp 2 (G × G)) :
    commonRootSecondCoordinate x = WithLp.toLp 2 (x.snd, 0) := by
  simp [commonRootSecondCoordinate]

noncomputable def commonRootS2ProducerOfPairData
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    CommonRootS2Producer
      (K := WithLp 2 (G × G)) (G := WithLp 2 (G × G)) sourceBasis :=
  { root :=
      (WithLp.prodContinuousLinearEquiv 2 ℂ G G).symm.toContinuousLinearMap ∘L
        data.left.prod data.right
    leftFactor := ContinuousLinearMap.id ℂ (WithLp 2 (G × G))
    rightFactor := commonRootSecondCoordinate
    steps := [{
      transfer := 0
      defect := ContinuousLinearMap.id ℂ (WithLp 2 (G × G))
      rangeSine := commonRootSecondCoordinate
      weight := 1
      weight_nonneg := by norm_num
      pythagorean := by
        intro x
        simp
      rangeSine_weighted_le_defect := by
        intro x
        simp only [one_mul, ContinuousLinearMap.id_apply]
        calc
          ‖commonRootSecondCoordinate x‖ ^ 2 = ‖x.snd‖ ^ 2 := by
            rw [commonRootSecondCoordinate_apply]
            simp
          _ ≤ ‖x‖ ^ 2 :=
            (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
              (WithLp.norm_snd_le (α := G) (β := G) (p := 2) x)
      }]
    root_summable_normSq := by
      apply (data.left_summable_normSq.add data.right_summable_normSq).congr
      intro i
      simpa only [ContinuousLinearMap.comp_apply] using
        (WithLp.prod_norm_sq_eq_of_L2
          (WithLp.toLp 2
            (data.left (sourceBasis i), data.right (sourceBasis i)))).symm
    right_energy_le := by
      intro i
      simp [juliaRangeEnergy, commonRootSecondCoordinate_apply]
    response := data.left.adjoint ∘L data.right
    response_eq := by
      apply ContinuousLinearMap.ext
      intro x
      apply ext_inner_left ℂ
      intro y
      simp [commonRootSecondCoordinate, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right, WithLp.prod_inner_apply]
  }

/-!
For the already assembled two-leg owner, the old second-coordinate row has a
literal Douglas realization.  This is an ownership/typing result, not the
finite-S Schur producer: its range column has one coordinate because the
underlying pair owner itself has one coordinate.
-/
noncomputable def commonRootS2ProducerOfPairData_douglasAligned
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    DouglasAlignedCommonRootS2Producer
      (K := WithLp 2 (G × G)) (G := WithLp 2 (G × G)) sourceBasis := by
  let base := commonRootS2ProducerOfPairData data
  let i0 : Fin base.steps.length :=
    ⟨0, by simp [base, commonRootS2ProducerOfPairData]⟩
  let factor : PiLp 2 (fun _ : Fin base.steps.length => WithLp 2 (G × G)) →L[ℂ]
      WithLp 2 (G × G) :=
    PiLp.proj (p := 2)
      (β := fun _ : Fin base.steps.length => WithLp 2 (G × G))
      i0
  have hfactorBound : ‖factor‖ ≤ (1 : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa [factor] using (PiLp.norm_apply_le x i0)
  apply douglasAlignedCommonRootS2ProducerOfJuliaRangeColumn base factor 1
    (by norm_num) hfactorBound
  apply ContinuousLinearMap.ext
  intro x
  change commonRootSecondCoordinate
      (WithLp.toLp 2 (data.left x, data.right x)) =
    (juliaRangeColumn (H := WithLp 2 (G × G))
      (G := WithLp 2 (G × G)) base.steps
      (WithLp.toLp 2 (data.left x, data.right x))) i0
  rw [juliaRangeColumn_apply]
  simp [base, i0, commonRootS2ProducerOfPairData,
    juliaRangeMaps, juliaRangeStepMap]

theorem commonRootS2ProducerOfPairData_response_eq
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    (commonRootS2ProducerOfPairData data).response = data.traceProduct := by
  rfl

theorem commonRootS2ProducerOfPairData_root_energy_eq
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    ∑' i, ‖(commonRootS2ProducerOfPairData data).root
        (sourceBasis i)‖ ^ 2 =
      ∑' i, (‖data.left (sourceBasis i)‖ ^ 2 +
        ‖data.right (sourceBasis i)‖ ^ 2) := by
  apply tsum_congr
  intro i
  change ‖WithLp.toLp 2
      (data.left (sourceBasis i), data.right (sourceBasis i))‖ ^ 2 = _
  exact WithLp.prod_norm_sq_eq_of_L2 _

/-!
The physical compact kernels have the opposite composition order from the
postcomposition-only interface above: a common full-window root is followed
by a negative or positive input projection.  Keep that order explicit.
-/
structure InputSideRootS2Producer
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ H) where
  root : H →L[ℂ] K
  leftInput : H →L[ℂ] H
  rightInput : H →L[ℂ] H
  leftFactor : K →L[ℂ] G
  rightFactor : K →L[ℂ] G
  leftRoot_summable_normSq : Summable fun i =>
    ‖root (leftInput (sourceBasis i))‖ ^ 2
  rightRoot_summable_normSq : Summable fun i =>
    ‖root (rightInput (sourceBasis i))‖ ^ 2
  steps : List (JuliaDefectStep K G)
  right_energy_le : ∀ i,
    ‖rightFactor (root (rightInput (sourceBasis i)))‖ ^ 2 ≤
      juliaRangeEnergy steps (root (rightInput (sourceBasis i)))
  response : H →L[ℂ] H
  response_eq :
    (leftFactor ∘L root ∘L leftInput).adjoint ∘L
        (rightFactor ∘L root ∘L rightInput) = response

/-!
The input-side version of the Julia/Douglas refinement.  The physical right
column is formed after the right source input has been applied, so the actual
Julia column must be pulled back through that same input map.  Keeping this
ordering in the type prevents the common mistake of proving visibility for
`root` while the trace consumer uses `root ∘L rightInput`.
-/
structure DouglasAlignedInputSideRootS2Producer
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ H) where
  base : InputSideRootS2Producer (K := K) (G := G) sourceBasis
  steps : List (JuliaDefectStep K G)
  rangeColumn : H →L[ℂ]
    PiLp 2 (fun _ : Fin steps.length => G)
  rangeColumn_energy_eq : ∀ x,
    ‖rangeColumn x‖ ^ 2 =
      juliaRangeEnergy steps
        (base.root (base.rightInput x))
  factor : PiLp 2 (fun _ : Fin steps.length => G) →L[ℂ] G
  factorBound : ℝ
  factorBound_nonneg : 0 ≤ factorBound
  factor_norm_le : ‖factor‖ ≤ factorBound
  factorization :
    base.rightFactor ∘L base.root ∘L base.rightInput =
      factor ∘L rangeColumn

/-!
The canonical constructor uses the literal finite Julia range column.  The
remaining argument is exactly the source-specific Douglas factorization; no
scalar Bessel estimate is allowed to manufacture it.
-/
noncomputable def douglasAlignedInputSideRootS2ProducerOfJuliaRangeColumn
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (steps : List (JuliaDefectStep K G))
    (factor : PiLp 2 (fun _ : Fin steps.length => G) →L[ℂ] G)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (factorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        factor ∘L ((juliaRangeColumn (H := K) (G := G) steps) ∘L
          base.root ∘L base.rightInput)) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis :=
  { base := base
    steps := steps
    rangeColumn := (juliaRangeColumn (H := K) (G := G) steps) ∘L
      base.root ∘L base.rightInput
    rangeColumn_energy_eq := fun x =>
      juliaRangeColumn_normSq_eq steps
        (base.root (base.rightInput x))
    factor := factor
    factorBound := factorBound
    factorBound_nonneg := factorBound_nonneg
    factor_norm_le := factor_norm_le
    factorization := factorization }

/-!
The explicit factor is now constructible from the genuine operator estimate.
This is the correct replacement for a caller-supplied Douglas map: the source
producer must prove domination on every source vector, and the closed-range
extension above supplies the bounded factor with the same constant.
-/
noncomputable def douglasAlignedInputSideRootS2ProducerOfOperatorDomination
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (steps : List (JuliaDefectStep K G))
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (hdom : ∀ x : H,
      ‖base.rightFactor (base.root (base.rightInput x))‖ ≤
        factorBound *
          ‖(juliaRangeColumn (H := K) (G := G) steps)
            (base.root (base.rightInput x))‖) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis := by
  let physicalColumn : H →L[ℂ] G :=
    base.rightFactor ∘L base.root ∘L base.rightInput
  let rangeColumn : H →L[ℂ]
      PiLp 2 (fun _ : Fin steps.length => G) :=
    (juliaRangeColumn (H := K) (G := G) steps) ∘L
      base.root ∘L base.rightInput
  let hfactor : ∃ factor :
      PiLp 2 (fun _ : Fin steps.length => G) →L[ℂ] G,
      ‖factor‖ ≤ factorBound ∧ factor ∘L rangeColumn = physicalColumn :=
    CCM24FiniteSDouglasFactor.exists_factor_of_norm_le
      physicalColumn rangeColumn factorBound factorBound_nonneg (by
        intro x
        exact hdom x)
  let factor : PiLp 2 (fun _ : Fin steps.length => G) →L[ℂ] G :=
    Classical.choose hfactor
  have factor_norm_le : ‖factor‖ ≤ factorBound := by
    simpa [factor] using (Classical.choose_spec hfactor).1
  have factorization : factor ∘L rangeColumn = physicalColumn := by
    simpa [factor] using (Classical.choose_spec hfactor).2
  exact douglasAlignedInputSideRootS2ProducerOfJuliaRangeColumn base steps
    factor factorBound factorBound_nonneg factor_norm_le factorization.symm

/-!
The quadratic source form is the direct pointwise readback of a positive
operator inequality such as Proof 382 `(JR.19)`.  It is equivalent to the norm
form under `factorBound_nonneg`, and the same closed-range Douglas factor is
constructed here rather than supplied by the caller.
-/
noncomputable def douglasAlignedInputSideRootS2ProducerOfOperatorNormSqDomination
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (steps : List (JuliaDefectStep K G))
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (hdom : ∀ x : H,
      ‖base.rightFactor (base.root (base.rightInput x))‖ ^ 2 ≤
        factorBound ^ 2 *
          ‖(juliaRangeColumn (H := K) (G := G) steps)
            (base.root (base.rightInput x))‖ ^ 2) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis := by
  let physicalColumn : H →L[ℂ] G :=
    base.rightFactor ∘L base.root ∘L base.rightInput
  let rangeColumn : H →L[ℂ]
      PiLp 2 (fun _ : Fin steps.length => G) :=
    (juliaRangeColumn (H := K) (G := G) steps) ∘L
      base.root ∘L base.rightInput
  let hfactor : ∃ factor :
      PiLp 2 (fun _ : Fin steps.length => G) →L[ℂ] G,
      ‖factor‖ ≤ factorBound ∧ factor ∘L rangeColumn = physicalColumn :=
    CCM24FiniteSDouglasFactor.exists_factor_of_norm_sq_le
      physicalColumn rangeColumn factorBound factorBound_nonneg (by
        intro x
        exact hdom x)
  let factor : PiLp 2 (fun _ : Fin steps.length => G) →L[ℂ] G :=
    Classical.choose hfactor
  have factor_norm_le : ‖factor‖ ≤ factorBound := by
    simpa [factor] using (Classical.choose_spec hfactor).1
  have factorization : factor ∘L rangeColumn = physicalColumn := by
    simpa [factor] using (Classical.choose_spec hfactor).2
  exact douglasAlignedInputSideRootS2ProducerOfJuliaRangeColumn base steps
    factor factorBound factorBound_nonneg factor_norm_le factorization.symm

theorem DouglasAlignedInputSideRootS2Producer.rightColumn_eq_zero_of_rangeColumn_eq_zero
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis)
    {x : H} (hx : producer.rangeColumn x = 0) :
    producer.base.rightFactor
        (producer.base.root (producer.base.rightInput x)) = 0 := by
  have h := congrArg (fun f => f x) producer.factorization
  simpa only [ContinuousLinearMap.comp_apply, hx, map_zero] using h

/-!
The operator-level Douglas domination is recorded before the weaker Julia
Bessel estimate.  This is the exact source obligation: the physical right
column must be controlled by the actual range column, not only by the raw
root energy.
-/
theorem DouglasAlignedInputSideRootS2Producer.rightColumn_normSq_le_of_rangeColumn
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (x : H) :
    ‖producer.base.rightFactor
        (producer.base.root (producer.base.rightInput x))‖ ^ 2 ≤
      producer.factorBound ^ 2 * ‖producer.rangeColumn x‖ ^ 2 := by
  have hfactorization := congrArg (fun f => f x) producer.factorization
  have hfactor_point :
      ‖producer.factor (producer.rangeColumn x)‖ ^ 2 ≤
        (‖producer.factor‖ * ‖producer.rangeColumn x‖) ^ 2 := by
    gcongr
    exact producer.factor.le_opNorm _
  have hfactor_bound_sq : ‖producer.factor‖ ^ 2 ≤
      producer.factorBound ^ 2 := by
    have hprod : 0 ≤ (producer.factorBound - ‖producer.factor‖) *
        (producer.factorBound + ‖producer.factor‖) :=
      mul_nonneg (sub_nonneg.mpr producer.factor_norm_le)
        (add_nonneg producer.factorBound_nonneg (norm_nonneg _))
    nlinarith
  rw [show producer.base.rightFactor
      (producer.base.root (producer.base.rightInput x)) =
        producer.factor (producer.rangeColumn x) by
        simpa only [ContinuousLinearMap.comp_apply] using hfactorization]
  calc
    ‖producer.factor (producer.rangeColumn x)‖ ^ 2 ≤
        (‖producer.factor‖ * ‖producer.rangeColumn x‖) ^ 2 := hfactor_point
    _ = ‖producer.factor‖ ^ 2 * ‖producer.rangeColumn x‖ ^ 2 := by
      ring
    _ ≤ producer.factorBound ^ 2 * ‖producer.rangeColumn x‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right hfactor_bound_sq (sq_nonneg _)

theorem DouglasAlignedInputSideRootS2Producer.rightColumn_normSq_le
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (x : H) :
    ‖producer.base.rightFactor
        (producer.base.root (producer.base.rightInput x))‖ ^ 2 ≤
      producer.factorBound ^ 2 *
        ‖producer.base.root (producer.base.rightInput x)‖ ^ 2 := by
  have hfactorization := congrArg (fun f => f x) producer.factorization
  have hfactorBound_nonneg : 0 ≤ producer.factorBound :=
    producer.factorBound_nonneg
  rw [show producer.base.rightFactor
      (producer.base.root (producer.base.rightInput x)) =
        producer.factor (producer.rangeColumn x) by
        simpa only [ContinuousLinearMap.comp_apply] using hfactorization]
  calc
    ‖producer.factor (producer.rangeColumn x)‖ ^ 2 ≤
        (‖producer.factor‖ * ‖producer.rangeColumn x‖) ^ 2 := by
      gcongr
      exact producer.factor.le_opNorm _
    _ ≤ (producer.factorBound * ‖producer.rangeColumn x‖) ^ 2 := by
      gcongr
      exact producer.factor_norm_le
    _ = producer.factorBound ^ 2 * ‖producer.rangeColumn x‖ ^ 2 := by
      ring
    _ = producer.factorBound ^ 2 *
        juliaRangeEnergy producer.steps
          (producer.base.root (producer.base.rightInput x)) := by
      rw [producer.rangeColumn_energy_eq]
    _ ≤ producer.factorBound ^ 2 *
        ‖producer.base.root (producer.base.rightInput x)‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (juliaRangeEnergy_le_normSq producer.steps
          (producer.base.root (producer.base.rightInput x)))
        (sq_nonneg _)

noncomputable def inputSideRootS2PairData
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : InputSideRootS2Producer (K := K) (G := G) sourceBasis) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis :=
  { left := producer.leftFactor ∘L producer.root ∘L producer.leftInput
    right := producer.rightFactor ∘L producer.root ∘L producer.rightInput
    left_summable_normSq :=
      summable_normSq_postcomp sourceBasis
        (producer.root ∘L producer.leftInput) producer.leftFactor
        producer.leftRoot_summable_normSq
    right_summable_normSq := by
      have henergy : Summable (fun i =>
          juliaRangeEnergy producer.steps
            (producer.root (producer.rightInput (sourceBasis i)))) :=
        summable_juliaRangeEnergy_comp sourceBasis producer.steps
          (producer.root ∘L producer.rightInput)
          producer.rightRoot_summable_normSq
      apply Summable.of_nonneg_of_le
        (fun i => sq_nonneg ‖producer.rightFactor
          (producer.root (producer.rightInput (sourceBasis i)))‖)
        (fun i => by
          simpa only [ContinuousLinearMap.comp_apply] using
            producer.right_energy_le i)
        henergy }

theorem inputSideRootS2PairData_traceProduct_eq_response
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : InputSideRootS2Producer (K := K) (G := G) sourceBasis) :
    (inputSideRootS2PairData producer).traceProduct = producer.response := by
  change (producer.leftFactor ∘L producer.root ∘L producer.leftInput).adjoint ∘L
      (producer.rightFactor ∘L producer.root ∘L producer.rightInput) =
      producer.response
  exact producer.response_eq

/-!
The pair-data owner can be lifted to the input-side interface without
changing the physical right leg.  The root is the orthogonal `L2` packing of
the two already assembled legs; the left factor keeps that complete packing,
while the right factor reads its second coordinate.  This is the canonical
common-root realization of a signed pair, so signs and quotient corrections
remain inside the packed legs rather than being estimated branchwise.

This theorem is an ownership result only.  Its Julia row is still the
bookkeeping row inherited from `commonRootS2ProducerOfPairData`; it does not
claim the moving Schur co-defect estimate.
-/
noncomputable def inputSideRootS2ProducerOfPairData
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    InputSideRootS2Producer
      (K := WithLp 2 (G × G))
      (G := WithLp 2 (G × G)) sourceBasis := by
  let base := commonRootS2ProducerOfPairData data
  refine
    { root := base.root
      leftInput := ContinuousLinearMap.id ℂ H
      rightInput := ContinuousLinearMap.id ℂ H
      leftFactor := base.leftFactor
      rightFactor := base.rightFactor
      leftRoot_summable_normSq := base.root_summable_normSq
      rightRoot_summable_normSq := base.root_summable_normSq
      steps := base.steps
      right_energy_le := by
        intro i
        simpa only [ContinuousLinearMap.id_apply] using base.right_energy_le i
      response := base.response
      response_eq := by
        simpa only [ContinuousLinearMap.id_comp,
          ContinuousLinearMap.comp_id] using base.response_eq }

theorem inputSideRootS2ProducerOfPairData_response_eq
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    (inputSideRootS2ProducerOfPairData data).response = data.traceProduct := by
  change (commonRootS2ProducerOfPairData data).response = data.traceProduct
  exact commonRootS2ProducerOfPairData_response_eq data

theorem inputSideRootS2ProducerOfPairData_root_energy_eq
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    ∑' i, ‖(inputSideRootS2ProducerOfPairData data).root
        (sourceBasis i)‖ ^ 2 =
      ∑' i, (‖data.left (sourceBasis i)‖ ^ 2 +
        ‖data.right (sourceBasis i)‖ ^ 2) := by
  exact commonRootS2ProducerOfPairData_root_energy_eq data

/-! A bookkeeping Julia row for an exact identity factor. -/
noncomputable def identityJuliaDefectStep
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] :
    JuliaDefectStep K K :=
  { transfer := 0
    defect := ContinuousLinearMap.id ℂ K
    rangeSine := ContinuousLinearMap.id ℂ K
    weight := 1
    weight_nonneg := by norm_num
    pythagorean := by
      intro x
      simp
    rangeSine_weighted_le_defect := by
      intro x
      simp }

/-!
The actual compact half-line pair has one full root and two input-side
projections.  This is the concrete order needed by the physical root bundle.
The identity Julia row is intentionally used only as a fixed-crossing
readback; it carries no finite-S or Schur information.
-/
noncomputable def compactBoundaryInputSideProducer
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    InputSideRootS2Producer (K := Lp ℂ 2
      (volume : Measure (BoundaryOutputInterval a c)))
      (G := Lp ℂ 2
        (volume : Measure (BoundaryOutputInterval a c))) globalBasis :=
  { root := CompactRootHalfLinePair.fullBoundaryRootFactor g a c
    leftInput := cc20NegativeHalfLineProjection
    rightInput := cc20PositiveHalfLineProjection
    leftFactor := ContinuousLinearMap.id ℂ _
    rightFactor := ContinuousLinearMap.id ℂ _
    leftRoot_summable_normSq := by
      have hpair :=
        (CompactRootHalfLinePair.pairData g a c negativeBasis positiveBasis
          outputBasis globalBasis).left_summable_normSq
      have hroot :=
        CompactRootHalfLinePair.fullBoundaryRootFactor_comp_negativeHalfLineProjection
          g a c hac
      change Summable (fun i =>
        ‖(CompactRootHalfLinePair.fullBoundaryRootFactor g a c ∘L
          cc20NegativeHalfLineProjection) (globalBasis i)‖ ^ 2)
      rw [hroot]
      exact hpair
    rightRoot_summable_normSq := by
      have hpair :=
        (CompactRootHalfLinePair.pairData g a c negativeBasis positiveBasis
          outputBasis globalBasis).right_summable_normSq
      have hroot :=
        CompactRootHalfLinePair.fullBoundaryRootFactor_comp_positiveHalfLineProjection
          g a c hac
      change Summable (fun i =>
        ‖(CompactRootHalfLinePair.fullBoundaryRootFactor g a c ∘L
          cc20PositiveHalfLineProjection) (globalBasis i)‖ ^ 2)
      rw [hroot]
      exact hpair
    steps := [identityJuliaDefectStep]
    right_energy_le := by
      intro i
      simp [identityJuliaDefectStep, juliaRangeEnergy]
    response :=
      (CompactRootHalfLinePair.pairData g a c negativeBasis positiveBasis
        outputBasis globalBasis).traceProduct
    response_eq := by
      rw [CompactRootHalfLinePair.pairData_traceProduct_eq]
      rw [← CompactRootHalfLinePair.fullBoundaryRootFactor_comp_negativeHalfLineProjection
        g a c hac]
      rw [← CompactRootHalfLinePair.fullBoundaryRootFactor_comp_positiveHalfLineProjection
        g a c hac]
      simp }

theorem compactBoundaryInputSideProducer_response_eq_pairData
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    (compactBoundaryInputSideProducer g a c hac negativeBasis positiveBasis
      outputBasis globalBasis).response =
      (CompactRootHalfLinePair.pairData g a c negativeBasis positiveBasis
        outputBasis globalBasis).traceProduct := by
  rfl

noncomputable def translatedCompactBoundaryInputSideProducer
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    InputSideRootS2Producer (K := Lp ℂ 2
      (volume : Measure (BoundaryOutputInterval a c)))
      (G := Lp ℂ 2
        (volume : Measure (BoundaryOutputInterval a c))) globalBasis := by
  let data := translatedCompactRootPairData owner lambda a c negativeBasis
    positiveBasis outputBasis globalBasis
  let uPlus :=
    (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
  let uMinus :=
    (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap
  have hnegative :=
    CompactRootHalfLinePair.fullBoundaryRootFactor_comp_negativeHalfLineProjection
      owner.sourceTest a c hac
  have hpositive :=
    CompactRootHalfLinePair.fullBoundaryRootFactor_comp_positiveHalfLineProjection
      owner.sourceTest a c hac
  have hleft :
      CompactRootHalfLinePair.fullBoundaryRootFactor owner.sourceTest a c ∘L
          (cc20NegativeHalfLineProjection ∘L uPlus) = data.left := by
    change CompactRootHalfLinePair.fullBoundaryRootFactor owner.sourceTest a c ∘L
          (cc20NegativeHalfLineProjection ∘L uPlus) =
        CompactRootHalfLinePair.negativeBoundaryRootFactor owner.sourceTest a c ∘L
          uMinus.adjoint
    calc
      CompactRootHalfLinePair.fullBoundaryRootFactor owner.sourceTest a c ∘L
          (cc20NegativeHalfLineProjection ∘L uPlus) =
          (CompactRootHalfLinePair.fullBoundaryRootFactor owner.sourceTest a c ∘L
            cc20NegativeHalfLineProjection) ∘L uPlus := by
              apply ContinuousLinearMap.ext
              intro u
              rfl
      _ = CompactRootHalfLinePair.negativeBoundaryRootFactor
            owner.sourceTest a c ∘L uPlus := by rw [hnegative]
      _ = CompactRootHalfLinePair.negativeBoundaryRootFactor
            owner.sourceTest a c ∘L uMinus.adjoint := by
            simp [uPlus, uMinus,
              SelectedCrossingOperatorBridge.cc20GlobalLogTranslation_neg_adjoint]
  have hright :
      CompactRootHalfLinePair.fullBoundaryRootFactor owner.sourceTest a c ∘L
          (cc20PositiveHalfLineProjection ∘L uPlus) = data.right := by
    change CompactRootHalfLinePair.fullBoundaryRootFactor owner.sourceTest a c ∘L
          (cc20PositiveHalfLineProjection ∘L uPlus) =
        CompactRootHalfLinePair.positiveBoundaryRootFactor owner.sourceTest a c ∘L
          uPlus
    calc
      CompactRootHalfLinePair.fullBoundaryRootFactor owner.sourceTest a c ∘L
          (cc20PositiveHalfLineProjection ∘L uPlus) =
          (CompactRootHalfLinePair.fullBoundaryRootFactor owner.sourceTest a c ∘L
            cc20PositiveHalfLineProjection) ∘L uPlus := by
              apply ContinuousLinearMap.ext
              intro u
              rfl
      _ = CompactRootHalfLinePair.positiveBoundaryRootFactor
            owner.sourceTest a c ∘L uPlus := by rw [hpositive]
  refine
    { root := CompactRootHalfLinePair.fullBoundaryRootFactor owner.sourceTest a c
      leftInput := cc20NegativeHalfLineProjection ∘L uPlus
      rightInput := cc20PositiveHalfLineProjection ∘L uPlus
      leftFactor := ContinuousLinearMap.id ℂ _
      rightFactor := ContinuousLinearMap.id ℂ _
      leftRoot_summable_normSq := by
        change Summable (fun i => ‖
          (CompactRootHalfLinePair.fullBoundaryRootFactor owner.sourceTest a c ∘L
            (cc20NegativeHalfLineProjection ∘L uPlus)) (globalBasis i)‖ ^ 2)
        rw [hleft]
        exact data.left_summable_normSq
      rightRoot_summable_normSq := by
        change Summable (fun i => ‖
          (CompactRootHalfLinePair.fullBoundaryRootFactor owner.sourceTest a c ∘L
            (cc20PositiveHalfLineProjection ∘L uPlus)) (globalBasis i)‖ ^ 2)
        rw [hright]
        exact data.right_summable_normSq
      steps := [identityJuliaDefectStep]
      right_energy_le := by
        intro i
        simp [identityJuliaDefectStep, juliaRangeEnergy]
      response := data.traceProduct
      response_eq := by
        simp only [ContinuousLinearMap.id_comp]
        rw [hleft, hright]
        rfl }

theorem translatedCompactBoundaryInputSideProducer_response_eq_pairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    (translatedCompactBoundaryInputSideProducer owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis globalBasis).response =
      (translatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).traceProduct := by
  rfl

noncomputable def commonRootS2PairData
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : CommonRootS2Producer (K := K) (G := G) sourceBasis) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis :=
  { left := producer.leftFactor ∘L producer.root
    right := producer.rightFactor ∘L producer.root
    left_summable_normSq :=
      summable_normSq_postcomp sourceBasis producer.root producer.leftFactor
        producer.root_summable_normSq
    right_summable_normSq := by
      have henergy : Summable (fun i =>
          juliaRangeEnergy producer.steps (producer.root (sourceBasis i))) :=
        summable_juliaRangeEnergy_comp sourceBasis producer.steps producer.root
          producer.root_summable_normSq
      apply Summable.of_nonneg_of_le
        (fun i => sq_nonneg ‖producer.rightFactor
          (producer.root (sourceBasis i))‖)
        (fun i => by
          simpa only [ContinuousLinearMap.comp_apply] using
            producer.right_energy_le i)
        henergy }

theorem commonRootS2PairData_traceProduct_eq_response
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : CommonRootS2Producer (K := K) (G := G) sourceBasis) :
    (commonRootS2PairData producer).traceProduct = producer.response := by
  change (producer.leftFactor ∘L producer.root).adjoint ∘L
      (producer.rightFactor ∘L producer.root) = producer.response
  exact producer.response_eq

theorem commonRootS2PairData_left_energy_le
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : CommonRootS2Producer (K := K) (G := G) sourceBasis) :
    ∑' i, ‖(commonRootS2PairData producer).left (sourceBasis i)‖ ^ 2 ≤
      ‖producer.leftFactor‖ ^ 2 *
        (∑' i, ‖producer.root (sourceBasis i)‖ ^ 2) := by
  have hleft := (commonRootS2PairData producer).left_summable_normSq
  have hmajorant : Summable (fun i =>
      ‖producer.leftFactor‖ ^ 2 *
        ‖producer.root (sourceBasis i)‖ ^ 2) :=
    producer.root_summable_normSq.mul_left (‖producer.leftFactor‖ ^ 2)
  calc
    ∑' i, ‖(commonRootS2PairData producer).left (sourceBasis i)‖ ^ 2 ≤
        ∑' i, ‖producer.leftFactor‖ ^ 2 *
          ‖producer.root (sourceBasis i)‖ ^ 2 := by
      apply hleft.tsum_le_tsum
      · intro i
        change ‖producer.leftFactor
            (producer.root (sourceBasis i))‖ ^ 2 ≤ _
        calc
          ‖producer.leftFactor
              (producer.root (sourceBasis i))‖ ^ 2 ≤
              (‖producer.leftFactor‖ *
                ‖producer.root (sourceBasis i)‖) ^ 2 := by
            gcongr
            exact producer.leftFactor.le_opNorm _
          _ = ‖producer.leftFactor‖ ^ 2 *
              ‖producer.root (sourceBasis i)‖ ^ 2 := by ring
      · exact hmajorant
    _ = ‖producer.leftFactor‖ ^ 2 *
        (∑' i, ‖producer.root (sourceBasis i)‖ ^ 2) := by
      rw [tsum_mul_left]

theorem commonRootS2PairData_right_energy_le
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : CommonRootS2Producer (K := K) (G := G) sourceBasis) :
    ∑' i, ‖(commonRootS2PairData producer).right (sourceBasis i)‖ ^ 2 ≤
      ∑' i, juliaRangeEnergy producer.steps
        (producer.root (sourceBasis i)) := by
  have hright := (commonRootS2PairData producer).right_summable_normSq
  have henergy : Summable (fun i =>
      juliaRangeEnergy producer.steps (producer.root (sourceBasis i))) :=
    summable_juliaRangeEnergy_comp sourceBasis producer.steps producer.root
      producer.root_summable_normSq
  apply hright.tsum_le_tsum
  · intro i
    simpa only [ContinuousLinearMap.comp_apply] using producer.right_energy_le i
  · exact henergy

theorem commonRootS2Producer_ordinaryTrace_norm_le
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : CommonRootS2Producer (K := K) (G := G) sourceBasis) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        producer.response‖ ≤
      (1 / 2 : ℝ) * (‖producer.leftFactor‖ ^ 2 + 1) *
        (∑' i, ‖producer.root (sourceBasis i)‖ ^ 2) := by
  let hdata := commonRootS2PairData producer
  have hresponse := commonRootS2PairData_traceProduct_eq_response producer
  have htrace : CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      producer.response := by
    rw [← hresponse]
    exact (commonRootS2PairData producer).traceProduct_isTraceClassAlong
  have hdiag : Summable (fun i =>
      ‖⟪sourceBasis i, producer.response (sourceBasis i)⟫_ℂ‖) :=
    htrace.norm
  have hmajorant : Summable (fun i =>
      (1 / 2 : ℝ) * (‖producer.leftFactor‖ ^ 2 + 1) *
        ‖producer.root (sourceBasis i)‖ ^ 2) := by
    exact producer.root_summable_normSq.mul_left
      ((1 / 2 : ℝ) * (‖producer.leftFactor‖ ^ 2 + 1))
  have hpoint : ∀ i, ‖⟪sourceBasis i,
      producer.response (sourceBasis i)⟫_ℂ‖ ≤
        (1 / 2 : ℝ) * (‖producer.leftFactor‖ ^ 2 + 1) *
          ‖producer.root (sourceBasis i)‖ ^ 2 := by
    intro i
    have hdiagonal :
        ⟪sourceBasis i, producer.response (sourceBasis i)⟫_ℂ =
          ⟪hdata.left (sourceBasis i), hdata.right (sourceBasis i)⟫_ℂ := by
      rw [← hresponse]
      exact hdata.traceProduct_diagonal i
    rw [hdiagonal]
    have hleft : ‖hdata.left (sourceBasis i)‖ ^ 2 ≤
        ‖producer.leftFactor‖ ^ 2 *
          ‖producer.root (sourceBasis i)‖ ^ 2 := by
      change ‖producer.leftFactor
          (producer.root (sourceBasis i))‖ ^ 2 ≤ _
      calc
        ‖producer.leftFactor
            (producer.root (sourceBasis i))‖ ^ 2 ≤
            (‖producer.leftFactor‖ *
              ‖producer.root (sourceBasis i)‖) ^ 2 := by
          gcongr
          exact producer.leftFactor.le_opNorm _
        _ = ‖producer.leftFactor‖ ^ 2 *
            ‖producer.root (sourceBasis i)‖ ^ 2 := by ring
    have hright : ‖hdata.right (sourceBasis i)‖ ^ 2 ≤
        juliaRangeEnergy producer.steps
          (producer.root (sourceBasis i)) := by
      change ‖producer.rightFactor
          (producer.root (sourceBasis i))‖ ^ 2 ≤ _
      exact producer.right_energy_le i
    have hrange := juliaRangeEnergy_le_normSq producer.steps
      (producer.root (sourceBasis i))
    have hsum : ‖hdata.left (sourceBasis i)‖ ^ 2 +
        ‖hdata.right (sourceBasis i)‖ ^ 2 ≤
        (‖producer.leftFactor‖ ^ 2 + 1) *
          ‖producer.root (sourceBasis i)‖ ^ 2 := by
      calc
        ‖hdata.left (sourceBasis i)‖ ^ 2 +
            ‖hdata.right (sourceBasis i)‖ ^ 2 ≤
            ‖producer.leftFactor‖ ^ 2 *
              ‖producer.root (sourceBasis i)‖ ^ 2 +
              juliaRangeEnergy producer.steps
                (producer.root (sourceBasis i)) :=
          add_le_add hleft hright
        _ ≤ ‖producer.leftFactor‖ ^ 2 *
              ‖producer.root (sourceBasis i)‖ ^ 2 +
              ‖producer.root (sourceBasis i)‖ ^ 2 :=
           add_le_add_right hrange _
        _ = (‖producer.leftFactor‖ ^ 2 + 1) *
            ‖producer.root (sourceBasis i)‖ ^ 2 := by ring
    calc
      ‖⟪hdata.left (sourceBasis i), hdata.right (sourceBasis i)⟫_ℂ‖ ≤
          ‖hdata.left (sourceBasis i)‖ *
            ‖hdata.right (sourceBasis i)‖ := norm_inner_le_norm _ _
      _ ≤ (1 / 2 : ℝ) *
          (‖hdata.left (sourceBasis i)‖ ^ 2 +
            ‖hdata.right (sourceBasis i)‖ ^ 2) := by
        nlinarith [sq_nonneg
          (‖hdata.left (sourceBasis i)‖ -
            ‖hdata.right (sourceBasis i)‖)]
      _ ≤ (1 / 2 : ℝ) * (‖producer.leftFactor‖ ^ 2 + 1) *
          ‖producer.root (sourceBasis i)‖ ^ 2 := by
        calc
          (1 / 2 : ℝ) *
              (‖hdata.left (sourceBasis i)‖ ^ 2 +
                ‖hdata.right (sourceBasis i)‖ ^ 2) ≤
              (1 / 2 : ℝ) *
                ((‖producer.leftFactor‖ ^ 2 + 1) *
                  ‖producer.root (sourceBasis i)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsum (by norm_num)
          _ = (1 / 2 : ℝ) *
              (‖producer.leftFactor‖ ^ 2 + 1) *
                ‖producer.root (sourceBasis i)‖ ^ 2 := by ring
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong]
  calc
    ‖∑' i, ⟪sourceBasis i,
        producer.response (sourceBasis i)⟫_ℂ‖ ≤
        ∑' i, ‖⟪sourceBasis i,
          producer.response (sourceBasis i)⟫_ℂ‖ :=
      norm_tsum_le_tsum_norm hdiag
    _ ≤ ∑' i, (1 / 2 : ℝ) *
        (‖producer.leftFactor‖ ^ 2 + 1) *
          ‖producer.root (sourceBasis i)‖ ^ 2 :=
      hdiag.tsum_le_tsum hpoint hmajorant
    _ = (1 / 2 : ℝ) * (‖producer.leftFactor‖ ^ 2 + 1) *
        (∑' i, ‖producer.root (sourceBasis i)‖ ^ 2) := by
      rw [tsum_mul_left]

theorem commonRootS2Producer_ordinaryTrace_norm_le_of_bounds
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : CommonRootS2Producer (K := K) (G := G) sourceBasis)
    (rootBound leftFactorBound : ℝ)
    (hroot : (∑' i, ‖producer.root (sourceBasis i)‖ ^ 2) ≤ rootBound)
    (hroot_nonneg : 0 ≤ rootBound)
    (hleft : ‖producer.leftFactor‖ ≤ leftFactorBound)
    (hleft_nonneg : 0 ≤ leftFactorBound) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        producer.response‖ ≤
      (1 / 2 : ℝ) * (leftFactorBound ^ 2 + 1) * rootBound := by
  have hfactor : ‖producer.leftFactor‖ ^ 2 + 1 ≤
      leftFactorBound ^ 2 + 1 := by
    have hprod : 0 ≤ (leftFactorBound - ‖producer.leftFactor‖) *
        (leftFactorBound + ‖producer.leftFactor‖) :=
      mul_nonneg (sub_nonneg.mpr hleft)
        (add_nonneg hleft_nonneg (norm_nonneg _))
    nlinarith
  have henergy_nonneg : 0 ≤
      (∑' i, ‖producer.root (sourceBasis i)‖ ^ 2) :=
    tsum_nonneg fun i => sq_nonneg _
  have hproduct :
      (‖producer.leftFactor‖ ^ 2 + 1) *
          (∑' i, ‖producer.root (sourceBasis i)‖ ^ 2) ≤
        (leftFactorBound ^ 2 + 1) * rootBound :=
    mul_le_mul hfactor hroot henergy_nonneg
      (add_nonneg (sq_nonneg _) zero_le_one)
  calc
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        producer.response‖ ≤
        (1 / 2 : ℝ) * (‖producer.leftFactor‖ ^ 2 + 1) *
          (∑' i, ‖producer.root (sourceBasis i)‖ ^ 2) :=
      commonRootS2Producer_ordinaryTrace_norm_le producer
    _ ≤ (1 / 2 : ℝ) * (leftFactorBound ^ 2 + 1) * rootBound := by
      calc
        (1 / 2 : ℝ) * (‖producer.leftFactor‖ ^ 2 + 1) *
            (∑' i, ‖producer.root (sourceBasis i)‖ ^ 2) =
            (1 / 2 : ℝ) *
              ((‖producer.leftFactor‖ ^ 2 + 1) *
                (∑' i, ‖producer.root (sourceBasis i)‖ ^ 2)) := by
          ring
        _ ≤ (1 / 2 : ℝ) *
              ((leftFactorBound ^ 2 + 1) * rootBound) :=
          mul_le_mul_of_nonneg_left hproduct (by norm_num)
        _ = (1 / 2 : ℝ) * (leftFactorBound ^ 2 + 1) * rootBound := by
          ring

/-!
The Douglas-aligned consumer uses the actual range column instead of the old
constant-one bookkeeping row.  The only right-leg estimate used below is the
factorization through `rangeColumn`; the Julia Bessel inequality is applied
after that factorization, so the source-specific visibility condition cannot be
lost in a total-energy estimate.
-/
theorem douglasAlignedCommonRootS2Producer_ordinaryTrace_norm_le
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : DouglasAlignedCommonRootS2Producer (K := K) (G := G) sourceBasis) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        producer.base.response‖ ≤
      (1 / 2 : ℝ) *
        (‖producer.base.leftFactor‖ ^ 2 + producer.factorBound ^ 2) *
        (∑' i, ‖producer.base.root (sourceBasis i)‖ ^ 2) := by
  let hdata := commonRootS2PairData producer.base
  have hresponse :=
    commonRootS2PairData_traceProduct_eq_response producer.base
  have htrace : CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      producer.base.response := by
    rw [← hresponse]
    exact (commonRootS2PairData producer.base).traceProduct_isTraceClassAlong
  have hdiag : Summable (fun i =>
      ‖⟪sourceBasis i, producer.base.response (sourceBasis i)⟫_ℂ‖) :=
    htrace.norm
  have hroot : Summable (fun i =>
      ‖producer.base.root (sourceBasis i)‖ ^ 2) :=
    producer.base.root_summable_normSq
  have hmajorant : Summable (fun i =>
      (1 / 2 : ℝ) *
        (‖producer.base.leftFactor‖ ^ 2 + producer.factorBound ^ 2) *
        ‖producer.base.root (sourceBasis i)‖ ^ 2) := by
    exact hroot.mul_left
      ((1 / 2 : ℝ) *
        (‖producer.base.leftFactor‖ ^ 2 + producer.factorBound ^ 2))
  have hpoint : ∀ i, ‖⟪sourceBasis i,
      producer.base.response (sourceBasis i)⟫_ℂ‖ ≤
      (1 / 2 : ℝ) *
        (‖producer.base.leftFactor‖ ^ 2 + producer.factorBound ^ 2) *
        ‖producer.base.root (sourceBasis i)‖ ^ 2 := by
    intro i
    have hdiagonal :
        ⟪sourceBasis i, producer.base.response (sourceBasis i)⟫_ℂ =
          ⟪hdata.left (sourceBasis i), hdata.right (sourceBasis i)⟫_ℂ := by
      rw [← hresponse]
      exact hdata.traceProduct_diagonal i
    rw [hdiagonal]
    have hleft : ‖hdata.left (sourceBasis i)‖ ^ 2 ≤
        ‖producer.base.leftFactor‖ ^ 2 *
          ‖producer.base.root (sourceBasis i)‖ ^ 2 := by
      change ‖producer.base.leftFactor
          (producer.base.root (sourceBasis i))‖ ^ 2 ≤ _
      calc
        ‖producer.base.leftFactor
            (producer.base.root (sourceBasis i))‖ ^ 2 ≤
            (‖producer.base.leftFactor‖ *
              ‖producer.base.root (sourceBasis i)‖) ^ 2 := by
          gcongr
          exact producer.base.leftFactor.le_opNorm _
        _ = ‖producer.base.leftFactor‖ ^ 2 *
            ‖producer.base.root (sourceBasis i)‖ ^ 2 := by ring
    have hright : ‖hdata.right (sourceBasis i)‖ ^ 2 ≤
        producer.factorBound ^ 2 *
          ‖producer.base.root (sourceBasis i)‖ ^ 2 := by
      change ‖producer.base.rightFactor
          (producer.base.root (sourceBasis i))‖ ^ 2 ≤ _
      exact producer.rightColumn_normSq_le (sourceBasis i)
    have hsum : ‖hdata.left (sourceBasis i)‖ ^ 2 +
        ‖hdata.right (sourceBasis i)‖ ^ 2 ≤
        (‖producer.base.leftFactor‖ ^ 2 + producer.factorBound ^ 2) *
          ‖producer.base.root (sourceBasis i)‖ ^ 2 := by
      exact (add_le_add hleft hright).trans_eq (by ring)
    calc
      ‖⟪hdata.left (sourceBasis i), hdata.right (sourceBasis i)⟫_ℂ‖ ≤
          ‖hdata.left (sourceBasis i)‖ *
            ‖hdata.right (sourceBasis i)‖ := norm_inner_le_norm _ _
      _ ≤ (1 / 2 : ℝ) *
          (‖hdata.left (sourceBasis i)‖ ^ 2 +
            ‖hdata.right (sourceBasis i)‖ ^ 2) := by
        nlinarith [sq_nonneg
          (‖hdata.left (sourceBasis i)‖ -
            ‖hdata.right (sourceBasis i)‖)]
      _ ≤ (1 / 2 : ℝ) *
          ((‖producer.base.leftFactor‖ ^ 2 + producer.factorBound ^ 2) *
            ‖producer.base.root (sourceBasis i)‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = (1 / 2 : ℝ) *
          (‖producer.base.leftFactor‖ ^ 2 + producer.factorBound ^ 2) *
            ‖producer.base.root (sourceBasis i)‖ ^ 2 := by ring
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong]
  calc
    ‖∑' i, ⟪sourceBasis i,
        producer.base.response (sourceBasis i)⟫_ℂ‖ ≤
        ∑' i, ‖⟪sourceBasis i,
          producer.base.response (sourceBasis i)⟫_ℂ‖ :=
      norm_tsum_le_tsum_norm hdiag
    _ ≤ ∑' i, (1 / 2 : ℝ) *
        (‖producer.base.leftFactor‖ ^ 2 + producer.factorBound ^ 2) *
        ‖producer.base.root (sourceBasis i)‖ ^ 2 :=
      hdiag.tsum_le_tsum hpoint hmajorant
    _ = (1 / 2 : ℝ) *
        (‖producer.base.leftFactor‖ ^ 2 + producer.factorBound ^ 2) *
        (∑' i, ‖producer.base.root (sourceBasis i)‖ ^ 2) := by
      rw [tsum_mul_left]

/-!
This is the route-facing form.  To use it for Gate 3U, the missing concrete
producer must set `response` to the complete corrected physical bracket and
prove the displayed factorization.  The theorem itself does not insert that
identity or any uniform numerical bound.
-/
theorem correctedPhysicalBracket_ordinaryTrace_norm_le_of_commonRoot
    {ι K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (a c : ℝ) (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (producer : CommonRootS2Producer
      (H := finiteSCarrier) (K := K)
      (G := correctedBoundaryCarrier a c) sourceBasis)
    (support secondSupport prolate detector transport :
      finiteSCarrier →L[ℂ] finiteSCarrier)
    (hresponse : producer.response =
      correctedPhysicalBracket support secondSupport prolate detector transport) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (correctedPhysicalBracket support secondSupport prolate detector transport)‖ ≤
      (1 / 2 : ℝ) * (‖producer.leftFactor‖ ^ 2 + 1) *
        (∑' i, ‖producer.root (sourceBasis i)‖ ^ 2) := by
  rw [← hresponse]
  exact commonRootS2Producer_ordinaryTrace_norm_le producer

/-! The same consumer on the actual source-Sonin trace carrier. -/
theorem sourceBandGramResponse_ordinaryTrace_norm_le_of_commonRoot
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (producer : CommonRootS2Producer
      (H := sourceSoninCarrier lambda) (K := K)
      (G := G) sourceBasis)
    (hresponse : producer.response =
      sourceBandGramResponse owner lambda family) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      (1 / 2 : ℝ) * (‖producer.leftFactor‖ ^ 2 + 1) *
        (∑' i, ‖producer.root (sourceBasis i)‖ ^ 2) := by
  rw [← hresponse]
  exact commonRootS2Producer_ordinaryTrace_norm_le producer

/-!
The route-facing theorem now demands the real Schur/Douglas producer.  In
particular, a `CommonRootS2Producer` with the identity bookkeeping row cannot
be substituted for this theorem: it has no `rangeColumn` or `factorization`.
-/
theorem sourceBandGramResponse_ordinaryTrace_norm_le_of_douglasAligned
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (producer : DouglasAlignedCommonRootS2Producer (K := K) (G := G) sourceBasis)
    (hresponse : producer.base.response =
      sourceBandGramResponse owner lambda family) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      (1 / 2 : ℝ) *
        (‖producer.base.leftFactor‖ ^ 2 + producer.factorBound ^ 2) *
        (∑' i, ‖producer.base.root (sourceBasis i)‖ ^ 2) := by
  rw [← hresponse]
  exact douglasAlignedCommonRootS2Producer_ordinaryTrace_norm_le producer

theorem sourceBandGramResponse_ordinaryTrace_norm_le_of_douglasAligned_bounds
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (producer : DouglasAlignedCommonRootS2Producer (K := K) (G := G) sourceBasis)
    (rootBound leftFactorBound factorBound : ℝ)
    (hroot : (∑' i, ‖producer.base.root (sourceBasis i)‖ ^ 2) ≤
      rootBound)
    (hroot_nonneg : 0 ≤ rootBound)
    (hleft : ‖producer.base.leftFactor‖ ≤ leftFactorBound)
    (hleft_nonneg : 0 ≤ leftFactorBound)
    (hfactor : producer.factorBound ≤ factorBound)
    (hfactor_nonneg : 0 ≤ factorBound)
    (hresponse : producer.base.response =
      sourceBandGramResponse owner lambda family) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      (1 / 2 : ℝ) *
        (leftFactorBound ^ 2 + factorBound ^ 2) * rootBound := by
  have hleft_sq : ‖producer.base.leftFactor‖ ^ 2 ≤
      leftFactorBound ^ 2 := by
    have hprod : 0 ≤ (leftFactorBound -
        ‖producer.base.leftFactor‖) *
        (leftFactorBound + ‖producer.base.leftFactor‖) :=
      mul_nonneg (sub_nonneg.mpr hleft)
        (add_nonneg hleft_nonneg (norm_nonneg _))
    nlinarith
  have hfactor_sq : producer.factorBound ^ 2 ≤
      factorBound ^ 2 := by
    have hprod : 0 ≤ (factorBound - producer.factorBound) *
        (factorBound + producer.factorBound) :=
      mul_nonneg (sub_nonneg.mpr hfactor)
        (add_nonneg hfactor_nonneg producer.factorBound_nonneg)
    nlinarith
  have hconstant : ‖producer.base.leftFactor‖ ^ 2 +
      producer.factorBound ^ 2 ≤
      leftFactorBound ^ 2 + factorBound ^ 2 :=
    add_le_add hleft_sq hfactor_sq
  have henergy_nonneg : 0 ≤
      (∑' i, ‖producer.base.root (sourceBasis i)‖ ^ 2) :=
    tsum_nonneg fun i => sq_nonneg _
  have hproduct :
      (‖producer.base.leftFactor‖ ^ 2 + producer.factorBound ^ 2) *
          (∑' i, ‖producer.base.root (sourceBasis i)‖ ^ 2) ≤
        (leftFactorBound ^ 2 + factorBound ^ 2) * rootBound :=
    mul_le_mul hconstant hroot henergy_nonneg (by positivity)
  calc
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
        (1 / 2 : ℝ) *
          (‖producer.base.leftFactor‖ ^ 2 + producer.factorBound ^ 2) *
          (∑' i, ‖producer.base.root (sourceBasis i)‖ ^ 2) :=
      sourceBandGramResponse_ordinaryTrace_norm_le_of_douglasAligned
        owner lambda family sourceBasis producer hresponse
    _ ≤ (1 / 2 : ℝ) *
        (leftFactorBound ^ 2 + factorBound ^ 2) * rootBound := by
      calc
        (1 / 2 : ℝ) *
            (‖producer.base.leftFactor‖ ^ 2 + producer.factorBound ^ 2) *
              (∑' i, ‖producer.base.root (sourceBasis i)‖ ^ 2) =
            (1 / 2 : ℝ) *
              ((‖producer.base.leftFactor‖ ^ 2 + producer.factorBound ^ 2) *
                (∑' i, ‖producer.base.root (sourceBasis i)‖ ^ 2)) := by
          ring
        _ ≤ (1 / 2 : ℝ) *
              ((leftFactorBound ^ 2 + factorBound ^ 2) * rootBound) :=
          mul_le_mul_of_nonneg_left hproduct (by norm_num)
        _ = (1 / 2 : ℝ) *
            (leftFactorBound ^ 2 + factorBound ^ 2) * rootBound := by
          ring

/-!
The two radial outer orientations are first combined in one pair owner.  The
minus sign in the reversed orientation is in the right leg of the `L2` sum.
-/
noncomputable def outerCommutatorPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := WithLp 2
        (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) ×
          Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
      globalBasis :=
  (translatedCompactRootPairData owner lambda a c negativeBasis positiveBasis
    outputBasis globalBasis).boundedAdjointSub outputBasis
      (radialSupportProjection lambda ∘L sourceFourierSupportProjection lambda)
      (ContinuousLinearMap.id ℂ finiteSCarrier)

theorem outerCommutatorPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (outerCommutatorPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis globalBasis).traceProduct =
      cc20OuterCommutatorBranch (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda) (detectorOperator owner) := by
  rw [outerCommutatorPairData,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedAdjointSub_traceProduct_eq]
  have hcomm := translatedSignedCompactRootPairOperator_eq_radialCommutator
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis
  unfold translatedSignedCompactRootPairOperator at hcomm
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  calc
    radialSupportProjection lambda
        (sourceFourierSupportProjection lambda
          ((translatedCompactRootPairData owner lambda a c negativeBasis
            positiveBasis outputBasis globalBasis).traceProduct.adjoint u)) -
        radialSupportProjection lambda
          (sourceFourierSupportProjection lambda
            ((translatedCompactRootPairData owner lambda a c negativeBasis
              positiveBasis outputBasis globalBasis).traceProduct u)) =
      radialSupportProjection lambda
        (sourceFourierSupportProjection lambda
          (((translatedCompactRootPairData owner lambda a c negativeBasis
            positiveBasis outputBasis globalBasis).traceProduct.adjoint -
            (translatedCompactRootPairData owner lambda a c negativeBasis
              positiveBasis outputBasis globalBasis).traceProduct) u)) := by
        simp only [ContinuousLinearMap.sub_apply, map_sub]
    _ = radialSupportProjection lambda
          (sourceFourierSupportProjection lambda
            (cc20Commutator (radialSupportProjection lambda)
              (detectorOperator owner) u)) := by rw [hcomm]
    _ = cc20OuterCommutatorBranch (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda) (detectorOperator owner) u := by
        rfl

/-! The reflected outer branch is the adjoint of the first branch with the
route sign retained in the same pair owner. -/
noncomputable def reflectedOuterCommutatorPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := WithLp 2
        (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))) ×
          Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
      globalBasis :=
  (reflectedTranslatedCompactRootPairData owner lambda a c negativeBasis
    positiveBasis outputBasis globalBasis).boundedAdjointSub outputBasis
      (ContinuousLinearMap.id ℂ finiteSCarrier)
      (sourceFourierSupportProjection lambda ∘L radialSupportProjection lambda)

theorem reflectedOuterCommutatorPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (reflectedOuterCommutatorPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis globalBasis).traceProduct =
      cc20ReflectedOuterCommutatorBranch (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda) (detectorOperator owner) := by
  sorry

/-!
The genuine second-support crossing is handled by the same signed pair
constructor.  Its target remains the reflected compact output carrier.
-/
noncomputable def secondSupportCommutatorPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := WithLp 2
        (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))) ×
          Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
      globalBasis :=
  (sourceSecondSupportCompactRootPairData owner lambda a c negativeBasis
    positiveBasis outputBasis globalBasis).boundedAdjointSub outputBasis
      (radialSupportProjection lambda)
      (radialSupportProjection lambda)

theorem secondSupportCommutatorPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (secondSupportCommutatorPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis globalBasis).traceProduct =
      cc20SecondSupportCommutatorBranch (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda) (detectorOperator owner) := by
  rw [secondSupportCommutatorPairData,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedAdjointSub_traceProduct_eq]
  have hcross := sourceSecondSupportCompactRootPairData_traceProduct_eq
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis
  have hcomm := cc20Commutator_eq_orientedBoundaryCrossing_adjoint_sub
    (sourceFourierSupportProjection lambda) (detectorOperator owner)
    (sourceFourierSupportProjection_isStarProjection lambda).isSelfAdjoint
    (detectorOperator_isSelfAdjoint owner)
  rw [hcross]
  unfold cc20SecondSupportCommutatorBranch
  calc
    radialSupportProjection lambda ∘L
          (cc20OrientedBoundaryCrossing
            (sourceFourierSupportProjection lambda) (detectorOperator owner)).adjoint ∘L
        radialSupportProjection lambda -
      radialSupportProjection lambda ∘L
          cc20OrientedBoundaryCrossing
            (sourceFourierSupportProjection lambda) (detectorOperator owner) ∘L
        radialSupportProjection lambda =
      radialSupportProjection lambda ∘L
          ((cc20OrientedBoundaryCrossing
            (sourceFourierSupportProjection lambda) (detectorOperator owner)).adjoint -
            cc20OrientedBoundaryCrossing
              (sourceFourierSupportProjection lambda) (detectorOperator owner)) ∘L
        radialSupportProjection lambda := by
          apply ContinuousLinearMap.ext
          intro u
          simp only [ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.sub_apply, map_sub]
    _ = radialSupportProjection lambda ∘L
          cc20Commutator (sourceFourierSupportProjection lambda)
            (detectorOperator owner) ∘L radialSupportProjection lambda := by
      rw [hcomm]

noncomputable def prolateForwardPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := finiteSCarrier) globalBasis :=
  CCM24SourceProlateTrace.sourceProlatePairData globalBasis lambda hfactor
    |>.boundedSandwich globalBasis
      (ContinuousLinearMap.id ℂ finiteSCarrier) (detectorOperator owner)

noncomputable def prolateReversePairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := finiteSCarrier) globalBasis :=
  CCM24SourceProlateTrace.sourceProlatePairData globalBasis lambda hfactor
    |>.boundedSandwich globalBasis
      (detectorOperator owner) (ContinuousLinearMap.id ℂ finiteSCarrier)

/-!
The prolate definition above is intentionally split into the two orientations;
the next owner puts the minus sign in the second coordinate and exposes the
actual commutator only after the pair has been formed.
-/
noncomputable def prolateCommutatorPairData'
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := WithLp 2 (finiteSCarrier × finiteSCarrier)) globalBasis :=
  CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum
    (prolateForwardPairData owner lambda globalBasis hfactor)
    ((prolateReversePairData owner lambda globalBasis hfactor).smulRight (-1))

theorem prolateCommutatorPairData'_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (prolateCommutatorPairData' owner lambda globalBasis hfactor).traceProduct =
      cc20Commutator (sourceProlateRemainder lambda)
        (detectorOperator owner) := by
  rw [prolateCommutatorPairData',
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    prolateForwardPairData, prolateReversePairData,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
  rw [CCM24SourceProlateTrace.sourceProlatePairData_traceProduct_eq
    globalBasis lambda hfactor]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.neg_apply, neg_one_smul, cc20Commutator]
  abel

/-! Keep the second-support and prolate terms paired. -/
noncomputable def secondSupportProlateRemainderPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := WithLp 2
        ((WithLp 2
          (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))) ×
            Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))))) ×
          (WithLp 2 (finiteSCarrier × finiteSCarrier)))) globalBasis :=
  CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum
    (secondSupportCommutatorPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis globalBasis)
    ((prolateCommutatorPairData' owner lambda globalBasis hfactor).smulRight (-1))

theorem secondSupportProlateRemainderPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (secondSupportProlateRemainderPairData owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis globalBasis hfactor).traceProduct =
      sourceSecondSupportProlateRemainder owner lambda := by
  rw [secondSupportProlateRemainderPairData,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    secondSupportCommutatorPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis globalBasis,
    prolateCommutatorPairData'_traceProduct_eq owner lambda globalBasis hfactor]
  unfold sourceSecondSupportProlateRemainder
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    neg_one_smul, sub_eq_add_neg, cc20ProlateCommutatorBranch]

/-!
The final fixed-source owner is one `A^dagger B` product.  Its target is a
nested `L2` sum, so all four physical signs and the prolate subtraction remain
inside one pair rather than becoming eleven trace-norm estimates.
-/
noncomputable def sourceThreeBranchPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := WithLp 2
        (WithLp 2
          (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) ×
            Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))) ×
          (WithLp 2
            ((WithLp 2
              (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))) ×
                Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))))) ×
              (WithLp 2 (finiteSCarrier × finiteSCarrier)))))) globalBasis :=
  by
    sorry

theorem sourceThreeBranchPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor).traceProduct =
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) := by
  sorry

/-!
The fixed-quotient first jet is a bounded sandwich of the complete physical
boundary pair.  The sandwich is formed after the signed ledger has been
assembled, so no outer, second-support, prolate, or quotient correction is
estimated in isolation.
-/
noncomputable def boundedFirstJetPairData
    {ι κ G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis :=
  sourceData.boundedSandwich targetBasis band
    (inner ∘L transport ∘L band)

theorem boundedFirstJetPairData_traceProduct_eq
    {ι κ G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (boundedFirstJetPairData targetBasis sourceData band inner transport).traceProduct =
      band ∘L sourceData.traceProduct ∘L
        (inner ∘L transport ∘L band) := by
  exact CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq
    targetBasis sourceData band
    (inner ∘L transport ∘L band)

theorem boundedFirstJetPairData_traceProduct_eq_of_physical
    {ι κ G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (physical : finiteSCarrier →L[ℂ] finiteSCarrier)
    (hphysical : sourceData.traceProduct = physical)
    (band inner transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (boundedFirstJetPairData targetBasis sourceData band inner transport).traceProduct =
      band ∘L physical ∘L (inner ∘L transport ∘L band) := by
  rw [boundedFirstJetPairData_traceProduct_eq, hphysical]

/-!
CC20's ledger is oriented as `[R,W]`, while the fixed-quotient first jet uses
`[W,R]`.  Keep this sign in the pair owner itself instead of correcting a
scalar after the trace has been taken.
-/
noncomputable def boundedBoundaryFirstJetPairData
    {ι κ G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis :=
  boundedFirstJetPairData targetBasis (sourceData.smulRight (-1)) band inner
    transport

theorem boundedBoundaryFirstJetPairData_traceProduct_eq_neg
    {ι κ G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (boundedBoundaryFirstJetPairData targetBasis sourceData band inner transport).traceProduct =
      -(band ∘L sourceData.traceProduct ∘L
        (inner ∘L transport ∘L band)) := by
  rw [boundedBoundaryFirstJetPairData,
    boundedFirstJetPairData_traceProduct_eq,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight_traceProduct_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    neg_smul, one_smul, ContinuousLinearMap.neg_apply, map_neg]

/-!
The single radial boundary crossing is now promoted to a reusable signed
`A†B` owner.  `boundedAdjointSub` puts the reverse and forward orientations in
orthogonal target coordinates, so the commutator is formed before any source
coframe or Schur prefix is attached.
-/
noncomputable def radialBoundaryCommutatorPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (left right : finiteSCarrier →L[ℂ] finiteSCarrier) :=
  (translatedCompactRootPairData owner lambda a c negativeBasis positiveBasis
    outputBasis globalBasis).boundedAdjointSub outputBasis left right

theorem radialBoundaryCommutatorPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (left right : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (radialBoundaryCommutatorPairData owner lambda a c negativeBasis
      positiveBasis outputBasis globalBasis left right).traceProduct =
      left ∘L cc20Commutator (radialSupportProjection lambda)
        (detectorOperator owner) ∘L right := by
  rw [radialBoundaryCommutatorPairData,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedAdjointSub_traceProduct_eq,
    translatedCompactRootPairData_traceProduct_eq_radialOrientedCrossing
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
        globalBasis]
  have hcomm := cc20Commutator_eq_orientedBoundaryCrossing_adjoint_sub
    (radialSupportProjection lambda) (detectorOperator owner)
    (radialSupportProjection_isStarProjection lambda).isSelfAdjoint
    (detectorOperator_isSelfAdjoint owner)
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg
    (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
      left (T (right u))) hcomm
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub,
    cc20OrientedBoundaryCrossing] using hu.symm

/-!
The ring-level physical ledger is read back with the sign used by the
fixed-quotient jet.  The source pair owns `[R,W]`; the first-jet corner needs
`[W_E,R]`, hence the leading minus and the two support compressions.
-/
theorem fixedPhysicalCommutator_eq_neg_compressedThreeBranch
    (support secondSupport prolate detector : finiteSCarrier →L[ℂ] finiteSCarrier)
    (hSupport : IsIdempotentElem support)
    (hLeftSupport : support ∘L prolate = prolate)
    (hRightSupport : prolate ∘L support = prolate) :
    fixedPhysicalCommutator support secondSupport prolate detector =
      -(support ∘L
        cc20ThreeBranchCommutator support secondSupport prolate detector ∘L
          support) := by
  have hSupport' : support * support = support := hSupport
  have hLeftSupport' : support * prolate = prolate := by
    simpa only [ContinuousLinearMap.mul_def] using hLeftSupport
  have hRightSupport' : prolate * support = prolate := by
    simpa only [ContinuousLinearMap.mul_def] using hRightSupport
  have hSourceLeft :
      support * sourceCompression support secondSupport prolate =
        sourceCompression support secondSupport prolate := by
    unfold sourceCompression
    calc
      support * (support * secondSupport * support - prolate) =
          (support * support) * secondSupport * support -
            support * prolate := by noncomm_ring
      _ = support * secondSupport * support - prolate := by
        rw [hSupport', hLeftSupport']
  have hSourceRight :
      sourceCompression support secondSupport prolate * support =
        sourceCompression support secondSupport prolate := by
    unfold sourceCompression
    calc
      (support * secondSupport * support - prolate) * support =
          support * secondSupport * (support * support) -
            prolate * support := by noncomm_ring
      _ = support * secondSupport * support - prolate := by
        rw [hSupport', hRightSupport']
  have hphysical := compressed_source_commutator_eq_physical
    support secondSupport prolate detector hSupport
    hLeftSupport' hRightSupport'
  have hcompressed := compressed_supported_commutator_eq support
    (sourceCompression support secondSupport prolate) detector
    hSourceLeft hSourceRight
  have hsign :
      commutator detector (sourceCompression support secondSupport prolate) =
        -(cc20Commutator (sourceCompression support secondSupport prolate)
          detector) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [CCM24FiniteSTwoSidedRootRecombination.commutator,
      cc20Commutator,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_def,
      map_neg, neg_smul, one_smul]
    abel
  have hsourceCompression :
      sourceCompression support secondSupport prolate =
        support ∘L secondSupport ∘L support - prolate := by
    simp only [sourceCompression, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc]
  have hthree := cc20Commutator_eq_threeBranch_of_eq
    support secondSupport (sourceCompression support secondSupport prolate)
      prolate detector hsourceCompression
  rw [← hphysical, hcompressed, hsign, hthree]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.smul_apply,
    neg_one_smul, map_neg]

/-! The source Sonin projection is absorbed by both actual support projections. -/
theorem radialSupportProjection_comp_sourceSoninProjection
    (lambda : CCM24SoninScale) :
    radialSupportProjection lambda ∘L sourceSoninProjection lambda =
      sourceSoninProjection lambda := by
  simpa [radialSupportProjection, sourceSoninProjection,
    ccm24ArchimedeanSoninClosedSubspace] using
    (_root_.ConnesWeilRH.CC20Concrete.left_starProjection_absorbs_intersection
      (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
      (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule)

theorem sourceSoninProjection_comp_radialSupportProjection
    (lambda : CCM24SoninScale) :
    sourceSoninProjection lambda ∘L radialSupportProjection lambda =
      sourceSoninProjection lambda := by
  simpa [radialSupportProjection, sourceSoninProjection,
    ccm24ArchimedeanSoninClosedSubspace] using
    (_root_.ConnesWeilRH.CC20Concrete.intersection_absorbs_left_starProjection
      (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
      (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule)

theorem radialSupportProjection_comp_sourceProlateRemainder
    (lambda : CCM24SoninScale) :
    radialSupportProjection lambda ∘L sourceProlateRemainder lambda =
      sourceProlateRemainder lambda := by
  have hE : radialSupportProjection lambda ∘L
      radialSupportProjection lambda = radialSupportProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  have hR := radialSupportProjection_comp_sourceSoninProjection lambda
  unfold sourceProlateRemainder
  calc
    radialSupportProjection lambda ∘L
        (radialSupportProjection lambda ∘L
          sourceFourierSupportProjection lambda ∘L
            radialSupportProjection lambda - sourceSoninProjection lambda) =
      (radialSupportProjection lambda ∘L radialSupportProjection lambda ∘L
        sourceFourierSupportProjection lambda ∘L radialSupportProjection lambda) -
        radialSupportProjection lambda ∘L sourceSoninProjection lambda := by
          apply ContinuousLinearMap.ext
          intro u
          simp only [ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.sub_apply, map_sub]
    _ = sourceProlateRemainder lambda := by
      apply ContinuousLinearMap.ext
      intro u
      simp only [sourceProlateRemainder, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply]
      rw [show radialSupportProjection lambda
          (radialSupportProjection lambda
            (sourceFourierSupportProjection lambda
              (radialSupportProjection lambda u))) =
          radialSupportProjection lambda
            (sourceFourierSupportProjection lambda
              (radialSupportProjection lambda u)) by
        exact congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
          T (sourceFourierSupportProjection lambda
            (radialSupportProjection lambda u))) hE,
        show radialSupportProjection lambda
            (sourceSoninProjection lambda u) =
          sourceSoninProjection lambda u by
        exact congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T u) hR]

theorem sourceProlateRemainder_comp_radialSupportProjection
    (lambda : CCM24SoninScale) :
    sourceProlateRemainder lambda ∘L radialSupportProjection lambda =
      sourceProlateRemainder lambda := by
  have hE : radialSupportProjection lambda ∘L
      radialSupportProjection lambda = radialSupportProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  have hR := sourceSoninProjection_comp_radialSupportProjection lambda
  unfold sourceProlateRemainder
  calc
    (radialSupportProjection lambda ∘L
        sourceFourierSupportProjection lambda ∘L radialSupportProjection lambda -
      sourceSoninProjection lambda) ∘L radialSupportProjection lambda =
      radialSupportProjection lambda ∘L sourceFourierSupportProjection lambda ∘L
          (radialSupportProjection lambda ∘L radialSupportProjection lambda) -
        sourceSoninProjection lambda ∘L radialSupportProjection lambda := by
          apply ContinuousLinearMap.ext
          intro u
          simp only [ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.sub_apply, map_sub]
    _ = sourceProlateRemainder lambda := by
      apply ContinuousLinearMap.ext
      intro u
      simp only [sourceProlateRemainder, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply]
      rw [show radialSupportProjection lambda
          (radialSupportProjection lambda u) =
          radialSupportProjection lambda u by
        exact congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T u) hE,
        show sourceSoninProjection lambda
            (radialSupportProjection lambda u) =
          sourceSoninProjection lambda u by
        exact congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T u) hR]

/-! Proof 405's two surviving first-jet branches on the actual source
carrier.  The intersection absorptions are discharged here, so later
consumers cannot accidentally apply the algebra to an unrelated inner range. -/
theorem sourceFixedQuotientCorner_eq_secondSupport_twoBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    sourceBandProjection lambda ∘L
        commutator (compressedDetector (radialSupportProjection lambda)
          (detectorOperator owner)) (sourceSoninProjection lambda) ∘L
        sourceSoninProjection lambda ∘L transport ∘L
        sourceBandProjection lambda =
      sourceBandProjection lambda ∘L sourceFourierSupportProjection lambda ∘L
          compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner) ∘L sourceSoninProjection lambda ∘L
          transport ∘L sourceBandProjection lambda +
        sourceBandProjection lambda ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier -
            sourceFourierSupportProjection lambda) ∘L
          commutator (compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner)) (sourceFourierSupportProjection lambda) ∘L
          sourceSoninProjection lambda ∘L transport ∘L
          sourceBandProjection lambda := by
  let support := radialSupportProjection lambda
  let secondSupport := sourceFourierSupportProjection lambda
  let inner := sourceSoninProjection lambda
  let band := sourceBandProjection lambda
  have hInner : IsIdempotentElem inner := by
    exact (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
  have hSupportInner : support * inner = inner := by
    simpa only [ContinuousLinearMap.mul_def] using
      radialSupportProjection_comp_sourceSoninProjection lambda
  have hBandInner : band * inner = 0 := by
    change (support - inner) * inner = 0
    calc
      (support - inner) * inner = support * inner - inner * inner := by
        noncomm_ring
      _ = 0 := by rw [hSupportInner, hInner]; noncomm_ring
  have hSecond : IsIdempotentElem secondSupport := by
    exact (sourceFourierSupportProjection_isStarProjection lambda).isIdempotentElem
  have hSecondInner : secondSupport * inner = inner := by
    simpa [sourceFourierSupportProjection, sourceSoninProjection,
      ccm24ArchimedeanSoninClosedSubspace] using
      (_root_.ConnesWeilRH.CC20Concrete.right_starProjection_absorbs_intersection
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule)
  simpa only [support, secondSupport, inner, band,
    sourceBandProjection, ContinuousLinearMap.mul_def] using
    (detector_innerCorner_transport_eq_secondSupport_twoBranch
      (band := support - inner) (inner := inner)
      (secondSupport := secondSupport)
    (detector := compressedDetector support (detectorOperator owner))
      (transport := transport) hInner hBandInner hSecond hSecondInner)

/-! The finite-S normalized causal inverse is the first concrete transport
instance of the preceding owner.  Its lower-factor normalization is kept in
the transport, while the two signed branches stay unreduced. -/
theorem sourceFiniteEulerFixedQuotientCorner_eq_secondSupport_twoBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandProjection lambda ∘L
        commutator (compressedDetector (radialSupportProjection lambda)
          (detectorOperator owner)) (sourceSoninProjection lambda) ∘L
        sourceSoninProjection lambda ∘L
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L radialSupportProjection lambda) ∘L
        sourceBandProjection lambda =
      sourceBandProjection lambda ∘L sourceFourierSupportProjection lambda ∘L
          compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner) ∘L sourceSoninProjection lambda ∘L
          (radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family ∘L radialSupportProjection lambda) ∘L
          sourceBandProjection lambda +
        sourceBandProjection lambda ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier -
            sourceFourierSupportProjection lambda) ∘L
          commutator (compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner)) (sourceFourierSupportProjection lambda) ∘L
          sourceSoninProjection lambda ∘L
          (radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family ∘L radialSupportProjection lambda) ∘L
          sourceBandProjection lambda := by
  exact sourceFixedQuotientCorner_eq_secondSupport_twoBranch owner lambda
    (radialSupportProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
      radialSupportProjection lambda)

/-! A genuine fixed physical `A†B` owner, before any quotient prefix. -/
noncomputable def fixedPhysicalPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :=
  boundedBoundaryFirstJetPairData boundaryBasis
    (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor)
    (radialSupportProjection lambda)
  (ContinuousLinearMap.id ℂ finiteSCarrier)
  (ContinuousLinearMap.id ℂ finiteSCarrier)

theorem fixedPhysicalPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (hSupport : IsIdempotentElem (radialSupportProjection lambda))
    (hLeftSupport : radialSupportProjection lambda ∘L
      sourceProlateRemainder lambda = sourceProlateRemainder lambda)
    (hRightSupport : sourceProlateRemainder lambda ∘L
      radialSupportProjection lambda = sourceProlateRemainder lambda) :
    (fixedPhysicalPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor).traceProduct =
      fixedPhysicalCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) := by
  rw [fixedPhysicalPairData,
    boundedBoundaryFirstJetPairData_traceProduct_eq_neg,
    sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]
  simp only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  exact (fixedPhysicalCommutator_eq_neg_compressedThreeBranch
    (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda)
    (sourceProlateRemainder lambda) (detectorOperator owner)
    hSupport hLeftSupport hRightSupport).symm

/-!
The corrected quotient bracket is one pair owner.  The first coordinate is the
fixed physical ledger dressed by the compressed prefix; the other two
coordinates are the two mandatory support-boundary corrections.  The minus
signs on the radial commutator coordinates convert CC20's `[E,W]` orientation
to the fixed-quotient `[W,E]` orientation.
-/
noncomputable def correctedPhysicalPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (support secondSupport prolate detector transport :
      finiteSCarrier →L[ℂ] finiteSCarrier) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := correctedBoundaryCarrier a c) globalBasis :=
  CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum
    (((fixedPhysicalPairData owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis hfactor).boundedSandwich
      boundaryBasis (compressedPrefix support transport)
        (ContinuousLinearMap.id ℂ finiteSCarrier)).smulRight (-1))
    (CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum
      ((radialBoundaryCommutatorPairData owner lambda a c negativeBasis
          positiveBasis outputBasis globalBasis support
          (transport ∘L support)).smulRight (-1))
      ((radialBoundaryCommutatorPairData owner lambda a c negativeBasis
          positiveBasis outputBasis globalBasis
          (support ∘L transport) support).smulRight (-1)))

theorem correctedPhysicalPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (support secondSupport prolate detector transport :
      finiteSCarrier →L[ℂ] finiteSCarrier)
    (hSupport : IsIdempotentElem support)
    (hLeftSupport : support ∘L prolate = prolate)
    (hRightSupport : prolate ∘L support = prolate)
    (hsupport_actual : support = radialSupportProjection lambda)
    (hsecondSupport_actual :
      secondSupport = sourceFourierSupportProjection lambda)
    (hprolate_actual : prolate = sourceProlateRemainder lambda)
    (hdetector_actual : detector = detectorOperator owner) :
    (correctedPhysicalPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor support
        secondSupport prolate detector transport).traceProduct =
      correctedPhysicalBracket support secondSupport prolate detector transport := by
  rw [hsupport_actual, hsecondSupport_actual, hprolate_actual,
    hdetector_actual]
  rw [correctedPhysicalPairData,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
    fixedPhysicalPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      hfactor
      (radialSupportProjection_isStarProjection lambda).isIdempotentElem
      (radialSupportProjection_comp_sourceProlateRemainder lambda)
      (sourceProlateRemainder_comp_radialSupportProjection lambda),
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    radialBoundaryCommutatorPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis globalBasis
        (radialSupportProjection lambda)
        (transport ∘L radialSupportProjection lambda),
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    radialBoundaryCommutatorPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis globalBasis
        (radialSupportProjection lambda ∘L transport)
        (radialSupportProjection lambda)]
  unfold correctedPhysicalBracket
    CCM24FiniteSTwoSidedRootRecombination.commutator compressedPrefix
    CCM24FiniteSTwoSidedRootRecombination.fixedPhysicalCommutator
    cc20Commutator
  simp only [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
  simp only [← ContinuousLinearMap.mul_def]
  have hSupportSq :
      radialSupportProjection lambda * radialSupportProjection lambda =
        radialSupportProjection lambda :=
    (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  simp [smul_smul, hSupportSq]
  noncomm_ring

/-!
The complete corrected physical ledger now has an explicit single-root
realization.  The root target is an `L2` product of the two assembled
corrected legs, so the fixed physical ledger, both quotient-boundary
corrections, and their signs are retained before the consumer sees the
response.  This is the physical base owner for the Gate 3U interface; its
inherited `steps` field remains bookkeeping only.  It is not a claim that the
moving Schur/Julia column has already been estimated.  The independent actual
cascade belongs in `DouglasAlignedInputSideRootS2Producer`.
-/
noncomputable def correctedPhysicalInputSideProducer
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (support secondSupport prolate detector transport :
      finiteSCarrier →L[ℂ] finiteSCarrier)
    (hSupport : IsIdempotentElem support)
    (hLeftSupport : support ∘L prolate = prolate)
    (hRightSupport : prolate ∘L support = prolate) :
    InputSideRootS2Producer
      (K := WithLp 2
        (correctedBoundaryCarrier a c × correctedBoundaryCarrier a c))
      (G := WithLp 2
        (correctedBoundaryCarrier a c × correctedBoundaryCarrier a c))
      globalBasis :=
  inputSideRootS2ProducerOfPairData
    (correctedPhysicalPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor support
      secondSupport prolate detector transport)

theorem correctedPhysicalInputSideProducer_response_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (support secondSupport prolate detector transport :
      finiteSCarrier →L[ℂ] finiteSCarrier)
    (hSupport : IsIdempotentElem support)
    (hLeftSupport : support ∘L prolate = prolate)
    (hRightSupport : prolate ∘L support = prolate)
    (hsupport_actual : support = radialSupportProjection lambda)
    (hsecondSupport_actual :
      secondSupport = sourceFourierSupportProjection lambda)
    (hprolate_actual : prolate = sourceProlateRemainder lambda)
    (hdetector_actual : detector = detectorOperator owner) :
    (correctedPhysicalInputSideProducer owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      hfactor support secondSupport prolate detector transport hSupport
      hLeftSupport hRightSupport).response =
      correctedPhysicalBracket support secondSupport prolate detector transport := by
  rw [correctedPhysicalInputSideProducer,
    inputSideRootS2ProducerOfPairData_response_eq,
    correctedPhysicalPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      hfactor support secondSupport prolate detector transport hSupport
      hLeftSupport hRightSupport hsupport_actual hsecondSupport_actual
      hprolate_actual hdetector_actual]

theorem correctedPhysicalInputSideProducer_root_energy_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (support secondSupport prolate detector transport :
      finiteSCarrier →L[ℂ] finiteSCarrier)
    (hSupport : IsIdempotentElem support)
    (hLeftSupport : support ∘L prolate = prolate)
    (hRightSupport : prolate ∘L support = prolate) :
    ∑' i, ‖(correctedPhysicalInputSideProducer owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        hfactor support secondSupport prolate detector transport hSupport
        hLeftSupport hRightSupport).root (globalBasis i)‖ ^ 2 =
      ∑' i, (‖(correctedPhysicalPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        hfactor support secondSupport prolate detector transport).left
          (globalBasis i)‖ ^ 2 +
        ‖(correctedPhysicalPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        hfactor support
        secondSupport prolate detector transport).right
          (globalBasis i)‖ ^ 2) := by
  exact inputSideRootS2ProducerOfPairData_root_energy_eq
    (correctedPhysicalPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor support
      secondSupport prolate detector transport)

theorem correctedPhysicalBracket_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (support secondSupport prolate detector transport :
      finiteSCarrier →L[ℂ] finiteSCarrier)
    (hSupport : IsIdempotentElem support)
    (hLeftSupport : support ∘L prolate = prolate)
    (hRightSupport : prolate ∘L support = prolate)
    (hsupport_actual : support = radialSupportProjection lambda)
    (hsecondSupport_actual :
      secondSupport = sourceFourierSupportProjection lambda)
    (hprolate_actual : prolate = sourceProlateRemainder lambda)
    (hdetector_actual : detector = detectorOperator owner) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (correctedPhysicalBracket support secondSupport prolate detector transport) := by
  rw [← correctedPhysicalPairData_traceProduct_eq owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    hfactor support secondSupport prolate detector transport hSupport
      hLeftSupport hRightSupport hsupport_actual hsecondSupport_actual
      hprolate_actual hdetector_actual]
  exact (correctedPhysicalPairData owner lambda a c hac hsupp negativeBasis
    positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis boundaryBasis hfactor support
      secondSupport prolate detector transport).traceProduct_isTraceClassAlong

/-! The fixed-quotient first jet is the physical owner with its two quotient
corners attached. -/
noncomputable def fixedQuotientFirstJetPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (band inner transport : finiteSCarrier →L[ℂ] finiteSCarrier) :=
  boundedFirstJetPairData boundaryBasis
    (fixedPhysicalPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor)
    band inner transport

theorem fixedQuotientFirstJetPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (hSupport : IsIdempotentElem (radialSupportProjection lambda))
    (hLeftSupport : radialSupportProjection lambda ∘L
      sourceProlateRemainder lambda = sourceProlateRemainder lambda)
    (hRightSupport : sourceProlateRemainder lambda ∘L
      radialSupportProjection lambda = sourceProlateRemainder lambda)
    (band inner transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (fixedQuotientFirstJetPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor band inner
        transport).traceProduct =
      band ∘L fixedPhysicalCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          (inner ∘L transport ∘L band) := by
  exact boundedFirstJetPairData_traceProduct_eq_of_physical
    boundaryBasis
    (fixedPhysicalPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor)
    (fixedPhysicalCommutator (radialSupportProjection lambda)
      (sourceFourierSupportProjection lambda)
      (sourceProlateRemainder lambda) (detectorOperator owner))
    (fixedPhysicalPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      hfactor hSupport hLeftSupport hRightSupport)
    band inner transport

theorem fixedQuotientFirstJetPairData_traceProduct_eq_corner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (hSupport : IsIdempotentElem (radialSupportProjection lambda))
    (hLeftSupport : radialSupportProjection lambda ∘L
      sourceProlateRemainder lambda = sourceProlateRemainder lambda)
    (hRightSupport : sourceProlateRemainder lambda ∘L
      radialSupportProjection lambda = sourceProlateRemainder lambda)
    (band transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (fixedQuotientFirstJetPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor band
        (sourceCompression (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda)) transport).traceProduct =
      band ∘L
        commutator (compressedDetector (radialSupportProjection lambda)
          (detectorOperator owner))
          (sourceCompression (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda)) ∘L
        sourceCompression (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) ∘L transport ∘L band := by
  rw [fixedQuotientFirstJetPairData_traceProduct_eq owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    hfactor hSupport hLeftSupport hRightSupport band
      (sourceCompression (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda)) transport]
  have hcorner := firstJetCorner_eq_physical
    (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda)
    (sourceProlateRemainder lambda) (detectorOperator owner) transport band
    hSupport
    (by simpa using hLeftSupport)
    (by simpa using hRightSupport)
  simpa only [ContinuousLinearMap.mul_def] using hcorner.symm

/-! The completed pair is declared before its fixed-quotient specialization so
Lean does not need a forward reference for the ordinary-trace consumer. -/
noncomputable def boundedFirstJetCompletedPairData
    {ι κ G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := WithLp 2 (G × G)) sourceBasis :=
  let first := boundedFirstJetPairData targetBasis sourceData band inner transport
  CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum first first.swap

theorem boundedFirstJetCompletedPairData_ordinaryTrace_eq_two_re
    {ι κ G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
      (boundedFirstJetCompletedPairData targetBasis sourceData band inner
        transport).traceProduct =
      (2 * (CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.traceProduct
          (boundedFirstJetPairData targetBasis sourceData band inner transport))).re : ℝ) := by
  let first := boundedFirstJetPairData targetBasis sourceData band inner transport
  have hfirst : CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      first.traceProduct := first.traceProduct_isTraceClassAlong
  unfold boundedFirstJetCompletedPairData
  rw [CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint]
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong_add sourceBasis _ _ hfirst
    (CC20Concrete.PositiveTrace.isTraceClassAlong_adjoint sourceBasis
      first.traceProduct hfirst)]
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong_adjoint, Complex.star_def,
    Complex.add_conj]

/-! The Hermitian completion is the legal `2 Re` scalar owner for the same
fixed-quotient first jet. -/
noncomputable def fixedQuotientFirstJetCompletedPairData
    {ι κ G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner transport : finiteSCarrier →L[ℂ] finiteSCarrier) :=
  boundedFirstJetCompletedPairData targetBasis sourceData band inner transport

theorem fixedQuotientFirstJetCompletedPairData_ordinaryTrace_eq_two_re
    {ι κ G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
      (fixedQuotientFirstJetCompletedPairData targetBasis sourceData band inner
        transport).traceProduct =
      2 * (CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.traceProduct
          (boundedFirstJetPairData targetBasis sourceData band inner transport))).re := by
  simpa [fixedQuotientFirstJetCompletedPairData] using
    (boundedFirstJetCompletedPairData_ordinaryTrace_eq_two_re
      targetBasis sourceData band inner transport)

/-! Concrete specialization of the corrected physical owner. -/
noncomputable def sourceCorrectedPhysicalPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :=
  correctedPhysicalPairData owner lambda a c hac hsupp negativeBasis
    positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis boundaryBasis hfactor
    (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda)
    (sourceProlateRemainder lambda) (detectorOperator owner) transport

theorem sourceCorrectedPhysicalPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (sourceCorrectedPhysicalPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor transport).traceProduct =
      correctedPhysicalBracket (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) transport := by
  exact correctedPhysicalPairData_traceProduct_eq owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    hfactor (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda)
    (sourceProlateRemainder lambda) (detectorOperator owner) transport
    (radialSupportProjection_isStarProjection lambda).isIdempotentElem
    (radialSupportProjection_comp_sourceProlateRemainder lambda)
    (sourceProlateRemainder_comp_radialSupportProjection lambda)
    rfl rfl rfl rfl

/-! Put the corrected physical owner back on the source Sonin carrier. -/
noncomputable def sourceCorrectedPhysicalSourcePairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ ρ σ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (correctedBoundaryBasis :
      HilbertBasis σ ℂ (correctedBoundaryCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :=
  CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp
    correctedBoundaryBasis
    sourceBasis
    (sourceCorrectedPhysicalPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor
      (ContinuousLinearMap.id ℂ finiteSCarrier))
    (sourceInclusion lambda)
    (finiteEulerAmbientGram family ∘L sourceInclusion lambda ∘L
      finiteEulerGramInv lambda family)

theorem sourceCorrectedPhysicalSourcePairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ ρ σ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (correctedBoundaryBasis :
      HilbertBasis σ ℂ (correctedBoundaryCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceCorrectedPhysicalSourcePairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      correctedBoundaryBasis sourceBasis hfactor).traceProduct =
      (sourceInclusion lambda)† ∘L
        correctedPhysicalBracket (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner)
          (ContinuousLinearMap.id ℂ finiteSCarrier) ∘L
        finiteEulerAmbientGram family ∘L sourceInclusion lambda ∘L
          finiteEulerGramInv lambda family := by
  rw [sourceCorrectedPhysicalSourcePairData,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
    sourceCorrectedPhysicalPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      hfactor]

/-! The source-band instance is the concrete `P [W_E,R] R X P` owner. -/
noncomputable def sourceFixedQuotientFirstJetPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :=
  fixedQuotientFirstJetPairData owner lambda a c hac hsupp negativeBasis
     positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
     reflectedOutputBasis globalBasis boundaryBasis hfactor
     (sourceBandProjection lambda)
     (sourceCompression (radialSupportProjection lambda)
       (sourceFourierSupportProjection lambda)
       (sourceProlateRemainder lambda))
     transport

theorem sourceFixedQuotientFirstJetPairData_traceProduct_eq_corner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (sourceFixedQuotientFirstJetPairData owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      hfactor transport).traceProduct =
      sourceBandProjection lambda ∘L
        commutator (compressedDetector (radialSupportProjection lambda)
          (detectorOperator owner))
          (sourceCompression (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda)) ∘L
        sourceCompression (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) ∘L transport ∘L
        sourceBandProjection lambda := by
  exact fixedQuotientFirstJetPairData_traceProduct_eq_corner owner lambda a c
    hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    hfactor
    (radialSupportProjection_isStarProjection lambda).isIdempotentElem
    (radialSupportProjection_comp_sourceProlateRemainder lambda)
    (sourceProlateRemainder_comp_radialSupportProjection lambda)
    (sourceBandProjection lambda) transport

/-! The actual finite-`S` normalized inverse enters only through its fixed
quotient compression `E U E`; no oblique projection is introduced. -/
noncomputable def sourceFiniteEulerFixedQuotientFirstJetPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :=
  sourceFixedQuotientFirstJetPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis hfactor
    (radialSupportProjection lambda ∘L
      normalizedFiniteEulerInverse family ∘L radialSupportProjection lambda)

/-!
The adjoint-completed first jet uses a two-copy `L2` target.  Its trace is the
Hermitian completion of the one-sided corner, so the signed scalar is exposed
as `2 * Re` only after the complete pair has been formed.
-/
theorem boundedFirstJetCompletedPairData_traceProduct_eq_add_adjoint
    {ι κ G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (boundedFirstJetCompletedPairData targetBasis sourceData band inner transport).traceProduct =
      (boundedFirstJetPairData targetBasis sourceData band inner transport).traceProduct +
        (boundedFirstJetPairData targetBasis sourceData band inner transport).traceProduct.adjoint := by
  unfold boundedFirstJetCompletedPairData
  rw [CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint]

theorem boundedFirstJetCompletedPairData_isTraceClassAlong
    {ι κ G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      (boundedFirstJetCompletedPairData targetBasis sourceData band inner transport).traceProduct := by
  rw [boundedFirstJetCompletedPairData_traceProduct_eq_add_adjoint
    targetBasis sourceData band inner transport]
  let first := boundedFirstJetPairData targetBasis sourceData band inner transport
  have hfirst : CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      first.traceProduct := first.traceProduct_isTraceClassAlong
  exact CC20Concrete.PositiveTrace.isTraceClassAlong_add sourceBasis
    first.traceProduct first.traceProduct.adjoint hfirst
    (CC20Concrete.PositiveTrace.isTraceClassAlong_adjoint sourceBasis
      first.traceProduct hfirst)

/-!
Reparameterize the common boundary owner onto the actual source Sonin
carrier.  The left leg sees the source inclusion `J`; the right leg carries
the complete ordered covariance and Gram inverse.  The minus sign is retained
inside the pair, so the resulting trace product is the route's
`sourceBandGramResponse`, not a separately estimated branch sum.
-/
noncomputable def sourceThreeBranchSourcePairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := commonBoundaryCarrier a c) sourceBasis :=
  (CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp
    boundaryBasis sourceBasis
    (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor)
    (sourceInclusion lambda)
    (finiteEulerAmbientGram family ∘L sourceInclusion lambda ∘L
      finiteEulerGramInv lambda family)).smulRight (-1)

theorem sourceThreeBranchSourcePairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).traceProduct =
      sourceBandGramResponse owner lambda family := by
  rw [sourceThreeBranchSourcePairData,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
    sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor,
    sourceBandGramResponse_eq_neg_threeBranch owner lambda family]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.smul_apply, neg_one_smul,
    ContinuousLinearMap.comp_apply]

theorem sourceBandGramResponse_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      (sourceBandGramResponse owner lambda family) := by
  rw [← sourceThreeBranchSourcePairData_traceProduct_eq owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  exact (sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor).traceProduct_isTraceClassAlong

theorem sourceBandGramResponse_isCompactOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    IsCompactOperator (sourceBandGramResponse owner lambda family) := by
  rw [← sourceThreeBranchSourcePairData_traceProduct_eq owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  exact (sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor).traceProduct_isCompactOperator boundaryBasis

end CCM24FiniteSCommonBoundaryPair
end CCM25Concrete
end Source
end ConnesWeilRH
