import ConnesWeilRH.Dev.C1G8P1ProjectionDefectEnergyBound

/-!
# G8 P1 projection-defect primitive-energy reduction

The Cauchy--Schwarz estimate for the sole signed projection defect initially
uses the two Hilbert--Schmidt legs carried by its trace owner.  This leaf
reduces those derived energies to the literal cutoff leg and its source-space
complement.  It does not assert that either energy has a cutoff limit.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1ProjectionDefectEnergyReduction

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSFrameGramCalculus
open CCM25Concrete.CCM24FiniteSProjectionTrace
open C1G8AdjointShearGram
open C1G8P1MetricProjectionDefectTraceClass
open C1G8P1ProjectionDefectEnergyBound
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- Hilbert--Schmidt energy contracts under bounded postcomposition. -/
theorem tsum_normSq_postcomp_le
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (basis : HilbertBasis ι ℂ H) (input : H →L[ℂ] K)
    (hinput : Summable fun i => ‖input (basis i)‖ ^ 2)
    (bounded : K →L[ℂ] G) :
    (∑' i, ‖(bounded ∘L input) (basis i)‖ ^ 2) ≤
      ‖bounded‖ ^ 2 * (∑' i, ‖input (basis i)‖ ^ 2) := by
  have houtput : Summable fun i => ‖(bounded ∘L input) (basis i)‖ ^ 2 :=
    summable_normSq_postcomp basis input bounded hinput
  have hpoint : ∀ i, ‖(bounded ∘L input) (basis i)‖ ^ 2 ≤
      ‖bounded‖ ^ 2 * ‖input (basis i)‖ ^ 2 := by
    intro i
    calc
      ‖(bounded ∘L input) (basis i)‖ ^ 2 = ‖bounded (input (basis i))‖ ^ 2 := rfl
      _ ≤ (‖bounded‖ * ‖input (basis i)‖) ^ 2 := by
        gcongr
        exact bounded.le_opNorm _
      _ = ‖bounded‖ ^ 2 * ‖input (basis i)‖ ^ 2 := by ring
  have hmajorant : Summable fun i =>
      ‖bounded‖ ^ 2 * ‖input (basis i)‖ ^ 2 :=
    hinput.mul_left (‖bounded‖ ^ 2)
  calc
    (∑' i, ‖(bounded ∘L input) (basis i)‖ ^ 2) ≤
        ∑' i, ‖bounded‖ ^ 2 * ‖input (basis i)‖ ^ 2 :=
      houtput.tsum_le_tsum hpoint hmajorant
    _ = ‖bounded‖ ^ 2 * (∑' i, ‖input (basis i)‖ ^ 2) := by
      rw [tsum_mul_left]

/-- The primitive energy of the original literal cutoff leg. -/
noncomputable def g8SourceCutoffLegEnergy
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) : ℝ :=
  ∑' i, ‖(g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
    (sourceBasis i)‖ ^ 2

/-- The primitive energy of the literal source-cutoff complement leg. -/
noncomputable def g8SourceCutoffComplementEnergy
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) : ℝ :=
  ∑' i, ‖g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
    (sourceBasis i)‖ ^ 2

/-- The projected leg in the signed defect costs no more energy than the
original literal cutoff leg. -/
theorem g8ProjectionDefectCrossLeftEnergy_le_sourceCutoffLegEnergy
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    g8ProjectionDefectCrossLeftEnergy owner lambda family globalBasis sourceBasis n ≤
      g8SourceCutoffLegEnergy owner lambda family globalBasis sourceBasis n := by
  let A := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  let J := CCM24FiniteSGramResponse.sourceInclusion lambda
  have hA :=
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left_summable_normSq
  have hpost := tsum_normSq_postcomp_le sourceBasis A hA (J ∘L J†)
  have hJ : ‖J‖ ≤ (1 : ℝ) := Submodule.norm_subtypeL_le _
  have hJadj : ‖J†‖ ≤ (1 : ℝ) := by
    calc
      ‖J†‖ = ‖J‖ := ContinuousLinearMap.adjoint.norm_map J
      _ ≤ 1 := hJ
  have hJJ : ‖J ∘L J†‖ ≤ (1 : ℝ) := by
    calc
      ‖J ∘L J†‖ ≤ ‖J‖ * ‖J†‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hJ hJadj (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have henergyNonneg : 0 ≤ ∑' i, ‖A (sourceBasis i)‖ ^ 2 :=
    tsum_nonneg fun i => sq_nonneg _
  have hsq : ‖J ∘L J†‖ ^ 2 ≤ (1 : ℝ) := by
    simpa using (sq_le_sq₀ (norm_nonneg (J ∘L J†)) (by norm_num)).mpr hJJ
  change (∑' i, ‖((J ∘L J†) ∘L A) (sourceBasis i)‖ ^ 2) ≤
    ∑' i, ‖A (sourceBasis i)‖ ^ 2
  calc
    (∑' i, ‖((J ∘L J†) ∘L A) (sourceBasis i)‖ ^ 2) ≤
        ‖J ∘L J†‖ ^ 2 * (∑' i, ‖A (sourceBasis i)‖ ^ 2) := hpost
    _ ≤ 1 * (∑' i, ‖A (sourceBasis i)‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hsq henergyNonneg
    _ = ∑' i, ‖A (sourceBasis i)‖ ^ 2 := by ring

/-- The other defect energy is exactly bounded postcomposition of the
literal complement by the G8 Gram. -/
theorem g8ProjectionDefectCrossRightEnergy_le_gram_norm_sq_mul_complementEnergy
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    g8ProjectionDefectCrossRightEnergy owner lambda family globalBasis sourceBasis n ≤
      ‖g8AdjointShearGram owner lambda family‖ ^ 2 *
        g8SourceCutoffComplementEnergy owner lambda family globalBasis sourceBasis n := by
  let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
  let G := g8AdjointShearGram owner lambda family
  have hD := g8SourceCutoffComplementLeg_summable_normSq owner lambda family
    globalBasis sourceBasis n
  change (∑' i, ‖(G ∘L D) (sourceBasis i)‖ ^ 2) ≤
    ‖G‖ ^ 2 * (∑' i, ‖D (sourceBasis i)‖ ^ 2)
  exact tsum_normSq_postcomp_le sourceBasis D hD G

end
end C1G8P1ProjectionDefectEnergyReduction
end Source
end ConnesWeilRH
