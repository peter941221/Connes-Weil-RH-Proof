import ConnesWeilRH.Dev.C1G8R3LeakageOrbitEnergy
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal
import ConnesWeilRH.Dev.C1G8R3ScaleDetectorRootSquareSum

namespace ConnesWeilRH
namespace Dev

open Filter
open Source
open Source.CC20Concrete
open Source.CC20YoshidaConvolution
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open C1SameOwnerWeil
open scoped InnerProduct InnerProductSpace Topology

set_option autoImplicit true

local notation "Carrier" => finiteSCarrier

/-- A Hilbert--Schmidt operator has summable squared outputs on every
orthonormal sequence, not only on the basis used to present its certificate. -/
theorem summable_normSq_of_orthonormal
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (operator : H →L[ℂ] G)
    (hoperator : Summable fun i => ‖operator (basis i)‖ ^ 2)
    {v : ℕ → H} (hv : Orthonormal ℂ v) :
    Summable fun n : ℕ => ‖operator (v n)‖ ^ 2 := by
  obtain ⟨wG, basisG, hbG⟩ := exists_hilbertBasis ℂ G
  have hadjoint : Summable fun j => ‖operator.adjoint (basisG j)‖ ^ 2 :=
    PositiveTrace.BasisHilbertSchmidtPairData.summable_adjoint_normSq
      basis basisG operator hoperator
  obtain ⟨wH, basisH, hsubset, hbH⟩ :=
    hv.toSubtypeRange.exists_hilbertBasis_extension
  have hback : Summable fun k : wH =>
      ‖(operator.adjoint.adjoint) (basisH k)‖ ^ 2 :=
    PositiveTrace.BasisHilbertSchmidtPairData.summable_adjoint_normSq
      basisG basisH operator.adjoint hadjoint
  have hbasisH : Summable fun k : wH => ‖operator (basisH k)‖ ^ 2 := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hback
  let embed : ℕ → wH := fun n =>
    ⟨v n, hsubset ⟨n, rfl⟩⟩
  have hembed : Function.Injective embed := by
    intro m n hmn
    apply hv.linearIndependent.injective
    exact congrArg Subtype.val hmn
  have hsub := hbasisH.comp_injective hembed
  apply hsub.congr
  intro n
  change ‖operator (basisH (embed n))‖ ^ 2 = ‖operator (v n)‖ ^ 2
  rw [hbH]

/-- A Hilbert--Schmidt certificate on any Hilbert basis would force the
ambient leakage columns to have summable squared energy on the separated
orthonormal translation orbit. The established lower bound rules this out. -/
theorem sourceRootCompletedRightCommutatorLeftLeg_not_hilbertSchmidt
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0)
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier) :
    ¬ Summable (fun i =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner CCM24UnitScaleProlateAlignment.unitSoninScale
        (basis i)‖ ^ 2) := by
  intro hbasis
  have horbit := summable_normSq_of_orthonormal basis
    (sourceRootCompletedRightCommutatorLeftLeg owner CCM24UnitScaleProlateAlignment.unitSoninScale)
    hbasis (normalizedSelectedSourceTranslationOrbit_orthonormal owner rho hvalue)
  have henergy : Summable (fun n : ℕ =>
      ‖normalizedSelectedSourceTranslationLeakageColumn owner n‖ ^ 2) := by
    apply horbit.congr
    intro n
    rw [normalizedSelectedSourceTranslationLeakageColumn_eq_actual]
  exact normalizedSelectedSourceTranslationLeakageColumn_energy_not_summable
    owner rho hvalue henergy


/-- The full ambient band-root inherits the separated-orbit obstruction:
the already Hilbert--Schmidt range leg tends to zero on that orbit, so it
cannot cancel the uniformly nonzero leakage leg. -/
theorem sourceRootCompletedBandRoot_not_hilbertSchmidt
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0)
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier) :
    ¬ Summable (fun i =>
      ‖(rootConvolution owner ∘L
          sourceBandProjection CCM24UnitScaleProlateAlignment.unitSoninScale)
        (basis i)‖ ^ 2) := by
  obtain ⟨w, basis0, hbasis0⟩ := exists_hilbertBasis ℂ Carrier
  let rangeOp :=
    sourceRootCompletedRangeLeftLeg owner
      CCM24UnitScaleProlateAlignment.unitSoninScale
  let leakOp :=
    sourceRootCompletedRightCommutatorLeftLeg owner
      CCM24UnitScaleProlateAlignment.unitSoninScale
  let bandOp :=
    rootConvolution owner ∘L
      sourceBandProjection CCM24UnitScaleProlateAlignment.unitSoninScale
  have hrange : Summable fun i : w => ‖rangeOp (basis0 i)‖ ^ 2 := by
    exact sourceRootCompletedRangeLeftLeg_summable_all_scales owner basis0
      CCM24UnitScaleProlateAlignment.unitSoninScale
  have hrangeOrbit : Summable fun n : ℕ =>
      ‖rangeOp (normalizedSelectedSourceTranslationOrbit owner n)‖ ^ 2 :=
    summable_normSq_of_orthonormal basis0 rangeOp hrange
      (normalizedSelectedSourceTranslationOrbit_orthonormal owner rho hvalue)
  have hrangeZero := hrangeOrbit.tendsto_atTop_zero
  have hleak := normalizedSelectedSourceTranslationLeakageColumn_norm_lowerBound
    owner rho hvalue
  let c : ℝ := sourceTestRootImageNorm owner /
      (2 * ‖owner.sourceTest.test.toLp 2‖)
  have hc : 0 < c := by
    dsimp [c]
    have hroot := sourceTestRootImageNorm_pos owner rho hvalue
    have hnorm := selectedSourceTestLp_norm_pos owner rho hvalue
    positivity
  have hlarge : ∀ᶠ n : ℕ in atTop,
      c ≤ ‖normalizedSelectedSourceTranslationLeakageColumn owner n‖ := by
    simpa only [c] using hleak
  have hsmallSq : ∀ᶠ n : ℕ in atTop,
      ‖rangeOp (normalizedSelectedSourceTranslationOrbit owner n)‖ ^ 2 <
        (c / 2) ^ 2 :=
    hrangeZero.eventually_lt_const (by positivity)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ‖rangeOp (normalizedSelectedSourceTranslationOrbit owner n)‖ < c / 2 := by
    filter_upwards [hsmallSq] with n hn
    nlinarith [norm_nonneg
      (rangeOp (normalizedSelectedSourceTranslationOrbit owner n))]
  have hbandLower : ∀ᶠ n : ℕ in atTop,
      c / 2 ≤ ‖bandOp (normalizedSelectedSourceTranslationOrbit owner n)‖ := by
    filter_upwards [hlarge, hsmall] with n hleakN hrangeN
    have hdecomp :
        (rangeOp + leakOp)
            (normalizedSelectedSourceTranslationOrbit owner n) =
          bandOp (normalizedSelectedSourceTranslationOrbit owner n) := by
      simpa only [rangeOp, leakOp, bandOp, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply] using congrArg
        (fun T : Carrier →L[ℂ] Carrier => T
          (normalizedSelectedSourceTranslationOrbit owner n))
        (sourceRootCompletedLeftLegs_add_eq_root_band owner
          CCM24UnitScaleProlateAlignment.unitSoninScale)
    have hreverse :
        ‖normalizedSelectedSourceTranslationLeakageColumn owner n‖ ≤
          ‖bandOp (normalizedSelectedSourceTranslationOrbit owner n)‖ +
            ‖rangeOp (normalizedSelectedSourceTranslationOrbit owner n)‖ := by
      rw [normalizedSelectedSourceTranslationLeakageColumn_eq_actual]
      calc
        ‖leakOp (normalizedSelectedSourceTranslationOrbit owner n)‖ =
            ‖(rangeOp + leakOp)
                (normalizedSelectedSourceTranslationOrbit owner n) -
              rangeOp (normalizedSelectedSourceTranslationOrbit owner n)‖ := by
          rw [ContinuousLinearMap.add_apply, add_sub_cancel_left]
        _ ≤ ‖(rangeOp + leakOp)
              (normalizedSelectedSourceTranslationOrbit owner n)‖ +
              ‖rangeOp (normalizedSelectedSourceTranslationOrbit owner n)‖ :=
          norm_sub_le _ _
        _ = ‖bandOp (normalizedSelectedSourceTranslationOrbit owner n)‖ +
              ‖rangeOp (normalizedSelectedSourceTranslationOrbit owner n)‖ := by
          rw [hdecomp]
    linarith
  have hbandLowerSq : ∀ᶠ n : ℕ in atTop,
      (c / 2) ^ 2 ≤ ‖bandOp (normalizedSelectedSourceTranslationOrbit owner n)‖ ^ 2 := by
    filter_upwards [hbandLower] with n hn
    nlinarith [sq_nonneg
      (‖bandOp (normalizedSelectedSourceTranslationOrbit owner n)‖ - c / 2)]
  intro hband
  have hbandOrbit := summable_normSq_of_orthonormal basis bandOp hband
    (normalizedSelectedSourceTranslationOrbit_orthonormal owner rho hvalue)
  have hbandZero := hbandOrbit.tendsto_atTop_zero
  have hsmallBand := hbandZero.eventually_lt_const (sq_pos_of_pos (by positivity : 0 < c / 2))
  obtain ⟨n, hlow, hsmallN⟩ := (hbandLowerSq.and hsmallBand).exists
  linarith

end Dev
end ConnesWeilRH
