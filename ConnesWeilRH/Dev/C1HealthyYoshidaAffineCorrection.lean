import ConnesWeilRH.Dev.C1HealthyYoshidaCorrectionFamily
import ConnesWeilRH.Source.CC20YoshidaConstruction

/-!
# C1HealthyYoshidaAffineCorrection - linear source-family layer

The existing windowed Mellin vectors span the finite node-value space.  This
leaf packages that fact as a surjective linear map, chooses a linear right
inverse, and transports the resulting coefficient family to `CompactLogTest`.
It proves no profile sign and no RH statement.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyYoshidaAffineCorrection

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedYoshidaBridge
open CC20YoshidaNearZeros
open CC20YoshidaInterpolationNode
open CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode

noncomputable section

/-- The finite-node evaluation map on finitely supported windowed test
combinations. -/
noncomputable def windowedMellinEvaluationMap
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    (WindowedPositiveIntervalCompactTest a b →₀ Complex) →ₗ[Complex]
      (FiniteMellinNode nodes → Complex) :=
  Finsupp.lsum Complex (fun p =>
    LinearMap.toSpanSingleton Complex (FiniteMellinNode nodes → Complex)
      (windowedFiniteMellinVector nodes a b p))

@[simp] theorem windowedMellinEvaluationMap_apply
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (c : WindowedPositiveIntervalCompactTest a b →₀ Complex)
    (z : FiniteMellinNode nodes) :
    windowedMellinEvaluationMap nodes a b ha ha_one hone_b c z =
      c.sum (fun p coefficient =>
        coefficient * windowedFiniteMellinVector nodes a b p z) := by
  simp only [windowedMellinEvaluationMap, Finsupp.lsum_apply,
    Finsupp.sum, LinearMap.toSpanSingleton, LinearMap.coe_smulRight,
    LinearMap.id_coe, id_eq, Finset.sum_apply, smul_eq_mul, Pi.smul_apply]

theorem windowedMellinEvaluationMap_surjective
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    Function.Surjective
      (windowedMellinEvaluationMap nodes a b ha ha_one hone_b) := by
  intro y
  have hspan := windowedFiniteMellinVector_span_top nodes ha ha_one hone_b
  have hy_mem : y ∈ Submodule.span Complex
      (Set.range (windowedFiniteMellinVector nodes a b)) := by
    rw [hspan]
    exact Submodule.mem_top
  rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hy_mem with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  funext z
  rw [windowedMellinEvaluationMap_apply]
  have hpoint := congr_fun hc z
  simpa [Finsupp.sum, Pi.smul_apply, smul_eq_mul] using hpoint

/-- A linear right inverse of the finite-node evaluation map.  Its existence
uses only surjectivity and the projectivity of finite function spaces over the
field `Complex`; it does not use any sign conclusion. -/
noncomputable def windowedMellinRightInverse
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    (FiniteMellinNode nodes → Complex) →ₗ[Complex]
    (WindowedPositiveIntervalCompactTest a b →₀ Complex) :=
  Classical.choose
    (LinearMap.exists_rightInverse_of_surjective
      (windowedMellinEvaluationMap nodes a b ha ha_one hone_b)
      (LinearMap.range_eq_top.mpr
        (windowedMellinEvaluationMap_surjective nodes a b ha ha_one hone_b)))

theorem windowedMellinEvaluationMap_comp_rightInverse
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    (windowedMellinEvaluationMap nodes a b ha ha_one hone_b).comp
        (windowedMellinRightInverse nodes a b ha ha_one hone_b) =
      LinearMap.id := by
  exact Classical.choose_spec
    (LinearMap.exists_rightInverse_of_surjective
      (windowedMellinEvaluationMap nodes a b ha ha_one hone_b)
      (LinearMap.range_eq_top.mpr
        (windowedMellinEvaluationMap_surjective nodes a b ha ha_one hone_b)))

/-- The affine-family correction obtained from the linear right inverse,
written in log coordinates. -/
noncomputable def affineResidualCorrection
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → Complex) : CompactLogTest :=
  let a : Real := Real.exp lower
  let b : Real := Real.exp upper
  let ha : 0 < a := Real.exp_pos lower
  let hb : 0 < b := Real.exp_pos upper
  let ha_one : a < 1 := Real.exp_lt_one_iff.mpr hlower
  let hone_b : 1 < b := Real.one_lt_exp_iff.mpr hupper
  let coeffs := windowedMellinRightInverse nodes a b ha ha_one hone_b y
  let source := windowedPositiveIntervalCompactTestCombination coeffs
  compactLogTestOfWindow source ha hb
    (windowedPositiveIntervalCompactTestCombination_support_subset coeffs)

theorem affineResidualCorrection_support_subset
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → Complex) :
    Function.support (affineResidualCorrection nodes hlower hupper y).test ⊆
      Set.Ioo lower upper := by
  dsimp [affineResidualCorrection]
  simpa using
    (compactLogTestOfWindow_support_subset
      (windowedPositiveIntervalCompactTestCombination
        (windowedMellinRightInverse nodes (Real.exp lower) (Real.exp upper)
          (Real.exp_pos lower) (Real.exp_lt_one_iff.mpr hlower)
          (Real.one_lt_exp_iff.mpr hupper) y))
      (Real.exp_pos lower) (Real.exp_pos upper)
      (windowedPositiveIntervalCompactTestCombination_support_subset _))

theorem affineResidualCorrection_laplaceAt
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → Complex)
    (z : FiniteMellinNode nodes) :
    laplaceAt (affineResidualCorrection nodes hlower hupper y) z.1 = y z := by
  dsimp [affineResidualCorrection]
  rw [laplaceAt_compactLogTestOfWindow_eq_mellin]
  have hbridge := windowedFiniteMellinVector_combination
    nodes
    (windowedMellinRightInverse nodes (Real.exp lower) (Real.exp upper)
      (Real.exp_pos lower) (Real.exp_lt_one_iff.mpr hlower)
      (Real.one_lt_exp_iff.mpr hupper) y)
    z
  have hright := congrArg (fun f => f z)
    (LinearMap.congr_fun
      (windowedMellinEvaluationMap_comp_rightInverse nodes
        (Real.exp lower) (Real.exp upper) (Real.exp_pos lower)
        (Real.exp_lt_one_iff.mpr hlower)
         (Real.one_lt_exp_iff.mpr hupper)) y)
  have hright' :
      (windowedMellinRightInverse nodes (Real.exp lower) (Real.exp upper)
        (Real.exp_pos lower) (Real.exp_lt_one_iff.mpr hlower)
        (Real.one_lt_exp_iff.mpr hupper) y).sum (fun p coefficient =>
          coefficient * windowedFiniteMellinVector nodes (Real.exp lower)
            (Real.exp upper) p z) = y z := by
    simpa [LinearMap.comp_apply, windowedMellinEvaluationMap_apply] using hright
  calc
    _ = normalizedCC20TestSpace.mellinAt
        (windowedPositiveIntervalCompactTestCombination
          (windowedMellinRightInverse nodes (Real.exp lower) (Real.exp upper)
            (Real.exp_pos lower) (Real.exp_lt_one_iff.mpr hlower)
            (Real.one_lt_exp_iff.mpr hupper) y)) z.1 := by
          simp only [normalizedCC20TestSpace_mellinAt_eq,
            normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin]
    _ = _ := hbridge
    _ = _ := hright'

end
end C1HealthyYoshidaAffineCorrection
end Source
end ConnesWeilRH
