import ConnesWeilRH.Dev.C1LaneRD3Root
import ConnesWeilRH.Dev.C1LaneRD3Detects
import ConnesWeilRH.Dev.C1LocalConfigurationDomination
import ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner

/-!
# Explicit finite-node corrections for map 106

Each cardinal test is an exponentially weighted seed followed by the
differential shifts at all other nodes. Its denominator is a nonzero seed
mass times an explicit product of node differences. No gate sign is assumed.
-/

namespace ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1LaneRD3Root
open C1LocalConfigurationDomination
open scoped BigOperators

noncomputable section

/-- A concrete seed whose support can be compressed before interpolation. -/
def explicitSeed (r : ℝ) (hr : 0 < r) : CompactLogTest :=
  rescale C1LaneRD3Detects.bumpLogTest r hr

theorem explicitSeed_mass_ne_zero (r : ℝ) (hr : 0 < r) :
    laplaceAt (explicitSeed r hr) 0 ≠ 0 := by
  rw [explicitSeed, laplaceAt_rescale]
  simpa using C1LaneRD3Detects.laplaceAt_bumpLogTest_zero_ne_zero

theorem explicitSeed_support (r : ℝ) (hr : 0 < r) :
    Function.support (explicitSeed r hr).test ⊆ Set.Icc (-(2*r)) (2*r) := by
  have hb : Function.support C1LaneRD3Detects.bumpLogTest.test ⊆
      Set.Ioo (-2 : ℝ) 2 := by
    intro x hx
    have hne : C1LaneRD3Detects.baseBump x ≠ 0 := by
      intro hz
      exact hx (by simp [C1LaneRD3Detects.bumpLogTest_apply, hz])
    have hm : x ∈ Metric.ball (0 : ℝ) C1LaneRD3Detects.baseBump.rOut := by
      rw [← C1LaneRD3Detects.baseBump.support_eq]
      exact hne
    simpa [C1LaneRD3Detects.baseBump, Metric.mem_ball, Real.dist_eq, abs_lt] using hm
  intro x hx
  have hs := rescale_support_subset_Ioo C1LaneRD3Detects.bumpLogTest hr hb hx
  constructor <;> nlinarith [hs.1, hs.2]

def shiftedProduct (nodes : List ℂ) (f : CompactLogTest) : CompactLogTest :=
  nodes.foldr (fun z g => derivativeShift g z) f

theorem laplaceAt_shiftedProduct (nodes : List ℂ) (f : CompactLogTest) (s : ℂ) :
    laplaceAt (shiftedProduct nodes f) s =
      (nodes.map (fun z => z - s)).prod * laplaceAt f s := by
  induction nodes with
  | nil => simp [shiftedProduct]
  | cons z zs ih =>
      simpa [shiftedProduct, laplaceAt_derivativeShift, mul_assoc] using
        congrArg (fun v : ℂ => (z - s) * v) ih

theorem shiftedProduct_support (nodes : List ℂ) (f : CompactLogTest) {w : ℝ}
    (hf : Function.support f.test ⊆ Set.Icc (-w) w) :
    Function.support (shiftedProduct nodes f).test ⊆ Set.Icc (-w) w := by
  induction nodes with
  | nil => exact hf
  | cons z zs ih => exact derivativeShift_support_subset_Icc _ z ih

theorem laplaceAt_weight (f : CompactLogTest) (a s : ℂ) :
    laplaceAt (exponentialWeight f a) s = laplaceAt f (s + a) := by
  unfold laplaceAt
  apply integral_congr_ae
  filter_upwards with x
  simp only [exponentialWeight_apply]
  rw [← mul_assoc, ← Complex.exp_add, ← add_mul]

def cardinalRaw (nodes : Finset ℂ) (seed : CompactLogTest) (z : ℂ) : CompactLogTest :=
  shiftedProduct (nodes.erase z).toList (exponentialWeight seed (-z))

def nodeProduct (nodes : Finset ℂ) (z s : ℂ) : ℂ :=
  ((nodes.erase z).toList.map (fun t => t - s)).prod

theorem laplaceAt_cardinalRaw (nodes : Finset ℂ) (seed : CompactLogTest) (z s : ℂ) :
    laplaceAt (cardinalRaw nodes seed z) s =
      nodeProduct nodes z s * laplaceAt seed (s - z) := by
  rw [cardinalRaw, laplaceAt_shiftedProduct, laplaceAt_weight]
  rfl

theorem nodeProduct_self_ne_zero (nodes : Finset ℂ) (z : ℂ) :
    nodeProduct nodes z z ≠ 0 := by
  classical
  unfold nodeProduct
  apply List.prod_ne_zero
  intro hx
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp hx
  have ht' : t ∈ nodes.erase z := Finset.mem_toList.mp ht
  exact (Finset.mem_erase.mp ht').1 (sub_eq_zero.mp heq)

theorem nodeProduct_other (nodes : Finset ℂ) {z s : ℂ}
    (hs : s ∈ nodes) (hne : s ≠ z) : nodeProduct nodes z s = 0 := by
  classical
  unfold nodeProduct
  apply List.prod_eq_zero
  apply List.mem_map.mpr
  exact ⟨s, Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hne, hs⟩), sub_self s⟩

def correction (nodes : Finset ℂ) (seed : CompactLogTest) (y : ℂ → ℂ) :
    CompactLogTest where
  test := ∑ z ∈ nodes,
    (y z / (nodeProduct nodes z z * laplaceAt seed 0)) • (cardinalRaw nodes seed z).test
  compactSupport := by
    convert hasCompactSupport_finset_sum nodes
      (fun z x => (y z / (nodeProduct nodes z z * laplaceAt seed 0)) •
        (cardinalRaw nodes seed z).test x)
      (fun z _ => (cardinalRaw nodes seed z).compactSupport.smul_left
        (f := fun _ => y z / (nodeProduct nodes z z * laplaceAt seed 0))) using 1
    ext x
    simp

theorem laplaceAt_correction (nodes : Finset ℂ) (seed : CompactLogTest)
    (y : ℂ → ℂ) (s : ℂ) :
    laplaceAt (correction nodes seed y) s =
      ∑ z ∈ nodes, (y z / (nodeProduct nodes z z * laplaceAt seed 0)) *
        (nodeProduct nodes z s * laplaceAt seed (s - z)) := by
  unfold laplaceAt
  simp only [exponentialWeight_apply, correction, SchwartzMap.sum_apply,
    SchwartzMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro z hz
    simp_rw [show ∀ x : ℝ, Complex.exp (s * (x : ℂ)) *
        (y z / (nodeProduct nodes z z * laplaceAt seed 0) *
          (cardinalRaw nodes seed z).test x) =
        (y z / (nodeProduct nodes z z * laplaceAt seed 0)) *
          (exponentialWeight (cardinalRaw nodes seed z) s).test x from
      fun x => by simp only [exponentialWeight_apply]; ring]
    rw [integral_const_mul]
    exact congrArg (fun v : ℂ => (y z / (nodeProduct nodes z z * laplaceAt seed 0)) * v)
      (laplaceAt_cardinalRaw nodes seed z s)
  · intro z hz
    have h := ((exponentialWeight (cardinalRaw nodes seed z) s).test.integrable
      (μ := volume)).const_mul
      (y z / (nodeProduct nodes z z * laplaceAt seed 0))
    convert h using 1
    ext x
    simp only [exponentialWeight_apply]
    ring

theorem correction_interpolates (nodes : Finset ℂ) (seed : CompactLogTest)
    (hmass : laplaceAt seed 0 ≠ 0) (y : ℂ → ℂ) {s : ℂ} (hs : s ∈ nodes) :
    laplaceAt (correction nodes seed y) s = y s := by
  classical
  rw [laplaceAt_correction, Finset.sum_eq_single s]
  · rw [sub_self]
    exact div_mul_cancel₀ _ (mul_ne_zero (nodeProduct_self_ne_zero nodes s) hmass)
  · intro z hz hzs
    rw [nodeProduct_other nodes hs (Ne.symm hzs)]
    simp
  · exact fun h => (h hs).elim

/-- Finite data are realized with the concrete compressed seed; there is no
nonvanishing or interpolation-sign premise left in this declaration. -/
theorem explicitSeed_correction_interpolates
    (nodes : Finset ℂ) (r : ℝ) (hr : 0 < r) (y : ℂ → ℂ)
    {s : ℂ} (hs : s ∈ nodes) :
    laplaceAt (correction nodes (explicitSeed r hr) y) s = y s :=
  correction_interpolates nodes _ (explicitSeed_mass_ne_zero r hr) y hs

theorem correction_support (nodes : Finset ℂ) (seed : CompactLogTest)
    (y : ℂ → ℂ) {w : ℝ}
    (hseed : Function.support seed.test ⊆ Set.Icc (-w) w) :
    Function.support (correction nodes seed y).test ⊆ Set.Icc (-w) w := by
  intro x hx
  by_contra hout
  have hz : ∀ z : ℂ, (cardinalRaw nodes seed z).test x = 0 := by
    intro z
    have hw : Function.support (exponentialWeight seed (-z)).test ⊆ Set.Icc (-w) w := by
      intro t ht
      apply hseed
      intro heq
      exact ht (by simp [exponentialWeight_apply, heq])
    have hs := shiftedProduct_support (nodes.erase z).toList _ hw
    exact not_not.mp (fun hne => hout (hs hne))
  exact hx (by simp [correction, hz])

theorem explicitSeed_correction_support (nodes : Finset ℂ)
    (r : ℝ) (hr : 0 < r) (y : ℂ → ℂ) :
    Function.support (correction nodes (explicitSeed r hr) y).test ⊆
      Set.Icc (-(2*r)) (2*r) :=
  correction_support nodes _ y (explicitSeed_support r hr)

theorem norm_laplaceAt_correction_le (nodes : Finset ℂ) (seed : CompactLogTest)
    (y : ℂ → ℂ) (s : ℂ) :
    ‖laplaceAt (correction nodes seed y) s‖ ≤
      ∑ z ∈ nodes, (‖y z‖ / (‖nodeProduct nodes z z‖ * ‖laplaceAt seed 0‖)) *
        (‖nodeProduct nodes z s‖ * ‖laplaceAt seed (s - z)‖) := by
  rw [laplaceAt_correction]
  simpa only [norm_mul, norm_div] using norm_sum_le nodes
    (fun z => (y z / (nodeProduct nodes z z * laplaceAt seed 0)) *
      (nodeProduct nodes z s * laplaceAt seed (s - z)))

/-- The explicit correction enters the existing support-growing selected owner;
the power is `n+1`, including the reserved base factor. -/
theorem selectedOwner_laplaceAt_explicit_correction
    (base seed : CompactLogTest) (nodes : Finset ℂ) (y : ℂ → ℂ)
    (n : ℕ) (s : ℂ) :
    laplaceAt (selectedOwner base (correction nodes seed y) n).sourceTest (s - 1/2) =
      laplaceAt base s ^ (n+1) *
        (∑ z ∈ nodes, (y z / (nodeProduct nodes z z * laplaceAt seed 0)) *
          (nodeProduct nodes z s * laplaceAt seed (s - z))) := by
  rw [selectedOwner_laplaceAt_sourceTest_centered, laplaceAt_convolution,
    laplaceAt_convolutionIterate, laplaceAt_correction]

theorem norm_selectedOwner_laplaceAt_explicit_correction_le
    (base seed : CompactLogTest) (nodes : Finset ℂ) (y : ℂ → ℂ)
    (n : ℕ) (s : ℂ) :
    ‖laplaceAt (selectedOwner base (correction nodes seed y) n).sourceTest (s - 1/2)‖ ≤
      ‖laplaceAt base s‖ ^ (n+1) *
        (∑ z ∈ nodes, (‖y z‖ / (‖nodeProduct nodes z z‖ * ‖laplaceAt seed 0‖)) *
          (‖nodeProduct nodes z s‖ * ‖laplaceAt seed (s - z)‖)) := by
  rw [selectedOwner_laplaceAt_sourceTest_centered, laplaceAt_convolution,
    laplaceAt_convolutionIterate, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (norm_laplaceAt_correction_le nodes seed y s)
    (by positivity)

/-- Unit base interpolation makes the explicit correction's target values
independent of the convolution count, exactly as required by the all-index route. -/
theorem selectedOwner_explicit_correction_target
    (base seed : CompactLogTest) (nodes : Finset ℂ) (y : ℂ → ℂ)
    (hmass : laplaceAt seed 0 ≠ 0) (n : ℕ) {s : ℂ}
    (hs : s ∈ nodes) (hbase : laplaceAt base s = 1) :
    laplaceAt (selectedOwner base (correction nodes seed y) n).sourceTest (s - 1/2) =
      y s := by
  rw [selectedOwner_laplaceAt_sourceTest_centered, laplaceAt_convolution,
    laplaceAt_convolutionIterate, hbase, correction_interpolates nodes seed hmass y hs]
  simp

/-- Both base and correction can be chosen by the explicit formula. The base
interpolates one on target nodes; the correction supplies the target data. -/
theorem selectedOwner_explicit_base_and_correction_target
    (targets nodes : Finset ℂ) (hsub : targets ⊆ nodes)
    (r : ℝ) (hr : 0 < r) (y : ℂ → ℂ) (n : ℕ)
    {s : ℂ} (hs : s ∈ targets) :
    laplaceAt
      (selectedOwner (correction targets (explicitSeed r hr) (fun _ => 1))
        (correction nodes (explicitSeed r hr) y) n).sourceTest (s - 1/2) = y s := by
  apply selectedOwner_explicit_correction_target _ _ nodes y
    (explicitSeed_mass_ne_zero r hr) n (hsub hs)
  exact explicitSeed_correction_interpolates targets r hr (fun _ => 1) hs

end
end ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection
