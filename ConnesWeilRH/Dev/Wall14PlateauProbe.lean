import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Wall14PlateauProbe

Large-plateau bump for the Wall-A 1.4 `arch(witness^2) != 0` closure (docs/970).
Only provable `ContDiffBump` lemmas are used; the opaque `someContDiffBumpBase`
internals are never touched.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14Plateau

open MeasureTheory
open scoped Topology
open Filter Set
open scoped ContDiff
open scoped ComplexConjugate
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

/-- The large-plateau bump: `=1` on `[-9/10, 9/10]`, `0<=f<=1`, support `[-1,1]`. -/
noncomputable def plateauBump : ContDiffBump (0 : ℝ) where
  rIn := 9 / 10
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The plateau bump as a complex-valued function. -/
noncomputable def plateauBumpFunction : ℝ → ℂ :=
  Complex.ofRealCLM ∘ (fun x => plateauBump x)

theorem plateauBumpFunction_hasCompactSupport : HasCompactSupport plateauBumpFunction := by
  exact plateauBump.hasCompactSupport.comp_left (map_zero _)

theorem plateauBumpFunction_contDiff : ContDiff ℝ ∞ plateauBumpFunction := by
  exact Complex.ofRealCLM.contDiff.comp plateauBump.contDiff

/-- The plateau bump as a Schwartz function (compact support). -/
noncomputable def plateauBumpSchwartz : SchwartzMap ℝ ℂ :=
  plateauBumpFunction_hasCompactSupport.toSchwartzMap plateauBumpFunction_contDiff

theorem plateauBumpSchwartz_apply (x : ℝ) : plateauBumpSchwartz x = plateauBump x := rfl

/-- The plateau value at 0 is 1 (0 lies in the plateau). -/
theorem plateauBump_zero_eq_one : plateauBump 0 = 1 := by
  apply plateauBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_self]
  exact plateauBump.rIn_pos.le

/-- The plateau test as a `CompactLogTest`. -/
noncomputable def plateauTest : CompactLogTest where
  test := plateauBumpSchwartz
  compactSupport := plateauBumpFunction_hasCompactSupport

/-- The plateau test is genuinely non-zero: its value at 0 is 1 != 0. -/
theorem plateauTest_ne_zero : plateauTest.test ≠ 0 := by
  intro h
  have h0 : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = plateauTest.test 0 := by
        simp [plateauTest, plateauBumpSchwartz_apply, plateauBump_zero_eq_one]
      _ = 0 := by rw [h]; rfl
  norm_num at h0

/-- The Wall-A owner at the plateau test (compact source test). -/
noncomputable def plateauOwner :
    ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner :=
  ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner.ofCompactLogTest
    plateauTest

/-- The real part of F(0) is the L2 norm-square of the test. -/
theorem plateauOwner_F0_re_eq_integral :
    (plateauOwner.convolutionSquare.test 0).re =
      ∫ t : ℝ, Complex.normSq (plateauTest.test t) := by
  change (plateauTest.convolutionSquare.test 0).re =
      ∫ t : ℝ, Complex.normSq (plateauTest.test t)
  rw [plateauTest.convolutionSquare_zero_eq_integral_normSq]
  simp


/-- The convolution-square mass A = F(0): the L2 norm-square of the test. -/
noncomputable def plateauA : ℝ :=
  (plateauOwner.convolutionSquare.test 0).re

/-- A equals the standard L2 norm-square integral. -/
theorem plateauA_eq_integral_normSq :
    plateauA = ∫ t : ℝ, Complex.normSq (plateauTest.test t) := by
  rw [plateauA, plateauOwner_F0_re_eq_integral]
/-- On the whole closed ball |t| <= 9/10 the plateau test is exactly 1. -/
theorem plateauTest_value_eq_one_of_abs_le (t : ℝ) (ht : |t| ≤ (9 / 10 : ℝ)) :
    plateauTest.test t = (1 : ℂ) := by
  have hb : plateauBump t = 1 := by
    apply plateauBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right]
    exact ht
  simpa [plateauTest, plateauBumpSchwartz_apply, hb]

/-- The pointwise norm-square on the plateau is one. -/
theorem plateauTest_normSq_eq_one_of_plate_le (t : ℝ) (ht : |t| ≤ (9 / 10 : ℝ)) :
    Complex.normSq (plateauTest.test t) = 1 := by
  have hv : plateauTest.test t = (1 : ℂ) := plateauTest_value_eq_one_of_abs_le t ht
  rw [hv]
  norm_num

/-- The norm-squared function of the plateau test is globally integrable. -/
theorem plateauTest_normSq_integrable :
    Integrable (fun t : ℝ => Complex.normSq (plateauTest.test t)) := by
  have hcont : Continuous (fun t : ℝ => Complex.normSq (plateauTest.test t)) := by
    fun_prop
  have hcomp : HasCompactSupport (fun t : ℝ => Complex.normSq (plateauTest.test t)) := by
    exact plateauTest.compactSupport.comp_left (map_zero _)
  exact hcont.integrable_of_hasCompactSupport hcomp

/-- The plateau contributes at least the full mass 9/5 to A. -/
theorem plateauA_ge_nine_fifths : (9 / 5 : ℝ) ≤ plateauA := by
  rw [plateauA_eq_integral_normSq]
  let s : Set ℝ := Set.Icc (-(9 / 10 : ℝ)) (9 / 10 : ℝ)
  have hmeas : MeasurableSet s := isClosed_Icc.measurableSet
  have hs_lt : (volume : Measure ℝ) s ≠ ⊤ := by
    rw [show s = Set.Icc (-(9 / 10 : ℝ)) (9 / 10 : ℝ) by rfl]
    simp [Real.volume_Icc]
  let h : ℝ → ℝ := fun x => Complex.normSq (plateauTest.test x)
  have hint : Integrable h := plateauTest_normSq_integrable
  let g : ℝ → ℝ := s.indicator (fun _ => (1 : ℝ))
  have hintg : Integrable g := by
    rw [MeasureTheory.integrable_indicator_iff hmeas]
    exact MeasureTheory.integrableOn_const (C := (1 : ℝ)) (hC := by simp) hs_lt
  have hmon : ∀ x : ℝ, g x ≤ h x := by
    intro x
    by_cases hx : x ∈ s
    · have htabs : |x| ≤ (9 / 10 : ℝ) := by
        rcases hx with ⟨hm, hM⟩
        exact abs_le.2 ⟨hm, hM⟩
      have hn : Complex.normSq (1 : ℂ) = 1 := by norm_num
      have hv : plateauTest.test x = (1 : ℂ) := plateauTest_value_eq_one_of_abs_le x htabs
      simp [g, h, hx, hv, hn]
    · simp [g, h, hx, Complex.normSq_nonneg]
  have hmain : ∫ x, g x = (9 / 5 : ℝ) := by
    calc
      ∫ x, g x = (volume : Measure ℝ).real s := by
        simpa [g] using (MeasureTheory.integral_indicator_one hmeas)
      _ = (9 / 5 : ℝ) := by norm_num [Real.volume_Icc, s]
  calc
    (9 / 5 : ℝ) = ∫ x, g x := hmain.symm
    _ ≤ ∫ x, h x := MeasureTheory.integral_mono hintg hint hmon
    _ = ∫ x, Complex.normSq (plateauTest.test x) := by rfl

/-- A is a genuinely positive mass. -/
theorem plateauA_pos : 0 < plateauA := by
  have hge : (9 / 5 : ℝ) ≤ plateauA := plateauA_ge_nine_fifths
  linarith


noncomputable def plateauReal (x : ℝ) : ℝ := plateauBump x

theorem plateauReal_nonneg (x : ℝ) : 0 ≤ plateauReal x := by
  exact plateauBump.nonneg

theorem plateauReal_neg (x : ℝ) : plateauReal (-x) = plateauReal x := by
  exact plateauBump.neg x

theorem plateauReal_continuous : Continuous plateauReal := by
  exact (plateauBump.contDiff (n := ⊤)).continuous

theorem plateauTest_value_eq_ofReal (x : ℝ) :
    plateauTest.test x = (plateauReal x : ℂ) := by
  simpa [plateauTest, plateauBumpSchwartz_apply, plateauReal]

theorem convIntegrand_st (y t : ℝ) :
    star (plateauTest.test (-t)) * plateauTest.test (y - t) =
      (plateauReal t * plateauReal (y - t) : ℂ) := by
  rw [plateauTest_value_eq_ofReal (-t), plateauTest_value_eq_ofReal (y - t)]
  simp [plateauReal_neg]

noncomputable def plateauF (y : ℝ) : ℝ :=
  (plateauOwner.convolutionSquare.test y).re

theorem plateauRealMul_integrable (y : ℝ) :
    Integrable (fun t : ℝ => plateauReal t * plateauReal (y - t)) := by
  have hcont : Continuous (fun t : ℝ => plateauReal t * plateauReal (y - t)) := by
    exact plateauReal_continuous.mul
      (plateauReal_continuous.comp (by fun_prop : Continuous fun t : ℝ => (y - t)))
  have hp : HasCompactSupport (fun t : ℝ => plateauReal t) :=
    ContDiffBump.hasCompactSupport plateauBump
  have hcomp : HasCompactSupport (fun t : ℝ => plateauReal t * plateauReal (y - t)) := by
    exact HasCompactSupport.mul_right hp
  exact hcont.integrable_of_hasCompactSupport hcomp

theorem plateauOwnerConvSquare_eq_real (y : ℝ) :
    plateauOwner.convolutionSquare.test y =
      ((∫ t : ℝ, plateauReal t * plateauReal (y - t) : ℝ) : ℂ) := by
  change (plateauTest.convolutionSquare.test y) =
      ((∫ t : ℝ, plateauReal t * plateauReal (y - t) : ℝ) : ℂ)
  rw [plateauTest.convolutionSquare_apply]
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun t => convIntegrand_st y t))]
  simp_rw [← Complex.ofReal_mul]
  exact ContinuousLinearMap.integral_comp_comm (L := Complex.ofRealCLM)
    (Integrable.ofReal (plateauRealMul_integrable y))

theorem plateauF_eq_conv (y : ℝ) :
    plateauF y = ∫ t : ℝ, plateauReal t * plateauReal (y - t) := by
  unfold plateauF
  rw [plateauOwnerConvSquare_eq_real y]
  simp

theorem plateauF_nonneg (y : ℝ) : 0 ≤ plateauF y := by
  rw [plateauF_eq_conv]
  exact integral_nonneg (fun t => mul_nonneg (plateauReal_nonneg t) (plateauReal_nonneg (y - t)))
lemma integral_neg_full_cont {f : ℝ → ℝ} (hfc : Continuous f) :
    (∫ t : ℝ, f (-t)) = ∫ t : ℝ, f t := by
  let φ : ℝ → ℝ := fun t : ℝ => -t
  have hφ : AEMeasurable φ (volume : Measure ℝ) := measurable_neg.aemeasurable
  have hmap : (volume : Measure ℝ).map φ = (volume : Measure ℝ) := by
    simp [φ, Measure.map_neg_eq_self]
  have hfm : AEStronglyMeasurable f ((volume : Measure ℝ).map φ) := by
    rw [hmap]; exact hfc.aestronglyMeasurable
  have h := MeasureTheory.integral_map hφ (f := f) hfm
  simpa [φ] using h.symm.trans (by rw [hmap])

-- full-real translation invariance (continuous integrand)
lemma integral_add_full_cont {f : ℝ → ℝ} (hfc : Continuous f) (c : ℝ) :
    (∫ t : ℝ, f (t + c)) = ∫ t : ℝ, f t := by
  let φ : ℝ → ℝ := fun t : ℝ => t + c
  have hmeas : AEMeasurable φ (volume : Measure ℝ) :=
    (continuous_id.add continuous_const).aemeasurable
  have hmap : (volume : Measure ℝ).map φ = (volume : Measure ℝ) :=
    MeasureTheory.map_add_right_eq_self volume c
  have hfm : AEStronglyMeasurable f ((volume : Measure ℝ).map φ) := by
    rw [hmap]; exact hfc.aestronglyMeasurable
  have h := MeasureTheory.integral_map hmeas (f := f) hfm
  simpa [φ] using h.symm.trans (by rw [hmap])

-- full-real reflection: ∫ f (y - t) = ∫ f
lemma integral_reflect_full_cont {f : ℝ → ℝ} (hfc : Continuous f) (y : ℝ) :
    (∫ t : ℝ, f (y - t)) = ∫ t : ℝ, f t := by
  let g : ℝ → ℝ := fun u => f (-u)
  have hgc : Continuous g := hfc.comp continuous_neg
  have htrans : (∫ t : ℝ, g (t + (-y))) = ∫ t : ℝ, g t := integral_add_full_cont hgc (-y)
  have htg : (∫ t : ℝ, g (t - y)) = ∫ t : ℝ, g t := by
    simpa [sub_eq_add_neg] using htrans
  have hneg : (∫ u : ℝ, g u) = ∫ t : ℝ, f t := integral_neg_full_cont hfc
  calc
    (∫ t : ℝ, f (y - t)) = ∫ t : ℝ, g (t - y) := by
      congr; funext t; simp [g]
    _ = ∫ t : ℝ, g t := htg
    _ = ∫ t : ℝ, f t := hneg

-- continuous square
lemma plateauRealSq_continuous : Continuous (fun t : ℝ => (plateauReal t) ^ 2) := by
  exact plateauReal_continuous.pow 2

-- (p t)^2 integrable
lemma plateauSq_integrable : Integrable (fun t : ℝ => (plateauReal t) ^ 2) := by
  have hcont : Continuous (fun t : ℝ => (plateauReal t) ^ 2) := plateauRealSq_continuous
  have hp : HasCompactSupport (fun t : ℝ => plateauReal t) :=
    ContDiffBump.hasCompactSupport plateauBump
  have hmul : HasCompactSupport (fun t : ℝ => plateauReal t * plateauReal t) :=
    HasCompactSupport.mul_right hp
  have hcomp : HasCompactSupport (fun t : ℝ => (plateauReal t) ^ 2) := by
    simpa [pow_two] using hmul
  exact hcont.integrable_of_hasCompactSupport hcomp

/-! ### Block 2c: compact-support of the reflected bump and the F <= A upper bound. -/

lemma plateauAffine_hasCompactSupport (y : ℝ) :
    HasCompactSupport (fun t : ℝ => plateauReal (y - t)) := by
  let B : Set ℝ := Metric.closedBall (0 : ℝ) 1
  have hB : tsupport plateauReal = B := by
    have ht : tsupport ↑plateauBump = Metric.closedBall (0 : ℝ) 1 :=
      ContDiffBump.tsupport_eq plateauBump
    simpa [plateauReal, B] using ht
  let pre : Set ℝ := (fun t : ℝ => y - t) ⁻¹' B
  have hcont : Continuous (fun t : ℝ => y - t) := continuous_const.sub continuous_id
  have hpre_closed : IsClosed pre := IsClosed.preimage hcont Metric.isClosed_closedBall
  have hsupp_comp : IsCompact pre := by
    have heq : pre = Metric.closedBall y 1 := by
      ext t; simp [B, pre, Metric.mem_closedBall, dist_eq_norm, abs_sub_comm]
    rw [heq]; exact isCompact_closedBall y 1
  have hsub : Function.support (fun t : ℝ => plateauReal (y - t)) ⊆ pre := by
    intro t ht
    have hyst : y - t ∈ tsupport plateauReal :=
      subset_tsupport _ (by simpa [Function.mem_support] using ht)
    rwa [hB] at hyst
  have hsubcl : closure (Function.support (fun t : ℝ => plateauReal (y - t))) ⊆ pre :=
    (closure_mono hsub).trans (IsClosed.closure_subset hpre_closed)
  change IsCompact (tsupport (fun t : ℝ => plateauReal (y - t)))
  exact IsCompact.of_isClosed_subset hsupp_comp isClosed_closure hsubcl

lemma plateauSqRefl_integrable (y : ℝ) : Integrable (fun t : ℝ => (plateauReal (y - t)) ^ 2) := by
  have hcont : Continuous (fun t : ℝ => (plateauReal (y - t)) ^ 2) :=
    (plateauReal_continuous.comp (continuous_const.sub continuous_id)).pow 2
  have hmul : HasCompactSupport (fun t : ℝ => plateauReal (y - t) * plateauReal (y - t)) :=
    HasCompactSupport.mul_right (plateauAffine_hasCompactSupport y)
  have hsc : HasCompactSupport (fun t : ℝ => (plateauReal (y - t)) ^ 2) := by
    simpa [pow_two] using hmul
  exact hcont.integrable_of_hasCompactSupport hsc

theorem plateauA_eq_integral_realSq :
    plateauA = ∫ t : ℝ, (plateauReal t) ^ 2 := by
  rw [plateauA_eq_integral_normSq]
  congr 1; funext t
  have ht : plateauTest.test t = (plateauReal t : ℂ) := plateauTest_value_eq_ofReal t
  rw [ht]
  change Complex.normSq (plateauReal t) = (plateauReal t) ^ 2
  simp [Complex.normSq]; ring

theorem plateauF_le_A (y : ℝ) : plateauF y ≤ plateauA := by
  rw [plateauF_eq_conv, plateauA_eq_integral_realSq]
  let q : ℝ → ℝ := fun t => plateauReal (y - t)
  have hA1 : Integrable (fun t : ℝ => (plateauReal t) ^ 2) := plateauSq_integrable
  have hA2 : Integrable (fun s : ℝ => (q s) ^ 2) := by simpa [q] using plateauSqRefl_integrable y
  have hsm : Integrable (fun t : ℝ => (plateauReal t) ^ 2 + (q t) ^ 2) := hA1.add hA2
  have hg : Integrable (fun t : ℝ => (1/2 : ℝ) * ((plateauReal t) ^ 2 + (q t) ^ 2)) := by
    simpa [mul_comm] using hsm.const_mul (1/2 : ℝ)
  have h1 : Integrable (fun t : ℝ => plateauReal t * q t) := by
    simpa [q] using plateauRealMul_integrable y
  have hopw : ∀ t : ℝ, plateauReal t * q t ≤ (1/2 : ℝ) * ((plateauReal t) ^ 2 + (q t) ^ 2) := by
    intro t; nlinarith [sq_nonneg (plateauReal t - q t)]
  have hmono : (∫ t : ℝ, plateauReal t * q t) ≤
      (∫ t : ℝ, (1/2 : ℝ) * ((plateauReal t) ^ 2 + (q t) ^ 2)) :=
    MeasureTheory.integral_mono h1 hg hopw
  have hreflect : (∫ t : ℝ, (q t) ^ 2) = ∫ t : ℝ, (plateauReal t) ^ 2 := by
    simpa [q] using integral_reflect_full_cont plateauRealSq_continuous y
  have hsum : (∫ t : ℝ, (plateauReal t) ^ 2 + (q t) ^ 2) =
      (∫ t : ℝ, (plateauReal t) ^ 2) + (∫ t : ℝ, (q t) ^ 2) := MeasureTheory.integral_add hA1 hA2
  have hlin : ∫ t : ℝ, (1/2 : ℝ) * ((plateauReal t) ^ 2 + (q t) ^ 2) =
      (1/2 : ℝ) * ((∫ t : ℝ, (plateauReal t) ^ 2) + (∫ t : ℝ, (q t) ^ 2)) := by
    rw [MeasureTheory.integral_const_mul (1/2 : ℝ) (fun t => (plateauReal t) ^ 2 + (q t) ^ 2)]
    rw [hsum]
  have hcollapse : (1/2 : ℝ) * ((∫ t : ℝ, (plateauReal t) ^ 2) + (∫ t : ℝ, (q t) ^ 2)) =
      ∫ t : ℝ, (plateauReal t) ^ 2 := by
    rw [hreflect]
    ring
  exact hmono.trans_eq (hlin.trans hcollapse)
/-! ### Block 3: the pointwise lower bound F(y) >= max(0, 2b - y), b = 9/10. -/

theorem plateauReal_eq_one_of_abs_le (t : ℝ) (ht : |t| ≤ (9/10 : ℝ)) : plateauReal t = 1 := by
  have h : (plateauReal t : ℂ) = (1 : ℂ) := by
    rw [← plateauTest_value_eq_ofReal t]
    exact plateauTest_value_eq_one_of_abs_le t ht
  exact (Complex.ofReal_inj.mp h)

/-- On the plateau-overlap block [y-b, b] (for 0 <= y <= 2b) both factors are >= are exactly 1. -/
theorem plateauOv_in (y : ℝ) (hy0 : 0 ≤ y) (hyb : y ≤ 2 * (9/10 : ℝ)) (t : ℝ)
    (ht : t ∈ Set.Icc (y - (9/10 : ℝ)) (9/10 : ℝ)) :
    |t| ≤ (9/10 : ℝ) ∧ |y - t| ≤ (9/10 : ℝ) := by
  have hyt_lo : y - (9/10 : ℝ) ≤ t := ht.1
  have ht_hi : t ≤ (9/10 : ℝ) := ht.2
  constructor
  · exact abs_le.mpr ⟨by linarith, ht_hi⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- On the plateau, F(y) >= 2b - y (the overlap area of two b-wide plateaus). -/
theorem plateauF_ge_two_sub_y (y : ℝ) (hy0 : 0 ≤ y) (hyb : y ≤ 2 * (9 / 10 : ℝ)) :
    (2 * (9 / 10 : ℝ) - y) ≤ plateauF y := by
  rw [plateauF_eq_conv]
  let S : Set ℝ := Set.Icc (y - (9/10:ℝ)) (9/10:ℝ)
  let g : ℝ → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hmeasS : MeasurableSet S := isClosed_Icc.measurableSet
  have hvolS : (volume : Measure ℝ) S ≠ ⊤ := by
    simp [S, Real.volume_Icc]
  have hintg : Integrable g := by
    rw [MeasureTheory.integrable_indicator_iff hmeasS]
    exact MeasureTheory.integrableOn_const (C := (1:ℝ)) (hC := by simp) hvolS
  let q : ℝ → ℝ := fun t => plateauReal t * plateauReal (y - t)
  have hintq : Integrable q := by simpa [q] using plateauRealMul_integrable y
  have hleq : ∀ t : ℝ, g t ≤ q t := by
    intro t
    by_cases ht : t ∈ S
    · have hb : |t| ≤ (9/10:ℝ) ∧ |y - t| ≤ (9/10:ℝ) := plateauOv_in y hy0 hyb t ht
      rcases hb with ⟨htlo, hthi⟩
      have hplt : plateauReal t = 1 := by
        apply plateauReal_eq_one_of_abs_le; exact htlo
      have hpyt : plateauReal (y - t) = 1 := by
        apply plateauReal_eq_one_of_abs_le; exact hthi
      simp [g, ht, hplt, hpyt, q]
    · have hg0 : g t = 0 := by simp [g, ht]
      have : 0 ≤ q t := by
        dsimp [q]
        exact mul_nonneg (plateauReal_nonneg t) (plateauReal_nonneg (y - t))
      rwa [hg0]
  have hmono : (∫ t : ℝ, g t) ≤ ∫ t : ℝ, q t := MeasureTheory.integral_mono hintg hintq hleq
  have hgin : (∫ t : ℝ, g t) = (2*(9/10 : ℝ) - y) := by
    have hgi := MeasureTheory.integral_indicator_one (μ := (volume : Measure ℝ)) (s := S) hmeasS
    calc
      (∫ t : ℝ, g t) = (volume : Measure ℝ).real S := by simpa [g] using hgi
      _ = (2*(9/10 : ℝ) - y) := by
        simp [S, Real.volume_Icc]
        have hm0 : 0 ≤ (9/10 : ℝ) - (y - 9/10) := by linarith
        rw [max_eq_left hm0]
        ring
  calc
    (2*(9/10 : ℝ) - y) = (∫ t : ℝ, g t) := hgin.symm
    _ ≤ ∫ t : ℝ, q t := hmono

/-
The safe lower bound over the whole range: F(y) >= max(0, 2b - y).
-/
theorem plateauF_ge_lower (y : ℝ) (hy0 : 0 ≤ y) :
    max 0 (2*(9/10:ℝ) - y) ≤ plateauF y := by
  apply max_le (plateauF_nonneg y)
  by_cases hyb : y ≤ 2*(9/10:ℝ)
  · exact plateauF_ge_two_sub_y y hy0 hyb
  · have hn : 2*(9/10:ℝ) - y < 0 := by linarith
    exact (le_of_lt hn).trans (plateauF_nonneg y)

/-! ### Block 6 (tail decay): for y>=2 the tail of 1/(e^y-e^-y) decays like e^-y.
  This avoids any need for the exact artanh(tanh) antiderivative: a pure
  exponential-decay majorant (tailC=1-e^-4) integrates immediately. -/

noncomputable def tailC : ℝ := 1 - Real.exp (-4)

lemma tailC_pos : 0 < tailC := by
  unfold tailC
  have h : Real.exp (-4 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  exact sub_pos.mpr h

noncomputable def den (y : ℝ) : ℝ := Real.exp y - Real.exp (-y)

lemma den_pos (y : ℝ) (hy : 0 < y) : 0 < den y := by
  rw [den, sub_pos, Real.exp_lt_exp]; linarith

/-- For y>=2, 1/(e^y-e^-y) <= e^-y / (1-e^-4). -/
lemma den_inv_le_y (y : ℝ) (hy : 2 ≤ y) :
    1 / den y ≤ (1 / tailC) * Real.exp (-y) := by
  have hdenpos : 0 < den y := den_pos y (by linarith)
  have hcpos : 0 < tailC := tailC_pos
  have hden1 : Real.exp (-y) * den y = 1 - Real.exp (-(2*y)) := by
    unfold den
    rw [mul_sub]
    rw [show Real.exp (-y) * Real.exp y = 1 by
      rw [← Real.exp_add, show (-y) + y = 0 by ring, Real.exp_zero]]
    rw [show Real.exp (-y) * Real.exp (-y) = Real.exp (-(2*y)) by
      rw [← Real.exp_add, show (-y) + (-y) = -(2*y) by ring]]
  have hcross : tailC ≤ Real.exp (-y) * den y := by
    rw [hden1]
    unfold tailC
    rw [sub_le_sub_iff_left]
    exact Real.exp_le_exp.mpr (by linarith)
  have hden_ne : den y ≠ 0 := ne_of_gt hdenpos
  have htc_ne : tailC ≠ 0 := ne_of_gt hcpos
  rw [div_le_iff₀ hdenpos]
  field_simp [hden_ne, htc_ne, Real.exp_ne_zero]
  nlinarith [mul_le_mul_of_nonneg_left hcross (by positivity : (0:ℝ) ≤ 1)]
lemma integral_inv_den_Ioi_le (R : ℝ) (hR : 2 ≤ R) :
    (∫ y in Ioi R, 1 / den y) ≤ (1 / tailC) * Real.exp (-R) := by
  let μ := (volume : Measure ℝ).restrict (Ioi R)
  have hmeas : MeasurableSet (Ioi R) := isOpen_Ioi.measurableSet
  have hg : Integrable (fun y : ℝ => (1 / tailC) * Real.exp (-y)) μ := by
    have hi' : Integrable (fun y : ℝ => Real.exp (-y)) μ := by
      change Integrable (fun y : ℝ => Real.exp (-y)) ((volume : Measure ℝ).restrict (Ioi R))
      exact integrableOn_exp_neg_Ioi R
    exact hi'.const_mul (1 / tailC)
  have hbnd : (fun y : ℝ => 1 / den y) ≤ᵐ[μ] (fun y : ℝ => (1 / tailC) * Real.exp (-y)) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas]
    intro y hy
    have hyy : R < y := by simpa using hy
    exact den_inv_le_y y (by nlinarith)
  have hnon : (fun y : ℝ => 0) ≤ᵐ[μ] (fun y : ℝ => 1 / den y) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas]
    intro y hy
    have hyy : R < y := by simpa using hy
    have hy0 : 0 < y := by nlinarith
    exact le_of_lt (one_div_pos.mpr (den_pos y hy0))
  have hm : (∫ y : ℝ, 1 / den y ∂μ) ≤ ∫ y : ℝ, (1 / tailC) * Real.exp (-y) ∂μ :=
    integral_mono_of_nonneg (μ := μ) hnon hg hbnd
  have hright : (∫ y : ℝ, (1 / tailC) * Real.exp (-y) ∂μ) = (1 / tailC) * Real.exp (-R) := by
    change (∫ y : ℝ, (1 / tailC) * Real.exp (-y) ∂((volume : Measure ℝ).restrict (Ioi R)))
      = (1 / tailC) * Real.exp (-R)
    rw [MeasureTheory.integral_const_mul]
    rw [integral_exp_neg_Ioi R]
  calc
    (∫ y in Ioi R, 1 / den y) = (∫ y : ℝ, 1 / den y ∂μ) := by rfl
    _ ≤ (∫ y : ℝ, (1 / tailC) * Real.exp (-y) ∂μ) := hm
    _ = (1 / tailC) * Real.exp (-R) := hright
end Wall14Plateau
end Dev
end Source
end ConnesWeilRH


