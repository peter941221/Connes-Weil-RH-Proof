import ConnesWeilRH.Dev.Wall14PlateauExplicitComplex
import ConnesWeilRH.Dev.Wall14PlateauIntegral

/-!
# Wall14PlateauExplicitF

Real convolution-square `F(y) = (f * f)(y)` for the explicit plateau bump
`bumpReal := bumpEx`, together with the pointwise upper bound `F(y) <= bumpA`
(Young / AM-GM) and the overlap lower bound `F(y) >= max(0, 2b - y)`.  This is
the analytic core of the Wall-A 1.4 near band.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14Plateau

open MeasureTheory
open scoped Topology
open Filter Set
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare
open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner
open scoped ComplexConjugate

/-- The explicit real plateau bump. -/
noncomputable def bumpReal (x : ℝ) : ℝ := bumpEx x

/-- `bumpReal` is compactly supported in `[-1, 1]`. -/
theorem bumpReal_hasCompactSupport : HasCompactSupport (fun t : ℝ => bumpReal t) := by
  unfold HasCompactSupport
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (-1 : ℝ)) (b := (1 : ℝ)))
  · exact isClosed_closure
  · have hsub : Function.support (fun t : ℝ => bumpReal t) ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro x hx
      have hb : bumpEx x ≠ 0 := by
        intro h0
        exact hx (by simpa [bumpReal] using h0)
      exact bumpEx_ne_zero_imp_mem_Icc x hb
    simpa [bumpReal] using closure_mono hsub


theorem bumpReal_nonneg (x : ℝ) : 0 ≤ bumpReal x := by
  exact bumpEx_nonneg x

theorem bumpReal_even (x : ℝ) : bumpReal (-x) = bumpReal x := by
  exact bumpEx_even x

theorem bumpReal_continuous : Continuous bumpReal := by
  exact bumpEx_contDiff.continuous

theorem bumpTest_value_eq_ofReal (x : ℝ) :
    bumpPlateauTest.test x = (bumpReal x : ℂ) := by
  simpa [bumpReal] using bumpPlateauTest_apply x

theorem convIntegrand_bump (y t : ℝ) :
    star (bumpPlateauTest.test (-t)) * bumpPlateauTest.test (y - t) =
      (bumpReal t * bumpReal (y - t) : ℂ) := by
  rw [bumpTest_value_eq_ofReal (-t), bumpTest_value_eq_ofReal (y - t)]
  simp [bumpReal_even]

noncomputable def bumpF (y : ℝ) : ℝ :=
  (bumpPlateauOwner.convolutionSquare.test y).re

theorem bumpRealMul_integrable (y : ℝ) :
    Integrable (fun t : ℝ => bumpReal t * bumpReal (y - t)) := by
  have hcont : Continuous (fun t : ℝ => bumpReal t * bumpReal (y - t)) := by
    exact bumpReal_continuous.mul
      (bumpReal_continuous.comp (by fun_prop : Continuous fun t : ℝ => (y - t)))
  have hp : HasCompactSupport (fun t : ℝ => bumpReal t) :=
    bumpReal_hasCompactSupport
  have hcomp : HasCompactSupport (fun t : ℝ => bumpReal t * bumpReal (y - t)) := by
    exact HasCompactSupport.mul_right hp
  exact hcont.integrable_of_hasCompactSupport hcomp

theorem bumpOwnerConvSquare_eq_real (y : ℝ) :
    bumpPlateauOwner.convolutionSquare.test y =
      ((∫ t : ℝ, bumpReal t * bumpReal (y - t) : ℝ) : ℂ) := by
  change (bumpPlateauTest.convolutionSquare.test y) =
      ((∫ t : ℝ, bumpReal t * bumpReal (y - t) : ℝ) : ℂ)
  rw [bumpPlateauTest.convolutionSquare_apply]
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun t => convIntegrand_bump y t))]
  simp_rw [← Complex.ofReal_mul]
  exact ContinuousLinearMap.integral_comp_comm (L := Complex.ofRealCLM)
    (Integrable.ofReal (bumpRealMul_integrable y))

theorem bumpF_eq_conv (y : ℝ) :
    bumpF y = ∫ t : ℝ, bumpReal t * bumpReal (y - t) := by
  unfold bumpF
  rw [bumpOwnerConvSquare_eq_real y]
  simp

theorem bumpF_nonneg (y : ℝ) : 0 ≤ bumpF y := by
  rw [bumpF_eq_conv]
  exact integral_nonneg (fun t => mul_nonneg (bumpReal_nonneg t) (bumpReal_nonneg (y - t)))
lemma bumpIntegralNegFullCont {f : ℝ → ℝ} (hfc : Continuous f) :
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
lemma bumpIntegralAddFullCont {f : ℝ → ℝ} (hfc : Continuous f) (c : ℝ) :
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
lemma bumpIntegralReflectFullCont {f : ℝ → ℝ} (hfc : Continuous f) (y : ℝ) :
    (∫ t : ℝ, f (y - t)) = ∫ t : ℝ, f t := by
  let g : ℝ → ℝ := fun u => f (-u)
  have hgc : Continuous g := hfc.comp continuous_neg
  have htrans : (∫ t : ℝ, g (t + (-y))) = ∫ t : ℝ, g t := bumpIntegralAddFullCont hgc (-y)
  have htg : (∫ t : ℝ, g (t - y)) = ∫ t : ℝ, g t := by
    simpa [sub_eq_add_neg] using htrans
  have hneg : (∫ u : ℝ, g u) = ∫ t : ℝ, f t := bumpIntegralNegFullCont hfc
  calc
    (∫ t : ℝ, f (y - t)) = ∫ t : ℝ, g (t - y) := by
      congr; funext t; simp [g]
    _ = ∫ t : ℝ, g t := htg
    _ = ∫ t : ℝ, f t := hneg

-- continuous square
lemma bumpRealSq_continuous : Continuous (fun t : ℝ => (bumpReal t) ^ 2) := by
  exact bumpReal_continuous.pow 2

-- (p t)^2 integrable
lemma bumpSq_integrable : Integrable (fun t : ℝ => (bumpReal t) ^ 2) := by
  have hcont : Continuous (fun t : ℝ => (bumpReal t) ^ 2) := bumpRealSq_continuous
  have hp : HasCompactSupport (fun t : ℝ => bumpReal t) :=
    bumpReal_hasCompactSupport
  have hmul : HasCompactSupport (fun t : ℝ => bumpReal t * bumpReal t) :=
    HasCompactSupport.mul_right hp
  have hcomp : HasCompactSupport (fun t : ℝ => (bumpReal t) ^ 2) := by
    simpa [pow_two] using hmul
  exact hcont.integrable_of_hasCompactSupport hcomp

/-! ### Block 2c: compact-support of the reflected bump and the F <= A upper bound. -/

lemma bumpAffine_hasCompactSupport (y : ℝ) :
    HasCompactSupport (fun t : ℝ => bumpReal (y - t)) := by
  unfold HasCompactSupport
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := y - 1) (b := y + 1))
  · exact isClosed_closure
  · have hsub : Function.support (fun t : ℝ => bumpReal (y - t)) ⊆ Set.Icc (y - 1) (y + 1) := by
      intro t ht
      have hb : bumpEx (y - t) ≠ 0 := by
        intro h0
        exact ht (by simpa [bumpReal] using h0)
      rcases (bumpEx_ne_zero_imp_mem_Icc (y - t) hb) with ⟨hl, hu⟩
      constructor <;> linarith
    simpa [bumpReal] using closure_mono hsub

lemma bumpSqRefl_integrable (y : ℝ) : Integrable (fun t : ℝ => (bumpReal (y - t)) ^ 2) := by
  have hcont : Continuous (fun t : ℝ => (bumpReal (y - t)) ^ 2) :=
    (bumpReal_continuous.comp (continuous_const.sub continuous_id)).pow 2
  have hmul : HasCompactSupport (fun t : ℝ => bumpReal (y - t) * bumpReal (y - t)) :=
    HasCompactSupport.mul_right (bumpAffine_hasCompactSupport y)
  have hsc : HasCompactSupport (fun t : ℝ => (bumpReal (y - t)) ^ 2) := by
    simpa [pow_two] using hmul
  exact hcont.integrable_of_hasCompactSupport hsc

theorem bumpA_eq_integral_realSq :
    bumpA = ∫ t : ℝ, (bumpReal t) ^ 2 := by
  rw [bumpA_eq_integral_normSq]
  congr 1; funext t
  have ht : bumpPlateauTest.test t = (bumpReal t : ℂ) := bumpTest_value_eq_ofReal t
  rw [ht]
  change Complex.normSq (bumpReal t) = (bumpReal t) ^ 2
  simp [Complex.normSq]; ring

theorem bumpF_le_bumpA (y : ℝ) : bumpF y ≤ bumpA := by
  rw [bumpF_eq_conv, bumpA_eq_integral_realSq]
  let q : ℝ → ℝ := fun t => bumpReal (y - t)
  have hA1 : Integrable (fun t : ℝ => (bumpReal t) ^ 2) := bumpSq_integrable
  have hA2 : Integrable (fun s : ℝ => (q s) ^ 2) := by simpa [q] using bumpSqRefl_integrable y
  have hsm : Integrable (fun t : ℝ => (bumpReal t) ^ 2 + (q t) ^ 2) := hA1.add hA2
  have hg : Integrable (fun t : ℝ => (1/2 : ℝ) * ((bumpReal t) ^ 2 + (q t) ^ 2)) := by
    simpa [mul_comm] using hsm.const_mul (1/2 : ℝ)
  have h1 : Integrable (fun t : ℝ => bumpReal t * q t) := by
    simpa [q] using bumpRealMul_integrable y
  have hopw : ∀ t : ℝ, bumpReal t * q t ≤ (1/2 : ℝ) * ((bumpReal t) ^ 2 + (q t) ^ 2) := by
    intro t; nlinarith [sq_nonneg (bumpReal t - q t)]
  have hmono : (∫ t : ℝ, bumpReal t * q t) ≤
      (∫ t : ℝ, (1/2 : ℝ) * ((bumpReal t) ^ 2 + (q t) ^ 2)) :=
    MeasureTheory.integral_mono h1 hg hopw
  have hreflect : (∫ t : ℝ, (q t) ^ 2) = ∫ t : ℝ, (bumpReal t) ^ 2 := by
    simpa [q] using bumpIntegralReflectFullCont bumpRealSq_continuous y
  have hsum : (∫ t : ℝ, (bumpReal t) ^ 2 + (q t) ^ 2) =
      (∫ t : ℝ, (bumpReal t) ^ 2) + (∫ t : ℝ, (q t) ^ 2) := MeasureTheory.integral_add hA1 hA2
  have hlin : ∫ t : ℝ, (1/2 : ℝ) * ((bumpReal t) ^ 2 + (q t) ^ 2) =
      (1/2 : ℝ) * ((∫ t : ℝ, (bumpReal t) ^ 2) + (∫ t : ℝ, (q t) ^ 2)) := by
    rw [MeasureTheory.integral_const_mul (1/2 : ℝ) (fun t => (bumpReal t) ^ 2 + (q t) ^ 2)]
    rw [hsum]
  have hcollapse : (1/2 : ℝ) * ((∫ t : ℝ, (bumpReal t) ^ 2) + (∫ t : ℝ, (q t) ^ 2)) =
      ∫ t : ℝ, (bumpReal t) ^ 2 := by
    rw [hreflect]
    ring
  exact hmono.trans_eq (hlin.trans hcollapse)
/-! ### Block 3: the pointwise lower bound F(y) >= max(0, 2b - y), b = 9/10. -/

theorem bumpReal_eq_one_of_abs_le (t : ℝ) (ht : |t| ≤ (9/10 : ℝ)) : bumpReal t = 1 := by
  have h : (bumpReal t : ℂ) = (1 : ℂ) := by
    rw [← bumpTest_value_eq_ofReal t]
    exact bumpPlateauTest_eq_one_of_abs_le t ht
  exact (Complex.ofReal_inj.mp h)

/-- On the plateau-overlap block [y-b, b] (for 0 <= y <= 2b) both factors are >= are exactly 1. -/
theorem bumpOv_in (y : ℝ) (hy0 : 0 ≤ y) (hyb : y ≤ 2 * (9/10 : ℝ)) (t : ℝ)
    (ht : t ∈ Set.Icc (y - (9/10 : ℝ)) (9/10 : ℝ)) :
    |t| ≤ (9/10 : ℝ) ∧ |y - t| ≤ (9/10 : ℝ) := by
  have hyt_lo : y - (9/10 : ℝ) ≤ t := ht.1
  have ht_hi : t ≤ (9/10 : ℝ) := ht.2
  constructor
  · exact abs_le.mpr ⟨by linarith, ht_hi⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- On the plateau, F(y) >= 2b - y (the overlap area of two b-wide plateaus). -/
theorem bumpF_ge_two_sub_y (y : ℝ) (hy0 : 0 ≤ y) (hyb : y ≤ 2 * (9 / 10 : ℝ)) :
    (2 * (9 / 10 : ℝ) - y) ≤ bumpF y := by
  rw [bumpF_eq_conv]
  let S : Set ℝ := Set.Icc (y - (9/10:ℝ)) (9/10:ℝ)
  let g : ℝ → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hmeasS : MeasurableSet S := isClosed_Icc.measurableSet
  have hvolS : (volume : Measure ℝ) S ≠ ⊤ := by
    simp [S, Real.volume_Icc]
  have hintg : Integrable g := by
    rw [MeasureTheory.integrable_indicator_iff hmeasS]
    exact MeasureTheory.integrableOn_const (C := (1:ℝ)) (hC := by simp) hvolS
  let q : ℝ → ℝ := fun t => bumpReal t * bumpReal (y - t)
  have hintq : Integrable q := by simpa [q] using bumpRealMul_integrable y
  have hleq : ∀ t : ℝ, g t ≤ q t := by
    intro t
    by_cases ht : t ∈ S
    · have hb : |t| ≤ (9/10:ℝ) ∧ |y - t| ≤ (9/10:ℝ) := bumpOv_in y hy0 hyb t ht
      rcases hb with ⟨htlo, hthi⟩
      have hplt : bumpReal t = 1 := by
        apply bumpReal_eq_one_of_abs_le; exact htlo
      have hpyt : bumpReal (y - t) = 1 := by
        apply bumpReal_eq_one_of_abs_le; exact hthi
      simp [g, ht, hplt, hpyt, q]
    · have hg0 : g t = 0 := by simp [g, ht]
      have : 0 ≤ q t := by
        dsimp [q]
        exact mul_nonneg (bumpReal_nonneg t) (bumpReal_nonneg (y - t))
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

/-- The safe lower bound over the whole range: F(y) >= max(0, 2b - y). -/
theorem bumpF_ge_lower (y : ℝ) (hy0 : 0 ≤ y) :
    max 0 (2*(9/10:ℝ) - y) ≤ bumpF y := by
  apply max_le (bumpF_nonneg y)
  by_cases hyb : y ≤ 2*(9/10:ℝ)
  · exact bumpF_ge_two_sub_y y hy0 hyb
  · have hn : 2*(9/10:ℝ) - y < 0 := by linarith
    exact (le_of_lt hn).trans (bumpF_nonneg y)
/-! ## Support, symmetry, and away facts for `bumpReal` / `bumpF`. -/

theorem bumpReal_eq_zero_of_abs_ge (t : ℝ) (ht : (1 : ℝ) ≤ |t|) : bumpReal t = 0 := by
  have hsq : (1 : ℝ) ≤ t ^ 2 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ht 2
    simpa [sq_abs] using (hp)
  have hze := bumpEx_eq_zero_of_one_le_sq t hsq
  simpa [bumpReal] using hze

theorem bumpReal_ne_zero_imp_abs_lt_one (t : ℝ) (ht : bumpReal t ≠ 0) : |t| < 1 := by
  by_contra h
  have hn : (1 : ℝ) ≤ |t| := le_of_not_gt h
  have hz : bumpReal t = 0 := bumpReal_eq_zero_of_abs_ge t hn
  exact ht hz

/-- `bumpF` is even: `F(-y) = F(y)`. -/
theorem bumpF_symm (y : ℝ) : bumpF (-y) = bumpF y := by
  let f : ℝ → ℝ := fun t => bumpReal t * bumpReal (y + t)
  have hfc : Continuous f :=
    bumpReal_continuous.mul
      (bumpReal_continuous.comp (by fun_prop : Continuous (fun t : ℝ => y + t)))
  have him : (∫ t : ℝ, f (-t)) = (∫ t : ℝ, f t) := bumpIntegralNegFullCont (f := f) hfc
  have heq : (∫ t : ℝ, f (-t)) = (∫ t : ℝ, bumpReal t * bumpReal (y - t)) := by
    congr 1; funext t
    simp [f]
    have th : y + (-t) = y - t := by ring
    rw [th, bumpReal_even]
  have hcross : (∫ t : ℝ, bumpReal t * bumpReal (y - t))
        = ∫ t : ℝ, bumpReal t * bumpReal (y + t) := (heq.symm.trans him)
  have hrepL : (∫ t : ℝ, bumpReal t * bumpReal ((-y) - t))
        = ∫ t : ℝ, bumpReal t * bumpReal (y + t) := by
    congr 1; funext t
    have hseg : (-y) - t = -(y + t) := by ring
    rw [hseg, bumpReal_even]
  calc
    bumpF (-y) = ∫ t : ℝ, bumpReal t * bumpReal ((-y) - t) := by rw [bumpF_eq_conv]
    _ = ∫ t : ℝ, bumpReal t * bumpReal (y + t) := hrepL
    _ = ∫ t : ℝ, bumpReal t * bumpReal (y - t) := hcross.symm
    _ = bumpF y := by rw [bumpF_eq_conv]

/-- `bumpF y = 0` when `|y| ≥ 2`. -/
theorem bumpF_eq_zero_of_two_le_abs (y : ℝ) (hy : (2 : ℝ) ≤ |y|) :
    bumpF y = 0 := by
  have hzero : (fun t : ℝ => bumpReal t * bumpReal (y - t)) = fun _ : ℝ => 0 := by
    funext t
    by_cases hp1 : bumpReal t = 0
    · simp [hp1]
    · have ht1 : |t| < 1 := bumpReal_ne_zero_imp_abs_lt_one t (by simpa using hp1)
      by_cases hp2 : |y - t| ≥ (1 : ℝ)
      · have ha : bumpReal (y - t) = 0 := bumpReal_eq_zero_of_abs_ge (y - t) hp2
        simp [ha]
      · have hy1 : |y - t| < 1 := lt_of_not_ge hp2
        have htri : |y| ≤ |t| + |y - t| := by
          rw [add_comm]
          exact (show |y| = |(y - t) + t| by congr 1; ring).trans_le (abs_add_le (y - t) t)
        have hy2 : |y| < (2 : ℝ) := by nlinarith
        have hc : (2 : ℝ) ≤ |y| := hy
        exfalso; linarith
  rw [bumpF_eq_conv]
  rw [hzero]
  simp


/-! ## Re (archimedean numerator) = 2(e^{y/2} F(y) - A), and the real part of the integrand. -/

lemma bumpArchimedeanNumeratorRe_eq_two_G (y : ℝ) :
    bumpPlateauOwner.archimedeanNumeratorRe y = 2 * (Real.exp (y / 2) * bumpF y - bumpA) := by
  unfold archimedeanNumeratorRe archimedeanNumerator
  rw [bumpPlateauOwner.convolutionSquare_add_neg_eq_two_re]
  change ((Real.exp (y / 2) : ℂ) * ((2 * bumpF y : ℝ) : ℂ) - (2 : ℂ) * bumpPlateauOwner.convolutionSquare.test 0).re
    = 2 * (Real.exp (y / 2) * bumpF y - bumpA)
  have h1 : ((Real.exp (y / 2) : ℂ) * ((2 * bumpF y : ℝ) : ℂ)).re
      = Real.exp (y / 2) * (2 * bumpF y) := by
    rw [Complex.re_ofReal_mul]; simp
  have h2 : ((2 : ℂ) * bumpPlateauOwner.convolutionSquare.test 0).re = 2 * bumpA := by
    simpa [bumpA] using (Complex.re_ofReal_mul (2 : ℝ) (bumpPlateauOwner.convolutionSquare.test 0))
  rw [Complex.sub_re]
  rw [h1, h2]
  ring

/-- Real part of the archimedean integrand (explicit bump). -/
noncomputable def bumpArchG (y : ℝ) : ℝ :=
  bumpPlateauOwner.archimedeanNumeratorRe y / den y

/-- `(Re (integrand y)) = bumpArchG y` for `y > 0`. -/
lemma archimedeanIntegrand_re_eq_bumpArchG (y : ℝ) (hy : 0 < y) :
    (bumpPlateauOwner.archimedeanIntegrand y).re = bumpArchG y := by
  unfold bumpArchG archimedeanIntegrand
  have hd0 : (den y : ℂ) ≠ 0 := by exact_mod_cast (den_pos y hy).ne'
  have him : (bumpPlateauOwner.archimedeanNumerator y).im = 0 :=
    bumpPlateauOwner.archimedeanNumerator_im_eq_zero y
  have hden : archimedeanDenominator y = den y := by rfl
  rw [hden]
  rw [Complex.div_re]
  have hd : ((den y : ℂ)).im = 0 := by simp
  have hr : ((den y : ℂ)).re = den y := by simp
  have hnorm : Complex.normSq (den y : ℂ) = (den y) ^ 2 := by
    rw [Complex.normSq_apply]; rw [hr, hd]; ring
  rw [him, hr, hd, hnorm]
  field_simp [(den_pos y hy).ne', hr]
  unfold archimedeanNumeratorRe
  ring

/-- Absolute value of the real part on the tail `y >= 2`: `|bumpArchG| = 2 A/den`. -/
lemma bumpG_abs_tail (y : ℝ) (hy : 2 ≤ y) :
    |bumpArchG y| = 2 * bumpA / den y := by
  unfold bumpArchG
  rw [bumpArchimedeanNumeratorRe_eq_two_G y]
  have hy0 : 0 ≤ y := by linarith
  have hF : bumpF y = 0 :=
    bumpF_eq_zero_of_two_le_abs y (by simpa [abs_of_nonneg hy0])
  have hdp : 0 < den y := den_pos y (by linarith)
  rw [hF, show 2 * (Real.exp (y / 2) * 0 - bumpA) = -(2 * bumpA) by ring]
  rw [abs_div, abs_neg]
  have h2A : (0 : ℝ) ≤ 2 * bumpA := mul_nonneg (by norm_num) (le_of_lt (bumpA_pos))
  have hdenAbs : |den y| = den y := abs_of_nonneg (le_of_lt hdp)
  rw [abs_of_nonneg h2A, hdenAbs]

/-! ## Differentiability of `bumpReal` (foundation for the F-Lipschitz / TV-2 leaf). -/

/-- `bumpReal` is differentiable everywhere (it is the smooth `bumpEx = ContDiff(real, top)`). -/
lemma bumpReal_differentiable : Differentiable ℝ (fun x : ℝ => bumpReal x) := by
  change Differentiable ℝ (fun x : ℝ => bumpEx x)
  exact bumpEx_contDiff.differentiable
    (by simpa using (ENat.top_ne_zero : (⊤ : ENat) ≠ (0 : ENat)))

end Wall14Plateau
end Dev
end Source
end ConnesWeilRH
