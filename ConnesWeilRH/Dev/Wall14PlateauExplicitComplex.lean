import ConnesWeilRH.Dev.Wall14PlateauExplicit
import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare

/-!
# Wall14PlateauExplicitComplex

Lift the explicit real flat-top bump `bumpEx` to a complex `CompactLogTest` and a
`SelectedWeilSquareOwner`, recording the analytic mass `bumpA := F(0) >= 9/5`
(plateau radius `9/10`, outer support `1`).  This is the foundation of the
Wall-A 1.4 explicit-F re-point (docs/971).  RH NOT claimed.
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

/-- The explicit real plateau bump as a complex-valued function. -/
noncomputable def bumpExFunction (x : ℝ) : ℂ := Complex.ofRealCLM (bumpEx x)

theorem bumpExFunction_apply (x : ℝ) : bumpExFunction x = (bumpEx x : ℂ) := rfl

/-- `bump` is `C^inf`: `smoothTransition` is smooth and the inner argument is smooth. -/
theorem bumpEx_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => bumpEx x) := by
  unfold bumpEx
  have hinner : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x ^ 2 - bSq) / (1 - bSq)) := by
    fun_prop
  have hst : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ => Real.smoothTransition ((x ^ 2 - bSq) / (1 - bSq))) :=
    Real.smoothTransition.contDiff.comp hinner
  have hconst : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (1 : ℝ)) := contDiff_const
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ => 1 - Real.smoothTransition ((x ^ 2 - bSq) / (1 - bSq))) :=
    hconst.sub hst
  simpa using hsmooth

/-- The complex bump is also `C^inf`. -/
theorem bumpExFunction_contDiff : ContDiff ℝ (⊤ : ℕ∞) bumpExFunction := by
  simpa [bumpExFunction] using Complex.ofRealCLM.contDiff.comp bumpEx_contDiff

/-- `bumpEx x != 0` forces `x^2 < 1` (contrapositive of the outer-zero). -/
theorem bumpEx_ne_zero_of_sq_lt_one (x : ℝ) (hx : bumpEx x ≠ 0) : x ^ 2 < 1 := by
  by_contra h
  have hle : (1 : ℝ) ≤ x ^ 2 := le_of_not_gt h
  exact hx (bumpEx_eq_zero_of_one_le_sq x hle)

/-- A nonzero plateau value forces the point into `[-1, 1]`. -/
theorem bumpEx_ne_zero_imp_mem_Icc (x : ℝ) (hx : bumpEx x ≠ 0) : x ∈ Set.Icc (-1 : ℝ) 1 := by
  have hsq : x ^ 2 < 1 := bumpEx_ne_zero_of_sq_lt_one x hx
  have habs : |x| < 1 := (sq_lt_one_iff_abs_lt_one x).mp hsq
  rcases (abs_lt.mp habs) with ⟨hm, hM⟩
  exact ⟨le_of_lt hm, le_of_lt hM⟩

/-- The complex explicit bump is compactly supported inside `[-1, 1]`. -/
theorem bumpExFunction_hasCompactSupport : HasCompactSupport bumpExFunction := by
  unfold HasCompactSupport
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (-1 : ℝ)) (b := (1 : ℝ)))
  · exact isClosed_closure
  · have hsub : Function.support bumpExFunction ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro x hx
      have hb : bumpEx x ≠ 0 := by
        intro h0
        apply hx
        simp [bumpExFunction, h0]
      exact bumpEx_ne_zero_imp_mem_Icc x hb
    simpa [isClosed_Icc.closure_eq] using closure_mono hsub

/-- The explicit bump as a Schwartz function. -/
noncomputable def bumpSchwartz : SchwartzMap ℝ ℂ :=
  bumpExFunction_hasCompactSupport.toSchwartzMap bumpExFunction_contDiff

/-- The explicit plateau test as a `CompactLogTest`. -/
noncomputable def bumpPlateauTest : CompactLogTest where
  test := bumpSchwartz
  compactSupport := bumpExFunction_hasCompactSupport

theorem bumpPlateauTest_apply (x : ℝ) : bumpPlateauTest.test x = (bumpEx x : ℂ) := by
  change bumpExFunction x = (bumpEx x : ℂ)
  exact bumpExFunction_apply x

/-- `bumpEx(0) = 1`, so the test is genuinely non-zero. -/
theorem bumpPlateauTest_zero_eq_one : bumpPlateauTest.test 0 = (1 : ℂ) := by
  have hb : bumpEx 0 = 1 := by
    apply bump_eq_one_of_sq_le
    simpa using (le_of_lt bSq_pos)
  simpa [bumpPlateauTest_apply] using hb

/-- The plateau test is not the zero function. -/
theorem bumpPlateauTest_ne_zero : bumpPlateauTest.test ≠ 0 := by
  intro h
  have hc : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = bumpPlateauTest.test 0 := bumpPlateauTest_zero_eq_one.symm
      _ = 0 := by rw [h]; rfl
  norm_num at hc

/-- On the plateau `|x| <= 9/10` the test equals 1. -/
theorem bumpPlateauTest_eq_one_of_abs_le (x : ℝ) (ht : |x| ≤ (9 / 10 : ℝ)) :
    bumpPlateauTest.test x = (1 : ℂ) := by
  have htabs : x ^ 2 ≤ bSq := by
    have hp := pow_le_pow_left₀ (abs_nonneg x) ht 2
    rw [sq_abs] at hp
    simpa [bSq, bplateau] using hp
  have hb : bumpEx x = 1 := bump_eq_one_of_sq_le x htabs
  simpa [bumpPlateauTest_apply] using hb

/-- The pointwise norm-square on the plateau is one. -/
theorem bumpPlateauTest_normSq_eq_one_of_plate_le (x : ℝ) (ht : |x| ≤ (9 / 10 : ℝ)) :
    Complex.normSq (bumpPlateauTest.test x) = 1 := by
  have hv : bumpPlateauTest.test x = (1 : ℂ) := bumpPlateauTest_eq_one_of_abs_le x ht
  rw [hv]
  norm_num

/-- The pointwise norm-square is globally integrable. -/
theorem bumpPlateauTest_normSq_integrable :
    Integrable (fun x : ℝ => Complex.normSq (bumpPlateauTest.test x)) := by
  have hcont : Continuous (fun x : ℝ => Complex.normSq (bumpPlateauTest.test x)) := by
    fun_prop
  have hcomp : HasCompactSupport (fun x : ℝ => Complex.normSq (bumpPlateauTest.test x)) := by
    exact bumpPlateauTest.compactSupport.comp_left (map_zero _)
  exact hcont.integrable_of_hasCompactSupport hcomp

/-- The selected owner at the explicit plateau test. -/
noncomputable def bumpPlateauOwner : SelectedWeilSquareOwner :=
  SelectedWeilSquareOwner.ofCompactLogTest bumpPlateauTest

/-- The real part of F(0) is the L2 norm-square of the test. -/
theorem bumpPlateauOwner_F0_re_eq_integral :
    (bumpPlateauOwner.convolutionSquare.test 0).re =
      ∫ t : ℝ, Complex.normSq (bumpPlateauTest.test t) := by
  change (bumpPlateauTest.convolutionSquare.test 0).re =
      ∫ t : ℝ, Complex.normSq (bumpPlateauTest.test t)
  rw [bumpPlateauTest.convolutionSquare_zero_eq_integral_normSq]
  simp

/-- The convolution mass A = F(0). -/
noncomputable def bumpA : ℝ := (bumpPlateauOwner.convolutionSquare.test 0).re

/-- A equals the L2 norm-square integral. -/
theorem bumpA_eq_integral_normSq :
    bumpA = ∫ x : ℝ, Complex.normSq (bumpPlateauTest.test x) := by
  rw [bumpA, bumpPlateauOwner_F0_re_eq_integral]

/-- The plateau contributes at least 2 * (9/10) = 9/5 to A. -/
theorem bumpA_ge_nine_fifths : (9 / 5 : ℝ) ≤ bumpA := by
  let p : Set ℝ := Set.Icc (-(9 / 10 : ℝ)) (9 / 10 : ℝ)
  have hmeas : MeasurableSet p := isClosed_Icc.measurableSet
  have hfin : (volume : Measure ℝ) p ≠ ⊤ := by
    rw [show p = Set.Icc (-(9 / 10 : ℝ)) (9 / 10 : ℝ) by rfl]
    simp [Real.volume_Icc]
  let g : ℝ → ℝ := p.indicator (fun _ : ℝ => (1 : ℝ))
  have hintg : Integrable g := by
    rw [MeasureTheory.integrable_indicator_iff hmeas]
    exact MeasureTheory.integrableOn_const (C := (1 : ℝ)) (hC := by simp) hfin
  let h : ℝ → ℝ := fun x => Complex.normSq (bumpPlateauTest.test x)
  have hinth : Integrable h := bumpPlateauTest_normSq_integrable
  have hpoint : ∀ x : ℝ, g x ≤ h x := by
    intro x
    by_cases hx : x ∈ p
    · have htabs : |x| ≤ (9 / 10 : ℝ) := by
        rcases hx with ⟨hl, hu⟩
        exact abs_le.2 ⟨hl, hu⟩
      have hn : Complex.normSq (1 : ℂ) = 1 := by norm_num
      have hv : bumpPlateauTest.test x = (1 : ℂ) := bumpPlateauTest_eq_one_of_abs_le x htabs
      simp [g, h, hx, hv, hn]
    · simp [g, h, hx, Complex.normSq_nonneg]
  have hmain : ∫ x, g x = 9 / 5 := by
    calc
      ∫ x, g x = (volume : Measure ℝ).real p := by
        simpa [g] using MeasureTheory.integral_indicator_one hmeas
      _ = 9 / 5 := by norm_num [Real.volume_Icc, p]
  calc
    9 / 5 = ∫ x, g x := hmain.symm
    _ ≤ ∫ x, h x := MeasureTheory.integral_mono hintg hinth hpoint
    _ = (bumpA) := by rw [bumpA_eq_integral_normSq]

/-- A is a genuinely positive mass. -/
theorem bumpA_pos : 0 < bumpA := by
  have hge : (9 / 5 : ℝ) ≤ bumpA := bumpA_ge_nine_fifths
  linarith





/-- The plateau test is real-valued and even, so its CCM25 involution
`f~(x) = star (f (-x))` fixes `f` pointwise. -/
theorem bumpPlateauInvolution_real_even (x : Real) :
    bumpPlateauTest.involution.test x = bumpPlateauTest.test x := by
  rw [ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest.involution_apply]
  calc
    star (bumpPlateauTest.test (-x)) = star ((bumpEx (-x) : Complex)) := by rw [bumpPlateauTest_apply]
    _ = star ((bumpEx x : Complex)) := by rw [bumpEx_even x]
    _ = (bumpEx x : Complex) := by simp [Complex.star_def]
    _ = bumpPlateauTest.test x := by rw [bumpPlateauTest_apply]

/-- The involution of the real plateau is the whole function. -/
theorem bumpPlateauInvolutionSelf :
    bumpPlateauTest.involution.test = bumpPlateauTest.test := by
  ext x
  exact bumpPlateauInvolution_real_even x


end Wall14Plateau
end Dev
end Source
end ConnesWeilRH