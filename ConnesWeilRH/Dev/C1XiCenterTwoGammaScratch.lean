import ConnesWeilRH.Dev.C1XiCenterTwoGamma
import ConnesWeilRH.Dev.C1XiGammaEulerProduct

open MeasureTheory Set Complex Filter
open scoped Topology

#check Complex.hasDerivAt_exp
#check HasDerivAt.cexp
#check HasDerivAt.const_mul
#check HasDerivAt.mul_const
#check HasDerivAt.clog
#check HasDerivAt.comp
#check norm_image_sub_le_of_norm_deriv_le_segment_01'
#check norm_image_sub_le_of_norm_deriv_le_segment'
#check HasDerivAt.comp_ofReal
#check Complex.ofRealCLM
#check Complex.ofRealCLM.hasDerivAt
#check HasDerivAt.const_add
#check HasDerivAt.add_const

example (a b : Complex) (x : Real) :
    HasDerivAt
      (fun t : Real => Complex.exp (((a + (t : Complex) * (b - a)) * (x : Complex))))
      (((b - a) * (x : Complex)) *
        Complex.exp (((a + (x : Complex) * (b - a)) * (x : Complex)))) x := by
  have hcast : HasDerivAt (fun t : Real => (t : Complex)) (1 : Complex) x := by
    simpa using (hasDerivAt_id (x : Complex)).comp_ofReal
  have hinner : HasDerivAt
      (fun t : Real => a + (t : Complex) * (b - a)) (b - a) x := by
    convert (hcast.mul_const (b - a)).const_add a using 1 <;> ring
  have hscaled : HasDerivAt
      (fun t : Real => (a + (t : Complex) * (b - a)) * (x : Complex))
      ((b - a) * (x : Complex)) x := by
    exact hinner.mul_const _
  convert hscaled.cexp using 1 <;> ring

example {a b : Complex} (ha : 0 < a.re) (hb : 0 < b.re)
    (x : Real) (hx : 0 ≤ x) :
    ‖Complex.exp (-(a * (x : Complex))) -
      Complex.exp (-(b * (x : Complex)))‖ ≤
      ‖a - b‖ * x * Real.exp (-(min a.re b.re) * x) := by
  let f : Real → Complex := fun t =>
    Complex.exp (-((a + (t : Complex) * (b - a)) * (x : Complex)))
  let f' : Real → Complex := fun t =>
    Complex.exp (-((a + (t : Complex) * (b - a)) * (x : Complex))) *
      (-((b - a) * (x : Complex)))
  have hderiv : ∀ t : Real, HasDerivAt f
      (f' t) t := by
    intro t
    have hcast : HasDerivAt (fun y : Real => (y : Complex)) (1 : Complex) t := by
      simpa using (hasDerivAt_id (t : Complex)).comp_ofReal
    have hinner : HasDerivAt
        (fun y : Real => a + (y : Complex) * (b - a)) (b - a) t := by
      convert (hcast.mul_const (b - a)).const_add a using 1 <;> ring
    have hscaled : HasDerivAt
        (fun y : Real => -((a + (y : Complex) * (b - a)) * (x : Complex)))
        (-((b - a) * (x : Complex))) t := by
      convert (hinner.mul_const (x : Complex)).neg using 1 <;> ring
    simpa only [f, f'] using hscaled.cexp
  have hbound : ∀ t ∈ Ico (0 : Real) 1,
      ‖f' t‖ ≤ ‖a - b‖ * x * Real.exp (-(min a.re b.re) * x) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := le_of_lt ht.2
    have hmin : min a.re b.re ≤
        (a + (t : Complex) * (b - a)).re := by
      simp only [add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_re, sub_im,
        zero_mul, sub_zero, add_zero]
      calc
        min a.re b.re ≤ (1 - t) * min a.re b.re + t * min a.re b.re := by
          have heq : (1 - t) * min a.re b.re + t * min a.re b.re =
              min a.re b.re := by ring
          rw [heq]
        _ ≤ (1 - t) * a.re + t * b.re := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (min_le_left _ _) (sub_nonneg.mpr ht1))
            (mul_le_mul_of_nonneg_left (min_le_right _ _) ht0)
        _ = a.re + t * (b.re - a.re) := by ring
    have hmin' : min a.re b.re ≤ a.re + t * (b.re - a.re) := by
      simpa only [add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_re, sub_im,
        zero_mul, sub_zero, add_zero] using hmin
    have hexp : ‖Complex.exp (-((a + (t : Complex) * (b - a)) * (x : Complex)))‖ ≤
        Real.exp (-(min a.re b.re) * x) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
        add_re, sub_re, zero_mul, add_zero]
      have hprod : 0 ≤
          ((a.re + t * (b.re - a.re) - min a.re b.re) * x) :=
        mul_nonneg (sub_nonneg.mpr hmin') hx
      nlinarith
    change ‖Complex.exp (-((a + (t : Complex) * (b - a)) * (x : Complex))) *
      (-((b - a) * (x : Complex)))‖ ≤ _
    rw [norm_mul]
    have hderivnorm : ‖-((b - a) * (x : Complex))‖ = ‖a - b‖ * x := by
      rw [norm_neg, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hx,
        norm_sub_rev]
    rw [hderivnorm]
    calc
      ‖Complex.exp (-((a + (t : Complex) * (b - a)) * (x : Complex)))‖ *
          (‖a - b‖ * x) ≤
          Real.exp (-(min a.re b.re) * x) *
            (‖a - b‖ * x) := by
        exact mul_le_mul_of_nonneg_right hexp (mul_nonneg (norm_nonneg _) hx)
      _ = ‖a - b‖ * x * Real.exp (-(min a.re b.re) * x) := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := f) (f' := f') (C :=
      ‖a - b‖ * x * Real.exp (-(min a.re b.re) * x))
    (fun t ht => (hderiv t).hasDerivWithinAt) hbound
  simpa [f, norm_sub_rev] using hmv

open MeasureTheory Set Complex Filter
open scoped Topology

#check Real.integral_rpow_mul_exp_neg_mul_Ioi
#check integrableOn_rpow_mul_exp_neg_mul_rpow

example (C : Real) {n : Nat} (hn : 0 < n) :
    IntegrableOn (fun x : Real => C * x * Real.exp (-((n : Real) * x)))
      (Ioi (0 : Real)) := by
  have hnreal : 0 < (n : Real) := by exact_mod_cast hn
  have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : Real)) (s := (1 : Real)) (b := (n : Real))
    (by norm_num) (by norm_num) hnreal
  have hbase' : IntegrableOn
      (fun x : Real => x * Real.exp (-((n : Real) * x)))
      (Ioi (0 : Real)) := by
    simpa [Real.rpow_one] using hbase
  simpa [mul_assoc] using hbase'.const_mul C

example {n : Nat} (hn : 0 < n) :
    (∫ x : Real in Ioi (0 : Real),
      x * Real.exp (-((n : Real) * x))) = (((n : Real) ^ 2)⁻¹) := by
  have hnreal : 0 < (n : Real) := by exact_mod_cast hn
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : Real)) (r := (n : Real)) (by norm_num) hnreal
  norm_num [Real.Gamma_nat_eq_factorial] at hgamma
  simpa [div_eq_mul_inv] using hgamma

open ConnesWeilRH Source C1XiCenterTwoGamma C1XiGammaEulerProduct

#check Summable.tsum_sub
#check Summable.hasSum
#check tendsto_inv_atTop_zero
#check tendsto_atTop_add_const_right
#check tendsto_natCast_atTop_atTop
#check Complex.continuous_ofReal
#check tendsto_inv_atTop_nhds_zero_nat
#check tendsto_natCast_div_add_atTop
#check Complex.continuous_ofReal

example {w : Complex} (hw : 0 < w.re) :
    Summable (fun n : Nat =>
      (1 / ((n : Complex) + w) - 1 / ((n : Complex) + 1))) := by
  have hhalf := summable_halfAnchorGaussReciprocalSeries
    (z := (1 : Complex)) (by norm_num)
  have hw' := summable_halfAnchorGaussReciprocalSeries hw
  have hsub := hhalf.sub hw'
  convert hsub using 1
  funext n
  ring

example {z : Complex} (hz : 1 < z.re) :
    ∑' n : Nat, (1 / ((n : Complex) + z) - 1 / ((n : Complex) + 1)) =
      -(Real.eulerMascheroniConstant : Complex) - Complex.digamma z := by
  have h := correctedEulerDigammaSeries (z := z - 1) (by
    norm_num [Complex.sub_re]
    linarith)
  convert h using 1
  · apply tsum_congr
    intro n
    congr 1 <;> ring
  · congr 1 <;> ring

example :
    ∑' n : Nat,
      (1 / ((n : Complex) + (3 / 2 : Complex)) -
        1 / ((n : Complex) + 1)) =
      -(Real.eulerMascheroniConstant : Complex) -
        Complex.digamma (3 / 2 : Complex) := by
  have h := correctedEulerDigammaSeries (z := (1 / 2 : Complex)) (by norm_num)
  convert h using 1
  · apply tsum_congr
    intro n
    congr 1 <;> ring
  · congr 1 <;> ring

example :
    ∑' n : Nat,
      (((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + (3 / 2 : Complex))⁻¹) = (2 : Complex) := by
  let u : Nat → Complex := fun n =>
    ((n : Complex) + (1 / 2 : Complex))⁻¹ -
      ((n : Complex) + (3 / 2 : Complex))⁻¹
  have hu : Summable u := by
    simpa [u] using
      (summable_halfAnchorGaussReciprocalSeries
        (z := (3 / 2 : Complex)) (by norm_num))
  have hpartial : ∀ N : Nat,
      ∑ n ∈ Finset.range N, u n =
        (2 : Complex) - ((N : Complex) + (1 / 2 : Complex))⁻¹ := by
    intro N
    induction N with
    | zero => norm_num [u]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        dsimp [u]
        have hshift : (N : Complex) + (3 / 2 : Complex) =
            ((N + 1 : Nat) : Complex) + (1 / 2 : Complex) := by
          push_cast
          ring
        rw [hshift]
        ring
  have hreal : Tendsto
      (fun N : Nat => (((N : Real) + (1 / 2 : Real))⁻¹ : Complex)) atTop
      (𝓝 (0 : Complex)) := by
    have hr : Tendsto
        (fun N : Nat => ((N : Real) + (1 / 2 : Real))⁻¹) atTop
        (𝓝 (0 : Real)) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 / 2 : Real)
          tendsto_natCast_atTop_atTop)
    convert (Complex.continuous_ofReal.tendsto (0 : Real)).comp hr using 1
    funext N
    simp [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_add]
  have hcomplex : Tendsto
      (fun N : Nat => ((N : Complex) + (1 / 2 : Complex))⁻¹) atTop
      (𝓝 (0 : Complex)) := by
    refine hreal.congr' ?_
    filter_upwards [] with N
    have hsum : (((N : Real) + (1 / 2 : Real) : Real) : Complex) =
        (N : Complex) + (1 / 2 : Complex) := by
      push_cast
      ring
    simpa only [Complex.ofReal_inv, Complex.ofReal_add] using
      congrArg (fun w : Complex => w⁻¹) hsum
  have hlim : Tendsto (fun N : Nat => ∑ n ∈ Finset.range N, u n) atTop
      (𝓝 (2 : Complex)) := by
    have heq : (fun N : Nat => ∑ n ∈ Finset.range N, u n) =
        (fun N : Nat => (2 : Complex) -
          ((N : Complex) + (1 / 2 : Complex))⁻¹) := by
      funext N
      exact hpartial N
    rw [heq]
    simpa using (tendsto_const_nhds.sub hcomplex)
  exact tendsto_nhds_unique (hu.hasSum.tendsto_sum_nat) hlim

theorem test_halfAnchor_shift_reciprocal (z : Complex) (hz : 0 < z.re) :
    ∑' n : Nat,
      (((n : Complex) + z)⁻¹ - ((n : Complex) + (z + 1))⁻¹) = z⁻¹ := by
  let u : Nat → Complex := fun n =>
    ((n : Complex) + z)⁻¹ - ((n : Complex) + (z + 1))⁻¹
  have hu : Summable u := by
    have hz1 : 0 < (z + 1).re := by
      norm_num [Complex.add_re]
      linarith
    have hleft := summable_halfAnchorGaussReciprocalSeries (z := z) hz
    have hright := summable_halfAnchorGaussReciprocalSeries (z := z + 1) hz1
    have hsub := hright.sub hleft
    exact hsub.congr (fun n => by
      dsimp [u]
      ring)
  have hpartial : ∀ N : Nat,
      ∑ n ∈ Finset.range N, u n = z⁻¹ - ((N : Complex) + z)⁻¹ := by
    intro N
    induction N with
    | zero => simp [u]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        dsimp [u]
        have hshift : (N : Complex) + (z + 1) =
            ((N + 1 : Nat) : Complex) + z := by
          push_cast
          ring
        rw [hshift]
        ring
  have htail : Tendsto
      (fun N : Nat => ((N : Complex) + z)⁻¹) atTop (𝓝 (0 : Complex)) := by
    have hdiv := tendsto_natCast_div_add_atTop (𝕜 := Complex) z
    have hinv := tendsto_inv_atTop_nhds_zero_nat (𝕜 := Complex)
    have hmul := hinv.mul hdiv
    have hmul' : Tendsto
        (fun N : Nat => (N : Complex)⁻¹ * ((N : Complex) / ((N : Complex) + z)))
        atTop (𝓝 (0 : Complex)) := by
      simpa using hmul
    refine hmul'.congr' ?_
    filter_upwards [Filter.eventually_ne_atTop 0] with N hN
    have hNcomplex : (N : Complex) ≠ 0 := by exact_mod_cast hN
    have hden : (N : Complex) + z ≠ 0 := by
      intro hzero
      have hreal := congrArg Complex.re hzero
      simp only [Complex.add_re, Complex.natCast_re] at hreal
      norm_num at hreal
      linarith
    field_simp [hNcomplex, hden]
  have hlim : Tendsto
      (fun N : Nat => ∑ n ∈ Finset.range N, u n) atTop (𝓝 z⁻¹) := by
    have heq : (fun N : Nat => ∑ n ∈ Finset.range N, u n) =
        (fun N : Nat => z⁻¹ - ((N : Complex) + z)⁻¹) := by
      funext N
      exact hpartial N
    rw [heq]
    simpa using (tendsto_const_nhds.sub htail)
  exact tendsto_nhds_unique (hu.hasSum.tendsto_sum_nat) hlim

theorem test_corrected_reciprocal_series (z : Complex) (hz : 0 < z.re) :
    ∑' n : Nat, (1 / ((n : Complex) + z) - 1 / ((n : Complex) + 1)) =
      -(Real.eulerMascheroniConstant : Complex) - Complex.digamma z := by
  have hz1 : 0 < (z + 1).re := by
    norm_num [Complex.add_re]
    linarith
  have hanchor : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + (1 : Complex))⁻¹) := by
    simpa only [one_div] using
      (summable_halfAnchorGaussReciprocalSeries
        (z := (1 : Complex)) (by norm_num))
  have hzA : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z)⁻¹) := by
    exact summable_halfAnchorGaussReciprocalSeries hz
  have hz1A : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + (z + 1))⁻¹) := by
    exact summable_halfAnchorGaussReciprocalSeries hz1
  have hB : Summable (fun n : Nat =>
      1 / ((n : Complex) + (z + 1)) -
        1 / ((n : Complex) + (1 : Complex))) := by
    exact (hanchor.sub hz1A).congr (fun n => by ring)
  have hD : Summable (fun n : Nat =>
      1 / ((n : Complex) + z) -
        1 / ((n : Complex) + (z + 1))) := by
    exact (hz1A.sub hzA).congr (fun n => by ring)
  have hBValue : ∑' n : Nat,
      (1 / ((n : Complex) + (z + 1)) -
        1 / ((n : Complex) + (1 : Complex))) =
      -(Real.eulerMascheroniConstant : Complex) - Complex.digamma (z + 1) := by
    convert correctedEulerDigammaSeries hz using 1
    · apply tsum_congr
      intro n
      congr 1 <;> ring
  have hDValue : ∑' n : Nat,
      (1 / ((n : Complex) + z) -
        1 / ((n : Complex) + (z + 1))) = z⁻¹ := by
    simpa only [one_div] using test_halfAnchor_shift_reciprocal z hz
  have hsum : ∑' n : Nat,
      (1 / ((n : Complex) + z) - 1 / ((n : Complex) + 1)) =
      (∑' n : Nat,
        (1 / ((n : Complex) + (z + 1)) -
          1 / ((n : Complex) + (1 : Complex)))) +
        ∑' n : Nat,
          (1 / ((n : Complex) + z) -
            1 / ((n : Complex) + (z + 1))) := by
    rw [← hB.tsum_add hD]
    apply tsum_congr
    intro n
    ring
  rw [hsum, hBValue, hDValue]
  have hrec := Complex.digamma_apply_add_one z (by
    intro m hm
    have hreal := congrArg Complex.re hm
    norm_num at hreal
    have hmnonneg : (0 : Real) ≤ (m : Real) := by positivity
    linarith)
  rw [hrec]
  ring

example {z : Complex} (hz : 0 < z.re) :
    ∑' n : Nat,
      (((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z)⁻¹) =
      Complex.digamma z - Complex.digamma (1 / 2 : Complex) := by
  have hanchor : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + (1 : Complex))⁻¹) := by
    simpa only [one_div] using
      (summable_halfAnchorGaussReciprocalSeries
        (z := (1 : Complex)) (by norm_num))
  have hzA : Summable (fun n : Nat =>
      ((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z)⁻¹) :=
    summable_halfAnchorGaussReciprocalSeries hz
  have hcz : Summable (fun n : Nat =>
      1 / ((n : Complex) + z) - 1 / ((n : Complex) + (1 : Complex))) := by
    exact (hanchor.sub hzA).congr (fun n => by ring)
  have hsum : ∑' n : Nat,
      (((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + z)⁻¹) =
      (∑' n : Nat,
        (((n : Complex) + (1 / 2 : Complex))⁻¹ -
          ((n : Complex) + (1 : Complex))⁻¹)) -
        ∑' n : Nat,
          (1 / ((n : Complex) + z) -
            1 / ((n : Complex) + (1 : Complex))) := by
    rw [← hanchor.tsum_sub hcz]
    apply tsum_congr
    intro n
    ring
  rw [hsum]
  have hbase : ∑' n : Nat,
      (((n : Complex) + (1 / 2 : Complex))⁻¹ -
        ((n : Complex) + (1 : Complex))⁻¹) =
      -(Real.eulerMascheroniConstant : Complex) -
        Complex.digamma (1 / 2 : Complex) := by
    simpa only [one_div] using
      test_corrected_reciprocal_series (1 / 2 : Complex) (by norm_num)
  have hzValue := test_corrected_reciprocal_series z hz
  rw [hbase, hzValue]
  ring
